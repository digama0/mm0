//! Implements the bridge between mm0-rs and an editor via an lsp [`Connection`]
//!
//! [`Connection`]: ../../lsp_server/struct.Connection.html

use std::{fs, io};
use std::sync::{Arc, Mutex, atomic::{AtomicBool, Ordering}, Condvar};
use std::collections::{HashMap, HashSet, hash_map::{Entry, DefaultHasher}};
use std::hash::{Hash, Hasher};
use std::result::Result as StdResult;
use std::thread::{ThreadId, self};
use std::time::Instant;
use futures::{FutureExt, future::BoxFuture};
use futures::channel::oneshot::{Sender as FSender, channel};
use futures::executor::ThreadPool;
use futures::lock::Mutex as FMutex;
use lsp_server::*;
use serde::ser::Serialize;
use serde_json::{from_value, to_value};
use serde_repr::{Serialize_repr, Deserialize_repr};
use lsp_types::*;
use crossbeam::channel::{SendError, RecvError};
use clap::ArgMatches;
use crate::util::*;
use crate::lined_string::LinedString;
use crate::parser::{AST, parse};
use crate::mmu::import::elab as mmu_elab;
use crate::elab::{ElabError, self, FrozenEnv,
  environment::{ObjectKind, DeclKey, StmtTrace, AtomID, SortID, TermID, ThmID},
  FrozenLispKind, FrozenAtomData,
  local_context::InferSort, proof::Subst,
  lisp::{print::FormatEnv, pretty::Pretty, LispKind, Proc, BuiltinProc},
  spans::Spans};

// Disabled because vscode doesn't handle them properly
const USE_LOCATION_LINKS: bool = false;

#[derive(Debug)]
struct ServerError(BoxError);

type Result<T> = StdResult<T, ServerError>;

impl From<serde_json::Error> for ServerError {
  fn from(e: serde_json::error::Error) -> Self { ServerError(Box::new(e)) }
}

impl From<ProtocolError> for ServerError {
  fn from(e: ProtocolError) -> Self { ServerError(Box::new(e)) }
}

impl<T: Send + Sync + 'static> From<SendError<T>> for ServerError {
  fn from(e: SendError<T>) -> Self { ServerError(Box::new(e)) }
}

impl From<&'static str> for ServerError {
  fn from(e: &'static str) -> Self { ServerError(e.into()) }
}

impl From<io::Error> for ServerError {
  fn from(e: io::Error) -> Self { ServerError(Box::new(e)) }
}

impl From<BoxError> for ServerError {
  fn from(e: BoxError) -> Self { ServerError(e) }
}

impl From<String> for ServerError {
  fn from(e: String) -> Self { ServerError(e.into()) }
}

fn nos_id(nos: NumberOrString) -> RequestId {
  match nos {
    NumberOrString::Number(n) => n.into(),
    NumberOrString::String(s) => s.into(),
  }
}

type LogMessage = (Instant, ThreadId, usize, String);

lazy_static! {
  static ref LOGGER: (Mutex<Vec<LogMessage>>, Condvar) = Default::default();
  static ref SERVER: Server = Server::new().expect("Initialization failed");
}

static LOG_ERRORS: AtomicBool = AtomicBool::new(true);
pub(crate) fn get_log_errors() -> bool { LOG_ERRORS.load(Ordering::Relaxed) }

#[allow(unused)]
pub(crate) fn log(s: String) {
  LOGGER.0.lock().unwrap().push((Instant::now(), thread::current().id(), get_memory_usage(), s));
  LOGGER.1.notify_one();
}

#[allow(unused)]
macro_rules! log {
  ($($es:tt)*) => {crate::server::log(format!($($es)*))}
}

async fn elaborate(path: FileRef, start: Option<Position>,
    cancel: Arc<AtomicBool>) -> Result<Option<(u64, FrozenEnv)>> {
  let Server {vfs, pool, ..} = &*SERVER;
  let (path, file) = vfs.get_or_insert(path)?;
  let v = file.text.lock().unwrap().0;
  let (old_ast, old_env, old_deps) = {
    let mut g = file.parsed.lock().await;
    let (old, res, senders) = match &mut *g {
      None => (None, (None, None, vec![]), vec![]),
      &mut Some(FileCache::InProgress {version, ref cancel, ref mut senders, ..}) => {
        if v == version {
          let (send, recv) = channel();
          senders.push(send);
          drop(g);
          return Ok(recv.await.ok())
        }
        cancel.store(true, Ordering::SeqCst);
        if let Some(FileCache::InProgress {old, senders, ..}) = g.take() {
          (old, (None, None, vec![]), senders)
        } else {unsafe {std::hint::unreachable_unchecked()}}
      }
      &mut Some(FileCache::Ready {hash, ref deps, ref env, ..}) => {
        let hasher = &mut DefaultHasher::new();
        v.hash(hasher);
        let matches = (|| -> bool {
          for path in deps {
            if let Some(file) = vfs.get(path) {
              if let Some(g) = file.parsed.try_lock() {
                if let Some(FileCache::Ready {hash, ..}) = *g {
                  hash.hash(hasher);
                } else {return false}
              } else {return false}
            } else {return false}
          }
          hasher.finish() == hash
        })();
        if matches { return Ok(Some((hash, env.clone()))) }
        if let Some(FileCache::Ready {ast, source, errors, deps, env, ..}) = g.take() {
          (Some((source.clone(), env.clone())),
            (start.map(|s| (s, source, ast)), Some((errors, env)), deps), vec![])
        } else {unsafe {std::hint::unreachable_unchecked()}}
      }
    };
    *g = Some(FileCache::InProgress {old, version: v, cancel: cancel.clone(), senders});
    res
  };
  let (version, text) = file.text.lock().unwrap().clone();
  let old_ast = old_ast.and_then(|(s, old_text, ast)|
    if Arc::ptr_eq(&text, &old_text) {Some((s, ast))} else {None});
  let mut hasher = DefaultHasher::new();
  version.hash(&mut hasher);
  let source = text.clone();
  let (idx, ast) = parse(text, old_ast);
  let ast = Arc::new(ast);

  let mut deps = Vec::new();
  let (toks, errors, env) = if path.has_extension("mmb") {
    unimplemented!()
  } else if path.has_extension("mmu") {
    let (error, env) = mmu_elab(path.clone(), ast.source.as_bytes());
    (vec![], if let Err(e) = error {vec![e]} else {vec![]}, FrozenEnv::new(env))
  } else {
    elab::elaborate(
      ast.clone(), path.clone(), path.has_extension("mm0"),
      crate::get_check_proofs(), cancel.clone(),
      old_env.map(|(errs, e)| (idx, errs, e)),
      |path| {
        let path = vfs.get_or_insert(path)?.0;
        let (send, recv) = channel();
        pool.spawn_ok(elaborate_and_send(path.clone(), Default::default(), send));
        deps.push(path);
        Ok(recv)
      }).await
  };
  for tok in toks {tok.hash(&mut hasher)}
  let hash = hasher.finish();
  log!("elabbed {:?}", path);
  let mut g = file.parsed.lock().await;
  if cancel.load(Ordering::SeqCst) { return Ok(None) }
  let mut srcs = HashMap::new();
  let mut to_loc = |fsp: &FileSpan| -> Location {
    if fsp.file.ptr_eq(&path) {
      &ast.source
    } else {
      srcs.entry(fsp.file.ptr()).or_insert_with(||
        vfs.0.lock().unwrap().get(&fsp.file).unwrap()
          .text.lock().unwrap().1.clone())
    }.to_loc(fsp)
  };

  let (mut n_errs, mut n_warns, mut n_infos, mut n_hints) = (0, 0, 0, 0);
  let errs: Vec<_> = ast.errors.iter().map(|e| e.to_diag(&ast.source))
    .chain(errors.iter().map(|e| e.to_diag(&ast.source, &mut to_loc)))
    .filter(|e| !e.message.is_empty())
    .inspect(|err| match err.severity {
      None => {}
      Some(DiagnosticSeverity::Error) => n_errs += 1,
      Some(DiagnosticSeverity::Warning) => n_warns += 1,
      Some(DiagnosticSeverity::Information) => n_infos += 1,
      Some(DiagnosticSeverity::Hint) => n_hints += 1,
    }).collect();

  send_diagnostics(path.url().clone(), version, errs)?;

  use std::fmt::Write;
  let mut log_msg = format!("diagged {:?}, {} errors", path, n_errs);
  if n_warns != 0 { write!(&mut log_msg, ", {} warnings", n_warns).unwrap() }
  if n_infos != 0 { write!(&mut log_msg, ", {} infos", n_infos).unwrap() }
  if n_hints != 0 { write!(&mut log_msg, ", {} hints", n_hints).unwrap() }
  if get_log_errors() {
    for e in &errors {
      let Position {line, character: col} = ast.source.to_pos(e.pos.start);
      write!(&mut log_msg, "\n\n{}: {}:{}:{}:\n{}",
        e.level, path.rel(), line+1, col+1, e.kind.msg()).unwrap();
    }
  }
  log(log_msg);

  vfs.update_downstream(&old_deps, &deps, &path);
  if let Some(FileCache::InProgress {senders, ..}) = g.take() {
    for s in senders {
      let _ = s.send((hash, env.clone()));
    }
  }
  *g = Some(FileCache::Ready {hash, source, ast, errors, deps, env: env.clone()});
  drop(g);
  for d in file.downstream.lock().unwrap().iter() {
    log!("{:?} affects {:?}", path, d);
    pool.spawn_ok(dep_change(d.clone()));
  }
  Ok(Some((hash, env)))
}

async fn elaborate_and_report(path: FileRef, start: Option<Position>, cancel: Arc<AtomicBool>) {
  if let Err(e) = std::panic::AssertUnwindSafe(elaborate(path, start, cancel))
      .catch_unwind().await
      .unwrap_or_else(|_| Err("server panic".into())) {
    log_message(format!("{:?}", e)).unwrap();
  }
}

fn elaborate_and_send(path: FileRef,
  cancel: Arc<AtomicBool>, send: FSender<(u64, FrozenEnv)>) ->
  BoxFuture<'static, ()> {
  async {
    if let Ok(Some(env)) = elaborate(path, Some(Position::default()), cancel).await {
      let _ = send.send(env);
    }
  }.boxed()
}

fn dep_change(path: FileRef) -> BoxFuture<'static, ()> {
  elaborate_and_report(path, None, Default::default()).boxed()
}

#[derive(DeepSizeOf)]
enum FileCache {
  InProgress {
    old: Option<(Arc<LinedString>, FrozenEnv)>,
    version: Option<i64>,
    cancel: Arc<AtomicBool>,
    senders: Vec<FSender<(u64, FrozenEnv)>>,
  },
  Ready {
    hash: u64,
    source: Arc<LinedString>,
    ast: Arc<AST>,
    errors: Vec<ElabError>,
    env: FrozenEnv,
    deps: Vec<FileRef>,
  }
}

#[derive(DeepSizeOf)]
struct VirtualFile {
  /// File data, saved (true) or unsaved (false)
  text: Mutex<(Option<i64>, Arc<LinedString>)>,
  /// File parse
  parsed: FMutex<Option<FileCache>>,
  /// Files that depend on this one
  downstream: Mutex<HashSet<FileRef>>,
}

impl VirtualFile {
  fn new(version: Option<i64>, text: String) -> VirtualFile {
    VirtualFile {
      text: Mutex::new((version, Arc::new(text.into()))),
      parsed: FMutex::new(None),
      downstream: Mutex::new(HashSet::new())
    }
  }
}

#[derive(DeepSizeOf)]
struct VFS(Mutex<HashMap<FileRef, Arc<VirtualFile>>>);

impl VFS {
  fn get(&self, path: &FileRef) -> Option<Arc<VirtualFile>> {
    self.0.lock().unwrap().get(path).cloned()
  }

  fn get_or_insert(&self, path: FileRef) -> io::Result<(FileRef, Arc<VirtualFile>)> {
    match self.0.lock().unwrap().entry(path) {
      Entry::Occupied(e) => Ok((e.key().clone(), e.get().clone())),
      Entry::Vacant(e) => {
        let path = e.key().clone();
        let s = fs::read_to_string(path.path())?;
        let val = e.insert(Arc::new(VirtualFile::new(None, s))).clone();
        Ok((path, val))
      }
    }
  }

  fn source(&self, file: &FileRef) -> Arc<LinedString> {
    self.0.lock().unwrap().get(&file).unwrap().text.lock().unwrap().1.clone()
  }

  fn open_virt(&self, path: FileRef, version: i64, text: String) -> Result<Arc<VirtualFile>> {
    let pool = &SERVER.pool;
    let file = Arc::new(VirtualFile::new(Some(version), text));
    let file = match self.0.lock().unwrap().entry(path.clone()) {
      Entry::Occupied(entry) => {
        for dep in entry.get().downstream.lock().unwrap().iter() {
          pool.spawn_ok(dep_change(dep.clone()));
        }
        file
      }
      Entry::Vacant(entry) => entry.insert(file).clone()
    };
    pool.spawn_ok(elaborate_and_report(path, Some(Position::default()),
      Arc::new(AtomicBool::new(false))));
    Ok(file)
  }

  fn close(&self, path: &FileRef) -> Result<()> {
    let mut g = self.0.lock().unwrap();
    if let Entry::Occupied(e) = g.entry(path.clone()) {
      if e.get().downstream.lock().unwrap().is_empty() {
        send_diagnostics(path.url().clone(), None, vec![])?;
        e.remove();
      } else if e.get().text.lock().unwrap().0.take().is_some() {
        let file = e.get().clone();
        drop(g);
        let pool = &SERVER.pool;
        for dep in file.downstream.lock().unwrap().clone() {
          pool.spawn_ok(dep_change(dep.clone()));
        }
      }
    }
    Ok(())
  }

  fn update_downstream(&self, old_deps: &[FileRef], deps: &[FileRef], to: &FileRef) {
    for from in old_deps {
      if !deps.contains(from) {
        let file = self.0.lock().unwrap().get(from).unwrap().clone();
        file.downstream.lock().unwrap().remove(to);
      }
    }
    for from in deps {
      if !old_deps.contains(from) {
        let file = self.0.lock().unwrap().get(from).unwrap().clone();
        file.downstream.lock().unwrap().insert(to.clone());
      }
    }
  }
}

enum RequestType {
  Completion(CompletionParams),
  CompletionResolve(Box<CompletionItem>),
  Hover(TextDocumentPositionParams),
  Definition(TextDocumentPositionParams),
  DocumentSymbol(DocumentSymbolParams),
  References(ReferenceParams),
  DocumentHighlight(DocumentHighlightParams),
}

fn parse_request(Request {id, method, params}: Request) -> Result<Option<(RequestId, RequestType)>> {
  Ok(match method.as_str() {
    "textDocument/completion"        => Some((id, RequestType::Completion(from_value(params)?))),
    "completionItem/resolve"         => Some((id, RequestType::CompletionResolve(from_value(params)?))),
    "textDocument/hover"             => Some((id, RequestType::Hover(from_value(params)?))),
    "textDocument/definition"        => Some((id, RequestType::Definition(from_value(params)?))),
    "textDocument/documentSymbol"    => Some((id, RequestType::DocumentSymbol(from_value(params)?))),
    "textDocument/references"        => Some((id, RequestType::References(from_value(params)?))),
    "textDocument/documentHighlight" => Some((id, RequestType::DocumentHighlight(from_value(params)?))),
    _ => None
  })
}

fn send_message<T: Into<Message>>(t: T) -> Result<()> {
  Ok(SERVER.conn.sender.send(t.into())?)
}

#[allow(unused)]
fn show_message(typ: MessageType, message: String) -> Result<()> {
  send_message(Notification {
    method: "window/showMessage".to_owned(),
    params: to_value(ShowMessageParams {typ, message})?
  })
}

#[allow(unused)]
fn register_capability(id: String, registrations: Vec<Registration>) -> Result<()> {
  send_message(Request {
    id: id.into(),
    method: "client/registerCapability".to_owned(),
    params: to_value(RegistrationParams {registrations})?
  })
}

#[allow(unused)]
fn log_message(message: String) -> Result<()> {
  send_message(Notification {
    method: "window/logMessage".to_owned(),
    params: to_value(LogMessageParams {typ: MessageType::Log, message})?
  })
}

fn send_diagnostics(uri: Url, version: Option<i64>, diagnostics: Vec<Diagnostic>) -> Result<()> {
  send_message(Notification {
    method: "textDocument/publishDiagnostics".to_owned(),
    params: to_value(PublishDiagnosticsParams {uri, version, diagnostics})?
  })
}

type OpenRequests = Mutex<HashMap<RequestId, Arc<AtomicBool>>>;

struct RequestHandler {
  id: RequestId,
  #[allow(unused)]
  cancel: Arc<AtomicBool>,
}

impl RequestHandler {
  async fn handle(self, req: RequestType) -> Result<()> {
    match req {
      RequestType::Hover(TextDocumentPositionParams {text_document: doc, position}) =>
        self.finish(hover(doc.uri.into(), position).await),
      RequestType::Definition(TextDocumentPositionParams {text_document: doc, position}) =>
        if USE_LOCATION_LINKS && matches!(SERVER.caps.lock().unwrap().definition_location_links, Some(true)) {
          self.finish(definition(doc.uri.into(), position,
            |text, text2, src, &FileSpan {ref file, span}, full| LocationLink {
              origin_selection_range: Some(text.to_range(src)),
              target_uri: file.url().clone(),
              target_range: text2.to_range(full),
              target_selection_range: text2.to_range(span),
            }).await)
        } else {
          self.finish(definition(doc.uri.into(), position,
            |_, text2, _, &FileSpan {ref file, span}, _| Location {
              uri: file.url().clone(),
              range: text2.to_range(span),
            }).await)
        },
      RequestType::DocumentSymbol(DocumentSymbolParams {text_document: doc, ..}) =>
        self.finish(document_symbol(doc.uri.into()).await),
      RequestType::Completion(p) => {
        let doc = p.text_document_position;
        self.finish(completion(doc.text_document.uri.into(), doc.position).await)
      }
      RequestType::CompletionResolve(ci) =>
        self.finish(completion_resolve(*ci).await),
      RequestType::References(ReferenceParams {text_document_position: doc, context, ..}) => {
        let file: FileRef = doc.text_document.uri.into();
        self.finish(references(file.clone(), doc.position, context.include_declaration,
          |range| Location { uri: file.url().clone(), range }).await)
      }
      RequestType::DocumentHighlight(DocumentHighlightParams {text_document_position_params: doc, ..}) => {
        let file: FileRef = doc.text_document.uri.into();
        self.finish(references(file.clone(), doc.position, true,
          |range| DocumentHighlight { range, kind: None }).await)
      }
    }
  }

  fn finish<T: Serialize>(self, resp: StdResult<T, ResponseError>) -> Result<()> {
    let Server {reqs, conn, ..} = &*SERVER;
    reqs.lock().unwrap().remove(&self.id);
    conn.sender.send(Message::Response(match resp {
      Ok(val) => Response { id: self.id, result: Some(to_value(val).unwrap()), error: None },
      Err(e) => Response { id: self.id, result: None, error: Some(e) }
    }))?;
    Ok(())
  }
}

async fn hover(path: FileRef, pos: Position) -> StdResult<Option<Hover>, ResponseError> {
  let Server {vfs, ..} = &*SERVER;
  macro_rules! or {($ret:expr, $e:expr)  => {match $e {
    Some(x) => x,
    None => return $ret
  }}}
  let file = vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "hover nonexistent file"))?;
  let text = file.text.lock().unwrap().1.clone();
  let idx = or!(Ok(None), text.to_idx(pos));
  let env = elaborate(path, Some(Position::default()), Default::default())
    .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?
    .ok_or_else(|| response_err(ErrorCode::RequestCanceled, ""))?.1;
  let env = unsafe { env.thaw() };
  let fe = FormatEnv { source: &text, env };
  let spans = or!(Ok(None), Spans::find(&env.spans, idx));
  enum HoverType { Doc, MM0 }
  use HoverType::*;
  let mut res: Vec<(Span, HoverType, String)> = vec![];
  for &(sp, ref k) in spans.find_pos(idx) {
    if let Some((r, doc)) = (|| Some(match k {
      &ObjectKind::Sort(s) => {
        let sd = &env.sorts[s];
        ((sp, MM0, format!("{}", sd)), sd.doc.clone())
      }
      &ObjectKind::Term(t, sp1) => {
        let td = &env.terms[t];
        ((sp1, MM0, format!("{}", fe.to(td))), td.doc.clone())
      }
      &ObjectKind::Thm(t) => {
        let td = &env.thms[t];
        ((sp, MM0, format!("{}", fe.to(td))), td.doc.clone())
      }
      &ObjectKind::Var(x) => ((sp, MM0, match spans.lc.as_ref().and_then(|lc| lc.vars.get(&x)) {
        Some((_, InferSort::Bound(sort))) => format!("{{{}: {}}}", fe.to(&x), fe.to(sort)),
        Some((_, InferSort::Reg(sort, deps))) => {
          let mut s = format!("({}: {}", fe.to(&x), fe.to(sort));
          for &a in &**deps {
            s += " ";
            s += &String::from_utf8_lossy(&env.data[a].name)
          }
          s + ")"
        }
        _ => return None,
      }), None),
      ObjectKind::Expr(e) => {
        let head = e.uncons().next().unwrap_or(e);
        let sp1 = head.fspan().map_or(sp, |fsp| fsp.span);
        let a = head.as_atom()?;
        let (s, doc) = if let Some(DeclKey::Term(t)) = env.data[a].decl {
          let td = &env.terms[t];
          (td.ret.0, td.doc.clone())
        } else {
          (spans.lc.as_ref()?.vars.get(&a)?.1.sort()?, None)
        };
        let mut out = String::new();
        fe.pretty(|p| p.expr(unsafe {e.thaw()}).render_fmt(80, &mut out).unwrap());
        use std::fmt::Write;
        write!(out, ": {}", fe.to(&s)).unwrap();
        ((sp1, MM0, out), doc)
      }
      ObjectKind::Proof(p) => {
        if let Some(e) = p.as_atom().and_then(|x|
          spans.lc.as_ref().and_then(|lc|
            lc.proofs.get(&x).map(|&i| &lc.proof_order[i].1))) {
          let mut out = String::new();
          fe.pretty(|p| p.hyps_and_ret(Pretty::nil(), std::iter::empty(), e)
            .render_fmt(80, &mut out).unwrap());
          ((sp, MM0, out), None)
        } else {
          let mut u = p.uncons();
          let head = u.next()?;
          let sp1 = head.fspan().map_or(sp, |fsp| fsp.span);
          let a = head.as_atom()?;
          if let Some(DeclKey::Thm(t)) = env.data[a].decl {
            let td = &env.thms[t];
            res.push((sp, MM0, format!("{}", fe.to(td))));
            let mut args = vec![];
            for _ in 0..td.args.len() {
              args.push(unsafe {u.next()?.thaw()}.clone());
            }
            let mut subst = Subst::new(&env, &td.heap, args);
            let mut out = String::new();
            let ret = subst.subst(&td.ret);
            fe.pretty(|p| p.hyps_and_ret(Pretty::nil(),
              td.hyps.iter().map(|(_, h)| subst.subst(h)),
              &ret).render_fmt(80, &mut out).unwrap());
            ((sp1, MM0, out), td.doc.clone())
          } else {return None}
        }
      }
      // Note: Uncomment this to turn on lisp syntax documentation.
      // &ObjectKind::Syntax(stx) => (sp, Doc, stx.doc().into()),
      ObjectKind::Syntax(_) => return None,
      &ObjectKind::Global(a) => {
        let (_, doc, val) = &env.data[a].lisp.as_ref()?;
        if let Some(doc) = doc {
          ((sp, Doc, doc.as_str().into()), None)
        } else {
          let bp = val.unwrapped(|e| match e {
            &LispKind::Proc(Proc::Builtin(p)) => Some(p),
            _ => None
          })?;
          ((sp, Doc, bp.doc().into()), None)
        }
      }
      ObjectKind::Import(_) => return None,
    }))() {
      let sp = r.0;
      res.push(r);
      if let Some(doc) = doc {
        res.push((sp, Doc, doc.as_str().into()))
      }
    }
  }
  if res.is_empty() {return Ok(None)}
  Ok(Some(Hover {
    range: Some(text.to_range(res[0].0)),
    contents: HoverContents::Array(res.into_iter().map(|(_, ty, value)| {
      match ty {
        Doc => MarkedString::String(value),
        MM0 => MarkedString::LanguageString(
          LanguageString { language: "metamath-zero".into(), value })
      }
    }).collect())
  }))
}

async fn definition<T>(path: FileRef, pos: Position,
    f: impl Fn(&LinedString, &LinedString, Span, &FileSpan, Span) -> T) ->
    StdResult<Vec<T>, ResponseError> {
  let Server {vfs, ..} = &*SERVER;
  macro_rules! or_none {($e:expr)  => {match $e {
    Some(x) => x,
    None => return Ok(vec![])
  }}}
  let file = vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "goto definition nonexistent file"))?;
  let text = file.text.lock().unwrap().1.clone();
  let idx = or_none!(text.to_idx(pos));
  let env = elaborate(path.clone(), Some(Position::default()), Default::default())
    .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?
    .ok_or_else(|| response_err(ErrorCode::RequestCanceled, ""))?.1;
  let spans = or_none!(env.find(idx));
  let mut res = vec![];
  for &(sp, ref k) in spans.find_pos(idx) {
    let g = |fsp: &FileSpan, full|
      if fsp.file.ptr_eq(&path) {
        f(&text, &text, sp, fsp, full)
      } else {
        f(&text, &vfs.source(&fsp.file), sp, fsp, full)
      };
    let sort = |s| {
      let sd = env.sort(s);
      g(&sd.span, sd.full)
    };
    let term = |t| {
      let td = env.term(t);
      g(&td.span, td.full)
    };
    let thm = |t| {
      let td = env.thm(t);
      g(&td.span, td.full)
    };
    match k {
      &ObjectKind::Sort(s) => res.push(sort(s)),
      &ObjectKind::Term(t, _) => res.push(term(t)),
      &ObjectKind::Thm(t) => res.push(thm(t)),
      ObjectKind::Var(_) => {}
      ObjectKind::Expr(e) => {
        let head = e.uncons().next().unwrap_or(e);
        if let Some(DeclKey::Term(t)) = head.as_atom().and_then(|a| env.data()[a].decl()) {
          res.push(term(t))
        }
      },
      ObjectKind::Proof(p) =>
        if let Some(DeclKey::Thm(t)) = p.uncons().next()
            .and_then(|head| head.as_atom()).and_then(|a| env.data()[a].decl()) {
          res.push(thm(t))
        },
      &ObjectKind::Global(a) => {
        let ad = &env.data()[a];
        match ad.decl() {
          Some(DeclKey::Term(t)) => res.push(term(t)),
          Some(DeclKey::Thm(t)) => res.push(thm(t)),
          None => {}
        }
        if let Some(s) = ad.sort() {res.push(sort(s))}
        if let Some((Some((ref fsp, full)), _, _)) = *ad.lisp() {
          res.push(g(&fsp, full))
        } else if let Some(sp) = ad.graveyard() {
          res.push(g(&sp.0, sp.1))
        }
      }
      ObjectKind::Syntax(_) => {}
      ObjectKind::Import(file) => {
        res.push(g(&FileSpan {file: file.clone(), span: 0.into()}, 0.into()))
      },
    }
  }
  Ok(res)
}

#[allow(deprecated)] // workaround rust#60681
async fn document_symbol(path: FileRef) -> StdResult<DocumentSymbolResponse, ResponseError> {
  let Server {vfs, ..} = &*SERVER;
  let file = vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "document symbol nonexistent file"))?;
  let text = file.text.lock().unwrap().1.clone();
  let env = elaborate(path.clone(), Some(Position::default()), Default::default())
    .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?
    .ok_or_else(|| response_err(ErrorCode::RequestCanceled, ""))?.1;
  let fe = unsafe { env.format_env(&text) };
  let f = |sp, name: &ArcString, desc, full, kind| DocumentSymbol {
    name: String::from_utf8_lossy(name).into(),
    detail: Some(desc),
    kind,
    #[allow(deprecated)] deprecated: None,
    range: text.to_range(full),
    selection_range: text.to_range(sp),
    children: None,
  };
  let mut res = vec![];
  macro_rules! push {($fsp:expr, $($e:expr),*) => {
    if $fsp.file == path { res.push(f($fsp.span, $($e),*)) }
  }}
  for s in env.stmts() {
    match *s {
      StmtTrace::Sort(a) => {
        let ad = &env.data()[a];
        let s = ad.sort().unwrap();
        let sd = env.sort(s);
        push!(sd.span, ad.name(), format!("{}", sd), sd.full, SymbolKind::Class)
      }
      StmtTrace::Decl(a) => {
        let ad = &env.data()[a];
        match ad.decl().unwrap() {
          DeclKey::Term(t) => {
            let td = env.term(t);
            push!(td.span, ad.name(), format!("{}", fe.to(td)), td.full, SymbolKind::Constructor)
          }
          DeclKey::Thm(t) => {
            let td = env.thm(t);
            push!(td.span, ad.name(), format!("{}", fe.to(td)), td.full, SymbolKind::Method)
          }
        }
      }
      StmtTrace::Global(a) => {
        let ad = &env.data()[a];
        if let Some((Some((ref fsp, full)), _, ref e)) = *ad.lisp() {
          push!(fsp, ad.name(), format!("{}", fe.to(unsafe { e.thaw() })), full,
            match (|| Some({
              let r = &**e.unwrap();
              match r {
                FrozenLispKind::Atom(_) |
                FrozenLispKind::MVar(_, _) |
                FrozenLispKind::Goal(_) => SymbolKind::Constant,
                FrozenLispKind::List(_) |
                FrozenLispKind::DottedList(_, _) =>
                  if r.is_list() {SymbolKind::Array} else {SymbolKind::Object},
                FrozenLispKind::Number(_) => SymbolKind::Number,
                FrozenLispKind::String(_) => SymbolKind::String,
                FrozenLispKind::Bool(_) => SymbolKind::Boolean,
                FrozenLispKind::Syntax(_) => SymbolKind::Event,
                FrozenLispKind::Undef => return None,
                FrozenLispKind::Proc(_) => SymbolKind::Function,
                FrozenLispKind::AtomMap(_) |
                FrozenLispKind::Annot(_, _) |
                FrozenLispKind::Ref(_) => SymbolKind::Object,
              }
            }))() {
              Some(sk) => sk,
              None => continue,
            });
        }
      }
      StmtTrace::OutputString(_) => {}
    }
  }
  Ok(DocumentSymbolResponse::Nested(res))
}

#[derive(Serialize_repr, Deserialize_repr)]
#[repr(u8)]
enum TraceKind {Sort, Decl, Global}

fn make_completion_item(path: &FileRef, fe: FormatEnv<'_>, ad: &FrozenAtomData, detail: bool, tk: TraceKind) -> Option<CompletionItem> {
  use CompletionItemKind::*;
  macro_rules! done {($desc:expr, $kind:expr) => {
    CompletionItem {
      label: String::from_utf8_lossy(ad.name()).into(),
      detail: if detail {Some($desc)} else {None},
      kind: Some($kind),
      data: Some(to_value((path.url(), tk)).unwrap()),
      ..Default::default()
    }
  }}
  match tk {
    TraceKind::Sort => ad.sort().map(|s| {
      let sd = &fe.sorts[s];
      done!(format!("{}", sd), Class)
    }),
    TraceKind::Decl => ad.decl().map(|dk| match dk {
      DeclKey::Term(t) => {let td = &fe.terms[t]; done!(format!("{}", fe.to(td)), Constructor)}
      DeclKey::Thm(t) => {let td = &fe.thms[t]; done!(format!("{}", fe.to(td)), Method)}
    }),
    TraceKind::Global => ad.lisp().as_ref().map(|(_, _, e)| {
      done!(format!("{}", fe.to(unsafe {e.thaw()})), match **e.unwrap() {
        FrozenLispKind::Atom(_) |
        FrozenLispKind::MVar(_, _) |
        FrozenLispKind::Goal(_) => CompletionItemKind::Constant,
        FrozenLispKind::List(_) |
        FrozenLispKind::DottedList(_, _) |
        FrozenLispKind::Undef |
        FrozenLispKind::Number(_) |
        FrozenLispKind::String(_) |
        FrozenLispKind::Bool(_) |
        FrozenLispKind::AtomMap(_) |
        FrozenLispKind::Annot(_, _) |
        FrozenLispKind::Ref(_) => CompletionItemKind::Value,
        FrozenLispKind::Syntax(_) => CompletionItemKind::Event,
        FrozenLispKind::Proc(_) => CompletionItemKind::Function,
      })
    })
  }
}

async fn completion(path: FileRef, _pos: Position) -> StdResult<CompletionResponse, ResponseError> {
  let Server {vfs, ..} = &*SERVER;
  let file = vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "document symbol nonexistent file"))?;
  let old = if let Some(g) = file.parsed.try_lock() {
    g.as_ref().and_then(|fc| match fc {
      FileCache::Ready {source, env, ..} => Some((source.clone(), env.clone())),
      FileCache::InProgress {old, ..} => old.clone()
    })
  } else {None};
  let (text, env) = match old {
    Some(old) => old,
    None => {
      let env = elaborate(path.clone(), Some(Position::default()), Default::default())
        .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?
        .ok_or_else(|| response_err(ErrorCode::RequestCanceled, ""))?.1;
      (file.text.lock().unwrap().1.clone(), env)
    }
  };
  let fe = unsafe { env.format_env(&text) };
  let mut res = vec![];
  for ad in env.data().iter() {
    if let Some(ci) = make_completion_item(&path, fe, ad, false, TraceKind::Sort) {res.push(ci)}
    if let Some(ci) = make_completion_item(&path, fe, ad, false, TraceKind::Decl) {res.push(ci)}
    if let Some(ci) = make_completion_item(&path, fe, ad, false, TraceKind::Global) {res.push(ci)}
  }
  Ok(CompletionResponse::Array(res))
}

async fn completion_resolve(ci: CompletionItem) -> StdResult<CompletionItem, ResponseError> {
  let Server {vfs, ..} = &*SERVER;
  let data = ci.data.ok_or_else(|| response_err(ErrorCode::InvalidRequest, "missing data"))?;
  let (uri, tk): (Url, TraceKind) = from_value(data).map_err(|e|
    response_err(ErrorCode::InvalidRequest, format!("bad JSON {:?}", e)))?;
  let path = uri.into();
  let file = vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "document symbol nonexistent file"))?;
  let text = file.text.lock().unwrap().1.clone();
  let env = elaborate(path.clone(), Some(Position::default()), Default::default())
    .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?
    .ok_or_else(|| response_err(ErrorCode::RequestCanceled, ""))?.1;
  let fe = unsafe { env.format_env(&text) };
  env.get_atom(ci.label.as_bytes()).and_then(|a| make_completion_item(&path, fe, &env.data()[a], true, tk))
    .ok_or_else(|| response_err(ErrorCode::ContentModified, "completion missing"))
}

async fn references<T>(path: FileRef, pos: Position, include_self: bool, f: impl Fn(Range) -> T) -> StdResult<Vec<T>, ResponseError> {
  let Server {vfs, ..} = &*SERVER;
  macro_rules! or_none {($e:expr)  => {match $e {
    Some(x) => x,
    None => return Ok(vec![])
  }}}
  let file = vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "references: nonexistent file"))?;
  let text = file.text.lock().unwrap().1.clone();
  let idx = or_none!(text.to_idx(pos));
  let env = elaborate(path, Some(Position::default()), Default::default())
    .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?
    .ok_or_else(|| response_err(ErrorCode::RequestCanceled, ""))?.1;
  let spans = or_none!(env.find(idx));
  #[derive(Copy, Clone, PartialEq, Eq)]
  enum Key {
    Var(AtomID),
    Sort(SortID),
    Term(TermID),
    Thm(ThmID),
    Global(AtomID),
  }
  let to_key = |k: &ObjectKind| match *k {
    ObjectKind::Expr(ref e) => {
      let a = e.uncons().next().unwrap_or(e).as_atom()?;
      if let Some(DeclKey::Term(t)) = env.data()[a].decl() {
        Some(Key::Term(t))
      } else {
        Some(Key::Var(a))
      }
    }
    ObjectKind::Proof(ref p) => {
      let a = p.uncons().next().unwrap_or(p).as_atom()?;
      if let Some(DeclKey::Thm(t)) = env.data()[a].decl() {
        Some(Key::Thm(t))
      } else {
        Some(Key::Var(a))
      }
    }
    ObjectKind::Import(_) |
    ObjectKind::Syntax(_) => None,
    ObjectKind::Var(a) => Some(Key::Var(a)),
    ObjectKind::Sort(a) => Some(Key::Sort(a)),
    ObjectKind::Term(a, _) => Some(Key::Term(a)),
    ObjectKind::Thm(a) => Some(Key::Thm(a)),
    ObjectKind::Global(a) => Some(Key::Global(a)),
  };

  let mut res = vec![];
  for &(sp, ref k) in spans.find_pos(idx) {
    let key = match to_key(k) {Some(k) => k, _ => continue};
    use std::convert::TryFrom;
    match key {
      Key::Global(a) if BuiltinProc::try_from(&**env.data()[a].name()).is_ok() => continue,
      _ => {}
    }
    let mut cont = |&(sp2, ref k2)| {
      let eq = match *k2 {
        ObjectKind::Expr(_) if !matches!(key, Key::Term(_) | Key::Var(_)) => false,
        ObjectKind::Proof(_) if !matches!(key, Key::Thm(_) | Key::Var(_)) => false,
        _ => Some(key) == to_key(k2),
      };
      if eq && (include_self || sp != sp2) {
        let sp2 = if let ObjectKind::Term(_, sp2) = *k2 {sp2} else {sp2};
        res.push(f(text.to_range(sp2)))
      }
    };
    if let Key::Var(_) = key {
      spans.into_iter().for_each(&mut cont);
    } else {
      for spans2 in env.spans() {
        spans2.into_iter().for_each(&mut cont);
      }
    }
  }
  Ok(res)
}

struct Server {
  conn: Connection,
  #[allow(unused)]
  params: InitializeParams,
  caps: Mutex<Capabilities>,
  reqs: OpenRequests,
  vfs: VFS,
  pool: ThreadPool,
}

struct Capabilities {
  reg_id: Option<RequestId>,
  definition_location_links: Option<bool>,
}

impl Capabilities {
  fn new(params: &InitializeParams) -> Capabilities {
    let dll = match params.capabilities.text_document.as_ref()
      .and_then(|d| d.definition.as_ref()) {
      Some(&GotoCapability {link_support: Some(b), ..}) => Some(b),
      Some(GotoCapability {dynamic_registration: Some(true), ..}) => Some(true),
      _ => Some(false)
    };
    Capabilities { reg_id: None, definition_location_links: dll }
  }

  fn register(&mut self) -> Result<()> {
    assert!(self.reg_id.is_none());
    let mut regs = vec![];
    if USE_LOCATION_LINKS && self.definition_location_links.is_none() {
      regs.push(Registration {
        id: String::new(),
        method: "textDocument/definition".into(),
        register_options: None
      })
    }
    if !regs.is_empty() {
      register_capability("regs".into(), regs)?;
      self.reg_id = Some(String::from("regs").into());
    }
    Ok(())
  }

  fn finish_register(&mut self, resp: Response) {
    assert!(self.reg_id.take().is_some());
    match resp {
      Response {result: None, error: None, ..} =>
        self.definition_location_links = Some(true),
      _ => self.definition_location_links = Some(false)
    }
  }
}

impl Server {
  fn new() -> Result<Server> {
    let (conn, _iot) = Connection::stdio();
    let params = from_value(conn.initialize(
      to_value(ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::Incremental)),
        hover_provider: Some(true.into()),
        completion_provider: Some(CompletionOptions {
          resolve_provider: Some(true),
          ..Default::default()
        }),
        definition_provider: Some(true),
        document_symbol_provider: Some(true),
        references_provider: Some(true),
        document_highlight_provider: Some(true),
        ..Default::default()
      })?
    )?)?;
    Ok(Server {
      caps: Mutex::new(Capabilities::new(&params)),
      params,
      conn,
      reqs: Mutex::new(HashMap::new()),
      vfs: VFS(Mutex::new(HashMap::new())),
      pool: ThreadPool::new()?
    })
  }

  fn run(&self) {
    crossbeam::scope(|s| {
      s.spawn(move |_| {
        let mut now = Instant::now();
        loop {
          for (i, id, mem, s) in LOGGER.1.wait(LOGGER.0.lock().unwrap()).unwrap().drain(..) {
            let d = i.saturating_duration_since(now).as_millis();
            let msg = if mem == 0 {
              format!("[{:?}: {:?}ms] {}", id, d, s)
            } else {
              format!("[{:?}: {:?}ms, {}k] {}", id, d, mem/1024, s)
            };
            log_message(msg).unwrap();
            now = i;
          }
        }
      });
      let _ = self.caps.lock().unwrap().register();
      let mut count: i64 = 1;
      loop {
        match (|| -> Result<bool> {
          let Server {conn, caps, reqs, vfs, pool, ..} = &*SERVER;
          match conn.receiver.recv() {
            Err(RecvError) => return Ok(true),
            Ok(Message::Request(req)) => {
              if conn.handle_shutdown(&req)? {
                return Ok(true)
              }
              if let Some((id, req)) = parse_request(req)? {
                let cancel = Arc::new(AtomicBool::new(false));
                reqs.lock().unwrap().insert(id.clone(), cancel.clone());
                pool.spawn_ok(async {
                  RequestHandler {id, cancel}.handle(req).await.unwrap()
                });
              }
            }
            Ok(Message::Response(resp)) => {
              let mut caps = caps.lock().unwrap();
              if caps.reg_id.as_ref().map_or(false, |rid| rid == &resp.id) {
                caps.finish_register(resp);
              } else {
                log!("response to unknown request {}", resp.id)
              }
            }
            Ok(Message::Notification(notif)) => {
              match notif.method.as_str() {
                "$/cancelRequest" => {
                  let CancelParams {id} = from_value(notif.params)?;
                  if let Some(cancel) = reqs.lock().unwrap().get(&nos_id(id)) {
                    cancel.store(true, Ordering::Relaxed);
                  }
                }
                "textDocument/didOpen" => {
                  let DidOpenTextDocumentParams {text_document: doc} = from_value(notif.params)?;
                  let path = doc.uri.into();
                  log!("open {:?}", path);
                  vfs.open_virt(path, doc.version, doc.text)?;
                }
                "textDocument/didChange" => {
                  let DidChangeTextDocumentParams {text_document: doc, content_changes} = from_value(notif.params)?;
                  if !content_changes.is_empty() {
                    let path = doc.uri.into();
                    log!("change {:?}", path);
                    let start = {
                      let file = vfs.get(&path).ok_or("changed nonexistent file")?;
                      let (version, text) = &mut *file.text.lock().unwrap();
                      *version = Some(doc.version.unwrap_or_else(|| {let c = count; count += 1; c}));
                      let (start, s) = text.apply_changes(content_changes.into_iter());
                      *text = Arc::new(s);
                      start
                    };
                    pool.spawn_ok(elaborate_and_report(path, Some(start),
                      Arc::new(AtomicBool::new(false))));
                  }
                }
                "textDocument/didClose" => {
                  let DidCloseTextDocumentParams {text_document: doc} = from_value(notif.params)?;
                  let path = doc.uri.into();
                  log!("close {:?}", path);
                  vfs.close(&path)?;
                }
                _ => {}
              }
            }
          }
          Ok(false)
        })() {
          Ok(true) => break,
          Ok(false) => {},
          Err(e) => eprintln!("Server panicked: {:?}", e)
        }
      }
    }).expect("other thread panicked")
  }
}

fn response_err(code: ErrorCode, message: impl Into<String>) -> ResponseError {
  ResponseError {code: code as i32, message: message.into(), data: None}
}

/// Main entry point for `mm0-rs server` subcommand.
///
/// This function is not intended for interactive use, but instead sets up an [LSP] connection
/// using stdin and stdout. This allows for extensions such as [`vscode-mm0`] to use `mm0-rs`
/// as a language server.
///
/// # Arguments
///
/// `mm0-rs server [--debug]`, where:
///
/// - `-d`, `--debug`: enables debugging output to `lsp.log`
///
/// [LSP]: https://microsoft.github.io/language-server-protocol/
/// [`vscode-mm0`]: https://github.com/digama0/mm0/tree/master/vscode-mm0
pub fn main(args: &ArgMatches<'_>) {
  if args.is_present("debug") {
    std::env::set_var("RUST_BACKTRACE", "1");
    use {simplelog::*, std::fs::File};
    let _ = WriteLogger::init(LevelFilter::Debug, Config::default(), File::create("lsp.log").unwrap());
  }
  if args.is_present("no_log_errors") { LOG_ERRORS.store(false, Ordering::Relaxed) }
  log_message("started".into()).unwrap();
  SERVER.run()
}