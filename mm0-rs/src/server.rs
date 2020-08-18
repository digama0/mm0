//! Implements the bridge between mm0-rs and an editor via an lsp [`Connection`]
//!
//! [`Connection`]: ../../lsp_server/struct.Connection.html

use std::{fs, io};
use std::sync::{Arc, Mutex, atomic::{AtomicBool, Ordering}, Condvar};
use std::collections::{HashMap, HashSet, hash_map::{Entry, DefaultHasher}};
use std::hash::{Hash, Hasher};
use std::result;
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
use crossbeam::{channel::{SendError, RecvError}};
use clap::ArgMatches;
use crate::util::*;
use crate::lined_string::LinedString;
use crate::parser::{AST, parse};
use crate::mmu::import::elab as mmu_elab;
use crate::elab::{ElabError, FrozenElaborator, FrozenEnv,
  environment::{ObjectKind, DeclKey, StmtTrace},
  FrozenLispKind, FrozenAtomData,
  local_context::InferSort, proof::Subst,
  lisp::{print::FormatEnv, pretty::Pretty}};

#[derive(Debug)]
struct ServerError(BoxError);

type Result<T> = result::Result<T, ServerError>;

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

type LogMessage = (Instant, ThreadId, String);

lazy_static! {
  static ref LOGGER: (Mutex<Vec<LogMessage>>, Condvar) = Default::default();
  static ref SERVER: Server = Server::new().expect("Initialization failed");
}

#[allow(unused)]
pub(crate) fn log(s: String) {
  LOGGER.0.lock().unwrap().push((Instant::now(), thread::current().id(), s));
  LOGGER.1.notify_one();
}

#[allow(unused)]
macro_rules! log {
  ($($es:tt)*) => {crate::server::log(format!($($es)*))}
}

async fn elaborate(path: FileRef, start: Option<Position>,
    cancel: Arc<AtomicBool>) -> Result<(u64, FrozenEnv)> {
  let Server {vfs, pool, ..} = &*SERVER;
  let (path, file) = vfs.get_or_insert(path)?;
  let v = file.text.lock().unwrap().0;
  let (old_ast, old_env, old_deps) = {
    let mut g = file.parsed.lock().await;
    let (res, senders) = match &mut *g {
      None => ((None, None, vec![]), vec![]),
      &mut Some(FileCache::InProgress {version, ref cancel, ref mut senders}) => {
        if v == version {
          let (send, recv) = channel();
          senders.push(send);
          drop(g);
          return Ok(recv.await.unwrap())
        }
        cancel.store(true, Ordering::SeqCst);
        if let Some(FileCache::InProgress {senders, ..}) = g.take() {
          ((None, None, vec![]), senders)
        } else {unsafe {std::hint::unreachable_unchecked()}}
      }
      &mut Some(FileCache::Ready {hash, ref deps, ref env, complete, ..}) => {
        if complete {
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
          if matches { return Ok((hash, env.clone())) }
        }
        if let Some(FileCache::Ready {ast, source, errors, deps, env, ..}) = g.take() {
          ((start.map(|s| (s, source, ast)), Some((errors, env)), deps), vec![])
        } else {unsafe {std::hint::unreachable_unchecked()}}
      }
    };
    *g = Some(FileCache::InProgress {version: v, cancel: cancel.clone(), senders});
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
    let (errors, env) = mmu_elab(path.clone(), &ast.source);
    (vec![], errors, FrozenEnv::new(env))
  } else {
    let elab = FrozenElaborator::new(
      ast.clone(), path.clone(), path.has_extension("mm0"), cancel.clone());
    elab.elaborate(
      old_env.map(|(errs, e)| (idx, errs, e)),
      |path| {
        let path = vfs.get_or_insert(path)?.0;
        let (send, recv) = channel();
        pool.spawn_ok(elaborate_and_send(path.clone(), cancel.clone(), send));
        deps.push(path);
        Ok(recv)
      }).await
  };
  for tok in toks {tok.hash(&mut hasher)}
  let hash = hasher.finish();
  log!("elabbed {:?}", path);
  let mut g = file.parsed.lock().await;
  let complete = !cancel.load(Ordering::SeqCst);
  if complete {
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
    let errs: Vec<_> = ast.errors.iter().map(|e| e.to_diag(&ast.source))
      .chain(errors.iter().map(|e| e.to_diag(&ast.source, &mut to_loc))).collect();

    let (mut n_errs, mut n_warns, mut n_infos, mut n_hints) = (0, 0, 0, 0);

    for err in &errs {
      match err.severity {
        None => continue,
        Some(DiagnosticSeverity::Error) => n_errs += 1,
        Some(DiagnosticSeverity::Warning) => n_warns += 1,
        Some(DiagnosticSeverity::Information) => n_infos += 1,
        Some(DiagnosticSeverity::Hint) => n_hints += 1,
      }
    }

    use std::fmt::Write;
    let mut log_msg = format!("diagged {:?}, {} errors", path, n_errs);
    if n_warns != 0 { write!(&mut log_msg, ", {} warnings", n_warns).unwrap(); }
    if n_infos != 0 { write!(&mut log_msg, ", {} infos", n_infos).unwrap(); }
    if n_hints != 0 { write!(&mut log_msg, ", {} hints", n_hints).unwrap(); }

    log(log_msg);
    send_diagnostics(path.url().clone(), errs)?;
  }
  vfs.update_downstream(&old_deps, &deps, &path);
  if let Some(FileCache::InProgress {senders, ..}) = g.take() {
    for s in senders {
      let _ = s.send((hash, env.clone()));
    }
  }
  *g = Some(FileCache::Ready {hash, source, ast, errors, deps, env: env.clone(), complete});
  drop(g);
  for d in file.downstream.lock().unwrap().iter() {
    log!("{:?} affects {:?}", path, d);
    pool.spawn_ok(dep_change(d.clone()));
  }
  Ok((hash, env))
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
    if let Ok(env) = elaborate(path, Some(Position::default()), cancel).await {
      let _ = send.send(env);
    }
  }.boxed()
}

fn dep_change(path: FileRef) -> BoxFuture<'static, ()> {
  elaborate_and_report(path, None, Arc::new(AtomicBool::new(false))).boxed()
}

enum FileCache {
  InProgress {
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
    complete: bool,
  }
}

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
        send_diagnostics(path.url().clone(), vec![])?;
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
}

fn parse_request(Request {id, method, params}: Request) -> Result<Option<(RequestId, RequestType)>> {
  Ok(match method.as_str() {
    "textDocument/completion"     => Some((id, RequestType::Completion(from_value(params)?))),
    "textDocument/hover"          => Some((id, RequestType::Hover(from_value(params)?))),
    "textDocument/definition"     => Some((id, RequestType::Definition(from_value(params)?))),
    "textDocument/documentSymbol" => Some((id, RequestType::DocumentSymbol(from_value(params)?))),
    "completionItem/resolve"      => Some((id, RequestType::CompletionResolve(from_value(params)?))),
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
fn log_message(message: String) -> Result<()> {
  send_message(Notification {
    method: "window/logMessage".to_owned(),
    params: to_value(LogMessageParams {typ: MessageType::Log, message})?
  })
}

fn send_diagnostics(uri: Url, diagnostics: Vec<Diagnostic>) -> Result<()> {
  send_message(Notification {
    method: "textDocument/publishDiagnostics".to_owned(),
    params: to_value(PublishDiagnosticsParams {uri, diagnostics})?
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
        if SERVER.caps.definition_location_links {
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
      RequestType::DocumentSymbol(DocumentSymbolParams {text_document: doc}) =>
        self.finish(document_symbol(doc.uri.into()).await),
      RequestType::Completion(p) => {
        let doc = p.text_document_position;
        self.finish(completion(doc.text_document.uri.into(), doc.position).await)
      }
      RequestType::CompletionResolve(ci) => {
        self.finish(completion_resolve(*ci).await)
      }
    }
  }

  fn finish<T: Serialize>(self, resp: result::Result<T, ResponseError>) -> Result<()> {
    let Server {reqs, conn, ..} = &*SERVER;
    reqs.lock().unwrap().remove(&self.id);
    conn.sender.send(Message::Response(match resp {
      Ok(val) => Response { id: self.id, result: Some(to_value(val)?), error: None },
      Err(e) => Response { id: self.id, result: None, error: Some(e) }
    }))?;
    Ok(())
  }
}

async fn hover(path: FileRef, pos: Position) -> result::Result<Option<Hover>, ResponseError> {
  let Server {vfs, ..} = &*SERVER;
  macro_rules! or {($ret:expr, $e:expr)  => {match $e {
    Some(x) => x,
    None => return $ret
  }}}
  let file = vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "hover nonexistent file"))?;
  let text = file.text.lock().unwrap().1.clone();
  let idx = or!(Ok(None), text.to_idx(pos));
  let env = elaborate(path, Some(Position::default()), Arc::new(AtomicBool::from(false)))
    .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?.1;
  let env = unsafe { env.thaw() };
  let fe = FormatEnv { source: &text, env };
  let spans = or!(Ok(None), env.find(idx));
  let mut res = vec![];
  for &(sp, ref k) in spans.find_pos(idx) {
    if let Some(r) = (|| Some(match k {
      &ObjectKind::Sort(s) => (sp, format!("{}", &env.sorts[s])),
      &ObjectKind::Term(t, sp1) => (sp1, format!("{}", fe.to(&env.terms[t]))),
      &ObjectKind::Thm(t) => (sp, format!("{}", fe.to(&env.thms[t]))),
      &ObjectKind::Var(x) => (sp, match spans.lc.as_ref().and_then(|lc| lc.vars.get(&x)) {
        Some((_, InferSort::Bound {sort})) => format!("{{{}: {}}}", fe.to(&x), fe.to(sort)),
        Some((_, InferSort::Reg {sort, deps})) => {
          let mut s = format!("({}: {}", fe.to(&x), fe.to(sort));
          for &a in deps {s += " "; s += &env.data[a].name}
          s + ")"
        }
        _ => return None,
      }),
      ObjectKind::Expr(e) => {
        let head = e.uncons().next().unwrap_or(e);
        let sp1 = head.fspan().map_or(sp, |fsp| fsp.span);
        let a = head.as_atom()?;
        let s = if let Some(DeclKey::Term(t)) = env.data[a].decl {
          env.terms[t].ret.0
        } else {
          spans.lc.as_ref()?.vars.get(&a)?.1.sort()?
        };
        let mut out = String::new();
        fe.pretty(|p| p.expr(unsafe {e.thaw()}).render_fmt(80, &mut out).unwrap());
        use std::fmt::Write;
        write!(out, ": {}", fe.to(&s)).unwrap();
        (sp1, out)
      }
      ObjectKind::Proof(p) => {
        if let Some(e) = p.as_atom().and_then(|x|
          spans.lc.as_ref().and_then(|lc|
            lc.proofs.get(&x).map(|&i| &lc.proof_order[i].1))) {
          let mut out = String::new();
          fe.pretty(|p| p.hyps_and_ret(Pretty::nil(), std::iter::empty(), e)
            .render_fmt(80, &mut out).unwrap());
          (sp, out)
        } else {
          let mut u = p.uncons();
          let head = u.next()?;
          let sp1 = head.fspan().map_or(sp, |fsp| fsp.span);
          let a = head.as_atom()?;
          if let Some(DeclKey::Thm(t)) = env.data[a].decl {
            let td = &env.thms[t];
            res.push((sp, format!("{}", fe.to(td))));
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
            (sp1, out)
          } else {return None}
        }
      }
      ObjectKind::Global(_) |
      ObjectKind::Import(_) => return None,
    }))() {res.push(r)}
  }
  if res.is_empty() {return Ok(None)}
  Ok(Some(Hover {
    range: Some(text.to_range(res[0].0)),
    contents: HoverContents::Array(res.into_iter().map(|(_, value)|
      MarkedString::LanguageString(LanguageString {language: "metamath-zero".into(), value})).collect())
  }))
}

async fn definition<T>(path: FileRef, pos: Position,
    f: impl Fn(&LinedString, &LinedString, Span, &FileSpan, Span) -> T) ->
    result::Result<Vec<T>, ResponseError> {
  let Server {vfs, ..} = &*SERVER;
  macro_rules! or_none {($e:expr)  => {match $e {
    Some(x) => x,
    None => return Ok(vec![])
  }}}
  let file = vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "goto definition nonexistent file"))?;
  let text = file.text.lock().unwrap().1.clone();
  let idx = or_none!(text.to_idx(pos));
  let env = elaborate(path.clone(), Some(Position::default()), Arc::new(AtomicBool::from(false)))
    .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?.1;
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
        if let Some((Some((ref fsp, full)), _)) = *ad.lisp() {
          res.push(g(&fsp, full))
        } else if let Some(sp) = ad.graveyard() {
          res.push(g(&sp.0, sp.1))
        }
      }
      ObjectKind::Import(file) => {
        res.push(g(&FileSpan {file: file.clone(), span: 0.into()}, 0.into()))
      },
    }
  }
  Ok(res)
}

async fn document_symbol(path: FileRef) -> result::Result<DocumentSymbolResponse, ResponseError> {
  let Server {vfs, ..} = &*SERVER;
  let file = vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "document symbol nonexistent file"))?;
  let text = file.text.lock().unwrap().1.clone();
  let env = elaborate(path, Some(Position::default()), Arc::new(AtomicBool::from(false)))
    .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?.1;
  let fe = unsafe { env.format_env(&text) };
  let f = |name: &ArcString, desc, sp, full, kind| DocumentSymbol {
    name: (*name.0).clone(),
    detail: Some(desc),
    kind,
    deprecated: None,
    range: text.to_range(full),
    selection_range: text.to_range(sp),
    children: None,
  };
  let mut res = vec![];
  for s in env.stmts() {
    match *s {
      StmtTrace::Sort(a) => {
        let ad = &env.data()[a];
        let s = ad.sort().unwrap();
        let sd = env.sort(s);
        res.push(f(ad.name(), format!("{}", sd), sd.span.span, sd.full, SymbolKind::Class))
      }
      StmtTrace::Decl(a) => {
        let ad = &env.data()[a];
        match ad.decl().unwrap() {
          DeclKey::Term(t) => {
            let td = env.term(t);
            res.push(f(ad.name(), format!("{}", fe.to(td)), td.span.span, td.full,
              SymbolKind::Constructor))
          }
          DeclKey::Thm(t) => {
            let td = env.thm(t);
            res.push(f(ad.name(), format!("{}", fe.to(td)), td.span.span, td.full,
              SymbolKind::Method))
          }
        }
      }
      StmtTrace::Global(a) => {
        let ad = &env.data()[a];
        if let Some((Some((ref fsp, full)), ref e)) = *ad.lisp() {
          res.push(f(ad.name(), format!("{}", fe.to(unsafe { e.thaw() })), fsp.span, full,
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
                FrozenLispKind::AtomMap(_) => SymbolKind::Object,
                FrozenLispKind::Annot(_, _) |
                FrozenLispKind::Ref(_) => unreachable!()
              }
            }))() {
              Some(sk) => sk,
              None => continue,
            }));
        }
      }
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
      label: (*ad.name().0).clone(),
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
    TraceKind::Global => ad.lisp().as_ref().map(|(_, e)| {
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
        FrozenLispKind::AtomMap(_) => CompletionItemKind::Value,
        FrozenLispKind::Syntax(_) => CompletionItemKind::Event,
        FrozenLispKind::Proc(_) => CompletionItemKind::Function,
        FrozenLispKind::Annot(_, _) |
        FrozenLispKind::Ref(_) => unreachable!()
      })
    })
  }
}

async fn completion(path: FileRef, _pos: Position) -> result::Result<CompletionResponse, ResponseError> {
  let Server {vfs, ..} = &*SERVER;
  let file = vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "document symbol nonexistent file"))?;
  let text = file.text.lock().unwrap().1.clone();
  let env = elaborate(path.clone(), Some(Position::default()), Arc::new(AtomicBool::from(false)))
    .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?.1;
  let fe = unsafe { env.format_env(&text) };
  let mut res = vec![];
  for ad in env.data().iter() {
    if let Some(ci) = make_completion_item(&path, fe, ad, false, TraceKind::Sort) {res.push(ci)}
    if let Some(ci) = make_completion_item(&path, fe, ad, false, TraceKind::Decl) {res.push(ci)}
    if let Some(ci) = make_completion_item(&path, fe, ad, false, TraceKind::Global) {res.push(ci)}
  }
  Ok(CompletionResponse::Array(res))
}

async fn completion_resolve(ci: CompletionItem) -> result::Result<CompletionItem, ResponseError> {
  let Server {vfs, ..} = &*SERVER;
  let data = ci.data.ok_or_else(|| response_err(ErrorCode::InvalidRequest, "missing data"))?;
  let (uri, tk): (Url, TraceKind) = from_value(data).map_err(|e|
    response_err(ErrorCode::InvalidRequest, format!("bad JSON {:?}", e)))?;
  let path = uri.into();
  let file = vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "document symbol nonexistent file"))?;
  let text = file.text.lock().unwrap().1.clone();
  let env = elaborate(path.clone(), Some(Position::default()), Arc::new(AtomicBool::from(false)))
    .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?.1;
  let fe = unsafe { env.format_env(&text) };
  env.get_atom(&*ci.label).and_then(|a| make_completion_item(&path, fe, &env.data()[a], true, tk))
    .ok_or_else(|| response_err(ErrorCode::ContentModified, "completion missing"))
}

struct Server {
  conn: Connection,
  #[allow(unused)]
  params: InitializeParams,
  caps: Capabilities,
  reqs: OpenRequests,
  vfs: VFS,
  pool: ThreadPool,
}

struct Capabilities {
  definition_location_links: bool,
}

impl Capabilities {
  fn new(params: &InitializeParams) -> Capabilities {
    Capabilities {
      definition_location_links: params.capabilities.text_document.as_ref()
        .and_then(|d| d.definition.as_ref())
        .and_then(|g| g.link_support).unwrap_or(false)
    }
  }
}

impl Server {
  fn new() -> Result<Server> {
    let (conn, _iot) = Connection::stdio();
    let params = from_value(conn.initialize(
      to_value(ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::Incremental)),
        hover_provider: Some(true),
        completion_provider: Some(CompletionOptions {
          resolve_provider: Some(true),
          ..Default::default()
        }),
        definition_provider: Some(true),
        document_symbol_provider: Some(true),
        ..Default::default()
      })?
    )?)?;
    Ok(Server {
      caps: Capabilities::new(&params),
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
          for (i, id, s) in LOGGER.1.wait(LOGGER.0.lock().unwrap()).unwrap().drain(..) {
            let d = i.saturating_duration_since(now).as_millis();
            log_message(format!("[{:?}: {:?}ms] {}", id, d, s)).unwrap();
            now = i;
          }
        }
      });
      let mut count: i64 = 1;
      loop {
        match (|| -> Result<bool> {
          let Server {conn, reqs, vfs, pool, ..} = &*SERVER;
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
              reqs.lock().unwrap().get(&resp.id).ok_or_else(|| "response to unknown request")?
                .store(true, Ordering::Relaxed);
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
  log_message("started".into()).unwrap();
  SERVER.run()
}