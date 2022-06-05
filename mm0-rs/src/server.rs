//! Implements the bridge between mm0-rs and an editor via an lsp [`Connection`]

use std::{fs, io};
use std::sync::{Arc, Mutex, atomic::{AtomicBool, Ordering}, Condvar};
use std::collections::{VecDeque, HashMap, HashSet, hash_map::{Entry, DefaultHasher}};
use std::hash::{Hash, Hasher};
use std::thread::{ThreadId, self};
use std::time::Instant;
use futures::{FutureExt, future::BoxFuture};
use futures::channel::oneshot::{Sender as FSender, channel};
use futures::executor::ThreadPool;
use futures::lock::Mutex as FMutex;
use lsp_server::{Connection, ErrorCode, Message, Notification, ProtocolError,
  Request, RequestId, Response, ResponseError};
use once_cell::sync::Lazy;
use serde::ser::Serialize;
use serde_json::{from_value, to_value};
use serde_repr::{Serialize_repr, Deserialize_repr};
use serde::Deserialize;
#[allow(clippy::wildcard_imports)] use lsp_types::*;
use crossbeam::channel::{SendError, RecvError};
use clap::ArgMatches;
use crate::{ArcList, ArcString, BoxError, FileRef, FileSpan, Span,
  MutexExt, CondvarExt};
use mm1_parser::{Ast, parse};
use crate::mmb::import::elab as mmb_elab;
use crate::mmu::import::elab as mmu_elab;
use crate::compiler::FileContents;
use crate::{ObjectKind, DeclKey, StmtTrace, AtomId, SortId, TermId, ThmId, LinedString, FrozenEnv,
  FrozenLispKind, FrozenAtomData};
use crate::elab::{ElabResult, ElaborateBuilder, GoalListener,
  local_context::InferSort, proof::Subst,
  lisp::{print::FormatEnv, pretty::Pretty, Syntax, LispKind, Proc, BuiltinProc},
  spans::Spans};

#[derive(Debug)]
struct ServerError(BoxError);

type Result<T, E = ServerError> = std::result::Result<T, E>;

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

#[cfg(feature = "memory")]
struct MemoryData(usize, usize);
#[cfg(not(feature = "memory"))]
struct MemoryData;

impl MemoryData {
  fn get() -> MemoryData {
    #[cfg(feature = "memory")] {
      use mm0_deepsize::DeepSizeOf;
      MemoryData(crate::get_memory_usage(), SERVER.vfs.deep_size_of())
    }
    #[cfg(not(feature = "memory"))] MemoryData
  }
}

impl std::fmt::Display for MemoryData {
  #[allow(unused_variables)]
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    #[cfg(feature = "memory")]
    if self.0 != 0 {
      write!(f, ", {}k / {}k", self.0 >> 10, self.1 >> 10)?
    }
    Ok(())
  }
}

type LogMessage = (Instant, ThreadId, MemoryData, String);

static LOGGER: Lazy<(Mutex<Vec<LogMessage>>, Condvar)> = Lazy::new(Default::default);
static SERVER: Lazy<Server> = Lazy::new(|| Server::new().expect("Initialization failed"));

#[allow(unused)]
pub(crate) fn log(s: String) {
  let data = (Instant::now(), thread::current().id(), MemoryData::get(), s);
  LOGGER.0.ulock().push(data);
  LOGGER.1.notify_one();
}

struct Logger(std::thread::JoinHandle<()>, Arc<AtomicBool>);

impl Logger {
  fn start() -> Self {
    let cancel: Arc<AtomicBool> = Arc::default();
    let cancel2 = cancel.clone();
    let jh = std::thread::spawn(move || {
      let mut now = Instant::now();
      while !cancel.load(Ordering::Acquire) {
        for (i, id, mem, s) in LOGGER.1.uwait(LOGGER.0.ulock()).drain(..) {
          let d = i.saturating_duration_since(now).as_millis();
          let msg = format!("[{:?}: {:?}ms{}] {}", id, d, mem, s);
          log_message(msg).expect("send failed");
          now = i;
        }
      }
    });
    Logger(jh, cancel2)
  }

  fn stop(self) {
    self.1.store(true, Ordering::Release);
    LOGGER.1.notify_one();
    self.0.join().expect("failed to join thread")
  }
}

#[allow(unused)]
macro_rules! log {
  ($($es:tt)*) => {crate::server::log(format!($($es)*))}
}

async fn elaborate(path: FileRef, start: Option<Position>,
    cancel: Arc<AtomicBool>, rd: ArcList<FileRef>) -> Result<ElabResult<u64>> {
  let vfs = &SERVER.vfs;
  debug_assert!(!rd.contains(&path));
  let (path, file) = vfs.get_or_insert(path)?;
  let v = file.text.ulock().0;
  let (old_ast, old_env, old_deps) = {
    let mut g = file.parsed.lock().await;
    let (old, res, senders) = match &mut *g {
      None => (None, (None, None, vec![]), vec![]),
      &mut Some(FileCache::InProgress {version, ref cancel, ref mut senders, ..}) => {
        if v == version {
          let (send, recv) = channel();
          senders.push(send);
          drop(g);
          return Ok(recv.await.unwrap_or(ElabResult::Canceled))
        }
        cancel.store(true, Ordering::SeqCst);
        let_unchecked!(Some(FileCache::InProgress {old, senders, ..}) = g.take(), {
          (old, (None, None, vec![]), senders)
        })
      }
      &mut Some(FileCache::Ready {hash, ref deps, ref res, ..}) => {
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
        if matches && !matches!(res, ElabResult::Canceled) {
          return Ok(res.clone())
        }
        let_unchecked!(Some(FileCache::Ready {ast, source, deps, res, ..}) = g.take(), {
          if let ElabResult::Ok(_, errors, env) = res {
            (Some((source.clone(), env.clone())),
              (start.map(|s| (s, source, ast)), Some((errors, env)), deps), vec![])
          } else {
            (None, (None, None, vec![]), vec![])
          }
        })
      }
    };
    *g = Some(FileCache::InProgress {old, version: v, cancel: cancel.clone(), senders});
    drop(g);
    res
  };
  let (version, text) = file.text.ulock().clone();
  let old_ast = old_ast.and_then(|(s, old_text, ast)|
    if text.ptr_eq(&old_text) {Some((s, ast?))} else {None});
  let mut hasher = DefaultHasher::new();
  version.hash(&mut hasher);
  let source = text.clone();

  let mut deps = Vec::new();
  let (ast, (cyc, toks, errors, env)) = if path.has_extension("mmb") {
    let (error, env) = mmb_elab(&path, &text);
    let errors = if let Err(e) = error {vec![e]} else {vec![]};
    (None, (None, vec![], errors, FrozenEnv::new(env)))
  } else if path.has_extension("mmu") {
    let (error, env) = mmu_elab(&path, &text);
    let errors = if let Err(e) = error {vec![e]} else {vec![]};
    (None, (None, vec![], errors, FrozenEnv::new(env)))
  } else {
    let (idx, ast) = parse(text.ascii().clone(), old_ast);
    let ast = Arc::new(ast);
    let rd = rd.push(path.clone());
    let elab = ElaborateBuilder {
      ast: &ast,
      path: path.clone(),
      mm0_mode: path.has_extension("mm0"),
      options: crate::get_options(),
      report_upstream_errors: SERVER.options.ulock().report_upstream_errors.unwrap_or(true),
      cancel: cancel.clone(),
      old: old_env.map(|(errs, e)| (idx, errs, e)),
      recv_dep: |p| {
        let (p, dep) = vfs.get_or_insert(p)?;
        let (send, recv) = channel();
        if rd.contains(&p) {
          send.send(ElabResult::ImportCycle(rd.clone())).expect("failed to send");
        } else {
          if let Some(Some(FileCache::Ready {res, ..})) =
            dep.parsed.try_lock().as_deref() {
            send.send(res.clone()).expect("failed to send");
          } else {
            Job::ElaborateDep(p.clone(), path.clone(), Some((send, rd.clone()))).spawn();
          }
          deps.push(p);
        }
        Ok(recv)
      },
      recv_goal: start.filter(|_| SERVER.caps.ulock().goal_view)
        .and_then(|start| ast.source.to_idx(start))
        .filter(|&pos| pos != 0)
        .map(|pos| {
          GoalListener::new(move |elab: &crate::elab::Elaborator, stat| {
            if elab.spans.stmt().contains(&pos) {
              log(format!("\n{}", stat));
            }
          })
        }),
    }.elab();
    (Some(ast.clone()), elab.await)
  };
  for tok in toks {tok.hash(&mut hasher)}
  let hash = hasher.finish();
  let is_canceled = cancel.load(Ordering::SeqCst);
  log!("elabbed {:?}{}", path, if is_canceled {" (canceled)"} else {""});
  let no_change_since_elab = file.text.ulock().0 == version;
  if !is_canceled && no_change_since_elab {
    let mut srcs = HashMap::new();
    let mut to_loc = |fsp: &FileSpan| -> Location {
      let fc = if fsp.file.ptr_eq(&path) {
        &source
      } else {
        srcs.entry(fsp.file.ptr())
        .or_insert_with(||
          vfs.0.ulock().get(&fsp.file).expect("missing file")
            .text.ulock().1.clone())
      };
      if let Some(file) = fc.try_ascii() {
        file.to_loc(fsp)
      } else {
        Location {uri: fsp.file.url().clone(), range: Range::default()}
      }
    };

    if let Some(ast) = &ast {
      use std::fmt::Write;
      let (mut n_errs, mut n_warns, mut n_infos, mut n_hints) = (0, 0, 0, 0);
      let errs: Vec<_> = ast.errors.iter().map(|e| e.to_diag(source.ascii()))
        .chain(errors.iter().map(|e| e.to_diag(source.ascii(), &mut to_loc)))
        .filter(|e| !e.message.is_empty())
        .inspect(|err| match err.severity {
          Some(DiagnosticSeverity::ERROR) => n_errs += 1,
          Some(DiagnosticSeverity::WARNING) => n_warns += 1,
          Some(DiagnosticSeverity::INFORMATION) => n_infos += 1,
          Some(DiagnosticSeverity::HINT) => n_hints += 1,
          _ => {}
        }).collect();

      send_diagnostics(path.url().clone(), version, errs)?;

      let mut log_msg = format!("diagged {:?}, {} errors", path, n_errs);
      if n_warns != 0 { write!(log_msg, ", {} warnings", n_warns).expect("impossible") }
      if n_infos != 0 { write!(log_msg, ", {} infos", n_infos).expect("impossible") }
      if n_hints != 0 { write!(log_msg, ", {} hints", n_hints).expect("impossible") }
      if SERVER.options.ulock().log_errors.unwrap_or(true) {
        for e in &errors {
          let Position {line, character: col} = source.ascii().to_pos(e.pos.start);
          write!(log_msg, "\n\n{}: {}:{}:{}:\n{}",
            e.level, path.rel(), line+1, col+1, e.kind.msg()).expect("impossible");
        }
      }
      log(log_msg);
    }
  }

  let res = if is_canceled {
    ElabResult::Canceled
  } else if let Some(cyc) = &cyc {
    ElabResult::ImportCycle(cyc.clone())
  } else {
    let errors = if errors.is_empty() { None } else { Some(errors.into()) };
    ElabResult::Ok(hash, errors, env.clone())
  };
  if !is_canceled { vfs.update_downstream(&old_deps, &deps, &path) }
  let mut g = file.parsed.lock().await;
  if let Some(FileCache::InProgress {senders, ..}) = g.take() {
    for s in senders {
      drop(s.send(res.clone()));
    }
  }
  if !is_canceled {
    *g = Some(FileCache::Ready {hash, source, ast, res: res.clone(), deps});
    drop(g);
    for d in file.downstream.ulock().iter() {
      log!("{:?} affects {:?}", path, d);
      Job::DepChange(path.clone(), d.clone(), DepChangeReason::Elab).spawn();
    }
  }
  Ok(res)
}

async fn elaborate_and_report(path: FileRef, start: Option<Position>, cancel: Arc<AtomicBool>) {
  if let Err(e) =
    std::panic::AssertUnwindSafe(elaborate(path, start, cancel, Default::default()))
      .catch_unwind().await
      .unwrap_or_else(|_| Err("server panic".into())) {
    log_message(format!("{:?}", e)).expect("failed to send");
  }
}

fn elaborate_and_send(path: FileRef,
  cancel: Arc<AtomicBool>,
  send: FSender<ElabResult<u64>>,
  rd: ArcList<FileRef>
) -> BoxFuture<'static, ()> {
  async {
    if let Ok(r) = elaborate(path, Some(Position::default()), cancel, rd).await {
      drop(send.send(r));
    }
  }.boxed()
}

fn dep_change(path: FileRef, cancel: Arc<AtomicBool>) -> BoxFuture<'static, ()> {
  elaborate_and_report(path, None, cancel).boxed()
}

#[derive(DeepSizeOf)]
enum FileCache {
  InProgress {
    old: Option<(FileContents, FrozenEnv)>,
    version: Option<i32>,
    cancel: Arc<AtomicBool>,
    senders: Vec<FSender<ElabResult<u64>>>,
  },
  Ready {
    hash: u64,
    source: FileContents,
    ast: Option<Arc<Ast>>,
    res: ElabResult<u64>,
    deps: Vec<FileRef>,
  }
}

#[derive(DeepSizeOf)]
struct VirtualFile {
  /// File data, saved (true) or unsaved (false)
  text: Mutex<(Option<i32>, FileContents)>,
  /// File parse
  parsed: FMutex<Option<FileCache>>,
  /// Files that depend on this one
  downstream: Mutex<HashSet<FileRef>>,
}

impl VirtualFile {
  fn new(version: Option<i32>, text: FileContents) -> VirtualFile {
    VirtualFile {
      text: Mutex::new((version, text)),
      parsed: FMutex::new(None),
      downstream: Mutex::new(HashSet::new())
    }
  }
}

#[derive(DeepSizeOf)]
struct Vfs(Mutex<HashMap<FileRef, Arc<VirtualFile>>>);

impl Vfs {
  fn get(&self, path: &FileRef) -> Option<Arc<VirtualFile>> {
    self.0.ulock().get(path).cloned()
  }

  fn get_or_insert(&self, path: FileRef) -> io::Result<(FileRef, Arc<VirtualFile>)> {
    match self.0.ulock().entry(path) {
      Entry::Occupied(e) => Ok((e.key().clone(), e.get().clone())),
      Entry::Vacant(e) => {
        let path = e.key().clone();
        let fc = if path.has_extension("mmb") {
          FileContents::new_bin_from_file(path.path())?
        } else {
          FileContents::new(fs::read_to_string(path.path())?)
        };
        let val = e.insert(Arc::new(VirtualFile::new(None, fc))).clone();
        Ok((path, val))
      }
    }
  }

  fn source(&self, file: &FileRef) -> Arc<LinedString> {
    self.0.ulock()[file].text.ulock().1.ascii().clone()
  }

  fn open_virt(&self, path: FileRef, version: i32, text: String) -> Arc<VirtualFile> {
    let file = Arc::new(VirtualFile::new(Some(version), FileContents::new(text)));
    let file = match self.0.ulock().entry(path.clone()) {
      Entry::Occupied(entry) => {
        for dep in entry.get().downstream.ulock().iter() {
          Job::DepChange(path.clone(), dep.clone(), DepChangeReason::Open).spawn();
        }
        file
      }
      Entry::Vacant(entry) => entry.insert(file).clone()
    };
    Job::Elaborate(path, ElabReason::Open).spawn();
    file
  }

  fn close(&self, path: &FileRef) -> Result<()> {
    let mut g = self.0.ulock();
    if let Entry::Occupied(e) = g.entry(path.clone()) {
      if e.get().downstream.ulock().is_empty() {
        send_diagnostics(path.url().clone(), None, vec![])?;
        e.remove();
      } else if e.get().text.ulock().0.take().is_some() {
        let file = e.get().clone();
        drop(g);
        for dep in file.downstream.ulock().clone() {
          Job::DepChange(path.clone(), dep.clone(), DepChangeReason::Close).spawn();
        }
      } else {}
    }
    Ok(())
  }

  fn update_downstream(&self, old_deps: &[FileRef], deps: &[FileRef], to: &FileRef) {
    for from in old_deps {
      if !deps.contains(from) {
        let file = self.0.ulock()[from].clone();
        file.downstream.ulock().remove(to);
      }
    }
    for from in deps {
      if !old_deps.contains(from) {
        let file = self.0.ulock()[from].clone();
        file.downstream.ulock().insert(to.clone());
      }
    }
  }
}

macro_rules! request_type {
  ($($s:literal => $name:ident($param:ty),)*) => {
    #[derive(Debug)]
    enum RequestType {
      $($name($param),)*
    }

    fn parse_request(Request {id, method, params}: Request) -> Result<Option<(RequestId, RequestType)>> {
      Ok(match method.as_str() {
        $($s => Some((id, RequestType::$name(from_value(params)?))),)*
        _ => None
      })
    }
  }
}

request_type! {
  "textDocument/completion"           => Completion(CompletionParams),
  "completionItem/resolve"            => CompletionResolve(Box<CompletionItem>),
  "textDocument/hover"                => Hover(TextDocumentPositionParams),
  "textDocument/definition"           => Definition(TextDocumentPositionParams),
  "textDocument/documentSymbol"       => DocumentSymbol(DocumentSymbolParams),
  "textDocument/references"           => References(ReferenceParams),
  "textDocument/documentHighlight"    => DocumentHighlight(DocumentHighlightParams),
  "textDocument/semanticTokens/full"  => SemanticTokens(SemanticTokensParams),
  "textDocument/semanticTokens/range" => SemanticTokensRange(SemanticTokensRangeParams),
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

fn register_capability(id: String, registrations: Vec<Registration>) -> Result<()> {
  send_message(Request {
    id: id.into(),
    method: "client/registerCapability".to_owned(),
    params: to_value(RegistrationParams {registrations})?
  })
}

fn log_message(message: String) -> Result<()> {
  send_message(Notification {
    method: "window/logMessage".to_owned(),
    params: to_value(LogMessageParams {typ: MessageType::LOG, message})?
  })
}

fn send_diagnostics(uri: Url, version: Option<i32>, diagnostics: Vec<Diagnostic>) -> Result<()> {
  send_message(Notification {
    method: "textDocument/publishDiagnostics".to_owned(),
    params: to_value(PublishDiagnosticsParams {uri, diagnostics, version})?
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
        if SERVER.caps.ulock().definition_location_links {
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
      RequestType::SemanticTokens(SemanticTokensParams {text_document: doc, ..}) =>
        self.finish(semantic_tokens(doc.uri.into(), None).await),
      RequestType::SemanticTokensRange(SemanticTokensRangeParams {text_document: doc, range, ..}) =>
        self.finish(semantic_tokens(doc.uri.into(), Some(range)).await),
    }
  }

  fn finish<T: Serialize>(self, resp: Result<T, ResponseError>) -> Result<()> {
    let Server {reqs, conn, ..} = &*SERVER;
    reqs.ulock().remove(&self.id);
    conn.sender.send(Message::Response(match resp {
      Ok(val) => Response { id: self.id, result: Some(to_value(val)?), error: None },
      Err(e) => Response { id: self.id, result: None, error: Some(e) }
    }))?;
    Ok(())
  }
}

/// Calculates the maximum `n` such that every nonempty line begins with at least `n` spaces.
fn get_margin(s: &str) -> usize {
  let mut margin = s.len();
  let mut it = s.chars();
  let mut this_line = 0;
  while let Some(c) = it.next() {
    if c == ' ' {this_line += 1}
    else if c == '\n' {this_line = 0}
    else {
      if this_line == 0 {return 0}
      margin = margin.min(this_line);
      while matches!(it.next(), Some(c) if c != '\n') {}
    }
  }
  margin
}

/// Remove the left margin from a doc string.
fn trim_margin(s: &str) -> String {
  let margin = get_margin(s);
  if margin == 0 {return s.into()}
  let mut last = 0;
  let mut out = String::new();
  let s = s.as_bytes();
  let mut nonempty = false;
  for (i, &c) in s.iter().enumerate() {
    if c == b'\n' {
      if nonempty {
        // Safety: last + margin is at a valid utf8 location
        // because it is some number of spaces after a newline,
        // and i+1 is because c == b'\n' is a one byte char
        unsafe { out.push_str(std::str::from_utf8_unchecked(&s[last + margin ..= i])) }
        nonempty = false;
      } else {
        out.push('\n')
      }
      last = i + 1;
    } else if c == b' ' { /* skip */ }
    else { nonempty = true }
  }
  out
}

impl<T> ElabResult<T> {
  fn into_response_error(self) -> Result<Option<(T, FrozenEnv)>, ResponseError> {
    match self {
      ElabResult::Ok(data, _, env) => Ok(Some((data, env))),
      ElabResult::Canceled => Err(response_err(ErrorCode::RequestCanceled, "")),
      ElabResult::ImportCycle(_) => Ok(None),
    }
  }
}

/// small abstraction for trying to get the last good environment.
/// `completion` always uses this, but the other users will only opt for this
/// if the user has chosen to elaborate on save instead of on change.
fn try_old(file: &Arc<VirtualFile>)  -> Option<(FileContents, FrozenEnv)> {
  file.parsed.try_lock().and_then(|g| g.as_ref().and_then(|fc| match fc {
    FileCache::Ready {source, res: ElabResult::Ok(_, _, env), ..} => Some((source.clone(), env.clone())),
    FileCache::Ready {..} => None,
    FileCache::InProgress {old, ..} => old.clone()
  }))
}

async fn hover(path: FileRef, pos: Position) -> Result<Option<Hover>, ResponseError> {
  macro_rules! or {($ret:expr, $e:expr)  => {match $e {
    Some(x) => x,
    None => return $ret
  }}}
  fn mk_mm0(value: String) -> MarkedString {
    MarkedString::LanguageString(
      LanguageString { language: "metamath-zero".into(), value })
  }
  fn mk_doc(doc: &str) -> MarkedString {
    MarkedString::String(trim_margin(doc))
  }

  let file = SERVER.vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "hover nonexistent file"))?;
  let text = file.text.ulock().1.ascii().clone();
  let idx = or!(Ok(None), text.to_idx(pos));
  let env = elaborate(path, Some(Position::default()), Default::default(), Default::default())
    .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?;
  let env = or!(Ok(None), env.into_response_error()?).1;
  // Safety: This is actually unsafe, but the issue is unlikely to come up in practice.
  // We are promising here to not Rc::clone the data, but we do below,
  // meaning that we could potentially race on the reference count.
  let env = unsafe { env.thaw() };
  let fe = FormatEnv { source: &text, env };
  let spans = or!(Ok(None), Spans::find(&env.spans, idx));

  let mut out: Vec<(Span, MarkedString)> = vec![];
  for &(sp, ref k) in spans.find_pos(idx) {
    if let Some((r, doc)) = (|| Some(match k {
      &ObjectKind::Sort(_, s) => {
        let sd = &env.sorts[s];
        ((sp, mk_mm0(format!("{}", sd))), sd.doc.clone())
      }
      &ObjectKind::Term(_, t, sp1) => {
        let td = &env.terms[t];
        ((sp1, mk_mm0(format!("{}", fe.to(td)))), td.doc.clone())
      }
      &ObjectKind::Thm(_, t) => {
        let td = &env.thms[t];
        ((sp, mk_mm0(format!("{}", fe.to(td)))), td.doc.clone())
      }
      &ObjectKind::Var(_, x) => ((sp, mk_mm0(match spans.lc.as_ref().and_then(|lc| lc.vars.get(&x)) {
        Some((_, InferSort::Bound { sort, .. })) => format!("{{{}: {}}}", fe.to(&x), fe.to(sort)),
        Some((_, InferSort::Reg { sort, deps, .. })) => {
          let mut s = format!("({}: {}", fe.to(&x), fe.to(sort));
          for &a in &**deps {
            s += " ";
            s += &String::from_utf8_lossy(&env.data[a].name)
          }
          s.push(')');
          s
        }
        _ => return None,
      })), None),
      &ObjectKind::Hyp(_, x) => match spans.lc.as_ref().and_then(|lc| lc.get_proof(x)) {
        Some((_, ty, _)) => {
          let mut out = format!("({}: ", fe.to(&x));
          // Safety: render_fmt doesn't clone the expression
          fe.pretty(|p| p.expr(ty).render_fmt(80, &mut out).expect("impossible"));
          out += ")";
          ((sp, mk_mm0(out)), None)
        }
        _ => return None,
      }
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
        // Safety: render_fmt doesn't clone the expression
        let e = unsafe { e.thaw() };
        fe.pretty(|p| p.expr(e).render_fmt(80, &mut out).expect("impossible"));
        { use std::fmt::Write; write!(out, ": {}", fe.to(&s)).expect("impossible"); }
        ((sp1, mk_mm0(out)), doc)
      }
      ObjectKind::Proof(p) => {
        if let Some(e) = p.as_atom().and_then(|x|
          spans.lc.as_ref().and_then(|lc|
            lc.proofs.get(&x).map(|&i| &lc.proof_order[i].1))) {
          let mut out = String::new();
          fe.pretty(|p| p.hyps_and_ret(Pretty::nil(), std::iter::empty(), e)
            .render_fmt(80, &mut out).expect("impossible"));
          ((sp, mk_mm0(out)), None)
        } else {
          let mut u = p.uncons();
          let head = u.next()?;
          let sp1 = head.fspan().map_or(sp, |fsp| fsp.span);
          let a = head.as_atom()?;
          if let Some(DeclKey::Thm(t)) = env.data[a].decl {
            let td = &env.thms[t];
            out.push((sp, mk_mm0(format!("{}", fe.to(td)))));
            let mut args = vec![];
            for _ in 0..td.args.len() {
              // Safety: FIXME this is actually unsafe. `Subst` both requires cloned expressions
              // and also clones expressions itself, but `FrozenEnv` does not permit us to do so,
              // and there can potentially be a data race if multiple threads attempt to do this
              // printing at the same time. But this is a hover output so this seems unlikely.
              args.push(unsafe { u.next()?.thaw() }.clone());
            }
            let mut subst = Subst::new(env, &td.heap, &td.store, args);
            let mut out = String::new();
            let ret = subst.subst(&td.ret);
            fe.pretty(|p| p.hyps_and_ret(Pretty::nil(),
              td.hyps.iter().map(|(_, h)| subst.subst(h)),
              &ret).render_fmt(80, &mut out).expect("impossible"));
            ((sp1, mk_mm0(out)), td.doc.clone())
          } else {return None}
        }
      }
      ObjectKind::Syntax(stx) => {
        if SERVER.options.ulock().syntax_docs.unwrap_or(false) {
          ((sp, mk_doc(stx.doc())), None)
        } else { return None }
      }
      ObjectKind::PatternSyntax(stx) => {
        if SERVER.options.ulock().syntax_docs.unwrap_or(false) {
          ((sp, mk_doc(stx.doc())), None)
        } else { return None }
      }
      ObjectKind::RefineSyntax(stx) => {
        if SERVER.options.ulock().syntax_docs.unwrap_or(false) {
          ((sp, mk_doc(stx.doc())), None)
        } else { return None }
      }
      &ObjectKind::Global(_, _, a) => {
        let ad = &env.data[a];
        if let Some(ld) = &ad.lisp {
          if let Some(doc) = &ld.doc {
            ((sp, mk_doc(doc)), None)
          } else {
            let bp = ld.unwrapped(|e| match *e {
              LispKind::Proc(Proc::Builtin(p)) => Some(p),
              _ => None
            })?;
            ((sp, mk_doc(bp.doc())), None)
          }
        } else {
          let bp = BuiltinProc::from_bytes(&ad.name)?;
          ((sp, mk_doc(bp.doc())), None)
        }
      }
      ObjectKind::LispVar(..) |
      ObjectKind::Import(_) => return None,
    }))() {
      let sp = r.0;
      out.push(r);
      if let Some(doc) = doc {
        out.push((sp, mk_doc(&doc)))
      }
    }
  }
  if out.is_empty() {return Ok(None)}
  Ok(Some(Hover {
    range: Some(text.to_range(out[0].0)),
    contents: HoverContents::Array(out.into_iter().map(|s| s.1).collect())
  }))
}

async fn definition<T>(path: FileRef, pos: Position,
    f: impl Fn(&LinedString, &LinedString, Span, &FileSpan, Span) -> T + Send) ->
    Result<Vec<T>, ResponseError> {
  let vfs = &SERVER.vfs;
  macro_rules! or_none {($e:expr)  => {match $e {
    Some(x) => x,
    None => return Ok(vec![])
  }}}
  let file = vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "goto definition nonexistent file"))?;
  let text = match &file.text.ulock().1 {
    FileContents::Ascii(text) => text.clone(),
    _ => return Ok(vec![])
  };
  let idx = or_none!(text.to_idx(pos));
  let env = elaborate(path.clone(), Some(Position::default()), Default::default(), Default::default())
    .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?;
  let env = or_none!(env.into_response_error()?).1;
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
      &ObjectKind::Sort(_, s) => res.push(sort(s)),
      &ObjectKind::Term(_, t, _) => res.push(term(t)),
      &ObjectKind::Thm(_, t) => res.push(thm(t)),
      ObjectKind::Var(..) |
      ObjectKind::Hyp(..) |
      ObjectKind::LispVar(..) |
      ObjectKind::Syntax(_) |
      ObjectKind::PatternSyntax(_) |
      ObjectKind::RefineSyntax(_) => {}
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
      &ObjectKind::Global(_, _, a) => {
        let ad = &env.data()[a];
        match ad.decl() {
          Some(DeclKey::Term(t)) => res.push(term(t)),
          Some(DeclKey::Thm(t)) => res.push(thm(t)),
          None => {}
        }
        if let Some(s) = ad.sort() {res.push(sort(s))}
        if let Some(&(ref fsp, full)) = ad.lisp().as_ref().and_then(|ld| ld.src().as_ref()) {
          res.push(g(fsp, full))
        } else if let Some(sp) = ad.graveyard() {
          res.push(g(&sp.0, sp.1))
        } else {}
      }
      ObjectKind::Import(file) => {
        res.push(g(&FileSpan {file: file.clone(), span: 0.into()}, 0.into()))
      },
    }
  }
  Ok(res)
}

#[allow(deprecated)] // workaround rust#60681
async fn document_symbol(path: FileRef) -> Result<DocumentSymbolResponse, ResponseError> {
  let file = SERVER.vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "document symbol nonexistent file"))?;

  let maybe_old = if SERVER.elab_on().unwrap_or_default() == ElabOn::Save { try_old(&file) } else { None };
  let (text, env) = if let Some((contents, frozen)) = maybe_old {
    (contents.ascii().clone(), frozen)
  } else {
    let env = elaborate(path.clone(), Some(Position::default()), Default::default(), Default::default())
      .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?;
    match env.into_response_error()? {
      None => return Ok(DocumentSymbolResponse::Nested(vec![])),
      Some((_, env)) => (file.text.ulock().1.ascii().clone(), env)
    }
  };
  // Safety: We don't use the env field on `fe` for anything other than printing
  let fe = unsafe { env.format_env(&text) };
  let f = |sp, name: &ArcString, desc, full, kind| DocumentSymbol {
    name: String::from_utf8_lossy(name).into(),
    detail: Some(desc),
    kind,
    #[allow(deprecated)] deprecated: None,
    range: text.to_range(full),
    selection_range: text.to_range(sp),
    children: None,
    tags: None,
  };
  let mut res = vec![];
  macro_rules! push {($fsp:expr, $($e:expr),*) => {
    if $fsp.file == path { res.push(f($fsp.span, $($e),*)) }
  }}
  for s in env.stmts() {
    match *s {
      StmtTrace::Sort(a) => {
        let ad = &env.data()[a];
        let s = ad.sort().expect("env well formed");
        let sd = env.sort(s);
        push!(sd.span, ad.name(), format!("{}", sd), sd.full, SymbolKind::CLASS)
      }
      StmtTrace::Decl(a) => {
        let ad = &env.data()[a];
        match ad.decl().expect("env well formed") {
          DeclKey::Term(t) => {
            let td = env.term(t);
            push!(td.span, ad.name(), format!("{}", fe.to(td)), td.full, SymbolKind::CONSTRUCTOR)
          }
          DeclKey::Thm(t) => {
            let td = env.thm(t);
            push!(td.span, ad.name(), format!("{}", fe.to(td)), td.full, SymbolKind::METHOD)
          }
        }
      }
      StmtTrace::Global(a) => {
        let ad = &env.data()[a];
        if let Some(ld) = ad.lisp() {
          if let Some((ref fsp, full)) = *ld.src() {
            let e = &**ld;
            // Safety: We only use the expression for printing and don't Rc::clone it
            push!(fsp, ad.name(), format!("{}", fe.to(unsafe { e.thaw() })), full,
              match (|| Some(match e.unwrap() {
                FrozenLispKind::Atom(_) |
                FrozenLispKind::MVar(_, _) |
                FrozenLispKind::Goal(_) => SymbolKind::CONSTANT,
                r @ (FrozenLispKind::List(_) | FrozenLispKind::DottedList(_, _)) =>
                  if r.is_list() {SymbolKind::ARRAY} else {SymbolKind::OBJECT},
                FrozenLispKind::Number(_) => SymbolKind::NUMBER,
                FrozenLispKind::String(_) => SymbolKind::STRING,
                FrozenLispKind::Bool(_) => SymbolKind::BOOLEAN,
                FrozenLispKind::Syntax(_) => SymbolKind::EVENT,
                FrozenLispKind::Undef => return None,
                FrozenLispKind::Proc(_) => SymbolKind::FUNCTION,
                FrozenLispKind::AtomMap(_) |
                FrozenLispKind::Annot(_, _) |
                FrozenLispKind::Ref(_) => SymbolKind::OBJECT,
              }))() {
                Some(sk) => sk,
                None => continue,
              });
          }
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
  macro_rules! done {($desc:expr, $kind:expr, $doc:expr) => {
    CompletionItem {
      label: String::from_utf8_lossy(ad.name()).into(),
      detail: if detail {Some($desc)} else {None},
      kind: Some($kind),
      documentation: $doc.as_ref().map(|doc| {
        Documentation::MarkupContent(MarkupContent {
          kind: MarkupKind::Markdown,
          value: doc.to_string(),
        })
      }),
      data: Some(to_value((path.url(), tk)).expect("serialization error")),
      ..Default::default()
    }
  }}
  match tk {
    TraceKind::Sort => ad.sort().map(|s| {
      let sd = &fe.sorts[s];
      done!(format!("{}", sd), CompletionItemKind::CLASS, sd.doc)
    }),
    TraceKind::Decl => ad.decl().map(|dk| match dk {
      DeclKey::Term(t) => {
        let td = &fe.terms[t];
        done!(format!("{}", fe.to(td)), CompletionItemKind::CONSTRUCTOR, td.doc)
      }
      DeclKey::Thm(t) => {
        let td = &fe.thms[t];
        done!(format!("{}", fe.to(td)), CompletionItemKind::METHOD, td.doc)
      }
    }),
    TraceKind::Global => {
      let e = ad.lisp().as_ref()?;
      // Safety: We only use the expression for printing and don't Rc::clone it
      Some(done!(format!("{}", fe.to(unsafe { e.thaw() })), match *e.unwrap() {
        FrozenLispKind::Atom(_) |
        FrozenLispKind::MVar(_, _) |
        FrozenLispKind::Goal(_) => CompletionItemKind::CONSTANT,
        FrozenLispKind::List(_) |
        FrozenLispKind::DottedList(_, _) |
        FrozenLispKind::Undef |
        FrozenLispKind::Number(_) |
        FrozenLispKind::String(_) |
        FrozenLispKind::Bool(_) |
        FrozenLispKind::AtomMap(_) |
        FrozenLispKind::Annot(_, _) |
        FrozenLispKind::Ref(_) => CompletionItemKind::VALUE,
        FrozenLispKind::Syntax(_) => CompletionItemKind::EVENT,
        FrozenLispKind::Proc(ref p) if
          // Safety: we don't clone any rc's here
          match *unsafe {p.thaw()} {
            Proc::Builtin(p) => p.to_str() == ad.name().as_str(),
            _ => false,
          } => return None,
        FrozenLispKind::Proc(_) => CompletionItemKind::FUNCTION
      }, e.doc()))
    }
  }
}

async fn completion(path: FileRef, _pos: Position) -> Result<CompletionResponse, ResponseError> {
  let file = SERVER.vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "document symbol nonexistent file"))?;
  let (text, env) = if let Some(old) = try_old(&file) { old } else {
    let env = elaborate(path.clone(), Some(Position::default()), Default::default(), Default::default())
      .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?;
    match env.into_response_error()? {
      None => return Ok(CompletionResponse::Array(vec![])),
      Some((_, env)) => (file.text.ulock().1.clone(), env)
    }
  };
  let text = text.ascii().clone();
  // Safety: We don't use the env field on `fe` for anything other than printing
  let fe = unsafe { env.format_env(&text) };
  let mut res = vec![];
  BuiltinProc::for_each(|_, s| {
    res.push(CompletionItem {
      label: s.into(),
      documentation: None,
      kind: Some(CompletionItemKind::KEYWORD),
      ..Default::default()
    })
  });
  for ad in env.data().iter() {
    if let Some(ci) = make_completion_item(&path, fe, ad, false, TraceKind::Sort) {res.push(ci)}
    if let Some(ci) = make_completion_item(&path, fe, ad, false, TraceKind::Decl) {res.push(ci)}
    if let Some(ci) = make_completion_item(&path, fe, ad, false, TraceKind::Global) {res.push(ci)}
  }
  Ok(CompletionResponse::Array(res))
}

async fn completion_resolve(ci: CompletionItem) -> Result<CompletionItem, ResponseError> {
  let data = if let Some(data) = ci.data {data} else {
    let p = BuiltinProc::from_str(&ci.label)
      .ok_or_else(|| response_err(ErrorCode::InvalidRequest, "missing data"))?;
    return Ok(CompletionItem {
      label: ci.label,
      documentation: Some(Documentation::MarkupContent(MarkupContent {
        kind: MarkupKind::Markdown,
        value: p.doc().into(),
      })),
      kind: Some(CompletionItemKind::KEYWORD),
      ..Default::default()
    })
  };
  let (uri, tk): (Url, TraceKind) = from_value(data).map_err(|e|
    response_err(ErrorCode::InvalidRequest, format!("bad JSON {:?}", e)))?;
  let path = uri.into();
  let file = SERVER.vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "document symbol nonexistent file"))?;

  let maybe_old = if SERVER.elab_on().unwrap_or_default() == ElabOn::Save { try_old(&file) } else { None };
  let (text, env) = if let Some((contents, frozen)) = maybe_old {
    (contents.ascii().clone(), frozen)
  } else {
    let text = file.text.ulock().1.ascii().clone();
    let env = elaborate(path.clone(), Some(Position::default()), Default::default(), Default::default())
      .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?
      .into_response_error()?
      .ok_or_else(|| response_err(ErrorCode::InternalError, "import cycle"))?.1;
    (text, env)
  };

  // Safety: We don't use the env field on `fe` for anything other than printing
  let fe = unsafe { env.format_env(&text) };
  env.get_atom(ci.label.as_bytes()).and_then(|a| make_completion_item(&path, fe, &env.data()[a], true, tk))
    .ok_or_else(|| response_err(ErrorCode::ContentModified, "completion missing"))
}

async fn references<T>(
  path: FileRef, pos: Position, include_self: bool, f: impl Fn(Range) -> T + Send
) -> Result<Vec<T>, ResponseError> {
  macro_rules! or_none {($e:expr)  => {match $e {
    Some(x) => x,
    None => return Ok(vec![])
  }}}
  #[derive(Copy, Clone, PartialEq, Eq)]
  enum Key {
    LispVar(AtomId),
    Var(AtomId),
    Hyp(AtomId),
    Sort(SortId),
    Term(TermId),
    Thm(ThmId),
    Global(AtomId),
  }

  let file = SERVER.vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "references: nonexistent file"))?;
  let text = file.text.ulock().1.ascii().clone();
  let idx = or_none!(text.to_idx(pos));
  let env = elaborate(path, Some(Position::default()), Default::default(), Default::default())
    .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?;
  let env = or_none!(env.into_response_error()?).1;
  let spans = or_none!(env.find(idx));

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
    ObjectKind::Syntax(_) |
    ObjectKind::PatternSyntax(_) |
    ObjectKind::RefineSyntax(_) => None,
    ObjectKind::Var(_, a) => Some(Key::Var(a)),
    ObjectKind::Hyp(_, a) => Some(Key::Hyp(a)),
    ObjectKind::LispVar(_, _, a) => Some(Key::LispVar(a)),
    ObjectKind::Sort(_, a) => Some(Key::Sort(a)),
    ObjectKind::Term(_, a, _) => Some(Key::Term(a)),
    ObjectKind::Thm(_, a) => Some(Key::Thm(a)),
    ObjectKind::Global(_, _, a) => Some(Key::Global(a)),
  };

  let mut res = vec![];
  for &(sp, ref k) in spans.find_pos(idx) {
    let key = match to_key(k) {Some(k) => k, None => continue};
    match key {
      Key::Global(a) if BuiltinProc::from_bytes(env.data()[a].name()).is_some() => continue,
      _ => {}
    }
    let mut cont = |&(sp2, ref k2)| {
      let eq = match *k2 {
        ObjectKind::Expr(_) if !matches!(key, Key::Term(_) | Key::Var(_)) => false,
        ObjectKind::Proof(_) if !matches!(key, Key::Thm(_) | Key::Hyp(_)) => false,
        _ => Some(key) == to_key(k2),
      };
      if eq && (include_self || sp != sp2) {
        let sp2 = if let ObjectKind::Term(_, _, sp2) = *k2 {sp2} else {sp2};
        res.push(f(text.to_range(sp2)))
      }
    };
    if let Key::Var(_) | Key::Hyp(_) | Key::LispVar(_) = key {
      spans.into_iter().for_each(&mut cont);
    } else {
      for spans2 in env.spans() {
        spans2.into_iter().for_each(&mut cont);
      }
    }
  }
  Ok(res)
}

macro_rules! token_types {
  ($([$e:literal]: const $name:ident => $val:path;)*) => {
    const _: () = { let mut _n = 0; $(assert!(_n == $e); _n += 1;)* };
    mod token_types { $(pub(super) const $name: u32 = $e;)* }
    fn get_token_types() -> Vec<SemanticTokenType> { vec![$($val),*] }
  }
}

token_types! {
  [0]: const FVAR => SemanticTokenType::VARIABLE; // local variable / lisp variable
  [1]: const BVAR => SemanticTokenType::PARAMETER; // dummy variable
  [2]: const HVAR => SemanticTokenType::PROPERTY; // hypothesis / subproof variable
  [3]: const THEOREM => SemanticTokenType::METHOD; // theorem
  [4]: const FUNCTION => SemanticTokenType::FUNCTION; // lisp function
  [5]: const MACRO => SemanticTokenType::MACRO; // lisp macro
  [6]: const KEYWORD => SemanticTokenType::KEYWORD; // lisp keyword
}

async fn semantic_tokens(path: FileRef, range: Option<Range>) -> Result<Option<SemanticTokens>, ResponseError> {
  let file = SERVER.vfs.get(&path).ok_or_else(||
    response_err(ErrorCode::InvalidRequest, "semantic tokens nonexistent file"))?;

  let maybe_old = if SERVER.elab_on().unwrap_or_default() == ElabOn::Save { try_old(&file) } else { None };
  let (text, env) = if let Some((contents, frozen)) = maybe_old {
    (contents.ascii().clone(), frozen)
  } else {
    let env = elaborate(path.clone(), Some(Position::default()), Default::default(), Default::default())
      .await.map_err(|e| response_err(ErrorCode::InternalError, format!("{:?}", e)))?;
    match env.into_response_error()? {
      None => return Ok(None),
      Some((_, env)) => (file.text.ulock().1.ascii().clone(), env)
    }
  };
  let range = range.map(|r| {
    let start = text.to_idx(r.start).unwrap_or(0);
    start..text.to_idx(r.end).unwrap_or(text.len())
  });

  let mut data = vec![];
  let mut last_end = 0;
  let mut last_start = Position::default();
  Spans::on_range(env.spans(), range, |spans, &(sp, ref k)| {
    if sp.start < last_end { return }
    let mut push = |token_type, token_modifiers_bitset| {
      let range = text.to_range(sp);
      if range.start.line != range.end.line { return }
      last_end = sp.end;
      data.push(SemanticToken {
        delta_line: range.start.line - last_start.line,
        delta_start: if last_start.line == range.start.line {
          range.start.character - last_start.character
        } else {
          range.start.character
        },
        length: range.end.character - range.start.character,
        token_type,
        token_modifiers_bitset,
      });
      last_start = range.start;
    };
    match k {
      ObjectKind::Sort(..) |
      ObjectKind::Term(..) |
      ObjectKind::Thm(true, _) |
      ObjectKind::RefineSyntax(_) |
      ObjectKind::Import(_) |
      // Don't highlight non-text keywords
      ObjectKind::Syntax(Syntax::Quote | Syntax::Unquote) => {}
      ObjectKind::Thm(false, _) |
      ObjectKind::Proof(_) => push(token_types::THEOREM, 0),
      ObjectKind::Syntax(_) => push(token_types::KEYWORD, 0),
      ObjectKind::PatternSyntax(_) => push(token_types::FUNCTION, 1),
      &ObjectKind::Var(_, x) => push(match spans.lc.as_ref().and_then(|lc| lc.vars.get(&x)) {
        Some((_, InferSort::Bound {..})) => token_types::BVAR,
        _ => token_types::FVAR,
      }, 0),
      &ObjectKind::Hyp(..) => push(token_types::HVAR, 0),
      ObjectKind::Expr(e) => {
        let head = e.uncons().next().unwrap_or(e);
        let a = if let Some(a) = head.as_atom() { a } else { return };
        if let Some(DeclKey::Term(_)) = env.data()[a].decl() { return }
        push(match spans.lc.as_ref().and_then(|lc| lc.vars.get(&a)) {
          Some((_, InferSort::Bound {..})) => token_types::BVAR,
          _ => token_types::FVAR,
        }, 0)
      }
      ObjectKind::LispVar(_, false, _) |
      ObjectKind::Global(true, false, _) => push(token_types::FVAR, 0),
      ObjectKind::LispVar(_, true, _) |
      ObjectKind::Global(true, true, _) => push(token_types::FUNCTION, 0),
      &ObjectKind::Global(false, call, a) => {
        let ad = &env.data()[a];
        if let Some(e) = ad.lisp().as_ref() {
          let (x, m) = match *e.unwrap() {
            FrozenLispKind::Syntax(_) => (token_types::MACRO, 0),
            FrozenLispKind::Proc(ref proc) => {
              // Safety: We are not cloning the expression
              let builtin = match unsafe { proc.thaw() } {
                Proc::Lambda { .. } => 0,
                _ => 1
              };
              (token_types::FUNCTION, builtin)
            }
            _ if call => (token_types::FUNCTION, 0),
            _ => (token_types::FVAR, 0),
          };
          push(x, m)
        } else if BuiltinProc::from_bytes(ad.name()).is_some() {
          push(token_types::FUNCTION, 1)
        }
      }
    }
  });
  Ok(Some(SemanticTokens { result_id: None, data }))
}

struct Server {
  conn: Connection,
  #[allow(unused)]
  caps: Mutex<ClientCapabilities>,
  reqs: OpenRequests,
  vfs: Vfs,
  pool: ThreadPool,
  #[allow(clippy::type_complexity)]
  threads: Arc<(Mutex<VecDeque<(Job, Arc<AtomicBool>)>>, Condvar)>,
  options: Mutex<ServerOptions>,
}


/// Options for [`Server`]; for example, whether to apply changes and
/// elaborate on change or save.
/// The fields are `Option<T>` rather than defaults for each T since it might
/// be useful to tell whether a certain option has been set by the user or left
/// as the default. If they were just T, `T::Default` could mean that the user selected
/// a value that's the same as the default, or it could mean that it was untouched.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct InitOptions {
  extra_capabilities: Option<ClientCapabilitiesExt>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct ClientCapabilitiesExt {
  goal_view: Option<bool>,
}

struct ClientCapabilities {
  reg_id: Option<RequestId>,
  definition_location_links: bool,
  goal_view: bool,
}

impl ClientCapabilities {
  fn new(params: InitializeParams) -> ClientCapabilities {
    let dll = match params.capabilities.text_document.as_ref()
      .and_then(|d| d.definition.as_ref()) {
      Some(&GotoCapability {link_support: Some(b), ..}) => b,
      _ => false
    };
    let goal_view = params.initialization_options
      .and_then(|o| from_value(o).ok()).and_then(|o: InitOptions| o.extra_capabilities)
      .and_then(|c| c.goal_view).unwrap_or(false);
    ClientCapabilities { reg_id: None, definition_location_links: dll, goal_view }
  }

  fn register(&mut self) -> Result<()> {
    assert!(self.reg_id.is_none());
    let regs = vec![
      Registration {
        id: String::new(),
        method: "workspace/didChangeConfiguration".into(),
        register_options: None,
      }
    ];

    if !regs.is_empty() {
      register_capability("regs".into(), regs)?;
      self.reg_id = Some(String::from("regs").into());
    }
    Ok(())
  }

  fn finish_register(&mut self, _resp: &Response) {
    assert!(self.reg_id.take().is_some());
  }
}

enum DepChangeReason { Open, Close, Elab }

impl std::fmt::Display for DepChangeReason {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Open => write!(f, "open"),
      Self::Close => write!(f, "close"),
      Self::Elab => write!(f, "elaboration"),
    }
  }
}

#[derive(Debug)]
enum ElabReason { Open, Save, Change(Position) }

impl ElabReason {
  fn start(&self) -> Option<Position> {
    match *self {
      Self::Change(p) => Some(p),
      Self::Open => Some(Position::default()),
      Self::Save => None
    }
  }
}

impl std::fmt::Display for ElabReason {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Open => write!(f, "open"),
      Self::Save => write!(f, "save"),
      Self::Change(_) => write!(f, "change"),
    }
  }
}

enum Job {
  RequestHandler(RequestId, Option<Box<RequestType>>),
  Elaborate(FileRef, ElabReason),
  ElaborateDep(FileRef, FileRef, Option<(FSender<ElabResult<u64>>, ArcList<FileRef>)>),
  DepChange(FileRef, FileRef, DepChangeReason),
}

impl std::fmt::Display for Job {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Job::RequestHandler(id, _) => write!(f, "handle request {}", id),
      Job::Elaborate(path, ElabReason::Open) => write!(f, "elaborate {} on open", path),
      Job::Elaborate(path, ElabReason::Save) => write!(f, "elaborate {} on save", path),
      Job::Elaborate(path, ElabReason::Change(_)) => write!(f, "elaborate {} on change", path),
      Job::ElaborateDep(from, to, _) => write!(f, "elaborate {} needed for {}", from, to),
      Job::DepChange(from, to, reason) => write!(f, "elaborate {} for {} {}", to, from, reason),
    }
  }
}

impl Job {
  fn spawn_core<F>(self, cancel: Arc<AtomicBool>, fut: F)
  where F: std::future::Future<Output=()> + Send + 'static {
    SERVER.threads.0.ulock().push_back((self, cancel.clone()));
    SERVER.pool.spawn_ok(async move {
      fut.await;
      let (m, cvar) = &*SERVER.threads;
      let mut vec = m.ulock();
      let a: *const AtomicBool = &*cancel;
      let i = vec.iter().enumerate().find(|&(_, (_, b))| a == &**b).expect("my job is missing").0;
      vec.swap_remove_front(i);
      drop(vec);
      cvar.notify_all();
    });
  }

  fn spawn(mut self) {
    let cancel: Arc<AtomicBool> = Default::default();
    match &mut self {
      Job::RequestHandler(id, req) => {
        SERVER.reqs.ulock().insert(id.clone(), cancel.clone());
        let req = req.take().expect("job already started");
        let id = id.clone();
        self.spawn_core(cancel.clone(), async {
          RequestHandler {id, cancel}.handle(*req).await
            .unwrap_or_else(|e| eprintln!("Request failed: {:?}", e))
        });
      }
      Job::Elaborate(path, reason) => {
        let f = elaborate_and_report(path.clone(), reason.start(), cancel.clone());
        self.spawn_core(cancel, f)
      }
      Job::ElaborateDep(p, _, args) => {
        let (send, rd) = args.take().expect("job already started");
        let f = elaborate_and_send(p.clone(), cancel.clone(), send, rd);
        self.spawn_core(cancel, f)
      }
      Job::DepChange(_, to, _) => {
        let f = dep_change(to.clone(), cancel.clone());
        self.spawn_core(cancel, f)
      }
    }
  }
}

/// Options for [`Server`]; for example, whether to apply changes and
/// elaborate on change or save.
/// The fields are `Option<T>` rather than defaults for each T since it might
/// be useful to tell whether a certain option has been set by the user or left
/// as the default. If they were just T, `T::Default` could mean that the user selected
/// a value that's the same as the default, or it could mean that it was untouched.
#[derive(Debug, Eq, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct ServerOptions {
  elab_on: Option<ElabOn>,
  executable_path: Option<std::path::PathBuf>,
  max_number_of_problems: usize,
  syntax_docs: Option<bool>,
  log_errors: Option<bool>,
  report_upstream_errors: Option<bool>,
}

impl std::default::Default for ServerOptions {
  fn default() -> Self {
    ServerOptions {
      elab_on: None,
      executable_path: None,
      max_number_of_problems: 100,
      syntax_docs: None,
      log_errors: None,
      report_upstream_errors: None,
    }
  }
}

/// Enum for use in [`ServerOptions`] showing when the user wants changes to be applied
/// and the new file to be elaborated.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
enum ElabOn {
  /// Apply changes and elaborate every time a change is received from the server
  Change,
  /// Apply changes and elaborate when a save message is received.
  Save,
}

impl std::default::Default for ElabOn {
  fn default() -> Self { Self::Change }
}

fn send_config_request() -> Result<()> {
  use lsp_types::request::{WorkspaceConfiguration, Request};
  let params = lsp_types::ConfigurationParams {
    items: vec![lsp_types::ConfigurationItem {
        scope_uri: None,
        section: Some("metamath-zero".to_string()),
    }],
  };
  let req = lsp_server::Request::new(
    RequestId::from("get_config".to_string()),
    WorkspaceConfiguration::METHOD.to_string(),
    params
  );
  send_message(req)
}

impl Server {
  fn new() -> Result<Server> {
    let (conn, _iot) = Connection::stdio();
    let params = from_value(conn.initialize(
      to_value(ServerCapabilities {
        text_document_sync: Some(
          TextDocumentSyncCapability::Kind(TextDocumentSyncKind::INCREMENTAL)),
        hover_provider: Some(true.into()),
        completion_provider: Some(CompletionOptions {
          resolve_provider: Some(true),
          ..Default::default()
        }),
        definition_provider: Some(OneOf::Left(true)),
        document_symbol_provider: Some(OneOf::Left(true)),
        references_provider: Some(OneOf::Left(true)),
        document_highlight_provider: Some(OneOf::Left(true)),
        semantic_tokens_provider: Some(SemanticTokensOptions {
          legend: SemanticTokensLegend {
            token_types: get_token_types(),
            token_modifiers: vec![SemanticTokenModifier::DEFAULT_LIBRARY],
          },
          range: Some(true),
          full: Some(SemanticTokensFullOptions::Bool(true)),
          ..Default::default()
        }.into()),
        ..Default::default()
      })?
    )?)?;
    Ok(Server {
      caps: Mutex::new(ClientCapabilities::new(params)),
      conn,
      reqs: Mutex::new(HashMap::new()),
      vfs: Vfs(Mutex::new(HashMap::new())),
      pool: ThreadPool::new()?,
      threads: Default::default(),
      options: Mutex::new(ServerOptions::default()),
    })
  }

  fn elab_on(&self) -> Option<ElabOn> {
    self.options.ulock().elab_on
  }

  fn run(&self) {
    let logger = Logger::start();
    drop(self.caps.ulock().register());

    // We need this to be able to match on the response for the config getter, but
    // we can't use a string slice since lsp_server doesn't export IdRepr
    let get_config_id = lsp_server::RequestId::from(String::from("get_config"));
    // Request the user's initial configuration on startup.
    if let Err(e) = send_config_request() {
      eprintln!("Server panicked: {:?}", e);
    }

    loop {
      match (|| -> Result<bool> {
        let Server {conn, caps, reqs, vfs, options, ..} = &*SERVER;
        match conn.receiver.recv() {
          Err(RecvError) => return Ok(true),
          Ok(Message::Request(req)) => {
            if conn.handle_shutdown(&req)? {
              return Ok(true)
            }
            if let Some((id, req)) = parse_request(req)? {
              Job::RequestHandler(id, Some(Box::new(req))).spawn();
            }
          }
          Ok(Message::Response(resp)) => {
            if resp.id == get_config_id {
              if let Some(val) = resp.result {
                let [config]: [ServerOptions; 1] = from_value(val)?;
                *self.options.ulock() = config;
              }
            } else {
              let mut caps = caps.ulock();
              if caps.reg_id.as_ref().map_or(false, |rid| rid == &resp.id) {
                caps.finish_register(&resp);
              } else {
                log!("response to unknown request {}", resp.id)
              }
            }
          }
          Ok(Message::Notification(notif)) => {
            #[allow(clippy::wildcard_imports)] use lsp_types::notification::*;
            match notif.method.as_str() {
              Cancel::METHOD => {
                let CancelParams {id} = from_value(notif.params)?;
                if let Some(cancel) = reqs.ulock().get(&nos_id(id)) {
                  cancel.store(true, Ordering::Relaxed);
                }
              }
              DidOpenTextDocument::METHOD => {
                let DidOpenTextDocumentParams {text_document: doc} = from_value(notif.params)?;
                let path = doc.uri.into();
                log!("open {:?}", path);
                vfs.open_virt(path, doc.version, doc.text);
              }
              DidChangeTextDocument::METHOD => {
                let DidChangeTextDocumentParams {text_document: doc, content_changes} = from_value(notif.params)?;
                if !content_changes.is_empty() {
                  let path = doc.uri.into();
                  log!("change {:?}", path);
                  let start = {
                    let file = vfs.get(&path).ok_or("changed nonexistent file")?;
                    let (version, text) = &mut *file.text.ulock();
                    *version = Some(doc.version);
                    let (start, s) = text.ascii().apply_changes(content_changes.into_iter());
                    *text = FileContents::Ascii(Arc::new(s));
                    start
                  };
                  if options.ulock().elab_on.unwrap_or_default() == ElabOn::Change {
                    Job::Elaborate(path, ElabReason::Change(start)).spawn();
                  }
                }
              }
              DidCloseTextDocument::METHOD => {
                let DidCloseTextDocumentParams {text_document: doc} = from_value(notif.params)?;
                let path = doc.uri.into();
                log!("close {:?}", path);
                vfs.close(&path)?;
              }
              DidSaveTextDocument::METHOD => {
                let DidSaveTextDocumentParams {text_document: doc, ..} = from_value(notif.params)?;
                let path = FileRef::from(doc.uri);
                log!("save {:?}", path);
                if options.ulock().elab_on.unwrap_or_default() == ElabOn::Save {
                  Job::Elaborate(path, ElabReason::Save).spawn();
                }
              }
              DidChangeConfiguration::METHOD => send_config_request()?,
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
    logger.stop();
    let (mutex, cvar) = &*self.threads;
    let mut g = mutex.ulock();
    g.iter().for_each(|(_, c)| c.store(true, Ordering::Relaxed));
    while !g.is_empty() {
      // use itertools::Itertools;
      // eprintln!("waiting on threads:\n  {}", g.iter().map(|(s, _)| s).format("\n  "));
      g = cvar.uwait(g)
    }
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
    use {simplelog::{Config, LevelFilter, WriteLogger}, std::fs::File};
    std::env::set_var("RUST_BACKTRACE", "1");
    if let Ok(f) = File::create("lsp.log") {
      let _ = WriteLogger::init(LevelFilter::Debug, Config::default(), f);
    }
  }
  let server = &*SERVER; // start the server
  drop(log_message("started".into()));
  if args.is_present("no_log_errors") {
    server.options.ulock().log_errors = Some(false)
  }
  server.run();
  std::mem::take(&mut *server.reqs.ulock());
  std::mem::take(&mut *server.vfs.0.ulock());
}
