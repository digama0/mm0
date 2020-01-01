use std::ops::Deref;
use std::{fs, io};
use std::sync::{Arc, Mutex, atomic::{AtomicBool, Ordering}, Condvar};
use std::collections::{HashMap, HashSet, hash_map::Entry, VecDeque};
use std::result;
use futures::{FutureExt, channel::oneshot::{Sender as FSender, channel}};
use futures::executor::ThreadPool;
use lsp_server::*;
use serde::ser::Serialize;
use serde_json::{from_value, to_value};
use lsp_types::*;
use crossbeam::{channel::{Sender, SendError, RecvError}};
use crate::util::*;
use crate::lined_string::LinedString;
use crate::parser::{AST, parse};
use crate::elab::{Environment, ElabError, Elaborator};

#[derive(Debug)]
struct ServerError(BoxError);

type Result<T> = result::Result<T, ServerError>;

impl From<serde_json::Error> for ServerError {
  fn from(e: serde_json::error::Error) -> Self { ServerError(Box::new(e)) }
}

impl From<ProtocolError> for ServerError {
  fn from(e: ProtocolError) -> Self { ServerError(Box::new(e)) }
}

impl From<RecvError> for ServerError {
  fn from(e: RecvError) -> Self { ServerError(Box::new(e)) }
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

lazy_static! {
  static ref LOGGER: (Mutex<Vec<String>>, Condvar) = Default::default();
}
#[allow(unused)]
pub fn log(s: String) {
  LOGGER.0.lock().unwrap().push(s);
  LOGGER.1.notify_one();
}

#[allow(unused)]
macro_rules! log {
  ($($es:tt)*) => {crate::server::log(format!($($es)*))}
}

#[derive(Debug, Clone)]
enum Job {
  Elaborate {path: FileRef, start: Position},
  DepChange(FileRef)
}

impl Job {
  fn path(&self) -> &FileRef {
    match self {
      Job::Elaborate{path, ..} => path,
      Job::DepChange(path) => path
    }
  }
  fn merge(&mut self, other: &Job) -> bool {
    if self.path() != other.path() {return false}
    match (self, other) {
      (Job::Elaborate {start, ..}, &Job::Elaborate {start: other, ..}) =>
        if *start > other {*start = other},
      (Job::Elaborate {..}, Job::DepChange(_)) => {}
      (s @ Job::DepChange(_), Job::Elaborate {..}) => *s = other.clone(),
      (Job::DepChange(_), Job::DepChange(_)) => {}
    }
    true
  }

  async fn run<'a>(self, server: ServerRef<'a>, cancel: Arc<AtomicBool>) -> Result<()> {
    match self {
      Job::Elaborate {path, start} => {
        if let Some(file) = server.vfs.get(&path) {
          let (old_ast, old_env, old_deps) = match file.parsed.lock().unwrap().0.take() {
            None => (None, None, Vec::new()),
            Some(FileCache::Dirty(ast)) => (Some((start, ast)), None, Vec::new()),
            Some(FileCache::Ready{ast, errors, deps, env}) => (Some((start, ast)), Some((errors, env)), deps),
          };
          let (idx, ast) = parse(file.text.lock().unwrap().1.clone(), old_ast);
          let ast = Arc::new(ast);
          server.elaborate(&file, &old_deps, idx, ast.clone(), &path, old_env, cancel).await?;
        }
      }
      Job::DepChange(path) => {
        if let Some(file) = server.vfs.get(&path) {
          let (idx, ast, old_env, old_deps) = match file.parsed.lock().unwrap().0.take() {
            None => {
              let (idx, ast) = parse(file.text.lock().unwrap().1.clone(), None);
              (idx, Arc::new(ast), None, Vec::new())
            }
            Some(FileCache::Dirty(ast)) => (ast.stmts.len(), ast, None, Vec::new()),
            Some(FileCache::Ready{ast, errors, deps, env}) => (ast.stmts.len(), ast, Some((errors, env)), deps),
          };
          server.elaborate(&file, &old_deps, idx, ast.clone(), &path, old_env, cancel).await?;
        }
      }
    }
    Ok(())
  }
}

struct Jobs {
  jobs: Mutex<(Option<(Job, Arc<AtomicBool>)>, Option<VecDeque<Job>>)>,
  wait: Condvar,
  pool: ThreadPool
}

impl Jobs {
  fn extend(&self, mut new: Vec<Job>) {
    if !new.is_empty() {
      // log!("jobs {:?}", new);
      let changed = {
        let mut g = self.jobs.lock().unwrap();
        if let Some((active, cancel)) = &mut g.0 {
          if new.iter().any(|njob| njob.path() == active.path()) {
            cancel.store(true, Ordering::Relaxed);
          }
        }
        if let Some(jobs) = &mut g.1 {
          jobs.retain(|job| new.iter_mut().all(|njob| !njob.merge(job)));
          jobs.extend(new);
          true
        } else {false}
      };
      if changed { self.wait.notify_one() }
    }
  }

  fn new_worker(&self, server: Arc<Server>) -> Result<()> {
    loop {
      let (job, cancel) = {
        let mut g = self.jobs.lock().unwrap();
        loop {
          if let (active, Some(jobs)) = &mut *g {
            // log!("done {:?}", active.take());
            if let Some(job) = jobs.pop_front() {
              let cancel = Arc::new(AtomicBool::new(false));
              *active = Some((job.clone(), cancel.clone()));
              break (job, cancel)
            } else {
              g = self.wait.wait(g).unwrap(); continue}
          } else {return Ok(())}
        }
      };
      // log!("start {:?}", job);
      let s = server.clone();
      self.pool.spawn_ok(async move {
        let server = (*s).as_ref();
        std::panic::AssertUnwindSafe(job.run(server, cancel)).catch_unwind().await
          .unwrap_or_else(|_| Err("server panic".into()))
          .unwrap_or_else(|e| server.log(format!("{:?}", e).into()).unwrap())
      });
    }
  }

  fn stop(&self) {
    {
      let (active, jobs) = &mut *self.jobs.lock().unwrap();
      if let Some((_, cancel)) = active {cancel.store(true, Ordering::Relaxed)}
      jobs.take();
    }
    self.wait.notify_all()
  }
}

enum FileCache {
  Dirty(Arc<AST>),
  Ready {
    ast: Arc<AST>,
    errors: Vec<ElabError>,
    env: Arc<Environment>,
    deps: Vec<FileRef>,
  }
}

struct VirtualFile {
  /// File data, saved (true) or unsaved (false)
  text: Mutex<(bool, Arc<LinedString>)>,
  /// File parse
  parsed: Mutex<(Option<FileCache>, Vec<FSender<Arc<Environment>>>)>,
  /// Get notified on cache fill
  cvar: Condvar,
  /// Files that depend on this one
  downstream: Mutex<HashSet<FileRef>>,
}

impl VirtualFile {
  fn new(text: String) -> VirtualFile {
    VirtualFile {
      text: Mutex::new((true, Arc::new(text.into()))),
      parsed: Mutex::new((None, vec![])),
      cvar: Condvar::new(),
      downstream: Mutex::new(HashSet::new())
    }
  }
}

struct VFS(Mutex<HashMap<FileRef, Arc<VirtualFile>>>);

impl VFS {
  fn get(&self, path: &FileRef) -> Option<Arc<VirtualFile>> {
    self.0.lock().unwrap().get(path).cloned()
  }

  fn open_virt(&self, queue: &mut Vec<Job>, path: FileRef, text: String) -> Result<Arc<VirtualFile>> {
    queue.push(Job::Elaborate {path: path.clone(), start: Position::new(0, 0)});
    let file = Arc::new(VirtualFile::new(text));
    match self.0.lock().unwrap().entry(path) {
      Entry::Occupied(entry) => {
        for dep in entry.get().downstream.lock().unwrap().clone() {
          self.dirty(queue, &dep);
        }
        Ok(file)
      }
      Entry::Vacant(entry) => Ok(entry.insert(file).clone())
    }
  }

  fn close(&self, queue: &mut Vec<Job>, path: &FileRef) {
    if let Some(file) = self.0.lock().unwrap().remove(path) {
      if !file.text.lock().unwrap().0 {
        for dep in file.downstream.lock().unwrap().clone() {
          self.dirty(queue, &dep);
        }
      }
    }
  }

  fn set_downstream(&self, from: &FileRef, to: FileRef, val: bool) {
    let file = self.0.lock().unwrap().get(from).unwrap().clone();
    let mut ds = file.downstream.lock().unwrap();
    if val { ds.insert(to); }
    else { ds.remove(&to); }
  }

  fn update_downstream(&self, old_deps: &Vec<FileRef>, deps: &Vec<FileRef>, to: &FileRef) {
    for from in old_deps {
      if !deps.contains(from) {
        self.set_downstream(from, to.clone(), false)
      }
    }
    for from in deps {
      if !old_deps.contains(from) {
        self.set_downstream(from, to.clone(), true)
      }
    }
  }

  fn dirty(&self, queue: &mut Vec<Job>, path: &FileRef) {
    queue.push(Job::DepChange(path.clone()));
    let file = self.0.lock().unwrap().get(path).unwrap().clone();
    {
      let lock = &mut file.parsed.lock().unwrap().0;
      match lock.take() {
        None => {}
        Some(FileCache::Ready{ast, ..}) => *lock = Some(FileCache::Dirty(ast)),
        Some(FileCache::Dirty(ast)) => *lock = Some(FileCache::Dirty(ast)),
      }
    }
    for dep in file.downstream.lock().unwrap().clone() {
      self.dirty(queue, &dep);
    }
  }
}

enum RequestType {
  Completion(CompletionParams),
  Hover(TextDocumentPositionParams),
  Definition(TextDocumentPositionParams),
  DocumentSymbol(DocumentSymbolParams),
}

fn parse_request(req: Request) -> Result<Option<(RequestId, RequestType)>> {
  let Request {id, method, params} = req;
  match method.as_str() {
    "textDocument/completion"     => Ok(Some((id, RequestType::Completion(from_value(params)?)))),
    "textDocument/hover"          => Ok(Some((id, RequestType::Hover(from_value(params)?)))),
    "textDocument/definition"     => Ok(Some((id, RequestType::Definition(from_value(params)?)))),
    "textDocument/documentSymbol" => Ok(Some((id, RequestType::DocumentSymbol(from_value(params)?)))),
    _ => Ok(None)
  }
}

#[derive(Clone, Copy)]
struct ServerRef<'a> {
  sender: &'a Sender<Message>,
  vfs: &'a VFS,
  jobs: &'a Jobs,
}

impl ServerRef<'_> {
  fn send<T: Into<Message>>(&self, t: T) -> Result<()> {
    Ok(self.sender.send(t.into())?)
  }

  #[allow(unused)]
  fn show_message(&self, typ: MessageType, message: String) -> Result<()> {
    self.send(Notification {
      method: "window/showMessage".to_owned(),
      params: to_value(ShowMessageParams {typ, message})?
    })
  }

  #[allow(unused)]
  fn log(&self, message: String) -> Result<()> {
    self.send(Notification {
      method: "window/logMessage".to_owned(),
      params: to_value(LogMessageParams {typ: MessageType::Log, message})?
    })
  }

  fn send_diagnostics(&self, uri: Url, diagnostics: Vec<Diagnostic>) -> Result<()> {
    self.send(Notification {
      method: "textDocument/publishDiagnostics".to_owned(),
      params: to_value(PublishDiagnosticsParams {uri, diagnostics})?
    })
  }


  async fn elaborate(&self,
    file: &VirtualFile,
    old_deps: &Vec<FileRef>,
    idx: usize,
    ast: Arc<AST>,
    path: &FileRef,
    old_env: Option<(Vec<ElabError>, Arc<Environment>)>,
    cancel: Arc<AtomicBool>
  ) -> Result<()> {
    let mut deps = Vec::new();
    let elab = Elaborator::new(ast.clone(), path.clone(), cancel.clone());
    let fut = elab.as_fut(old_env.map(|(errs, e)| (idx, errs, e)), |path| {
      // log!("request {:?}", path);
      let (path, val) = match self.vfs.0.lock().unwrap().entry(FileRef::new(path)) {
        Entry::Occupied(e) => (e.key().clone(), e.get().clone()),
        Entry::Vacant(e) => {
          let path = e.key().clone();
          let s = fs::read_to_string(path.path())?;
          // log!("got ({:?}, {})", path, s.len());
          let val = e.insert(Arc::new(VirtualFile::new(s))).clone();
          (path, val)
        }
      };
      let (send, recv) = channel();
      {
        let (fc, waiting) = &mut *val.parsed.lock().unwrap();
        if let Some(FileCache::Ready {env, ..}) = fc {
          send.send(env.clone()).unwrap_or_else(|_| panic!("send failed"));
        } else {
          waiting.push(send);
          self.jobs.extend(vec![Job::Elaborate {path: path.clone(), start: Position::default()}]);
        }
      }
      deps.push(path);
      Ok(recv)
    });
    let (errors, env) = fut.await;
    // log!("elabbed {:?}", path);
    if !cancel.load(Ordering::Relaxed) {
      self.send_diagnostics(path.url().clone(),
        ast.errors.iter().map(|e| e.to_diag(&ast.source))
          .chain(errors.iter().map(|e| e.to_diag(&ast.source))).collect())?;
      self.vfs.update_downstream(&old_deps, &deps, &path);
      let env = Arc::new(env);
      let (fc, waiting) = &mut *file.parsed.lock().unwrap();
      for w in waiting.drain(..) {
        let _ = w.send(env.clone());
      }
      *fc = Some(FileCache::Ready {ast, errors, deps, env});
    }
    file.cvar.notify_all();
    Ok(())
  }
}

type OpenRequests = Mutex<HashMap<RequestId, Arc<AtomicBool>>>;

struct RequestHandler<'a> {
  server: ServerRef<'a>,
  reqs: &'a OpenRequests,
  id: RequestId,
  #[allow(unused)]
  cancel: &'a AtomicBool,
}

impl<'a> Deref for RequestHandler<'a> {
  type Target = ServerRef<'a>;
  fn deref(&self) -> &ServerRef<'a> { &self.server }
}

impl RequestHandler<'_> {
  fn handle(self, req: RequestType) -> Result<()> {
    match req {
      _ => {}
    }

    self.finish(Ok(()))
  }

  fn finish<T: Serialize>(self, resp: result::Result<T, ResponseError>) -> Result<()> {
    self.reqs.lock().unwrap().remove(&self.id);
    self.sender.send(Message::Response(match resp {
      Ok(val) => Response { id: self.id, result: Some(to_value(val)?), error: None },
      Err(e) => Response { id: self.id, result: None, error: Some(e) }
    }))?;
    Ok(())
  }
}

struct Server {
  conn: Connection,
  #[allow(unused)]
  params: InitializeParams,
  reqs: OpenRequests,
  vfs: VFS,
  jobs: Jobs,
}

impl Server {
  fn new() -> Result<Server> {
    let (conn, _iot) = Connection::stdio();
    Ok(Server {
      params: from_value(conn.initialize(
        to_value(ServerCapabilities {
          text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::Incremental)),
          // hover_provider: Some(true),
          // completion_provider: Some(CompletionOptions {
          //   resolve_provider: Some(true),
          //   ..Default::default()
          // }),
          // definition_provider: Some(true),
          // document_symbol_provider: Some(true),
          ..Default::default()
        })?)?)?,
      conn,
      reqs: Mutex::new(HashMap::new()),
      vfs: VFS(Mutex::new(HashMap::new())),
      jobs: Jobs {
        jobs: Mutex::new((None, Some(VecDeque::new()))),
        wait: Condvar::new(),
        pool: ThreadPool::new().unwrap()
      },
    })
  }

  fn as_ref(&self) -> ServerRef {
    ServerRef {sender: &self.conn.sender, vfs: &self.vfs, jobs: &self.jobs}
  }
  fn run(self) {
    let this = &Arc::new(self);
    crossbeam::scope(|s| {
      let server = (**this).as_ref();
      let jobs = &this.jobs;
      s.spawn(move |_| jobs.new_worker(this.clone()).unwrap());
      s.spawn(move |_| loop {
        for s in LOGGER.1.wait(LOGGER.0.lock().unwrap()).unwrap().drain(..) {
          server.log(s).unwrap()
        }
      });
      let conn = &this.conn;
      let reqs = &this.reqs;
      let vfs = &this.vfs;
      loop {
        match (move || -> Result<bool> {
          let server = ServerRef {sender: &conn.sender, vfs, jobs};
          match conn.receiver.recv()? {
            Message::Request(req) => {
              if conn.handle_shutdown(&req)? {
                jobs.stop();
                return Ok(true)
              }
              if let Some((id, req)) = parse_request(req)? {
                let cancel = Arc::new(AtomicBool::new(false));
                reqs.lock().unwrap().insert(id.clone(), cancel.clone());
                s.spawn(move |_|
                  RequestHandler {reqs, id, cancel: &cancel, server}.handle(req).unwrap());
              }
            }
            Message::Response(resp) => {
              reqs.lock().unwrap().get(&resp.id).ok_or_else(|| "response to unknown request")?
                .store(true, Ordering::Relaxed);
            }
            Message::Notification(notif) => {
              match notif.method.as_str() {
                "$/cancelRequest" => {
                  let CancelParams {id} = from_value(notif.params)?;
                  if let Some(cancel) = reqs.lock().unwrap().get(&nos_id(id)) {
                    cancel.store(true, Ordering::Relaxed);
                  }
                }
                "textDocument/didOpen" => {
                  let DidOpenTextDocumentParams {text_document: doc} = from_value(notif.params)?;
                  let mut queue = Vec::new();
                  let path = FileRef::from_url(doc.uri);
                  vfs.open_virt(&mut queue, path, doc.text)?;
                  jobs.extend(queue);
                }
                "textDocument/didChange" => {
                  let DidChangeTextDocumentParams {text_document: doc, content_changes} = from_value(notif.params)?;
                  if !content_changes.is_empty() {
                    let path = FileRef::from_url(doc.uri);
                    let start = {
                      let file = vfs.get(&path).ok_or("changed nonexistent file")?;
                      let mut text = file.text.lock().unwrap();
                      text.0 = true;
                      let (start, s) = text.1.apply_changes(content_changes.into_iter());
                      text.1 = Arc::new(s);
                      start
                    };
                    jobs.extend(vec![Job::Elaborate {path, start}]);
                  }
                }
                "textDocument/didClose" => {
                  let DidCloseTextDocumentParams {text_document: doc} = from_value(notif.params)?;
                  let path = FileRef::from_url(doc.uri);
                  let mut queue = Vec::new();
                  vfs.close(&mut queue, &path);
                  jobs.extend(queue);
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

pub fn main(mut args: impl Iterator<Item=String>) {
  if args.next().map_or(false, |s| s == "--debug") {
    std::env::set_var("RUST_BACKTRACE", "1");
    use {simplelog::*, std::fs::File};
    let _ = WriteLogger::init(LevelFilter::Debug, Config::default(), File::create("lsp.log").unwrap());
  }
  Server::new().expect("Initialization failed").run()
}