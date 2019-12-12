use std::ops::Deref;
use std::{fs, io};
use std::path::{PathBuf};
use std::sync::{Arc, Mutex, atomic::{AtomicBool, Ordering}, Condvar};
use std::collections::{HashMap, HashSet, hash_map::Entry, VecDeque};
use std::result;
use lsp_server::*;
use serde::ser::Serialize;
use serde_json::{from_value, to_value};
use lsp_types::*;
use crossbeam::{channel::{Sender, SendError, RecvError}};
use crate::util::*;
use crate::lined_string::LinedString;
use crate::parser::{AST, parse};
use crate::elab::{Environment, ElabError, FileServer};

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

fn nos_id(nos: NumberOrString) -> RequestId {
  match nos {
    NumberOrString::Number(n) => n.into(),
    NumberOrString::String(s) => s.into(),
  }
}

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
}

struct Jobs(Mutex<Option<VecDeque<Job>>>, Condvar);

impl Jobs {
  fn extend(&self, new: Vec<Job>) {
    if !new.is_empty() {
      let changed = if let Some(jobs) = &mut *self.0.lock().unwrap() {
        jobs.retain(|job| new.iter().all(|njob| njob.path() != job.path()));
        jobs.extend(new); true
      } else {false};
      if changed { self.1.notify_one() }
    }
  }

  fn new_worker(&self, server: ServerRef) -> Result<()> {
    loop {
      let job = match &mut *self.1.wait(self.0.lock().unwrap()).unwrap() {
        None => return Ok(()),
        Some(jobs) => match jobs.pop_front() {
          None => continue,
          Some(job) => job,
        }
      };
      match job {
        Job::Elaborate {path, start} => {
          if let Some(file) = server.vfs.get(&path) {
            let (old_ast, old_env, old_deps) = match file.parsed.lock().unwrap().take() {
              None => (None, None, Vec::new()),
              Some(FileCache::Dirty(ast)) => (Some((start, ast)), None, Vec::new()),
              Some(FileCache::Ready{ast, errors, deps, env}) => (Some((start, ast)), Some((errors, env)), deps),
            };
            let (idx, ast) = parse(file.text.lock().unwrap().1.clone(), old_ast);
            let (errors, env, deps) = server.elaborate(path.clone(), &ast,
              old_env.map(|(errs, e)| (idx, errs, e)));
            server.send_diagnostics(path.url().clone(),
              ast.errors.iter().map(|e| e.to_diag(&ast.source))
                .chain(errors.iter().map(|e| e.to_diag(&ast.source))).collect())?;
            server.vfs.update_downstream(&old_deps, &deps, &path);
            *file.parsed.lock().unwrap() = Some(FileCache::Ready {ast, errors, deps, env: Arc::new(env)});
            file.cvar.notify_all();
          }
        }
        Job::DepChange(path) => {
          if let Some(file) = server.vfs.get(&path) {
            let ((idx, ast), old_env, old_deps) = match file.parsed.lock().unwrap().take() {
              None => (parse(file.text.lock().unwrap().1.clone(), None), None, Vec::new()),
              Some(FileCache::Dirty(ast)) => ((ast.stmts.len(), ast), None, Vec::new()),
              Some(FileCache::Ready{ast, errors, deps, env}) => ((ast.stmts.len(), ast), Some((errors, env)), deps),
            };
            let (errors, env, deps) = server.elaborate(path.clone(), &ast,
              old_env.map(|(errs, e)| (idx, errs, e)));
            server.send_diagnostics(path.url().clone(),
              ast.errors.iter().map(|e| e.to_diag(&ast.source))
                .chain(errors.iter().map(|e| e.to_diag(&ast.source))).collect())?;
            server.vfs.update_downstream(&old_deps, &deps, &path);
            *file.parsed.lock().unwrap() = Some(FileCache::Ready {ast, errors, deps, env: Arc::new(env)});
            file.cvar.notify_all();
          }
        }
      }
    }
  }

  fn stop(&self) {
    self.0.lock().unwrap().take();
    self.1.notify_all()
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

enum FileCache {
  Dirty(AST),
  Ready {
    ast: AST,
    errors: Vec<ElabError>,
    env: Arc<Environment>,
    deps: Vec<FileRef>,
  }
}

struct VirtualFile {
  /// File data, saved (true) or unsaved (false)
  text: Mutex<(bool, Arc<LinedString>)>,
  /// File parse
  parsed: Mutex<Option<FileCache>>,
  /// Get notified on cache fill
  cvar: Condvar,
  /// Files that depend on this one
  downstream: Mutex<HashSet<FileRef>>,
}

impl VirtualFile {
  fn new(text: String) -> Result<VirtualFile> {
    Ok(VirtualFile {
      text: Mutex::new((true, Arc::new(text.into()))),
      parsed: Mutex::new(None),
      cvar: Condvar::new(),
      downstream: Mutex::new(HashSet::new())
    })
  }
}

struct VFS(Mutex<HashMap<FileRef, Arc<VirtualFile>>>);

impl VFS {
  fn get(&self, path: &FileRef) -> Option<Arc<VirtualFile>> {
    self.0.lock().unwrap().get(path).cloned()
  }

  fn open_virt(&self, queue: &mut Vec<Job>, path: FileRef, text: String) -> Result<Arc<VirtualFile>> {
    queue.push(Job::Elaborate {path: path.clone(), start: Position::new(0, 0)});
    let file = Arc::new(VirtualFile::new(text)?);
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
      let lock = &mut *file.parsed.lock().unwrap();
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
}

impl FileServer for ServerRef<'_> {
  type WaitToken = Arc<VirtualFile>;

  fn request_elab(&self, path: PathBuf, f: impl Fn(BoxError) -> ElabError) ->
      std::result::Result<(FileRef, Arc<VirtualFile>), ElabError> {
    (move || -> Result<_> {
      let res = match self.vfs.0.lock().unwrap().entry(FileRef::new(path)) {
        Entry::Occupied(e) => (e.key().clone(), e.get().clone()),
        Entry::Vacant(e) => {
          let path = e.key().clone();
          let val = e.insert(Arc::new(VirtualFile::new(fs::read_to_string(path.path())?)?)).clone();
          (path, val)
        }
      };
      self.jobs.extend(vec![Job::Elaborate {path: res.0.clone(), start: Position::default()}]);
      Ok(res)
    })().map_err(|e| f(e.0))
  }

  fn get_elab(&self, tok: &Self::WaitToken) -> Arc<Environment> {
    loop {
      if let Some(FileCache::Ready {env, ..}) = &*tok.cvar.wait(tok.parsed.lock().unwrap()).unwrap() {
        return env.clone()
      }
    }
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
          hover_provider: Some(true),
          completion_provider: Some(CompletionOptions {
            resolve_provider: Some(true),
            ..Default::default()
          }),
          definition_provider: Some(true),
          document_symbol_provider: Some(true),
          ..Default::default()
        })?)?)?,
      conn,
      reqs: Mutex::new(HashMap::new()),
      vfs: VFS(Mutex::new(HashMap::new())),
      jobs: Jobs(Mutex::new(Some(VecDeque::new())), Condvar::new())
    })
  }

  fn as_ref(&self) -> ServerRef {
    ServerRef {sender: &self.conn.sender, vfs: &self.vfs, jobs: &self.jobs}
  }
  fn run(self) {
    crossbeam::scope(|s| {
      let server = self.as_ref();
      let jobs = &self.jobs;
      s.spawn(move |_| jobs.new_worker(server).unwrap());
      s.spawn(move |_| loop {
        for s in LOGGER.1.wait(LOGGER.0.lock().unwrap()).unwrap().drain(..) {
          server.log(s).unwrap()
        }
      });
      let conn = &self.conn;
      let reqs = &self.reqs;
      let vfs = &self.vfs;
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
  // log::debug!("hi");
  Server::new().expect("Initialization failed").run()
}