use std::any::Any;
use std::mem;
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, atomic::{AtomicBool, Ordering}, Condvar, PoisonError};
use std::collections::{HashMap, HashSet, hash_map::Entry, VecDeque};
use std::result;
use lsp_server::*;
use serde::ser::Serialize;
use serde_json::{from_value, to_value};
use lsp_types::*;
use crossbeam::{channel::{Sender, SendError, RecvError}};

#[derive(Debug)]
struct ServerError(Box<(dyn Any + Send + 'static)>);

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

impl<T: Send + 'static> From<SendError<T>> for ServerError {
  fn from(e: SendError<T>) -> Self { ServerError(Box::new(e)) }
}

impl From<&'static str> for ServerError {
  fn from(e: &'static str) -> Self { ServerError(Box::new(e)) }
}

impl<T> From<PoisonError<T>> for ServerError {
  fn from(_: PoisonError<T>) -> Self { "poison error".into() }
}

impl From<Box<(dyn Any + Send + 'static)>> for ServerError {
  fn from(e: Box<(dyn Any + Send + 'static)>) -> Self { ServerError(e) }
}

fn nos_id(nos: NumberOrString) -> RequestId {
  match nos {
    NumberOrString::Number(n) => n.into(),
    NumberOrString::String(s) => s.into(),
  }
}

enum Job {
  Elaborate {path: Arc<PathBuf>, start: Position},
  DepChange(Arc<PathBuf>)
}

impl Job {
  fn path(&self) -> &Arc<PathBuf> {
    match self {
      Job::Elaborate{path, ..} => path,
      Job::DepChange(path) => path
    }
  }
}

struct Jobs(Mutex<Option<VecDeque<Job>>>, Condvar);

impl Jobs {
  fn extend(&self, new: Vec<Job>) -> Result<()> {
    if !new.is_empty() {
      let changed = if let Some(jobs) = &mut *self.0.lock()? {
        jobs.retain(|job| new.iter().all(|njob| njob.path() != job.path()));
        jobs.extend(new); true
      } else {false};
      if changed { self.1.notify_one() }
    }
    Ok(())
  }

  fn new_worker(&self, server: ServerRef) -> Result<()> {
    loop {
      let job = match &mut *self.1.wait(self.0.lock()?)? {
        None => return Ok(()),
        Some(jobs) => match jobs.pop_front() {
          None => continue,
          Some(job) => job,
        }
      };
      match job {
        Job::Elaborate {path, start} => {
          if let Some(file) = server.vfs.get(&path)? {
            let (old_ast, old_env, old_deps) = match file.parsed.lock()?.take() {
              None => (None, None, Vec::new()),
              Some(FileCache::Dirty(ast)) => (Some((start, ast)), None, Vec::new()),
              Some(FileCache::Ready{ast, deps, env}) => (Some((start, ast)), Some(env), deps),
            };
            let (idx, ast) = parse(&file.text.lock()?.1.clone(), old_ast);
            let (env, deps) = elaborate(&ast, old_env.map(|e| (idx, e)));
            server.vfs.update_downstream(&old_deps, &deps, &path)?;
            *file.parsed.lock()? = Some(FileCache::Ready {ast, deps, env});
            file.cvar.notify_all();
          }
        }
        Job::DepChange(path) => {
          if let Some(file) = server.vfs.get(&path)? {
            let ((idx, ast), old_env, old_deps) = match file.parsed.lock()?.take() {
              None => (parse(&file.text.lock()?.1.clone(), None), None, Vec::new()),
              Some(FileCache::Dirty(ast)) => ((ast.size, ast), None, Vec::new()),
              Some(FileCache::Ready{ast, deps, env}) => ((ast.size, ast), Some(env), deps),
            };
            let (env, deps) = elaborate(&ast, old_env.map(|e| (idx, e)));
            server.vfs.update_downstream(&old_deps, &deps, &path)?;
            *file.parsed.lock()? = Some(FileCache::Ready {ast, deps, env});
            file.cvar.notify_all();
          }
        }
      }
    }
  }

  fn stop(&self) -> Result<()> {
    self.0.lock()?.take();
    Ok(self.1.notify_all())
  }
}

struct AST { size: usize }
struct Environment;

fn parse(_file: &str, _old: Option<(Position, AST)>) -> (usize, AST) { unimplemented!() }
fn elaborate(_ast: &AST, _old: Option<(usize, Environment)>) -> (Environment, Vec<Arc<PathBuf>>) {
  unimplemented!()
}

enum FileCache {
  Dirty(AST),
  Ready {
    ast: AST,
    env: Environment,
    deps: Vec<Arc<PathBuf>>,
  }
}

struct VirtualFile {
  /// Cached Url for the file path
  _url: Url,
  /// File data, saved (true) or unsaved (false)
  text: Mutex<(bool, Arc<LinedString>)>,
  /// File parse
  parsed: Mutex<Option<FileCache>>,
  /// Get notified on cache fill
  cvar: Condvar,
  /// Files that depend on this one
  downstream: Mutex<HashSet<Arc<PathBuf>>>,
}

#[derive(Default, Clone)]
struct LinedString { s: String, lines: Vec<usize> }

impl LinedString {

  fn get_lines(s: &str) -> Vec<usize> {
    let mut lines = vec![0];
    for (b, c) in s.char_indices() {
      if c == '\n' { lines.push(b + 1) }
    }
    lines
  }

  fn to_pos(&self, idx: usize) -> Position {
    let (pos, line) = match self.lines.binary_search(&idx) {
      Ok(n) => (idx, n),
      Err(n) => (self.lines[n], n)
    };
    Position::new(line as u64, (idx - pos) as u64)
  }

  fn num_lines(&self) -> u64 { self.lines.len() as u64 - 1 }
  fn end(&self) -> Position { self.to_pos(self.s.len()) }

  fn to_idx(&self, pos: Position) -> Option<usize> {
    self.lines.get(pos.line as usize).map(|&idx| idx + (pos.character as usize))
  }

  fn extend(&mut self, s: &str) {
    let len = self.s.len();
    self.s.push_str(s);
    for (b, c) in s.char_indices() {
      if c == '\n' { self.lines.push(b + len + 1) }
    }
  }

  fn extend_until<'a>(&mut self, s: &'a str, pos: Position) -> &'a str {
    debug_assert!(self.end() <= pos);
    let len = self.s.len();
    self.s.push_str(s);
    let mut it = s.char_indices();
    let tail = loop {
      if let Some((b, c)) = it.next() {
        if c == '\n' {
          self.lines.push(b + len + 1);
          if pos.line == self.num_lines() {
            break unsafe { s.get_unchecked(b+1..) }
          }
        }
      } else {break ""}
    };
    let off = pos.character as usize;
    let (left, right) = if off < tail.len() {tail.split_at(off)} else {(tail, "")};
    self.extend(left);
    right
  }

  fn truncate(&mut self, pos: Position) {
    if let Some(idx) = self.to_idx(pos) {
      if idx < self.s.len() {
        self.s.truncate(idx);
        self.lines.truncate(pos.line as usize + 1);
      }
    }
  }

  fn apply_changes(&self, changes: impl Iterator<Item=TextDocumentContentChangeEvent>) ->
      (Position, LinedString) {
    let mut old: LinedString;
    let mut out = LinedString::default();
    let mut uncopied: &str = &self.s;
    let mut first_change = None;
    for TextDocumentContentChangeEvent {range, text: change, ..} in changes {
      if let Some(Range {start, end}) = range {
        if first_change.map_or(true, |c| start < c) { first_change = Some(start) }
        if out.end() > start {
          out.extend(uncopied);
          old = mem::replace(&mut out, LinedString::default());
          uncopied = &old;
        }
        uncopied = out.extend_until(uncopied, end);
        out.truncate(start);
        out.extend(&change);
      } else {
        out = change.into();
        first_change = Some(Position::default());
        uncopied = "";
      }
    }
    out.extend(uncopied);
    if let Some(pos) = first_change {
      let start = out.to_idx(pos).unwrap();
      let from = unsafe { self.s.get_unchecked(start..) };
      let to = unsafe { out.s.get_unchecked(start..) };
      for ((b, c1), c2) in from.char_indices().zip(to.chars()) {
        if c1 != c2 {return (out.to_pos(b + start), out)}
      }
    }
    (out.end(), out)
  }
}

impl Deref for LinedString {
  type Target = String;
  fn deref(&self) -> &String { &self.s }
}

impl From<String> for LinedString {
  fn from(s: String) -> LinedString {
    LinedString {lines: LinedString::get_lines(&s), s}
  }
}

impl VirtualFile {
  fn new(path: impl AsRef<Path>, text: String) -> Result<VirtualFile> {
    Ok(VirtualFile {
      _url: Url::from_file_path(path).map_err(|_| "bad path")?,
      text: Mutex::new((true, Arc::new(text.into()))),
      parsed: Mutex::new(None),
      cvar: Condvar::new(),
      downstream: Mutex::new(HashSet::new())
    })
  }
}

struct VFS(Mutex<HashMap<Arc<PathBuf>, Arc<VirtualFile>>>);

impl VFS {
  fn get(&self, path: &PathBuf) -> Result<Option<Arc<VirtualFile>>> {
    Ok(self.0.lock()?.get(path).cloned())
  }

  fn open_virt(&self, queue: &mut Vec<Job>, path: Arc<PathBuf>, text: String) -> Result<Arc<VirtualFile>> {
    queue.push(Job::Elaborate {path: path.clone(), start: Position::new(0, 0)});
    let file = Arc::new(VirtualFile::new(&*path, text)?);
    match self.0.lock()?.entry(path.clone()) {
      Entry::Occupied(entry) => {
        for dep in entry.get().downstream.lock()?.clone() {
          self.dirty(queue, &dep)?;
        }
        Ok(file)
      }
      Entry::Vacant(entry) => Ok(entry.insert(file).clone())
    }
  }

  fn close(&self, queue: &mut Vec<Job>, path: &PathBuf) -> Result<()> {
    if let Some(file) = self.0.lock()?.remove(path) {
      if !file.text.lock()?.0 {
        for dep in file.downstream.lock()?.clone() {
          self.dirty(queue, &dep)?;
        }
      }
    }
    Ok(())
  }

  fn set_downstream(&self, from: &PathBuf, to: Arc<PathBuf>, val: bool) -> Result<()> {
    let file = self.0.lock()?.get(from).unwrap().clone();
    let mut ds = file.downstream.lock()?;
    if val { ds.insert(to); }
    else { ds.remove(&to); }
    Ok(())
  }

  fn update_downstream(&self, old_deps: &Vec<Arc<PathBuf>>, deps: &Vec<Arc<PathBuf>>, to: &Arc<PathBuf>) -> Result<()> {
    for from in old_deps {
      if !deps.contains(from) {
        self.set_downstream(from, to.clone(), false)?
      }
    }
    for from in deps {
      if !old_deps.contains(from) {
        self.set_downstream(from, to.clone(), true)?
      }
    }
    Ok(())
  }

  fn dirty(&self, queue: &mut Vec<Job>, path: &Arc<PathBuf>) -> Result<()> {
    queue.push(Job::DepChange(path.clone()));
    let file = self.0.lock()?.get(path).unwrap().clone();
    {
      let lock = &mut *file.parsed.lock()?;
      match lock.take() {
        None => {}
        Some(FileCache::Ready{ast, ..}) => *lock = Some(FileCache::Dirty(ast)),
        Some(FileCache::Dirty(ast)) => *lock = Some(FileCache::Dirty(ast)),
      }
    }
    for dep in file.downstream.lock()?.clone() {
      self.dirty(queue, &dep)?;
    }
    Ok(())
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
  fn log_message(&self, typ: MessageType, message: String) -> Result<()> {
    self.send(Notification {
      method: "window/logMessage".to_owned(),
      params: to_value(LogMessageParams {typ, message})?
    })
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
    self.reqs.lock()?.remove(&self.id);
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
    ServerRef {sender: &self.conn.sender, vfs: &self.vfs}
  }
  fn run(self) -> Result<()> {
    crossbeam::scope(|s| {
      let server = self.as_ref();
      let jobs = &self.jobs;
      s.spawn(move |_| jobs.new_worker(server).unwrap());
      let conn = &self.conn;
      let reqs = &self.reqs;
      let vfs = &self.vfs;
      loop {
        match (move || -> Result<bool> {
          let server = ServerRef {sender: &conn.sender, vfs};
          match conn.receiver.recv()? {
            Message::Request(req) => {
              if conn.handle_shutdown(&req)? {
                jobs.stop()?;
                return Ok(true)
              }
              if let Some((id, req)) = parse_request(req)? {
                let cancel = Arc::new(AtomicBool::new(false));
                reqs.lock()?.insert(id.clone(), cancel.clone());
                s.spawn(move |_|
                  RequestHandler {reqs, id, cancel: &cancel, server}.handle(req).unwrap());
              }
            }
            Message::Response(resp) => {
              reqs.lock()?.get(&resp.id).ok_or_else(
                  || ServerError(Box::new("response to unknown request")))?
                .store(true, Ordering::Relaxed);
            }
            Message::Notification(notif) => {
              match notif.method.as_str() {
                "$/cancelRequest" => {
                  let CancelParams {id} = from_value(notif.params)?;
                  if let Some(cancel) = reqs.lock()?.get(&nos_id(id)) {
                    cancel.store(true, Ordering::Relaxed);
                  }
                }
                "textDocument/didOpen" => {
                  let DidOpenTextDocumentParams {text_document: doc} = from_value(notif.params)?;
                  let mut queue = Vec::new();
                  let path = Arc::new(doc.uri.to_file_path().map_err(|_| "bad URI")?);
                  vfs.open_virt(&mut queue, path, doc.text)?;
                  jobs.extend(queue)?;
                }
                "textDocument/didChange" => {
                  let DidChangeTextDocumentParams {text_document: doc, content_changes} = from_value(notif.params)?;
                  if !content_changes.is_empty() {
                    let path = Arc::new(doc.uri.to_file_path().map_err(|_| "bad URI")?);
                    let start = {
                      let file = vfs.get(&path)?.ok_or("changed nonexistent file")?;
                      let mut text = file.text.lock()?;
                      text.0 = true;
                      let (start, s) = text.1.apply_changes(content_changes.into_iter());
                      text.1 = Arc::new(s);
                      start
                    };
                    jobs.extend(vec![Job::Elaborate{path, start}])?;
                  }
                }
                "textDocument/didClose" => {
                  let DidCloseTextDocumentParams {text_document: doc} = from_value(notif.params)?;
                  let path = doc.uri.to_file_path().map_err(|_| "bad URI")?;
                  let mut queue = Vec::new();
                  vfs.close(&mut queue, &path)?;
                  jobs.extend(queue)?;
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
    })?;
    Ok(())
  }
}

pub fn main(mut args: impl Iterator<Item=String>) {
  if args.next().map_or(false, |s| s == "--debug") {
    use {simplelog::*, std::fs::File};
    let _ = WriteLogger::init(LevelFilter::Debug, Config::default(), File::create("lsp.log").unwrap());
  }
  // log::debug!("hi");
  (|| Server::new()?.run())().unwrap_or_else(|e| {
    eprintln!("Server panicked: {:?}", e);
  })
}