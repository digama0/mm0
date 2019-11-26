use std::any::Any;
use std::sync::{Arc, Mutex, atomic::{AtomicBool, Ordering}, PoisonError};
use std::collections::HashMap;
use lsp_server::*;
use serde::ser::Serialize;
use serde_json::{from_value, to_value};
use lsp_types::*;
use crossbeam::{channel::{Sender, SendError, RecvError}};

#[derive(Debug)]
struct ServerError(Box<(dyn Any + Send + 'static)>);

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

impl<T> From<PoisonError<T>> for ServerError {
  fn from(_: PoisonError<T>) -> Self { ServerError(Box::new("poison error")) }
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

enum RequestType {
  Completion(CompletionParams),
  Hover(TextDocumentPositionParams),
  Definition(TextDocumentPositionParams),
  DocumentSymbol(DocumentSymbolParams),
}

fn parse_request(req: Request) -> Result<Option<(RequestId, RequestType)>, ServerError> {
  let Request {id, method, params} = req;
  match method.as_str() {
    "textDocument/completion"     => Ok(Some((id, RequestType::Completion(from_value(params)?)))),
    "textDocument/hover"          => Ok(Some((id, RequestType::Hover(from_value(params)?)))),
    "textDocument/definition"     => Ok(Some((id, RequestType::Definition(from_value(params)?)))),
    "textDocument/documentSymbol" => Ok(Some((id, RequestType::DocumentSymbol(from_value(params)?)))),
    _ => Ok(None)
  }
}

type OpenRequests = Mutex<HashMap<RequestId, Arc<AtomicBool>>>;

struct RequestHandler<'a> {
  reqs: &'a OpenRequests,
  id: RequestId,
  #[allow(unused)]
  req: RequestType,
  #[allow(unused)]
  cancel: &'a AtomicBool,
  sender: &'a Sender<Message>,
}

impl RequestHandler<'_> {
  fn handle(self) -> Result<(), ServerError> {
    self.finish(Ok(()))
  }

  fn finish<T: Serialize>(self, resp: Result<T, ResponseError>) -> Result<(), ServerError> {
    self.reqs.lock()?.remove(&self.id);
    self.sender.send(Message::Response(match resp {
      Ok(val) => Response { id: self.id, result: Some(to_value(val)?), error: None },
      Err(e) => Response { id: self.id, result: None, error: Some(e) }
    }))?;
    Ok(())
  }
}

fn run_server() -> Result<(), ServerError> {
  let (conn, _iot) = Connection::stdio();
  let _params: InitializeParams = from_value(conn.initialize(
    to_value(ServerCapabilities {
      text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::Full)),
      hover_provider: Some(true),
      completion_provider: Some(CompletionOptions {
        resolve_provider: Some(true),
        ..Default::default()
      }),
      definition_provider: Some(true),
      document_symbol_provider: Some(true),
      ..Default::default()
    })?)?)?;

  let reqs: OpenRequests = Mutex::new(HashMap::new());
  crossbeam::scope(|s| {
    loop {
      let conn = &conn;
      let reqs = &reqs;
      match (move || -> Result<bool, ServerError> {
        match conn.receiver.recv()? {
          Message::Request(req) => {
            if conn.handle_shutdown(&req)? {return Ok(true)}
            if let Some((id, req)) = parse_request(req)? {
              let cancel = Arc::new(AtomicBool::new(false));
              reqs.lock()?.insert(id.clone(), cancel.clone());
              s.spawn(move |_| RequestHandler {
                  reqs, id, req, cancel: &cancel, sender: &conn.sender
                }.handle().unwrap());
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
                let _params: DidOpenTextDocumentParams = from_value(notif.params)?;
              }
              "textDocument/didChange" => {
                let _params: DidChangeTextDocumentParams = from_value(notif.params)?;
              }
              "textDocument/didClose" => {
                let _params: DidCloseTextDocumentParams = from_value(notif.params)?;
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

pub fn main(mut args: impl Iterator<Item=String>) {
  if args.next().map_or(false, |s| s == "--debug") {
    use {simplelog::*, std::fs::File};
    let _ = WriteLogger::init(LevelFilter::Debug, Config::default(), File::create("lsp.log").unwrap());
  }
  // log::debug!("hi");
  run_server().unwrap_or_else(|e| {
    eprintln!("Server panicked: {:?}", e);
  })
}