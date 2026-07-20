use std::path::PathBuf;
use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;
use mm0_rs::server::*;

/// Make an example available to the VFS without elaborating it, so that an
/// `import` from another file can resolve. There is no filesystem to fall back
/// on here, so every file reachable by `import` must be seeded up front.
#[wasm_bindgen]
pub fn seed_file(file: String, text: String) {
  SERVER.vfs.seed(PathBuf::from(file).into(), text);
}

#[wasm_bindgen]
pub fn open_file(file: String, version: i32, text: String) {
  SERVER.vfs.open_virt(PathBuf::from(file).into(), version, text);
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Range {
  start_line_number: u32,
  start_column: u32,
  end_line_number: u32,
  end_column: u32,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct ModelContentChange {
  range: Range,
  text: String,
}

#[wasm_bindgen]
pub fn update_file(file: String, version: i32, changes: JsValue) {
  let changes: Vec<ModelContentChange> = serde_wasm_bindgen::from_value(changes).unwrap();
  SERVER.vfs.update(PathBuf::from(file).into(), version,
    |s| s.apply_changes(changes.into_iter().map(|change| {
      lsp_types::TextDocumentContentChangeEvent {
        range: Some(lsp_types::Range {
          start: lsp_types::Position {
            line: change.range.start_line_number - 1,
            character: change.range.start_column - 1
          },
          end: lsp_types::Position {
            line: change.range.end_line_number - 1,
            character: change.range.end_column - 1
          },
        }),
        range_length: None,
        text: change.text
      }
    }))).unwrap();
}

/// Compile a file to an `.mmb`, for handing to the proof explorer.
#[wasm_bindgen]
pub async fn export_mmb(file: String) -> Result<Vec<u8>, JsValue> {
  mm0_rs::server::export_mmb(PathBuf::from(file).into())
    .await.map_err(|e| JsValue::from_str(&format!("{e:?}")))
}

/// Send an LSP request (hover, definition, semantic tokens, ...). The reply is
/// not returned here: it comes back from `poll_message` as a response carrying
/// this `id`, just as it would over a socket.
#[wasm_bindgen]
pub fn send_request(id: i32, method: String, params: JsValue) -> Result<(), JsValue> {
  let params = serde_wasm_bindgen::from_value(params)?;
  handle_request(id, method, params).map_err(|e| JsValue::from_str(&format!("{e:?}")))
}

#[wasm_bindgen]
pub fn poll_message() -> JsValue {
  match SERVER.conn.receiver.try_recv() {
    // `params` is a `serde_json::Value`, whose maps serde_wasm_bindgen would
    // otherwise hand back as JS `Map`s rather than plain objects -- so
    // `msg.params.diagnostics` would silently read as `undefined`.
    Ok(msg) => msg.serialize(
      &serde_wasm_bindgen::Serializer::new().serialize_maps_as_objects(true)
    ).unwrap(),
    Err(_) => JsValue::NULL,
  }
}

#[wasm_bindgen(start)]
pub fn init() -> Result<(), JsValue> {
  std::panic::set_hook(Box::new(console_error_panic_hook::hook));
  Ok(())
}
