use std::path::PathBuf;
use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;
use mm0_rs::server::*;

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
