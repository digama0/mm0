use std::path::PathBuf;
use serde::Deserialize;
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
  let changes: Vec<ModelContentChange> = JsValue::into_serde(&changes).unwrap();
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
    Ok(msg) => JsValue::from_serde(&msg).unwrap(),
    Err(_) => JsValue::NULL,
  }
}

#[wasm_bindgen(start)]
pub fn init() -> Result<(), JsValue> {
  std::panic::set_hook(Box::new(console_error_panic_hook::hook));
  Ok(())
}
