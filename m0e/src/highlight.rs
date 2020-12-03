// use wasm_bindgen::prelude::*;
// use std::{mem::{self, ManuallyDrop, MaybeUninit}, sync::atomic::{AtomicU8, Ordering}};

// struct Settings {
//   language_id: u8,
//   colors: MaybeUninit<Box<[u32]>>,
// }

// static mut LANGUAGE_SETTINGS: Settings =
//   Settings {language_id: 0, colors: MaybeUninit::uninit()};

// #[wasm_bindgen(js_name = "setLanguageSettings")]
// pub fn set_language_settings(language_id: u8, colors: Box<[u32]>) {
//   unsafe { LANGUAGE_SETTINGS = Settings {
//     language_id, colors: MaybeUninit::new(colors)
//   } }
// }

// fn get_language_id() -> u8 { unsafe { LANGUAGE_SETTINGS.language_id } }
// fn get_colors() -> &'static [u32] {
//   unsafe {
//     &**(&LANGUAGE_SETTINGS.colors as *const MaybeUninit<Box<[u32]>> as *const Box<[u32]>)
//   }
// }

// #[wasm_bindgen]
// pub enum Stack {
//     Start = 0
// }

// #[wasm_bindgen]
// #[derive(Clone, PartialEq, Eq)]
// pub struct State {
//     value: Vec<u32>,
// }

// #[wasm_bindgen]
// impl State {
//   #[wasm_bindgen(constructor)]
//   pub fn new() -> Self { Self {value: vec![]} }
//   #[wasm_bindgen]
//   pub fn clone(&self) -> Self { <Self as Clone>::clone(self) }
//   #[wasm_bindgen]
//   pub fn equals(&self, other: &State) -> bool { self == other }
// }

// #[wasm_bindgen(inline_js =
//   "export function encodedLineTokens(tokens, endState) {return {tokens, endState};}")]
// extern "C" {
//   pub type EncodedLineTokens;

//   #[wasm_bindgen(js_name = "encodedLineTokens")]
//   fn encoded_line_tokens(tokens: Vec<u32>, end_state: State) -> EncodedLineTokens;
// }

// // Next let's define a macro that's like `println!`, only it works for
// // `console.log`. Note that `println!` doesn't actually work on the wasm target
// // because the standard library currently just eats all output. To get
// // `println!`-like behavior in your app you'll likely want a macro like this.

// macro_rules! console_log {
//   // Note that this is using the `log` function imported above during
//   // `bare_bones`
//   ($($t:tt)*) => {
//     #[allow(unused_unsafe)]
//     unsafe {web_sys::console::log_1(&format!($($t)*).into())}
//   }
// }

// #[wasm_bindgen]
// pub fn tokenize(line: &str, mut state: State) -> EncodedLineTokens {
//   console_log!("{}", line);
//   let mut toks = Tokens(vec![]);
//   state.tokenize(&mut toks);
//   #[allow(unused_unsafe)] unsafe { encoded_line_tokens(toks.0, state) }
// }

// /**
// * The tokens on the line in a binary, encoded format. Each token occupies two array indices. For token i:
// *  - at offset 2*i => startIndex
// *  - at offset 2*i + 1 => metadata
// * Meta data is in binary format:
// * - -------------------------------------------
// *     3322 2222 2222 1111 1111 1100 0000 0000
// *     1098 7654 3210 9876 5432 1098 7654 3210
// * - -------------------------------------------
// *     bbbb bbbb bfff ffff ffFF FTTT LLLL LLLL
// * - -------------------------------------------
// *  - L = EncodedLanguageId (8 bits): Use `getEncodedLanguageId` to get the encoded ID of a language.
// *  - T = StandardTokenType (3 bits): Other = 0, Comment = 1, String = 2, RegEx = 4.
// *  - F = FontStyle (3 bits): None = 0, Italic = 1, Bold = 2, Underline = 4.
// *  - f = foreground ColorId (9 bits)
// *  - b = background ColorId (9 bits)
// *  - The color value for each colorId is defined in IStandaloneThemeData.customTokenColors:
// * e.g. colorId = 1 is stored in IStandaloneThemeData.customTokenColors[1]. Color id = 0 means no color,
// * id = 1 is for the default foreground color, id = 2 for the default background.
// */
// struct Tokens(Vec<u32>);

// const TOKEN_TYPE_CONSTANT: u32 = 1 << 8;
// const TOKEN_TYPE_STRING: u32 = 2 << 8;
// const TOKEN_TYPE_REGEX: u32 = 4 << 8;
// const FONT_STYLE_ITALIC: u32 = 1 << 11;
// const FONT_STYLE_BOLD: u32 = 2 << 11;
// const FONT_STYLE_UNDERLINE: u32 = 4 << 11;

// impl Tokens {
//   fn push(mut self, start_index: u32) {
//     self.0.extend_from_slice(&[start_index, 0]);
//   }
// }

// impl State {
//   fn tokenize(&mut self, tokens: &mut Tokens) {

//   }
// }