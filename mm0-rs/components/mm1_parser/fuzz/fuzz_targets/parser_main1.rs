#![no_main]
use libfuzzer_sys::fuzz_target;
extern crate mm1_parser;
extern crate mm0_util;
use mm1_parser::parse;
use std::sync::Arc;
use mm0_util::lined_string::LinedString;

fuzz_target!(|data: &[u8]| {
    let _ = parse(Arc::new(LinedString::from(String::from_utf8_lossy(data).to_string())), None);
});
