use mm0b_parser::{BareMmbFile, ParseError};
use std::fs::OpenOptions;
use std::io::Read;
use std::path::PathBuf;

#[repr(align(1))]
struct AlignFile<T>(T);

#[test]
fn try_next_decl_infinite_loop() {
  let filedata = AlignFile([
    77, 77, 48, 66, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 40, 0, 0, 0, 40, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0,
  ]);
  let mut iter = BareMmbFile::parse(&filedata.0).unwrap().proof();
  assert!(matches!(iter.next().unwrap().unwrap_err(), ParseError::BadProofLen(40)));
}

#[test]
fn peano0() {
  let mut mmb_bytes = Vec::new();
  let mut mmb_file = OpenOptions::new()
    .read(true)
    .truncate(false)
    .open(&PathBuf::from("./test_resources/peano.mmb"))
    .unwrap();
  mmb_file.read_to_end(&mut mmb_bytes).unwrap();
  assert!(!mmb_bytes.is_empty());
  assert!(BareMmbFile::parse(mmb_bytes.as_slice()).is_ok());
}
