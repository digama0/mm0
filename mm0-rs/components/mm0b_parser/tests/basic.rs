use mm0b_parser::{BareMmbFile, BasicMmbFile, NumdStmtCmd, ParseError};
use std::fs::OpenOptions;
use std::io::Read;
use std::path::PathBuf;

/// Force the test data to the 8-byte alignment [`BareMmbFile::parse`] requires.
///
/// This must be `align(8)`, not `align(1)`: `repr(align(N))` can only *raise* a
/// type's alignment, so `align(1)` is a no-op on a `[u8; N]` and leaves the array
/// wherever the compiler happens to put a 1-aligned local — making the parse fail
/// with [`ParseError::Unaligned`] depending only on stack layout.
#[repr(align(8))]
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

fn peano_bytes() -> Vec<u8> {
  let mut mmb_bytes = Vec::new();
  let mut mmb_file = OpenOptions::new()
    .read(true)
    .truncate(false)
    .open(PathBuf::from("./test_resources/peano.mmb"))
    .unwrap();
  mmb_file.read_to_end(&mut mmb_bytes).unwrap();
  assert!(!mmb_bytes.is_empty());
  mmb_bytes
}

#[test]
fn peano0() {
  assert!(BareMmbFile::parse(peano_bytes().as_slice()).is_ok());
}

/// Parse the fixture *with* its index, and check that names resolve.
///
/// `peano0` only parses as a [`BareMmbFile`], which ignores the index entirely,
/// so it keeps passing even if the fixture's index is stale or malformed — which
/// is exactly how the fixture came to be a format version behind. This test pins
/// the index format down.
#[test]
fn peano_index() {
  let bytes = peano_bytes();
  let file = BasicMmbFile::parse(bytes.as_slice()).expect("fixture index should parse");
  let names = file
    .proof()
    .take(4)
    .map(|decl| match decl.unwrap().0 {
      NumdStmtCmd::Sort { sort_id } => file.sort_name(sort_id).into_owned(),
      NumdStmtCmd::TermDef { term_id, .. } => file.term_name(term_id).into_owned(),
      NumdStmtCmd::Axiom { thm_id } | NumdStmtCmd::Thm { thm_id, .. } =>
        file.thm_name(thm_id).into_owned(),
    })
    .collect::<Vec<_>>();
  assert_eq!(names, ["wff", "im", "not", "ax_1"]);
}
