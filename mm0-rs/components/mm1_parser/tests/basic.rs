use mm0_util::LinedString;
use mm1_parser::parse;
use std::fs::read_to_string;
use std::path::PathBuf;
use std::sync::Arc;

#[test]
fn fuzz0() { let _ = parse(Arc::new(LinedString::from(String::from("@0"))), None); }

#[test]
fn peano_mm1() {
  let mmz = read_to_string(PathBuf::from("./test_resources/peano.mm1")).unwrap();
  let (_, ast) = parse(Arc::new(LinedString::from(mmz)), None);
  assert!(ast.errors.is_empty());
}

#[test]
fn peano_mm0() {
  let mmz = read_to_string(PathBuf::from("./test_resources/peano.mm0")).unwrap();
  let (_, ast) = parse(Arc::new(LinedString::from(mmz)), None);
  assert!(ast.errors.is_empty());
}
