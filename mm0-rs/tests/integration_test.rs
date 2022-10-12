mod common;

use mm0_rs::{compiler::elab_for_result, FileRef};

#[test]
fn elaborate_examples() {
  for file in glob::glob("../examples/*.mm[01]").unwrap() {
    let file = file.unwrap();
    println!("\n--- Elaborating {} ---", file.display());
    let file_ref = FileRef::from(file);
    let (_, _) = elab_for_result(file_ref.clone()).expect(&format!("failed to elaborate {}", file_ref.clone()));
  }
}
