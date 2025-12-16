use std::path::Path;
use crate::compiler;
use test_each_file::test_each_path;

fn compile_mm1([input]: [&Path; 1]) {
  compiler::Args { input: input.to_owned(), ..<_>::default() }.main().expect("IO failure")
}

test_each_path! { for ["mm1"] in "../tests/mm1" => compile_mm1 }
