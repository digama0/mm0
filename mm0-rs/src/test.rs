use std::io;
use crate::compiler;

fn compile_mm1(file: &str) -> io::Result<()> {
  compiler::Args { input: format!("../tests/mm1/{file}.mm1"), ..<_>::default() }.main()
}

#[test] fn issue171() -> io::Result<()> { compile_mm1("issue171") }
