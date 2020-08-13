use crate::elab::Result;
use crate::util::FileSpan;
use super::{parser::AST, Compiler};

impl Compiler {
  pub fn typeck(&mut self, _fsp: &FileSpan, _ast: &[AST]) -> Result<()> {
    // let mut waiting_jobs = vec![];
    Ok(())
  }
}
