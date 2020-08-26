//! MMC type checking pass.
use crate::elab::Result;
use crate::util::FileSpan;
use super::{parser::AST, Compiler};

impl Compiler {
  /// Performs type checking of the input AST.
  pub fn typeck(&mut self, _fsp: &FileSpan, _ast: &[AST]) -> Result<()> {
    // let mut waiting_jobs = vec![];
    Ok(())
  }
}
