// This module may become a plugin in the future, but for now let's avoid the complexity
// of dynamic loading.

//! Compiler tactic for the metamath C language.
//!
//! See [`mmc.md`] for information on the MMC format.
//!
//! [`mmc.md`]: https://github.com/digama0/mm0/blob/master/mm0-rs/mmc.md
pub mod parser;

use std::mem;
use std::collections::hash_map::HashMap;
use num::BigInt;
use crate::util::{Span, FileSpan};
use crate::elab::{
  Result, Elaborator, ElabError,
  environment::{AtomID, Environment, Remap},
  lisp::{LispKind, LispVal, Uncons, LispRemapper},
  local_context::try_get_span};
use parser::{Keyword, Parser, AST};

impl<R> Remap<R> for Keyword {
  fn remap(&self, _: &mut R) -> Self { *self }
}

pub struct Compiler {
  keywords: HashMap<AtomID, Keyword>,
}

impl std::fmt::Debug for Compiler {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "#<mmc-compiler>")
  }
}

impl Remap<LispRemapper> for Compiler {
  fn remap(&self, r: &mut LispRemapper) -> Self {
    Compiler { keywords: self.keywords.remap(r) }
  }
}

impl Compiler {
  pub fn new(e: &mut Elaborator) -> Compiler {
    Compiler {keywords: e.env.make_keywords()}
  }

  pub fn add(&mut self, elab: &mut Elaborator, fsp: FileSpan, it: impl Iterator<Item=LispVal>) -> Result<()> {
    let mut p = Parser {elab, kw: &self.keywords, fsp};
    for e in it {
      if let Some(fsp) = e.fspan() {p.fsp = fsp}
      let _ast = p.parse_ast(&e)?;
    }
    Ok(())
  }

  pub fn finish(&mut self, _elab: &mut Elaborator, _fsp: &FileSpan, _a1: AtomID, _a2: AtomID) -> Result<()> {
    Ok(())
  }

  pub fn call(&mut self, elab: &mut Elaborator, fsp: FileSpan, args: Vec<LispVal>) -> Result<LispVal> {
    let mut it = args.into_iter();
    let e = it.next().unwrap();
    match e.as_atom().and_then(|a| self.keywords.get(&a)) {
      Some(Keyword::Add) => {
        self.add(elab, fsp, it)?;
        Ok(LispVal::undef())
      }
      Some(Keyword::Finish) => {
        let a1 = it.next().and_then(|e| e.as_atom()).ok_or_else(||
          ElabError::new_e(fsp.span, "mmc-finish: syntax error"))?;
        let a2 = it.next().and_then(|e| e.as_atom()).ok_or_else(||
          ElabError::new_e(fsp.span, "mmc-finish: syntax error"))?;
        self.add(elab, fsp.clone(), it)?;
        self.finish(elab, &fsp, a1, a2)?;
        Ok(LispVal::undef())
      }
      _ => Err(ElabError::new_e(fsp.span,
        format!("mmc-compiler: unknown subcommand '{}'", elab.print(&e))))?
    }
  }
}