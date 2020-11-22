//! Importer for MMB files into the `Environment`.

use std::convert::TryInto;
use std::fs::File;
use crate::elab::environment::{SortID, Modifiers, Environment};
use crate::util::{FileRef, FileSpan};
use super::{StmtCmd, parser::{Buffer, ParseError}};

fn parse(fref: &FileRef, file: &File) -> Result<Environment, ParseError> {
  use ParseError::StrError;
  let mut env = Environment::new();
  let buf = Buffer::new(file)?;
  let file = buf.parse()?;
  let diff = |p: *const u8| p as usize - buf.as_ptr() as usize;
  let mut it = file.proof();
  let mut start = it.pos;
  while let Some(e) = it.next() {
    match e.map_err(|p| StrError("bad statement", p))? {
      (StmtCmd::Sort, pf) => {
        if !pf.is_null() { return Err(StrError("unexpected commands", pf.pos)) }
        #[allow(clippy::cast_possible_truncation)]
        let sort = SortID(env.sorts.len() as u8);
        let a = file.sort_name(sort, |s| env.get_atom(s.as_bytes()))
          .ok_or(ParseError::BadIndex)?;
        let span = (start..pf.pos).into();
        let fsp = FileSpan {file: fref.clone(), span};
        let sd = file.sort(sort).and_then(|sd| sd.try_into().ok())
          .ok_or(StrError("not a sort", start))?;
        env.add_sort(a, fsp, span, sd, None)
          .map_err(|_| StrError("double add sort", start))?;
      }
      _ => todo!()
    }
    start = it.pos;
  }
  Ok(env)
}