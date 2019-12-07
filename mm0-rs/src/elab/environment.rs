use std::collections::HashMap;
use super::ElabError;
use crate::util::*;
pub use crate::parser::ast::Modifiers;
pub use crate::lined_string::{Span, FileSpan};

#[derive(Default, Clone)]
pub struct Environment {
  pub sorts: HashMap<String, (FileSpan, Modifiers)>,
  pub delims_l: Delims,
  pub delims_r: Delims,
}

#[derive(Default, Clone)]
pub struct Delims([u8; 32]);

impl Delims {
  pub fn get(&self, c: u8) -> bool { self.0[(c >> 3) as usize] & (1 << (c & 7)) != 0 }
  pub fn set(&mut self, c: u8) { self.0[(c >> 3) as usize] |= 1 << (c & 7) }
  pub fn merge(&mut self, other: &Self) {
    for i in 0..32 { self.0[i] |= other.0[i] }
  }
}

pub struct Redeclaration {
  pub msg: String,
  pub othermsg: String,
  pub other: FileSpan
}

impl Environment {
  pub fn add_sort(&mut self, s: String, fsp: FileSpan, sd: Modifiers) -> Result<(), Redeclaration> {
    if let Some(((_, sd), e)) = self.sorts.try_insert(s, (fsp, sd)) {
      if sd != e.get().1 {
        return Err(Redeclaration {
          msg: format!("sort '{}' redeclared", e.key()),
          othermsg: "previously declared here".to_owned(),
          other: e.get().0.clone()
        })
      }
    }
    Ok(())
  }

  pub fn merge(&mut self, other: &Self, sp: Span, errors: &mut Vec<ElabError>) {
    for (s, &(ref fs, m)) in &other.sorts {
      self.add_sort(s.clone(), fs.clone(), m).unwrap_or_else(|r|
        errors.push(ElabError::with_info(sp, r.msg.into(), vec![
          (fs.clone(), r.othermsg.clone().into()),
          (r.other, r.othermsg.into())
        ])))
    }
    self.delims_l.merge(&other.delims_l);
    self.delims_r.merge(&other.delims_r);
    unimplemented!()
  }
}
