use std::sync::Arc;
use crate::lined_string::LinedString;

pub type Span = std::ops::Range<usize>;

bitflags! {
  pub struct Modifiers: u8 {
    const PURE = 1;
    const STRICT = 2;
    const PROVABLE = 4;
    const FREE = 8;

    const PUB = 16;
    const ABSTRACT = 32;
    const LOCAL = 64;
  }
}

impl Modifiers {
  pub fn sort_data() -> Modifiers {
    Modifiers::PURE | Modifiers::STRICT | Modifiers::PROVABLE | Modifiers::FREE
  }
  pub fn _visibility() -> Modifiers {
    Modifiers::PUB | Modifiers::ABSTRACT | Modifiers::LOCAL
  }
  pub fn from_name(s: &str) -> Option<Modifiers> {
    match s {
      "pure" => Some(Modifiers::PURE),
      "strict" => Some(Modifiers::STRICT),
      "provable" => Some(Modifiers::PROVABLE),
      "free" => Some(Modifiers::FREE),
      "pub" => Some(Modifiers::PUB),
      "abstract" => Some(Modifiers::ABSTRACT),
      "local" => Some(Modifiers::LOCAL),
      _ => None
    }
  }
}

pub enum Decl {
  Sort(Span, Modifiers),
}

pub struct AST {
  pub source: Arc<LinedString>,
  pub decls: Vec<Decl>,
}

impl AST {
  pub fn _span(&self, s: Span) -> &str {
    unsafe { std::str::from_utf8_unchecked(&self.source.as_bytes()[s]) }
  }
}