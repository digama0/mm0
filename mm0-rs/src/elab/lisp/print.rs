use std::ops::Deref;
use std::fmt::{self, Display};
use itertools::Itertools;
use super::super::{LinedString, FileServer, Environment, Elaborator, TermID, ThmID, SortID};
use super::{AtomID, LispKind, Uncons, InferTarget, Proc, ProcPos};

#[derive(Copy, Clone)]
pub struct FormatEnv<'a> {
  pub source: &'a LinedString,
  pub env: &'a Environment,
}

pub struct Print<'a, D: ?Sized> {
  pub fe: FormatEnv<'a>,
  pub e: &'a D,
}

impl<'a> FormatEnv<'a> {
  pub fn to<D: ?Sized>(self, e: &'a D) -> Print<'a, D> {
    Print {fe: self, e}
  }
}

impl<'a> Deref for FormatEnv<'a> {
  type Target = Environment;
  fn deref(&self) -> &Environment {self.env}
}

pub trait EnvDisplay {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result;
}

impl<'a, F: FileServer + ?Sized> Elaborator<'a, F> {
  pub fn format_env<'b>(&'b self) -> FormatEnv<'b> {
    FormatEnv {source: &self.ast.source, env: self}
  }
  pub fn print<'b, D: ?Sized>(&'b self, e: &'b D) -> Print<'b, D> {
    self.format_env().to(e)
  }
}

impl<'a, D: EnvDisplay + ?Sized> fmt::Display for Print<'a, D> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.e.fmt(self.fe, f) }
}

impl LispKind {
  fn list(&self, n: usize, mut start: bool, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      LispKind::List(es) => {
        for e in &es[n..] {
          if start {
            write!(f, "({}", fe.to(e))?;
            start = false
          } else {
            write!(f, " {}", fe.to(e))?
          }
        }
        if start {write!(f, "()")} else {write!(f, ")")}
      }
      LispKind::DottedList(es, r) => {
        for e in &es[n..] {
          if start {
            write!(f, "({}", fe.to(e))?;
            start = false
          } else {
            write!(f, " {}", fe.to(e))?
          }
        }
        if r.exactly(0) {
          if start {write!(f, "()")} else {write!(f, ")")}
        } else {
          r.list(0, start, fe, f)
        }
      }
      e => if start {write!(f, "{}", fe.to(e))} else {write!(f, " . {})", fe.to(e))}
    }
  }
}

fn alphanumber(n: usize) -> String {
  let mut out = String::with_capacity(2);
  let mut n = n + 1;
  while n != 0 {
    out.push((b'a' + ((n - 1) % 26) as u8) as char);
    n = (n - 1) / 26;
  }
  out
}

impl EnvDisplay for AtomID {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    fe.data[*self].name.fmt(f)
  }
}
impl EnvDisplay for SortID {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    fe.sorts[*self].atom.fmt(fe, f)
  }
}
impl EnvDisplay for TermID {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    fe.terms[*self].atom.fmt(fe, f)
  }
}
impl EnvDisplay for ThmID {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    fe.thms[*self].atom.fmt(fe, f)
  }
}

impl EnvDisplay for LispKind {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      LispKind::Atom(a) => a.fmt(fe, f),
      LispKind::List(es) if es.is_empty() => "()".fmt(f),
      LispKind::DottedList(es, r) if es.is_empty() => r.fmt(fe, f),
      LispKind::DottedList(_, _) |
      LispKind::List(_) => self.list(0, true, fe, f),
      LispKind::Annot(_, e) => e.fmt(fe, f),
      LispKind::Number(n) => n.fmt(f),
      LispKind::String(s) => write!(f, "{:?}", s),
      LispKind::Bool(true) => "#t".fmt(f),
      LispKind::Bool(false) => "#f".fmt(f),
      LispKind::Syntax(s) => s.fmt(f),
      LispKind::Undef => write!(f, "#undef"),
      LispKind::Proc(Proc::Builtin(p)) => p.fmt(f),
      LispKind::Proc(Proc::Lambda {pos: ProcPos::Unnamed(pos), ..}) => {
        let r = fe.source.to_pos(pos.span.start);
        let fname = pos.file.path().file_name().unwrap().to_str().unwrap();
        write!(f, "#[fn at {} {}:{}]", fname, r.line + 1, r.character + 1)
      }
      &LispKind::Proc(Proc::Lambda {pos: ProcPos::Named(ref pos, a), ..}) => {
        let r = fe.source.to_pos(pos.span.start);
        let fname = pos.file.path().file_name().unwrap().to_str().unwrap();
        let x = &fe.data[a].name;
        write!(f, "#[fn {} at {} {}:{}]", x, fname, r.line + 1, r.character + 1)
      }
      LispKind::Proc(Proc::MatchCont(_)) => write!(f, "#[match cont]"),
      LispKind::Proc(Proc::RefineCallback(_)) => write!(f, "#[refine]"),
      LispKind::AtomMap(m) => {
        write!(f, "(atom-map!")?;
        for (a, v) in m {write!(f, " [{} {}]", fe.data[*a].name, fe.to(v))?}
        write!(f, ")")
      }
      LispKind::Ref(m) => m.try_lock().unwrap().fmt(fe, f),
      &LispKind::MVar(n, _) => write!(f, "?{}", alphanumber(n)),
      LispKind::Goal(e) => write!(f, "(goal {})", fe.to(e)),
    }
  }
}

impl EnvDisplay for Uncons {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    self.0.list(self.1, true, fe, f)
  }
}

impl<T: EnvDisplay> EnvDisplay for [T] {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "[{}]", self.iter().map(|e| fe.to(e)).format(", "))
  }
}

impl EnvDisplay for crate::util::Span {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    fe.source[*self].fmt(f)
  }
}

impl<T: EnvDisplay> EnvDisplay for Vec<T> {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result { self.deref().fmt(fe, f) }
}
impl<T: EnvDisplay> EnvDisplay for Box<T> {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result { self.deref().fmt(fe, f) }
}
impl<T: EnvDisplay> EnvDisplay for std::sync::Arc<T> {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result { self.deref().fmt(fe, f) }
}


impl EnvDisplay for InferTarget {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      InferTarget::Unknown => "?".fmt(f),
      InferTarget::Provable => "provable".fmt(f),
      InferTarget::Bound(a) => write!(f, "{{{}}}", fe.to(a)),
      InferTarget::Reg(a) => a.fmt(fe, f),
    }
  }
}