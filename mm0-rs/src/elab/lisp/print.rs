use std::ops::Deref;
use std::fmt::{self, Display};
use itertools::Itertools;
use super::super::{LinedString, Environment, Elaborator, TermID, ThmID, SortID,
  Sort, Term, Thm};
use super::{AtomID, LispKind, LispVal, Uncons, InferTarget, Proc, ProcPos};

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

impl Elaborator {
  pub fn format_env(&self) -> FormatEnv {
    FormatEnv {source: &self.ast.source, env: self}
  }
  pub fn print<'a, D: ?Sized>(&'a self, e: &'a D) -> Print<'a, D> {
    self.format_env().to(e)
  }
}

impl<'a, D: EnvDisplay + ?Sized> fmt::Display for Print<'a, D> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.e.fmt(self.fe, f) }
}

fn list(init: &[LispVal], e: Option<&LispKind>, mut start: bool, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
  for e in init {
    if start {
      write!(f, "({}", fe.to(e))?;
      start = false
    } else {
      write!(f, " {}", fe.to(e))?
    }
  }
  match e {
    None => if start {write!(f, "()")} else {write!(f, ")")},
    Some(LispKind::List(es)) => list(es, None, start, fe, f),
    Some(LispKind::DottedList(es, r)) => list(es, Some(&r), start, fe, f),
    Some(e) if e.exactly(0) => if start {write!(f, "()")} else {write!(f, ")")},
    Some(e) => if start {write!(f, "{}", fe.to(e))} else {write!(f, " . {})", fe.to(e))}
  }
}

fn alphanumber(n: usize) -> String {
  let mut out = Vec::with_capacity(2);
  let mut n = n + 1;
  while n != 0 {
    out.push(b'a' + ((n - 1) % 26) as u8);
    n = (n - 1) / 26;
  }
  out.reverse();
  unsafe { String::from_utf8_unchecked(out) }
}

impl EnvDisplay for AtomID {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    fe.data[*self].name.fmt(f)
  }
}
impl EnvDisplay for Option<AtomID> {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      None => "_".fmt(f),
      Some(a) => a.fmt(fe, f)
    }
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

impl EnvDisplay for LispVal {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(fe, f) }
}

impl EnvDisplay for LispKind {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      LispKind::Atom(a) => a.fmt(fe, f),
      LispKind::List(es) if es.is_empty() => "()".fmt(f),
      LispKind::DottedList(es, r) if es.is_empty() => r.fmt(fe, f),
      LispKind::DottedList(es, r) => list(es, Some(&r), true, fe, f),
      LispKind::List(es) => list(es, None, true, fe, f),
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
      &LispKind::Proc(Proc::Lambda {pos: ProcPos::Named(ref pos, _, a), ..}) => {
        let r = fe.source.to_pos(pos.span.start);
        let fname = pos.file.path().file_name().unwrap().to_str().unwrap();
        let x = &fe.data[a].name;
        write!(f, "#[fn {} at {} {}:{}]", x, fname, r.line + 1, r.character + 1)
      }
      LispKind::Proc(Proc::MatchCont(_)) => write!(f, "#[match cont]"),
      LispKind::Proc(Proc::RefineCallback) => write!(f, "#[refine]"),
      LispKind::Proc(Proc::ProofThunk(x, _)) => write!(f, "#[proof of {}]", fe.to(x)),
      LispKind::AtomMap(m) => {
        write!(f, "(atom-map!")?;
        for (a, v) in m {write!(f, " [{} {}]", fe.data[*a].name, fe.to(v))?}
        write!(f, ")")
      }
      LispKind::Ref(m) => m.get().fmt(fe, f),
      &LispKind::MVar(n, _) => write!(f, "?{}", alphanumber(n)),
      LispKind::Goal(e) => write!(f, "(goal {})", fe.to(e)),
    }
  }
}

impl EnvDisplay for Uncons {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Uncons::New(e) => e.fmt(fe, f),
      Uncons::List(es) => list(es, None, true, fe, f),
      Uncons::DottedList(es, r) => list(es, Some(&r), true, fe, f),
    }
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
impl<T: EnvDisplay> EnvDisplay for std::rc::Rc<T> {
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

impl Display for Sort {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}sort {};", self.mods, self.name)
  }
}

impl EnvDisplay for Term {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    fe.pretty(|p| p.term(self).render_fmt(80, f))
  }
}

impl EnvDisplay for Thm {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    fe.pretty(|p| p.thm(self).render_fmt(80, f))
  }
}
