//! Basic printer for lisp terms.
//!
//! This is essentially an implementation of [`Display`] for lisp terms,
//! but we can't do this literally because a [`Display`] implementation doesn't
//! get side information besides the [`Formatter`](std::fmt::Formatter), while we need
//! the source text and the environment, packaged as the [`FormatEnv`] struct.
//!
//! The main trait for [`Display`] modulo [`FormatEnv`] is [`EnvDisplay`]. It is
//! possible to use a [`EnvDisplay`] object in a macro like [`format!`] or [`write!`]
//! using [`FormatEnv::to`], or [`Elaborator::print`].

use std::ops::Deref;
use std::fmt::{self, Display};
use itertools::Itertools;
use crate::{AtomId, LispKind, LispVal, lisp::{Uncons, InferTarget, Proc, ProcPos},
  LinedString, Environment, Elaborator, TermId, ThmId, SortId,
  Sort, Term, Thm, DeclKey, ast::{SExpr, SExprKind, span_atom}};

/// The side information required to print an object in the environment.
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct FormatEnv<'a> {
  /// The source text, used to resolve line/col information for procedure printing.
  pub source: &'a LinedString,
  /// The environment, used to resolve atom names.
  pub env: &'a Environment,
}

/// A trait for displaying data given access to the environment.
pub trait EnvDisplay {
  /// Print formatted output to the given formatter. The signature is exactly the same
  /// as [`Display::fmt`] except it has an extra argument for the environment.
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

/// The result of [`FormatEnv::to`], a struct that implements [`Display`] if the
/// argument implements [`EnvDisplay`].
pub struct Print<'a, D: ?Sized> {
  fe: FormatEnv<'a>,
  e: &'a D,
}

impl<'a> FormatEnv<'a> {
  /// Given a [`FormatEnv`], convert an `impl EnvDisplay` into an `impl Display`.
  /// This can be used in macros like `println!("{}", fe.to(e))` to print objects.
  pub fn to<D: ?Sized>(self, e: &'a D) -> Print<'a, D> {
    Print {fe: self, e}
  }
}

impl<'a> Deref for FormatEnv<'a> {
  type Target = Environment;
  fn deref(&self) -> &Environment {self.env}
}

impl Elaborator {
  /// Build a [`FormatEnv`] from the current environment.
  pub fn format_env(&self) -> FormatEnv<'_> {
    FormatEnv {source: &self.ast.source, env: self}
  }
  /// Convert an `impl EnvDisplay` into an `impl Display` in the current environment.
  /// This can be used in macros like `println!("{}", elab.print(e))` to print objects.
  pub fn print<'a, D: ?Sized>(&'a self, e: &'a D) -> Print<'a, D> {
    self.format_env().to(e)
  }
}

impl<'a, D: EnvDisplay + ?Sized> fmt::Display for Print<'a, D> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.e.fmt(self.fe, f) }
}

/// Items implementing [`EnvDebug`] can be put in formatters using `{:#?}`.
impl<'a, D: crate::elab::lisp::debug::EnvDebug + ?Sized> fmt::Debug for Print<'a, D> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.e.env_dbg(self.fe, f)
  }
}


fn list(init: &[LispVal], e: Option<&LispKind>, mut start: bool, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
    Some(LispKind::DottedList(es, r)) => list(es, Some(r), start, fe, f),
    Some(e) if e.exactly(0) => if start {write!(f, "()")} else {write!(f, ")")},
    Some(e) => if start {write!(f, "{}", fe.to(e))} else {write!(f, " . {})", fe.to(e))}
  }
}

fn alphanumber(n: usize) -> String {
  let mut out = Vec::with_capacity(2);
  let mut n = n + 1;
  while n != 0 {
    #[allow(clippy::cast_possible_truncation)]
    { out.push(b'a' + ((n - 1) % 26) as u8); }
    #[allow(clippy::integer_division)]
    { n = (n - 1) / 26; }
  }
  out.reverse();
  unsafe { String::from_utf8_unchecked(out) }
}

impl EnvDisplay for AtomId {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fe.data[*self].name.fmt(f)
  }
}
impl EnvDisplay for Option<AtomId> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      None => "_".fmt(f),
      Some(a) => a.fmt(fe, f)
    }
  }
}
impl EnvDisplay for SortId {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fe.sorts[*self].atom.fmt(fe, f)
  }
}
impl EnvDisplay for TermId {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fe.terms[*self].atom.fmt(fe, f)
  }
}
impl EnvDisplay for ThmId {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fe.thms[*self].atom.fmt(fe, f)
  }
}

impl EnvDisplay for LispVal {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(fe, f) }
}

impl EnvDisplay for LispKind {
  #[allow(clippy::match_overlapping_arm)]
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      LispKind::Atom(a) => a.fmt(fe, f),
      LispKind::List(es) if es.is_empty() => "()".fmt(f),
      LispKind::DottedList(es, r) if es.is_empty() => r.fmt(fe, f),
      LispKind::DottedList(es, r) => list(es, Some(r), true, fe, f),
      LispKind::List(es) => list(es, None, true, fe, f),
      LispKind::Annot(_, e) => e.fmt(fe, f),
      LispKind::Number(n) => n.fmt(f),
      LispKind::String(s) => {
        write!(f, "\"")?;
        for &c in &**s {
          match c {
            b'\\' => write!(f, "\\\\")?,
            b'\n' => write!(f, "\\n")?,
            b'\r' => write!(f, "\\r")?,
            b'\"' => write!(f, "\\\"")?,
            0x20..=0x7e => write!(f, "{}", c as char)?,
            _ => write!(f, "\\x{:02x}", c)?,
          }
        }
        write!(f, "\"")
      }
      LispKind::Bool(true) => "#t".fmt(f),
      LispKind::Bool(false) => "#f".fmt(f),
      LispKind::Syntax(s) => s.fmt(f),
      LispKind::Undef => write!(f, "#undef"),
      LispKind::Proc(Proc::Builtin(p)) => p.fmt(f),
      LispKind::Proc(Proc::Lambda {pos: ProcPos::Unnamed(pos), ..}) => {
        let r = fe.source.to_pos(pos.span.start);
        let fname = pos.file.path().file_name().and_then(std::ffi::OsStr::to_str).unwrap_or("?");
        write!(f, "#[fn at {} {}:{}]", fname, r.line + 1, r.character + 1)
      }
      &LispKind::Proc(Proc::Lambda {pos: ProcPos::Named(ref pos, _, a), ..}) => {
        let r = fe.source.to_pos(pos.span.start);
        let fname = pos.file.path().file_name().and_then(std::ffi::OsStr::to_str).unwrap_or("?");
        let x = &fe.data[a].name;
        write!(f, "#[fn {} at {} {}:{}]", x, fname, r.line + 1, r.character + 1)
      }
      LispKind::Proc(Proc::MatchCont(_)) => write!(f, "#[match cont]"),
      LispKind::Proc(Proc::RefineCallback) => write!(f, "#[refine]"),
      LispKind::Proc(Proc::ProofThunk(x, _)) => write!(f, "#[proof of {}]", fe.to(x)),
      LispKind::Proc(Proc::MergeMap(_)) => write!(f, "#[merge-map]"),
      #[cfg(feature = "mmc")]
      LispKind::Proc(Proc::MmcCompiler(_)) => write!(f, "#[mmc-compiler]"),
      LispKind::AtomMap(m) => {
        write!(f, "(atom-map!")?;
        for (a, v) in m {write!(f, " [{} {}]", fe.data[*a].name, fe.to(v))?}
        write!(f, ")")
      }
      LispKind::Ref(m) if m.too_many_readers() => write!(f, "#[ref]"),
      LispKind::Ref(m) => m.get(|e| e.fmt(fe, f)),
      &LispKind::MVar(n, _) => write!(f, "?{}", alphanumber(n)),
      LispKind::Goal(e) => write!(f, "(goal {})", fe.to(e)),
    }
  }
}

impl EnvDisplay for Uncons {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Uncons::New(e) => e.fmt(fe, f),
      Uncons::List(es) => list(es, None, true, fe, f),
      Uncons::DottedList(es, r) => list(es, Some(r), true, fe, f),
    }
  }
}

impl<T: EnvDisplay> EnvDisplay for [T] {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "[{}]", self.iter().map(|e| fe.to(e)).format(", "))
  }
}

impl EnvDisplay for crate::Span {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fe.source.str_at(*self).fmt(f)
  }
}

impl<T: EnvDisplay> EnvDisplay for Vec<T> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.deref().fmt(fe, f) }
}
impl<T: EnvDisplay> EnvDisplay for Box<T> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.deref().fmt(fe, f) }
}
impl<T: EnvDisplay> EnvDisplay for std::sync::Arc<T> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.deref().fmt(fe, f) }
}
impl<T: EnvDisplay> EnvDisplay for std::rc::Rc<T> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.deref().fmt(fe, f) }
}

impl EnvDisplay for InferTarget {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      InferTarget::Unknown => "?".fmt(f),
      InferTarget::Provable => "provable".fmt(f),
      InferTarget::Bound(a) => write!(f, "{{{}}}", fe.to(a)),
      InferTarget::Reg(a) => a.fmt(fe, f),
    }
  }
}

impl Display for Sort {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}sort {};", self.mods, self.name)
  }
}

impl EnvDisplay for Term {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if let Some(DeclKey::Term(tid)) = fe.env.data[self.atom].decl {
      fe.pretty(|p| p.term(tid, true).render_fmt(80, f))
    } else { panic!("undeclared term") }
  }
}

impl EnvDisplay for Thm {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if let Some(DeclKey::Thm(tid)) = fe.env.data[self.atom].decl {
      fe.pretty(|p| p.thm(tid).render_fmt(80, f))
    } else { panic!("undeclared theorem") }
  }
}

impl EnvDisplay for SExpr {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &self.k {
      &SExprKind::Atom(a) => {
        unsafe {std::str::from_utf8_unchecked(span_atom(fe.source, self.span, a))}.fmt(f)
      }
      SExprKind::List(es) => {
        let mut it = es.iter();
        match it.next() {
          None => "()".fmt(f),
          Some(e) => {
            write!(f, "({}", fe.to(e))?;
            for e in it {write!(f, " {}", fe.to(e))?}
            ")".fmt(f)
          }
        }
      }
      SExprKind::DottedList(es, r) => {
        "(".fmt(f)?;
        for e in es {write!(f, "{} ", fe.to(e))?}
        write!(f, ". {})", fe.to(r))
      }
      SExprKind::Number(n) => n.fmt(f),
      SExprKind::String(s) => write!(f, "{:?}", s),
      SExprKind::Bool(true) => "#t".fmt(f),
      SExprKind::Bool(false) => "#f".fmt(f),
      SExprKind::DocComment(_, e) => e.fmt(fe, f),
      SExprKind::Undef => "#undef".fmt(f),
      SExprKind::Formula(s) => fe.source.str_at(s.0).fmt(f),
    }
  }
}
