use std::ops::Deref;
use std::fmt::{self, Display};
use itertools::Itertools;
use super::super::{LinedString, Environment, Elaborator, TermID, ThmID, SortID,
  Sort, Term, environment::Type, Thm, ExprNode};
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

fn dep_type(bvs: &[AtomID], ds: u64, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
  let mut i = 1;
  for x in bvs {
    if ds & i != 0 {write!(f, "{}", fe.to(x))?}
    i *= 2;
  }
  Ok(())
}

fn grouped_binders(bis: &[(Option<AtomID>, Type)], bvs: &mut Vec<AtomID>,
    fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
  let mut rest = bis;
  loop {
    let mut it = rest.iter();
    let ty = match it.next() {
      None => return Ok(()),
      Some((_, ty)) => ty,
    };
    let (bis1, bis2) = rest.split_at(it.position(|(_, ty2)| ty != ty2).unwrap_or(rest.len()));
    match ty {
      &Type::Bound(s) => {
        write!(f, " {{{}: {}}}", bis1.iter().map(|(a, _)| {
          bvs.push(a.unwrap_or(AtomID::UNDER));
          fe.to(a)
        }).format(" "), fe.to(&s))?;
      }
      &Type::Reg(s, ds) => {
        write!(f, " ({}: {}", bis1.iter().map(|(a, _)| fe.to(a)).format(" "), fe.to(&s))?;
        dep_type(bvs, ds, fe, f)?;
        write!(f, ")")?;
      }
    }
    rest = bis2;
  }
}

impl EnvDisplay for Term {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}{} {}", self.vis,
      if self.val.is_some() {"def"} else {"term"},
      fe.to(&self.atom))?;
    let mut bvs = vec![];
    grouped_binders(&self.args, &mut bvs, fe, f)?;
    write!(f, ": {}", fe.to(&self.ret.0))?;
    dep_type(&bvs, self.ret.1, fe, f)?;
    write!(f, ";")?;
    Ok(())
  }
}

fn expr_node(bis: &[(Option<AtomID>, Type)], heap: &[ExprNode], e: &ExprNode,
    fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
  match e {
    &ExprNode::Ref(n) => match bis.get(n) {
      Some(&(a, _)) => write!(f, "{}", fe.to(&a.unwrap_or(AtomID::UNDER))),
      None => expr_node(bis, heap, &heap[n], fe, f),
    }
    &ExprNode::Dummy(a, _) => write!(f, "{}", fe.to(&a)),
    ExprNode::App(t, es) if es.is_empty() => write!(f, "{}", fe.to(t)),
    ExprNode::App(t, es) => {
      write!(f, "({}", fe.to(t))?;
      for e in es {
        write!(f, " ")?;
        expr_node(bis, heap, e, fe, f)?;
      }
      write!(f, ")")
    }
  }
}

impl EnvDisplay for Thm {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}{} {}:", self.vis,
      if self.proof.is_some() {"theorem"} else {"axiom"},
      fe.to(&self.atom))?;
    let mut bvs = vec![];
    grouped_binders(&self.args, &mut bvs, fe, f)?;
    for (_, h) in &self.hyps {
      write!(f, "\n  $ ")?;
      expr_node(&self.args, &self.heap, h, fe, f)?;
      write!(f, " $ >")?;
    }
    write!(f, "\n  $ ")?;
    expr_node(&self.args, &self.heap, &self.ret, fe, f)?;
    write!(f, " $;")
  }
}
