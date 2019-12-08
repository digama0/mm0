use std::ops::Deref;
use std::hash::Hash;
use std::sync::{Arc, Mutex};
use std::collections::HashMap;
use num::BigInt;
use crate::parser::ast;
use super::*;

pub enum Syntax {
  Define,
  Lambda,
  Quote,
  Unquote,
  If,
  Focus,
  Let,
  Letrec,
  Match,
  MatchFn,
  MatchFns,
}

impl Syntax {
  pub fn from_str(s: &str) -> Option<Syntax> {
    match s {
      "def" => Some(Syntax::Define),
      "fn" => Some(Syntax::Lambda),
      "quote" => Some(Syntax::Quote),
      "unquote" => Some(Syntax::Unquote),
      "if" => Some(Syntax::If),
      "focus" => Some(Syntax::Focus),
      "let" => Some(Syntax::Let),
      "letrec" => Some(Syntax::Letrec),
      "match" => Some(Syntax::Match),
      "match-fn" => Some(Syntax::MatchFn),
      "match-fn*" => Some(Syntax::MatchFns),
      _ => None
    }
  }
  pub fn from_atom(s: &str, a: ast::Atom) -> Option<Syntax> {
    match a {
      ast::Atom::Ident => Self::from_str(s),
      ast::Atom::Quote => Some(Syntax::Quote),
      ast::Atom::Unquote => Some(Syntax::Unquote),
    }
  }
}

pub type LispVal = Arc<LispKind>;
pub enum LispKind {
  Atom(AtomID),
  List(Vec<LispVal>), // reversed
  DottedList(Vec<LispVal>, LispVal), // vec is reversed
  Number(BigInt),
  String(String),
  UnparsedFormula(String),
  Bool(bool),
  Syntax(Syntax),
  Undef,
  Proc(Proc),
  AtomMap(HashMap<AtomID, LispVal>),
  Ref(Mutex<LispVal>),
  MVar(usize, ArcString, bool),
  Goal(LispVal),
}
lazy_static! {
  pub static ref UNDEF: LispVal = Arc::new(LispKind::Undef);
}

pub enum Proc {
  Builtin(BuiltinProc),
  LambdaExact(Vec<LispVal>, usize, Vec<Code>),
  LambdaAtLeast(Vec<LispVal>, usize, Vec<Code>),
}

#[derive(Copy, Clone)]
pub enum BuiltinProc {

}

pub enum Code {
  Local(usize),
  Global(AtomID),
}

#[derive(Default)]
pub struct LispRemapper {
  pub atom: Vec<AtomID>,
  pub lisp: HashMap<*const LispKind, LispVal>,
}
impl Remap<LispRemapper> for AtomID {
  fn remap(&self, r: &mut LispRemapper) -> Self { *r.atom.get(self.0).unwrap_or(self) }
}
impl<R, K: Clone + Hash + Eq, V: Remap<R>> Remap<R> for HashMap<K, V> {
  fn remap(&self, r: &mut R) -> Self { self.iter().map(|(k, v)| (k.clone(), v.remap(r))).collect() }
}
impl<R, A: Remap<R>> Remap<R> for Mutex<A> {
  fn remap(&self, r: &mut R) -> Self { Mutex::new(self.lock().unwrap().remap(r)) }
}
impl Remap<LispRemapper> for LispVal {
  fn remap(&self, r: &mut LispRemapper) -> Self {
    let p: *const LispKind = self.deref();
    if let Some(v) = r.lisp.get(&p) {return v.clone()}
    let v = match self.deref() {
      LispKind::Atom(a) => Arc::new(LispKind::Atom(a.remap(r))),
      LispKind::List(v) => Arc::new(LispKind::List(v.remap(r))),
      LispKind::DottedList(v, l) => Arc::new(LispKind::DottedList(v.remap(r), l.remap(r))),
      LispKind::Proc(f) => Arc::new(LispKind::Proc(f.remap(r))),
      LispKind::AtomMap(m) => Arc::new(LispKind::AtomMap(m.remap(r))),
      LispKind::Ref(m) => Arc::new(LispKind::Ref(m.remap(r))),
      _ => self.clone(),
    };
    r.lisp.entry(p).or_insert(v).clone()
  }
}
impl Remap<LispRemapper> for Proc {
  fn remap(&self, r: &mut LispRemapper) -> Self {
    match self {
      &Proc::LambdaExact(ref env, n, ref c) => Proc::LambdaExact(env.remap(r), n, c.remap(r)),
      &Proc::LambdaAtLeast(ref env, n, ref c) => Proc::LambdaAtLeast(env.remap(r), n, c.remap(r)),
      &Proc::Builtin(p) => Proc::Builtin(p),
    }
  }
}
impl Remap<LispRemapper> for Code {
  fn remap(&self, r: &mut LispRemapper) -> Self {
    match self {
      &Code::Local(i) => Code::Local(i),
      &Code::Global(a) => Code::Global(a.remap(r)),
    }
  }
}

pub struct Compiler<'a, T: FileServer + ?Sized> {
  elab: &'a mut Elaborator<'a, T>,
  code: Vec<Code>,
  ctx: (HashMap<ArcString, usize>, Vec<(ArcString, bool)>),
}
impl<'a, T: FileServer + ?Sized> Deref for Compiler<'a, T> {
  type Target = Elaborator<'a, T>;
  fn deref(&self) -> &Elaborator<'a, T> { self.elab }
}
impl<'a, T: FileServer + ?Sized> DerefMut for Compiler<'a, T> {
  fn deref_mut(&mut self) -> &mut Elaborator<'a, T> { self.elab }
}

impl<'a, T: FileServer + ?Sized> Compiler<'a, T> {
  pub fn compile_expr(&mut self, e: &SExpr) -> Result<()> {
    match e.k {
      SExprKind::Atom(a) => {
        let s = self.span(e.span);
        if Syntax::from_atom(s, a).is_some() {
          Err(ElabError::new_e(e.span, "keyword in invalid position"))?
        }
        if let Some(&i) = self.ctx.0.get(s) {
          self.code.push(Code::Local(i));
        } else {
          let s = s.into();
          let id = self.get_atom(s);
          self.code.push(Code::Global(id));
        }
      }
      _ => unimplemented!()
    }
    Ok(())
  }
}