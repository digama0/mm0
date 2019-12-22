pub mod parser;
pub mod eval;
pub mod print;

use std::ops::Deref;
use std::hash::Hash;
use std::sync::{Arc, Mutex, atomic::AtomicBool};
use std::collections::HashMap;
use num::BigInt;
use crate::parser::ast::{Atom};
use crate::util::{ArcString, FileSpan};
use super::{AtomID, AtomVec, Remap};
use parser::IR;
pub use super::math_parser::{QExpr, QExprKind};

macro_rules! str_enum {
  (enum $name:ident {$($e:ident: $s:expr,)*}) => {
    #[derive(Copy, Clone, Debug)]
    pub enum $name { $($e),* }
    impl $name {
      pub fn from_str(s: &str) -> Option<$name> {
        match s {
          $($s => Some($name::$e),)*
          _ => None
        }
      }
      pub fn to_str(self) -> &'static str {
        match self {
          $($name::$e => $s),*
        }
      }
    }
  }
}

str_enum! {
  enum Syntax {
    Define: "def",
    Lambda: "fn",
    Quote: "quote",
    Unquote: "unquote",
    If: "if",
    Focus: "focus",
    Let: "let",
    Letrec: "letrec",
    Match: "match",
    MatchFn: "match-fn",
    MatchFns: "match-fn*",
  }
}

impl Syntax {
  pub fn parse(s: &str, a: Atom) -> Result<Syntax, &str> {
    match a {
      Atom::Ident => Self::from_str(s).ok_or(s),
      Atom::Quote => Ok(Syntax::Quote),
      Atom::Unquote => Ok(Syntax::Unquote),
      Atom::Nfx => Err(":nfx"),
    }
  }
}

impl std::fmt::Display for Syntax {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    self.to_str().fmt(f)
  }
}

#[derive(Copy, Clone, Debug)]
pub enum InferTarget {
  Unknown,
  Provable,
  Bound(AtomID),
  Reg(AtomID),
}

pub type LispVal = Arc<LispKind>;
#[derive(Debug)]
pub enum LispKind {
  Atom(AtomID),
  List(Vec<LispVal>),
  DottedList(Vec<LispVal>, LispVal),
  Annot(Annot, LispVal),
  Number(BigInt),
  String(ArcString),
  UnparsedFormula(ArcString),
  Bool(bool),
  Syntax(Syntax),
  Undef,
  Proc(Proc),
  AtomMap(HashMap<AtomID, LispVal>),
  Ref(Mutex<LispVal>),
  MVar(usize, InferTarget),
  Goal(LispVal),
}
lazy_static! {
  pub static ref UNDEF: LispVal = Arc::new(LispKind::Undef);
  pub static ref TRUE: LispVal = Arc::new(LispKind::Bool(true));
  pub static ref FALSE: LispVal = Arc::new(LispKind::Bool(false));
  pub static ref NIL: LispVal = Arc::new(LispKind::List(vec![]));
}

impl From<&LispKind> for bool {
  fn from(e: &LispKind) -> bool { e.truthy() }
}
impl LispKind {
  pub fn unwrapped<T>(&self, f: impl FnOnce(&Self) -> T) -> T {
    match self {
      LispKind::Ref(m) => m.lock().unwrap().unwrapped(f),
      LispKind::Annot(_, v) => v.unwrapped(f),
      _ => f(self)
    }
  }

  pub fn truthy(&self) -> bool {
    self.unwrapped(|e| if let LispKind::Bool(false) = e {false} else {true})
  }
  pub fn is_bool(&self) -> bool {
    self.unwrapped(|e| if let LispKind::Bool(_) = e {true} else {false})
  }
  pub fn as_bool(&self) -> Option<bool> {
    self.unwrapped(|e| if let &LispKind::Bool(b) = e {Some(b)} else {None})
  }
  pub fn is_atom(&self) -> bool {
    self.unwrapped(|e| if let LispKind::Atom(_) = e {true} else {false})
  }
  pub fn as_atom(&self) -> Option<AtomID> {
    self.unwrapped(|e| if let &LispKind::Atom(a) = e {Some(a)} else {None})
  }
  pub fn is_pair(&self) -> bool {
    self.unwrapped(|e| match e {
      LispKind::List(es) => !es.is_empty(),
      LispKind::DottedList(es, r) => !es.is_empty() || r.is_pair(),
      _ => false,
    })
  }
  pub fn is_null(&self) -> bool {
    self.unwrapped(|e| if let LispKind::List(es) = e {es.is_empty()} else {false})
  }
  pub fn is_int(&self) -> bool {
    self.unwrapped(|e| if let LispKind::Number(_) = e {true} else {false})
  }
  pub fn is_proc(&self) -> bool {
    self.unwrapped(|e| if let LispKind::Proc(_) = e {true} else {false})
  }
  pub fn is_string(&self) -> bool {
    self.unwrapped(|e| if let LispKind::String(_) = e {true} else {false})
  }
  pub fn is_map(&self) -> bool {
    self.unwrapped(|e| if let LispKind::AtomMap(_) = e {true} else {false})
  }
  pub fn is_def(&self) -> bool {
    self.unwrapped(|e| if let LispKind::Undef = e {false} else {true})
  }
  pub fn is_ref(&self) -> bool {
    match self {
      LispKind::Ref(_) => true,
      LispKind::Annot(_, v) => v.is_ref(),
      _ => false,
    }
  }
  pub fn fspan(&self) -> Option<FileSpan> {
    match self {
      LispKind::Ref(m) => m.lock().unwrap().fspan(),
      LispKind::Annot(Annot::Span(sp), _) => Some(sp.clone()),
      // LispKind::Annot(_, e) => e.fspan(),
      _ => None
    }
  }
  pub fn is_mvar(&self) -> bool {
    self.unwrapped(|e| if let LispKind::MVar(_, _) = e {true} else {false})
  }
  pub fn is_goal(&self) -> bool {
    self.unwrapped(|e| if let LispKind::Goal(_) = e {true} else {false})
  }
  pub fn goal_type(&self) -> Option<LispVal> {
    self.unwrapped(|e| if let LispKind::Goal(e) = e {Some(e.clone())} else {None})
  }

  pub fn exactly(&self, n: usize) -> bool {
    self.unwrapped(|e| match e {
      LispKind::List(es) => n == es.len(),
      LispKind::DottedList(es, _) if n <= es.len() => false,
      LispKind::DottedList(es, r) => r.exactly(n - es.len()),
      _ => false,
    })
  }
  pub fn is_list(&self) -> bool {
    self.unwrapped(|e| match e {
      LispKind::List(_) => true,
      LispKind::DottedList(_, r) => r.is_list(),
      _ => false,
    })
  }
  pub fn len(&self) -> usize {
    self.unwrapped(|e| match e {
      LispKind::List(es) => es.len(),
      LispKind::DottedList(es, r) => es.len() + r.len(),
      _ => 0,
    })
  }
  pub fn at_least(&self, n: usize) -> bool {
    self.unwrapped(|e| match e {
      LispKind::List(es) => return n == es.len(),
      LispKind::DottedList(es, r) if n <= es.len() => r.is_list(),
      LispKind::DottedList(es, r) => r.at_least(n - es.len()),
      _ => false,
    })
  }
}

#[derive(Clone, Debug)]
pub enum Annot {
  Span(FileSpan),
}

#[derive(Clone, Debug)]
pub enum ProcPos {
  Named(FileSpan, AtomID),
  Unnamed(FileSpan),
}
impl ProcPos {
  fn fspan(&self) -> &FileSpan {
    match self {
      ProcPos::Named(fsp, _) => fsp,
      ProcPos::Unnamed(fsp) => fsp,
    }
  }
}

#[derive(Debug)]
pub enum Proc {
  Builtin(BuiltinProc),
  Lambda {
    pos: ProcPos,
    env: Vec<LispVal>,
    spec: ProcSpec,
    code: Arc<IR>
  },
  MatchCont(Arc<AtomicBool>),
}

#[derive(Copy, Clone, Debug)]
pub enum ProcSpec {
  Exact(usize),
  AtLeast(usize),
}

impl ProcSpec {
  pub fn valid(self, i: usize) -> bool {
    match self {
      ProcSpec::Exact(n) => i == n,
      ProcSpec::AtLeast(n) => i >= n,
    }
  }
}

impl Proc {
  pub fn spec(&self) -> ProcSpec {
    match self {
      Proc::Builtin(p) => p.spec(),
      &Proc::Lambda {spec, ..} => spec,
      Proc::MatchCont(_) => ProcSpec::AtLeast(0),
    }
  }
}

str_enum! {
  enum BuiltinProc {
    Display: "display",
    Error: "error",
    Print: "print",
    Begin: "begin",
    Apply: "apply",
    Add: "+",
    Mul: "*",
    Max: "max",
    Min: "min",
    Sub: "-",
    Div: "//",
    Mod: "%",
    Lt: "<",
    Le: "<=",
    Gt: ">",
    Ge: ">=",
    Eq: "=",
    ToString: "->string",
    StringToAtom: "string->atom",
    StringAppend: "string-append",
    Not: "not",
    And: "and",
    Or: "or",
    List: "list",
    Cons: "cons",
    Head: "hd",
    Tail: "tl",
    Map: "map",
    IsBool: "bool?",
    IsAtom: "atom?",
    IsPair: "pair?",
    IsNull: "null?",
    IsNumber: "number?",
    IsString: "string?",
    IsProc: "fn?",
    IsDef: "def?",
    IsRef: "ref?",
    NewRef: "ref!",
    GetRef: "get!",
    SetRef: "set!",
    Async: "async",
    IsAtomMap: "atom-map?",
    NewAtomMap: "atom-map!",
    Lookup: "lookup",
    Insert: "insert!",
    InsertNew: "insert",
    SetTimeout: "set-timeout",
    IsMVar: "mvar?",
    IsGoal: "goal?",
    NewMVar: "mvar!",
    PrettyPrint: "pp",
    NewGoal: "goal",
    GoalType: "goal-type",
    InferType: "infer-type",
    GetMVars: "get-mvars",
    GetGoals: "get-goals",
    SetGoals: "set-goals",
    ToExpr: "to-expr",
    Refine: "refine",
    Have: "have",
    Stat: "stat",
    GetDecl: "get-decl",
    AddDecl: "add-decl!",
    AddTerm: "add-term!",
    AddThm: "add-thm!",
    SetReporting: "set-reporting",
    RefineExtraArgs: "refine-extra-args",
  }
}

impl std::fmt::Display for BuiltinProc {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    self.to_str().fmt(f)
  }
}

#[derive(Clone, Debug)]
pub struct Uncons(LispVal, usize);
impl Uncons {
  pub fn from(e: LispVal) -> Uncons { Uncons(e, 0) }
  pub fn exactly(&self, n: usize) -> bool { self.0.exactly(self.1 + n) }
  pub fn at_least(&self, n: usize) -> bool { self.0.at_least(self.1 + n) }

  pub fn as_lisp(self) -> LispVal {
    if self.1 == 0 {return self.0}
    self.0.unwrapped(|e| match e {
      LispKind::List(es) if self.1 == es.len() => NIL.clone(),
      LispKind::List(es) => Arc::new(LispKind::List(es[self.1..].into())),
      LispKind::DottedList(es, r) if self.1 == es.len() => r.clone(),
      LispKind::DottedList(es, r) => Arc::new(LispKind::DottedList(es[self.1..].into(), r.clone())),
      _ => unreachable!()
    })
  }
}

impl Iterator for Uncons {
  type Item = LispVal;
  fn next(&mut self) -> Option<LispVal> {
    loop {
      match &*self.0 {
        LispKind::Ref(m) => {let e = m.lock().unwrap().clone(); self.0 = e}
        LispKind::Annot(_, v) => self.0 = v.clone(),
        LispKind::List(es) => match es.get(self.1) {
          None => return None,
          Some(e) => {self.1 += 1; return Some(e.clone())}
        },
        LispKind::DottedList(es, r) => match es.get(self.1) {
          None => *self = Self::from(r.clone()),
          Some(e) => {self.1 += 1; return Some(e.clone())}
        }
        _ => return None
      }
    }
  }
}

#[derive(Default)]
pub struct LispRemapper {
  pub atom: AtomVec<AtomID>,
  pub lisp: HashMap<*const LispKind, LispVal>,
}
impl Remap<LispRemapper> for AtomID {
  fn remap(&self, r: &mut LispRemapper) -> Self { *r.atom.get(*self).unwrap_or(self) }
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
      LispKind::Annot(sp, m) => Arc::new(LispKind::Annot(sp.clone(), m.remap(r))),
      LispKind::Proc(f) => Arc::new(LispKind::Proc(f.remap(r))),
      LispKind::AtomMap(m) => Arc::new(LispKind::AtomMap(m.remap(r))),
      LispKind::Ref(m) => Arc::new(LispKind::Ref(m.remap(r))),
      &LispKind::MVar(n, is) => Arc::new(LispKind::MVar(n, is.remap(r))),
      LispKind::Number(_) |
      LispKind::String(_) |
      LispKind::UnparsedFormula(_) |
      LispKind::Bool(_) |
      LispKind::Syntax(_) |
      LispKind::Undef |
      LispKind::Goal(_) => self.clone(),
    };
    r.lisp.entry(p).or_insert(v).clone()
  }
}

impl Remap<LispRemapper> for InferTarget {
  fn remap(&self, r: &mut LispRemapper) -> Self {
    match self {
      InferTarget::Unknown => InferTarget::Unknown,
      InferTarget::Provable => InferTarget::Provable,
      InferTarget::Bound(a) => InferTarget::Bound(a.remap(r)),
      InferTarget::Reg(a) => InferTarget::Reg(a.remap(r)),
    }
  }
}
impl Remap<LispRemapper> for ProcPos {
  fn remap(&self, r: &mut LispRemapper) -> Self {
    match self {
      ProcPos::Named(sp, a) => ProcPos::Named(sp.clone(), a.remap(r)),
      ProcPos::Unnamed(sp) => ProcPos::Unnamed(sp.clone()),
    }
  }
}
impl Remap<LispRemapper> for Proc {
  fn remap(&self, r: &mut LispRemapper) -> Self {
    match self {
      &Proc::Builtin(p) => Proc::Builtin(p),
      &Proc::Lambda {ref pos, ref env, spec, ref code} =>
        Proc::Lambda {pos: pos.remap(r), env: env.remap(r), spec, code: code.remap(r)},
      Proc::MatchCont(_) => Proc::MatchCont(Arc::new(AtomicBool::new(false))),
    }
  }
}
