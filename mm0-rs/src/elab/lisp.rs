pub mod parser;
pub mod eval;
pub mod print;

use std::ops::Deref;
use std::borrow::Cow;
use std::hash::Hash;
use std::sync::{Arc, Mutex, atomic::AtomicBool};
use std::collections::HashMap;
use num::BigInt;
use crate::parser::ast::{Atom};
use crate::util::{ArcString, FileSpan};
use super::{AtomID, AtomVec, Remap};
use parser::IR;

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

pub type LispVal = Arc<LispKind>;
#[derive(Debug)]
pub enum LispKind {
  Atom(AtomID),
  List(Vec<LispVal>),
  DottedList(Vec<LispVal>, LispVal),
  Span(FileSpan, LispVal),
  Number(BigInt),
  String(ArcString),
  UnparsedFormula(ArcString),
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
  pub static ref TRUE: LispVal = Arc::new(LispKind::Bool(true));
  pub static ref FALSE: LispVal = Arc::new(LispKind::Bool(false));
  pub static ref NIL: LispVal = Arc::new(LispKind::List(vec![]));
}

pub fn unwrap(e: &LispVal) -> Cow<LispVal> {
  let mut ret = Cow::Borrowed(e);
  loop {
    match &**ret {
      LispKind::Ref(m) => {
        let e = m.lock().unwrap().clone();
        ret = Cow::Owned(e)
      }
      LispKind::Span(_, v) => ret = Cow::Owned(v.clone()),
      _ => return ret
    }
  }
}

impl From<&LispKind> for bool {
  fn from(e: &LispKind) -> bool { e.truthy() }
}
impl LispKind {
  fn truthy(&self) -> bool {
    match self {
      LispKind::Bool(false) => false,
      LispKind::Span(_, v) => v.truthy(),
      LispKind::Ref(m) => m.lock().unwrap().truthy(),
      _ => true
    }
  }
  pub fn is_bool(&self) -> bool {
    if let LispKind::Bool(_) = self {true} else {false}
  }
  pub fn is_atom(&self) -> bool {
    if let LispKind::Atom(_) = self {true} else {false}
  }
  pub fn is_pair(&self) -> bool {
    match self {
      LispKind::List(es) => !es.is_empty(),
      LispKind::DottedList(es, r) => !es.is_empty() || r.is_pair(),
      _ => false,
    }
  }
  pub fn is_null(&self) -> bool {
    if let LispKind::List(es) = self {es.is_empty()} else {false}
  }
  pub fn is_int(&self) -> bool {
    if let LispKind::Number(_) = self {true} else {false}
  }
  pub fn is_proc(&self) -> bool {
    if let LispKind::Proc(_) = self {true} else {false}
  }
  pub fn is_string(&self) -> bool {
    if let LispKind::String(_) = self {true} else {false}
  }
  pub fn is_map(&self) -> bool {
    if let LispKind::AtomMap(_) = self {true} else {false}
  }
  pub fn is_def(&self) -> bool {
    if let LispKind::Undef = self {false} else {true}
  }
  pub fn is_ref(&self) -> bool {
    if let LispKind::Ref(_) = self {true} else {false}
  }

  pub fn fspan(&self) -> Option<FileSpan> {
    match self {
      LispKind::Ref(m) => m.lock().unwrap().fspan(),
      LispKind::Span(sp, _) => Some(sp.clone()),
      _ => None
    }
  }

}

#[derive(Clone, Debug)]
pub enum ProcPos {
  Named(FileSpan, AtomID),
  Unnamed(FileSpan),
}
impl ProcPos {
  fn into_fspan(self) -> FileSpan {
    match self {
      ProcPos::Named(fsp, _) => fsp,
      ProcPos::Unnamed(fsp) => fsp,
    }
  }
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
    SetMVar: "mvar!",
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
      LispKind::Proc(f) => Arc::new(LispKind::Proc(f.remap(r))),
      LispKind::AtomMap(m) => Arc::new(LispKind::AtomMap(m.remap(r))),
      LispKind::Ref(m) => Arc::new(LispKind::Ref(m.remap(r))),
      _ => self.clone(),
    };
    r.lisp.entry(p).or_insert(v).clone()
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
