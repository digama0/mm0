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

#[derive(Copy, Clone, Debug)]
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
  pub fn to_str(self) -> &'static str {
    match self {
      Syntax::Define => "def",
      Syntax::Lambda => "fn",
      Syntax::Quote => "quote",
      Syntax::Unquote => "unquote",
      Syntax::If => "if",
      Syntax::Focus => "focus",
      Syntax::Let => "let",
      Syntax::Letrec => "letrec",
      Syntax::Match => "match",
      Syntax::MatchFn => "match-fn",
      Syntax::MatchFns => "match-fn*",
    }
  }
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

macro_rules! make_builtins {
  ($($e:ident: $s:expr, $ty:ident($n:expr);)*) => {
    #[derive(Copy, Clone, Debug)]
    pub enum BuiltinProc { $($e),* }
    impl BuiltinProc {
      pub fn from_str(s: &str) -> Option<BuiltinProc> {
        match s {
          $($s => Some(BuiltinProc::$e),)*
          _ => None
        }
      }
      pub fn to_str(self) -> &'static str {
        match self {
          $(BuiltinProc::$e => $s),*
        }
      }
      pub fn spec(self) -> ProcSpec {
        match self {
          $(BuiltinProc::$e => ProcSpec::$ty($n)),*
        }
      }
    }
  }
}

make_builtins! {
  Display: "display", Exact(1);
  Error: "error", Exact(1);
  Print: "print", Exact(1);
  Begin: "begin", AtLeast(0);
  Apply: "apply", AtLeast(2);
  Add: "+", AtLeast(0);
  Mul: "*", AtLeast(0);
  Max: "max", AtLeast(1);
  Min: "min", AtLeast(1);
  Sub: "-", AtLeast(1);
  Div: "//", AtLeast(1);
  Mod: "%", AtLeast(1);
  Lt: "<", AtLeast(1);
  Le: "<=", AtLeast(1);
  Gt: ">", AtLeast(1);
  Ge: ">=", AtLeast(1);
  Eq: "=", AtLeast(1);
  ToString: "->string", Exact(1);
  StringToAtom: "string->atom", Exact(1);
  StringAppend: "string-append", AtLeast(0);
  Not: "not", AtLeast(0);
  And: "and", AtLeast(0);
  Or: "or", AtLeast(0);
  List: "list", AtLeast(0);
  Cons: "cons", AtLeast(0);
  Head: "hd", Exact(1);
  Tail: "tl", Exact(1);
  Map: "map", AtLeast(1);
  IsBool: "bool?", Exact(1);
  IsAtom: "atom?", Exact(1);
  IsPair: "pair?", Exact(1);
  IsNull: "null?", Exact(1);
  IsNumber: "number?", Exact(1);
  IsString: "string?", Exact(1);
  IsProc: "fn?", Exact(1);
  IsDef: "def?", Exact(1);
  IsRef: "ref?", Exact(1);
  NewRef: "ref!", AtLeast(0);
  GetRef: "get!", Exact(1);
  SetRef: "set!", Exact(2);
  Async: "async", AtLeast(1);
  IsAtomMap: "atom-map?", Exact(1);
  NewAtomMap: "atom-map!", AtLeast(0);
  Lookup: "lookup", AtLeast(2);
  Insert: "insert!", AtLeast(2);
  InsertNew: "insert", AtLeast(2);
  SetTimeout: "set-timeout", Exact(1);
  IsMVar: "mvar?", Exact(1);
  IsGoal: "goal?", Exact(1);
  SetMVar: "mvar!", Exact(2);
  PrettyPrint: "pp", Exact(1);
  NewGoal: "goal", Exact(1);
  GoalType: "goal-type", Exact(1);
  InferType: "infer-type", Exact(1);
  GetMVars: "get-mvars", AtLeast(0);
  GetGoals: "get-goals", AtLeast(0);
  SetGoals: "set-goals", AtLeast(0);
  ToExpr: "to-expr", Exact(1);
  Refine: "refine", AtLeast(0);
  Have: "have", AtLeast(2);
  Stat: "stat", Exact(0);
  GetDecl: "get-decl", Exact(1);
  AddDecl: "add-decl!", AtLeast(4);
  AddTerm: "add-term!", AtLeast(3);
  AddThm: "add-thm!", AtLeast(4);
  SetReporting: "set-reporting", AtLeast(1);
  RefineExtraArgs: "refine-extra-args", AtLeast(2);
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
