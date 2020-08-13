//! Implementation of the Scheme-like metaprogramming language of MM1.
//!
//! See [`mm1.md`] for a description of the MM1 metaprogramming language.
//!
//! [`mm1.md`]: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#evaluation

pub mod parser;
pub mod eval;
pub mod print;
pub mod pretty;

use std::ops::{Deref, DerefMut};
use std::hash::Hash;
use std::sync::{Arc, Mutex, RwLock, atomic::AtomicBool};
use std::collections::{HashMap, hash_map::Entry};
use num::BigInt;
use owning_ref::{OwningRef, StableAddress, CloneStableAddress};
use crate::parser::ast::{Atom};
use crate::util::{ArcString, FileSpan, Span};
use super::{AtomID, ThmID, AtomVec, Remap, Modifiers};
use parser::IR;
pub use super::math_parser::{QExpr, QExprKind};

macro_rules! str_enum {
  (enum $name:ident {$($e:ident: $s:expr,)*}) => {
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
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
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

impl InferTarget {
  pub fn sort(self) -> Option<AtomID> {
    match self {
      InferTarget::Bound(s) | InferTarget::Reg(s) => Some(s),
      _ => None
    }
  }
  pub fn bound(self) -> bool {
    match self {
      InferTarget::Bound(_) => true,
      _ => false
    }
  }
}

#[derive(Default, Debug, Clone)]
pub struct LispVal(Arc<LispKind>);

#[derive(Debug)]
pub enum LispKind {
  Atom(AtomID),
  List(Vec<LispVal>),
  DottedList(Vec<LispVal>, LispVal),
  Annot(Annot, LispVal),
  Number(BigInt),
  String(ArcString),
  Bool(bool),
  Syntax(Syntax),
  Undef,
  Proc(Proc),
  AtomMap(HashMap<AtomID, LispVal>),
  Ref(LispRef),
  MVar(usize, InferTarget),
  Goal(LispVal),
}

#[derive(Debug)]
pub struct LispRef(RwLock<LispVal>);

impl LispVal {
  pub fn new(e: LispKind) -> LispVal { LispVal(Arc::new(e)) }
  pub fn atom(a: AtomID) -> LispVal { LispVal::new(LispKind::Atom(a)) }
  pub fn list(es: Vec<LispVal>) -> LispVal { LispVal::new(LispKind::List(es)) }
  pub fn dotted_list(es: Vec<LispVal>, r: LispVal) -> LispVal { LispVal::new(LispKind::DottedList(es, r)) }
  pub fn number(n: BigInt) -> LispVal { LispVal::new(LispKind::Number(n)) }
  pub fn string(s: ArcString) -> LispVal { LispVal::new(LispKind::String(s)) }
  pub fn syntax(s: Syntax) -> LispVal { LispVal::new(LispKind::Syntax(s)) }
  pub fn undef() -> LispVal { LispVal::new(LispKind::Undef) }
  pub fn nil() -> LispVal { LispVal::list(vec![]) }
  pub fn bool(b: bool) -> LispVal { LispVal::new(LispKind::Bool(b)) }
  pub fn proc(p: Proc) -> LispVal { LispVal::new(LispKind::Proc(p)) }
  pub fn new_ref(e: LispVal) -> LispVal { LispVal::new(LispKind::Ref(LispRef::new(e))) }
  pub fn goal(fsp: FileSpan, ty: LispVal) -> LispVal {
    LispVal::new(LispKind::Goal(ty)).span(fsp)
  }

  pub fn span(self, fsp: FileSpan) -> LispVal {
    LispVal::new(LispKind::Annot(Annot::Span(fsp), self))
  }

  pub fn replace_span(&self, fsp: FileSpan) -> LispVal {
    match &**self {
      LispKind::Annot(_, v) => v.replace_span(fsp),
      _ => self.clone().span(fsp)
    }
  }

  pub fn unwrapped_mut<T>(&mut self, f: impl FnOnce(&mut LispKind) -> T) -> Option<T> {
    Arc::get_mut(&mut self.0).and_then(|e| match e {
      LispKind::Ref(m) => Self::unwrapped_mut(&mut m.get_mut(), f),
      LispKind::Annot(_, v) => Self::unwrapped_mut(v, f),
      _ => Some(f(e))
    })
  }

  pub fn unwrapped_arc(&self) -> LispVal {
    match &**self {
      LispKind::Ref(m) => Self::unwrapped_arc(&m.get()),
      LispKind::Annot(_, v) => Self::unwrapped_arc(v),
      _ => self.clone()
    }
  }

  pub fn ptr_eq(&self, e: &Self) -> bool { Arc::ptr_eq(&self.0, &e.0) }
  pub fn try_unwrap(self) -> Result<LispKind, LispVal> { Arc::try_unwrap(self.0).map_err(LispVal) }
  pub fn get_mut(&mut self) -> Option<&mut LispKind> { Arc::get_mut(&mut self.0) }

  pub fn try_unwrapped(self) -> Result<LispKind, LispVal> {
    match Arc::try_unwrap(self.0) {
      Ok(LispKind::Annot(_, e)) => e.try_unwrapped(),
      Ok(LispKind::Ref(m)) => m.into_inner().try_unwrapped(),
      Ok(e) => Ok(e),
      Err(e) => Err(LispVal(e))
    }
  }

  pub fn extend_into(mut self, mut n: usize, vec: &mut Vec<LispVal>) -> bool {
    loop {
      match &*self {
        LispKind::Ref(m) => {let e = m.unref(); self = e}
        LispKind::Annot(_, v) => self = v.clone(),
        LispKind::List(es) | LispKind::DottedList(es, _) if n <= es.len() => {
          vec.extend_from_slice(&es[..n]);
          return true
        },
        LispKind::List(es) => {vec.extend_from_slice(&es); return false},
        LispKind::DottedList(es, r) => {
          vec.extend_from_slice(&es);
          n -= es.len();
          self = r.clone()
        }
        _ => return false
      }
    }
  }
}

impl Deref for LispVal {
  type Target = LispKind;
  fn deref(&self) -> &LispKind { &self.0 }
}
unsafe impl StableAddress for LispVal {}
unsafe impl CloneStableAddress for LispVal {}

impl PartialEq<LispVal> for LispVal {
  fn eq(&self, other: &LispVal) -> bool {
    self.ptr_eq(other) || **self == **other
  }
}
impl Eq for LispVal {}

impl LispRef {
  pub fn new(e: LispVal) -> LispRef { LispRef(RwLock::new(e)) }
  pub fn get<'a>(&'a self) -> impl Deref<Target=LispVal> + 'a { self.0.read().unwrap() }
  pub fn get_mut<'a>(&'a self) -> impl DerefMut<Target=LispVal> + 'a { self.0.write().unwrap() }
  pub fn unref(&self) -> LispVal { self.get().clone() }
  pub fn into_inner(self) -> LispVal { self.0.into_inner().unwrap() }
}

impl PartialEq<LispRef> for LispRef {
  fn eq(&self, other: &LispRef) -> bool { *self.get() == *other.get() }
}
impl Eq for LispRef {}

impl From<&LispKind> for bool {
  fn from(e: &LispKind) -> bool { e.truthy() }
}

impl LispKind {
  pub fn unwrapped<T>(&self, f: impl FnOnce(&Self) -> T) -> T {
    match self {
      LispKind::Ref(m) => m.get().unwrapped(f),
      LispKind::Annot(_, v) => v.unwrapped(f),
      _ => f(self)
    }
  }

  pub fn unwrapped_span<T>(&self, fsp: Option<&FileSpan>,
      f: impl FnOnce(Option<&FileSpan>, &Self) -> T) -> T {
    match self {
      LispKind::Ref(m) => m.get().unwrapped_span(fsp, f),
      LispKind::Annot(Annot::Span(fsp), v) => v.unwrapped_span(Some(fsp), f),
      _ => f(fsp, self)
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
  pub fn is_int(&self) -> bool {
    self.unwrapped(|e| if let LispKind::Number(_) = e {true} else {false})
  }
  pub fn as_int<T>(&self, f: impl FnOnce(&BigInt) -> T) -> Option<T> {
    self.unwrapped(|e| if let LispKind::Number(n) = e {Some(f(n))} else {None})
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
  pub fn as_ref_<T>(&self, f: impl FnOnce(&mut LispVal) -> T) -> Option<T> {
    match self {
      LispKind::Ref(m) => Some(f(&mut m.get_mut())),
      LispKind::Annot(_, e) => e.as_ref_(f),
      _ => None
    }
  }
  pub fn fspan(&self) -> Option<FileSpan> {
    match self {
      LispKind::Ref(m) => m.get().fspan(),
      LispKind::Annot(Annot::Span(sp), _) => Some(sp.clone()),
      // LispKind::Annot(_, e) => e.fspan(),
      _ => None
    }
  }
  pub fn is_mvar(&self) -> bool {
    self.unwrapped(|e| if let LispKind::MVar(_, _) = e {true} else {false})
  }
  pub fn mvar_target(&self) -> Option<InferTarget> {
    self.unwrapped(|e| if let &LispKind::MVar(_, is) = e {Some(is)} else {None})
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
      LispKind::DottedList(es, _) if n < es.len() => false,
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

  pub fn list_at_least(&self, n: usize) -> bool {
    self.unwrapped(|e| match e {
      LispKind::List(es) => return n <= es.len(),
      LispKind::DottedList(es, r) if n <= es.len() => r.is_list(),
      LispKind::DottedList(es, r) => r.list_at_least(n - es.len()),
      _ => false,
    })
  }
  pub fn at_least(&self, n: usize) -> bool {
    self.unwrapped(|e| match e {
      LispKind::List(es) => return n <= es.len(),
      LispKind::DottedList(es, _) if n <= es.len() => true,
      LispKind::DottedList(es, r) => r.at_least(n - es.len()),
      _ => n == 0,
    })
  }

  pub fn decorate_span(self, fsp: &Option<FileSpan>) -> LispVal {
    if let Some(fsp) = fsp {
      LispVal::new(self).span(fsp.clone())
    } else {LispVal::new(self)}
  }

  fn eq_list<'a>(&self, mut it: impl Iterator<Item=&'a LispVal>) -> bool {
    self.unwrapped(|e| match e {
      LispKind::List(b) => it.eq(b.iter()),
      LispKind::DottedList(b, c) =>
        b.iter().all(|e| it.next() == Some(e)) && c.eq_list(it),
      _ => false
    })
  }
}

impl Default for LispKind {
  fn default() -> Self { Self::Undef }
}

impl PartialEq<LispKind> for LispKind {
  fn eq(&self, other: &LispKind) -> bool {
    self.unwrapped(|s| other.unwrapped(|o| match (s, o) {
      (&LispKind::Atom(a), &LispKind::Atom(b)) => a == b,
      (LispKind::Number(a), LispKind::Number(b)) => a == b,
      (LispKind::String(a), LispKind::String(b)) => a == b,
      (LispKind::Bool(a), LispKind::Bool(b)) => a == b,
      (LispKind::Syntax(a), LispKind::Syntax(b)) => a == b,
      (LispKind::Undef, LispKind::Undef) => true,
      (LispKind::List(a), LispKind::List(b)) => a == b,
      (LispKind::List(a), _) => other.eq_list(a.iter()),
      (_, LispKind::List(b)) => self.eq_list(b.iter()),
      (LispKind::DottedList(a, b), LispKind::DottedList(c, d)) => {
        let mut it1 = a.iter();
        let mut it2 = c.iter();
        loop {
          match (it1.next(), it2.next()) {
            (None, None) => break b == d,
            (Some(e1), Some(e2)) => if e1 != e2 {break false},
            (Some(e), None) =>
              break d.eq_list(Some(e).into_iter().chain(it1)),
            (None, Some(e)) =>
              break b.eq_list(Some(e).into_iter().chain(it2)),
          }
        }
      }
      _ => false // Goal, Proc, MVar, AtomMap all have only reference equality
    }))
  }
}
impl Eq for LispKind {}

#[derive(Clone, Debug)]
pub enum Annot {
  Span(FileSpan),
}

#[derive(Clone, Debug)]
pub enum ProcPos {
  Named(FileSpan, Span, AtomID),
  Unnamed(FileSpan),
}
impl ProcPos {
  fn fspan(&self) -> &FileSpan {
    match self {
      ProcPos::Named(fsp, _, _) => fsp,
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
  RefineCallback,
  ProofThunk(AtomID, Mutex<Result<LispVal, Vec<LispVal>>>),
  MMCCompiler(Mutex<crate::mmc::Compiler>) // TODO: use extern instead
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
      Proc::RefineCallback => ProcSpec::AtLeast(1),
      Proc::ProofThunk(_, _) => ProcSpec::AtLeast(0),
      Proc::MMCCompiler(_) => ProcSpec::AtLeast(1),
    }
  }
}

str_enum! {
  enum BuiltinProc {
    Display: "display",
    Error: "error",
    Print: "print",
    ReportAt: "report-at",
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
    Equal: "==",
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
    Nth: "nth",
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
    CopySpan: "copy-span",
    StackSpan: "stack-span",
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
    SetCloseFn: "set-close-fn",
    LocalCtx: "local-ctx",
    ToExpr: "to-expr",
    Refine: "refine",
    Have: "have",
    Stat: "stat",
    GetDecl: "get-decl",
    AddDecl: "add-decl!",
    AddTerm: "add-term!",
    AddThm: "add-thm!",
    NewDummy: "dummy!",
    CheckProofs: "check-proofs",
    SetReporting: "set-reporting",
    RefineExtraArgs: "refine-extra-args",
    MMCInit: "mmc-init",
  }
}

impl std::fmt::Display for BuiltinProc {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.to_str().fmt(f)
  }
}

#[derive(Clone, Debug)]
pub enum Uncons {
  New(LispVal),
  List(OwningRef<LispVal, [LispVal]>),
  DottedList(OwningRef<LispVal, [LispVal]>, LispVal),
}

impl Uncons {
  pub fn from(e: LispVal) -> Uncons { Uncons::New(e) }
  pub fn exactly(&self, n: usize) -> bool {
    match self {
      Uncons::New(e) => e.exactly(n),
      Uncons::List(es) => es.len() == n,
      Uncons::DottedList(es, r) => n.checked_sub(es.len()).map_or(false, |i| r.exactly(i)),
    }
  }
  pub fn at_least(&self, n: usize) -> bool {
    n == 0 || match self {
      Uncons::New(e) => e.at_least(n),
      Uncons::List(es) => es.len() >= n,
      Uncons::DottedList(es, r) => n.checked_sub(es.len()).map_or(true, |i| r.at_least(i)),
    }
  }
  pub fn list_at_least(&self, n: usize) -> bool {
    n == 0 || match self {
      Uncons::New(e) => e.list_at_least(n),
      Uncons::List(es) => es.len() >= n,
      Uncons::DottedList(es, r) => n.checked_sub(es.len()).map_or(true, |i| r.list_at_least(i)),
    }
  }

  pub fn as_lisp(self) -> LispVal {
    match self {
      Uncons::New(e) => e,
      Uncons::List(es) if es.is_empty() => LispVal::nil(),
      Uncons::List(es) => LispVal::list((*es).into()),
      Uncons::DottedList(es, r) if es.is_empty() => r,
      Uncons::DottedList(es, r) => LispVal::dotted_list((*es).into(), r),
    }
  }

  pub fn len(&self) -> usize {
    match self {
      Uncons::New(e) => e.len(),
      Uncons::List(es) => es.len(),
      Uncons::DottedList(es, r) => es.len() + r.len(),
    }
  }

  pub fn extend_into(&self, n: usize, vec: &mut Vec<LispVal>) -> bool {
    match self {
      Uncons::New(e) => e.clone().extend_into(n, vec),
      Uncons::List(es) | Uncons::DottedList(es, _) if n <= es.len() =>
        {vec.extend_from_slice(&es[..n]); true}
      Uncons::List(es) => {vec.extend_from_slice(&es); false}
      Uncons::DottedList(es, r) => {
        vec.extend_from_slice(&es);
        r.clone().extend_into(n - es.len(), vec)
      }
    }
  }
}

impl Iterator for Uncons {
  type Item = LispVal;
  fn next(&mut self) -> Option<LispVal> {
    'l: loop {
      match self {
        Uncons::New(e) => loop {
          match &**e {
            LispKind::Ref(m) => {let e2 = m.unref(); *e = e2}
            LispKind::Annot(_, v) => *e = v.clone(),
            LispKind::List(_) => {
              *self = Uncons::List(OwningRef::from(e.clone()).map(|e| {
                if let LispKind::List(es) = e {&**es}
                else {unsafe {std::hint::unreachable_unchecked()}}
              }));
              continue 'l
            }
            LispKind::DottedList(_, r) => {
              *self = Uncons::DottedList(OwningRef::from(e.clone()).map(|e| {
                if let LispKind::DottedList(es, _) = e {&**es}
                else {unsafe {std::hint::unreachable_unchecked()}}
              }), r.clone());
              continue 'l
            }
            _ => return None
          }
        },
        Uncons::List(es) if es.is_empty() => return None,
        Uncons::List(es) => return (Some(es[0].clone()), *es = es.clone().map(|es| &es[1..])).0,
        Uncons::DottedList(es, r) if es.is_empty() => *self = Uncons::New(r.clone()),
        Uncons::DottedList(es, _) => return (Some(es[0].clone()), *es = es.clone().map(|es| &es[1..])).0,
      }
    }
  }
}

#[derive(Default, Debug)]
pub struct LispRemapper {
  pub atom: AtomVec<AtomID>,
  pub lisp: HashMap<*const LispKind, (LispVal, LispVal)>,
  pub refs: HashMap<*const LispKind, LispVal>,
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
    if let Some(v) = r.lisp.get(&p) {return v.1.clone()}
    let v = match self.deref() {
      LispKind::Atom(a) => LispVal::atom(a.remap(r)),
      LispKind::List(v) => LispVal::list(v.remap(r)),
      LispKind::DottedList(v, l) => LispVal::dotted_list(v.remap(r), l.remap(r)),
      LispKind::Annot(sp, m) => LispVal::new(LispKind::Annot(sp.clone(), m.remap(r))),
      LispKind::Proc(f) => LispVal::proc(f.remap(r)),
      LispKind::AtomMap(m) => LispVal::new(LispKind::AtomMap(m.remap(r))),
      LispKind::Ref(m) => match r.refs.entry(p) {
        Entry::Occupied(e) => e.get().clone(),
        Entry::Vacant(e) => {
          let w = LispVal::new(LispKind::Ref(LispRef::new(LispVal::undef())));
          e.insert(w.clone());
          w.as_ref_(|v| *v = m.get().remap(r)).unwrap();
          r.refs.remove(&p);
          w
        }
      },
      &LispKind::MVar(n, is) => LispVal::new(LispKind::MVar(n, is.remap(r))),
      LispKind::Goal(e) => LispVal::new(LispKind::Goal(e.remap(r))),
      LispKind::Number(_) |
      LispKind::String(_) |
      LispKind::Bool(_) |
      LispKind::Syntax(_) |
      LispKind::Undef => self.clone(),
    };
    r.lisp.entry(p).or_insert_with(|| (self.clone(), v)).1.clone()
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
      ProcPos::Named(fsp, sp, a) => ProcPos::Named(fsp.clone(), *sp, a.remap(r)),
      ProcPos::Unnamed(fsp) => ProcPos::Unnamed(fsp.clone()),
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
      Proc::RefineCallback => Proc::RefineCallback,
      Proc::ProofThunk(x, m) => Proc::ProofThunk(x.remap(r), Mutex::new(
        match &*m.lock().unwrap() {
          Ok(e) => Ok(e.remap(r)),
          Err(v) => Err(v.remap(r)),
        }
      )),
      Proc::MMCCompiler(c) => Proc::MMCCompiler(c.remap(r)),
    }
  }
}
