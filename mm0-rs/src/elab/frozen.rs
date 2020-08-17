use std::mem;
use std::cell::RefCell;
use std::ops::Deref;
use std::sync::{Arc, atomic::AtomicBool};
use std::collections::{HashMap, hash_map::Entry};
use num::BigInt;
use super::{Spans, ObjectKind, Remap,
  environment::{Environment, ParserEnv,
    AtomVec, TermVec, ThmVec, SortVec, DeclKey, StmtTrace,
    SortID, TermID, ThmID, AtomID, Sort, Term, Thm, AtomData},
  lisp::{LispVal, LispKind, LispRef, LispRemapper,
    InferTarget, Proc, Annot, Syntax, print::FormatEnv}};
use crate::util::{ArcString, FileSpan, Span};
use crate::{lined_string::LinedString, __mk_lisp_kind};

#[derive(Clone, Debug)]
pub struct FrozenEnv(Arc<Environment>);
unsafe impl Send for FrozenEnv {}
unsafe impl Sync for FrozenEnv {}

impl FrozenEnv {
  pub fn new(env: Environment) -> Self { Self(Arc::new(env)) }
  pub unsafe fn thaw(&self) -> &Environment { &self.0 }

  pub fn format_env<'a>(&'a self, source: &'a LinedString) -> FormatEnv<'a> {
    FormatEnv {source, env: unsafe {self.thaw()}}
  }

  pub fn find(&self, pos: usize) -> Option<&Spans<ObjectKind>> {
    unsafe { self.thaw() }.find(pos)
  }

  pub fn data(&self) -> &AtomVec<FrozenAtomData> {
    unsafe { mem::transmute::<&AtomVec<AtomData>, &AtomVec<FrozenAtomData>>(&self.thaw().data) }
  }

  pub fn sorts(&self) -> &SortVec<Sort> { &unsafe { self.thaw() }.sorts }
  pub fn sort(&self, s: SortID) -> &Sort { &self.sorts()[s] }
  pub fn terms(&self) -> &TermVec<Term> { &unsafe { self.thaw() }.terms }
  pub fn term(&self, t: TermID) -> &Term { &self.terms()[t] }
  pub fn thms(&self) -> &ThmVec<Thm> { &unsafe { self.thaw() }.thms }
  pub fn thm(&self, t: ThmID) -> &Thm { &self.thms()[t] }
  pub fn stmts(&self) -> &[StmtTrace] { &unsafe { self.thaw() }.stmts }
  pub fn get_atom(&self, s: &str) -> Option<AtomID> { unsafe { self.thaw() }.atoms.get(s).copied() }
  pub fn pe(&self) -> &ParserEnv { &unsafe { self.thaw() }.pe }
}

#[derive(Debug)]
pub struct FrozenAtomData(AtomData);

impl FrozenAtomData {
  pub fn name(&self) -> &ArcString { &self.0.name }
  pub fn sort(&self) -> Option<SortID> { self.0.sort }
  pub fn decl(&self) -> Option<DeclKey> { self.0.decl }
  pub fn lisp(&self) -> &Option<(Option<(FileSpan, Span)>, FrozenLispVal)> {
    unsafe { mem::transmute::<&Option<(Option<(FileSpan, Span)>, LispVal)>, _>(&self.0.lisp) }
  }
  pub fn graveyard(&self) -> &Option<Box<(FileSpan, Span)>> { &self.0.graveyard }
}

#[derive(Debug)]
pub struct FrozenLispVal(LispVal);

#[derive(Debug)]
pub struct FrozenLispRef(LispRef);

#[derive(Debug)]
pub struct FrozenProc(Proc);

__mk_lisp_kind! {FrozenLispKind, FrozenLispVal, FrozenLispRef, FrozenProc}

impl LispKind {
  pub fn freeze(&self) -> &FrozenLispKind { unsafe { mem::transmute(self) } }
}

impl LispVal {
  pub fn freeze(&self) -> &FrozenLispVal { unsafe { mem::transmute(self) } }
}

impl LispRef {
  pub fn freeze(&self) -> &FrozenLispRef { unsafe { mem::transmute(self) } }
}

impl Proc {
  pub fn freeze(&self) -> &FrozenProc { unsafe { mem::transmute(self) } }
}

impl FrozenLispVal {
  pub unsafe fn new(e: LispVal) -> Self { Self(e) }
  pub unsafe fn thaw(&self) -> &LispVal { &self.0 }

  pub fn uncons(&self) -> FrozenUncons<'_> { FrozenUncons::New(self) }

  pub fn unwrap(&self) -> &Self {
    match &**self {
      FrozenLispKind::Ref(m) => m.unwrap(),
      FrozenLispKind::Annot(_, v) => v.unwrap(),
      _ => self
    }
  }
}

impl FrozenLispKind {
  pub fn unwrap(&self) -> &Self {
    match self {
      FrozenLispKind::Ref(m) => m.unwrap(),
      FrozenLispKind::Annot(_, v) => v.unwrap(),
      _ => self
    }
  }

  pub fn as_atom(&self) -> Option<AtomID> {
    if let &FrozenLispKind::Atom(a) = self.unwrap() {Some(a)} else {None}
  }

  pub fn is_list(&self) -> bool {
    match self.unwrap() {
      FrozenLispKind::List(_) => true,
      FrozenLispKind::DottedList(_, r) => r.is_list(),
      _ => false,
    }
  }

  pub fn fspan(&self) -> Option<FileSpan> {
    match self.unwrap() {
      FrozenLispKind::Ref(m) => m.fspan(),
      FrozenLispKind::Annot(Annot::Span(sp), _) => Some(sp.clone()),
      _ => None
    }
  }
}

impl Deref for FrozenLispVal {
  type Target = FrozenLispKind;
  fn deref(&self) -> &FrozenLispKind { unsafe {self.thaw()}.deref().freeze() }
}

impl Remap<LispRemapper> for FrozenLispVal {
  type Target = LispVal;
  fn remap(&self, r: &mut LispRemapper) -> LispVal {
    let p: *const FrozenLispKind = self.deref();
    if let Some(v) = r.lisp.get(&p) {return v.clone()}
    let v = match self.deref() {
      FrozenLispKind::Atom(a) => LispVal::atom(a.remap(r)),
      FrozenLispKind::List(v) => LispVal::list(v.remap(r)),
      FrozenLispKind::DottedList(v, l) => LispVal::dotted_list(v.remap(r), l.remap(r)),
      FrozenLispKind::Annot(sp, m) => LispVal::new(LispKind::Annot(sp.clone(), m.remap(r))),
      FrozenLispKind::Proc(f) => LispVal::proc(f.remap(r)),
      FrozenLispKind::AtomMap(m) => LispVal::new(LispKind::AtomMap(m.remap(r))),
      FrozenLispKind::Ref(m) => match r.refs.entry(p) {
        Entry::Occupied(e) => e.get().clone(),
        Entry::Vacant(e) => {
          let w = LispVal::new(LispKind::Ref(LispRef::new(LispVal::undef())));
          e.insert(w.clone());
          w.as_ref_(|v| *v = m.remap(r)).unwrap();
          r.refs.remove(&p);
          w
        }
      },
      &FrozenLispKind::MVar(n, is) => LispVal::new(LispKind::MVar(n, is.remap(r))),
      FrozenLispKind::Goal(e) => LispVal::new(LispKind::Goal(e.remap(r))),
      FrozenLispKind::Number(n) => LispVal::number(n.clone()),
      FrozenLispKind::String(s) => LispVal::string(s.clone()),
      &FrozenLispKind::Bool(b) => LispVal::bool(b),
      &FrozenLispKind::Syntax(s) => LispVal::syntax(s),
      FrozenLispKind::Undef => LispVal::undef(),
    };
    r.lisp.entry(p).or_insert(v).clone()
  }
}

impl Remap<LispRemapper> for FrozenProc {
  type Target = Proc;
  fn remap(&self, r: &mut LispRemapper) -> Proc {
    match &self.0 {
      &Proc::Builtin(p) => Proc::Builtin(p),
      &Proc::Lambda {ref pos, ref env, spec, ref code} =>
        Proc::Lambda {pos: pos.remap(r), env: env.remap(r), spec, code: code.remap(r)},
      Proc::MatchCont(_) => Proc::MatchCont(Arc::new(AtomicBool::new(false))),
      Proc::RefineCallback => Proc::RefineCallback,
      Proc::ProofThunk(x, m) => Proc::ProofThunk(x.remap(r), RefCell::new(
        match &*unsafe { m.try_borrow_unguarded() }.unwrap() {
          Ok(e) => Ok(e.remap(r)),
          Err(v) => Err(v.remap(r)),
        }
      )),
      Proc::MMCCompiler(c) => Proc::MMCCompiler(c.remap(r)),
    }
  }
}

impl FrozenLispRef {
  pub unsafe fn thaw(&self) -> &LispRef { &self.0 }
}

impl Deref for FrozenLispRef {
  type Target = FrozenLispVal;
  fn deref(&self) -> &FrozenLispVal {
    unsafe { self.thaw().get_unsafe() }.freeze()
  }
}

#[derive(Copy, Clone, Debug)]
pub enum FrozenUncons<'a> {
  New(&'a FrozenLispVal),
  List(&'a [FrozenLispVal]),
  DottedList(&'a [FrozenLispVal], &'a FrozenLispVal),
}

impl<'a> Iterator for FrozenUncons<'a> {
  type Item = &'a FrozenLispVal;
  fn next(&mut self) -> Option<&'a FrozenLispVal> {
    'l: loop {
      match self {
        FrozenUncons::New(e) => loop {
          match &***e {
            FrozenLispKind::Ref(m) => *e = m,
            FrozenLispKind::Annot(_, v) => *e = v,
            FrozenLispKind::List(es) => {
              *self = FrozenUncons::List(es);
              continue 'l
            }
            FrozenLispKind::DottedList(es, r) => {
              *self = FrozenUncons::DottedList(es, r);
              continue 'l
            }
            _ => return None
          }
        },
        FrozenUncons::List(es) if es.is_empty() => return None,
        FrozenUncons::List(es) => return (Some(&es[0]), *es = &es[1..]).0,
        FrozenUncons::DottedList(es, r) if es.is_empty() => *self = FrozenUncons::New(r),
        FrozenUncons::DottedList(es, _) => return (Some(&es[0]), *es = &es[1..]).0,
      }
    }
  }
}
