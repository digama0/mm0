//! Operations for working on a frozen environment object.
//!
//! Because we use a thread unsafe data structure for lisp objects, it is important
//! that we separate processing into two phases. In the first phase, the file is
//! elaborated, lisp data structures are created and destroyed, and everything is
//! single-threaded. This is the "unfrozen" period. During this time, no other thread
//! can safely interact with the data without causing a data race.
//!
//! When elaboration completes, the elaborator is discarded and the environment is
//! frozen. During this second phase, the environment is completely read-only, including
//! in particular all internal mutability. Because [`LispVal`] is a wrapper around
//! `Rc`, it is not safe to clone a `LispVal` during this period, and instead the
//! [`FrozenLispVal`] type is used as a read only wrapper around `LispVal`.
//! At this point the data becomes safe to read from other threads, such as other files
//! that `import` this one and were waiting on elaboration to complete.
//!
//! There are two ways in which this strict time separation is violated. One is that
//! an elaborator may yield when it hits an `import` statement, while waiting for that
//! file to be ready, and it may restart on another thread since the executor is
//! multithreaded. To represent this we use the [`FrozenElaborator`] wrapper, which
//! represents a "paused" elaboration. This object is `Send` but cannot be cloned,
//! and it provides no access to the data under construction (and any access to the
//! inner data by a thread that does not own the elaborator is UB).
//!
//! The other way is for a lisp object to be temporarily frozen during elaboration using
//! the [`freeze`] method. This is also unsafe in general because the [`FrozenLispVal`]
//! methods do not touch reference counts and ignore writer locks around references.
//! This is safe as long as the object is not mutated (via another shared reference,
//! or a clone) during the lifetime of the object returned by `freeze`.
//!
//! [`LispVal`]: ../environment/struct.LispVal.html
//! [`FrozenLispVal`]: struct.FrozenLispVal.html

use std::cell::{Cell, RefCell};
use std::ops::Deref;
use std::sync::Arc;
use std::rc::Rc;
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

/// A "frozen" environment, which is a thread-safe read only
/// wrapper around `Environment`.
#[derive(Clone, Debug)]
pub struct FrozenEnv(Arc<Environment>);
unsafe impl Send for FrozenEnv {}
unsafe impl Sync for FrozenEnv {}

impl FrozenEnv {
  /// Create a new `FrozenEnv` from an Environment.
  pub fn new(env: Environment) -> Self { Self(Arc::new(env)) }

  /// Convert a `&FrozenEnv` into an `&Environment`.
  /// # Safety
  /// The reference derived here is only usable for reading, so in particular
  /// `Rc::clone()` should be avoided because it could race with other readers.
  pub unsafe fn thaw(&self) -> &Environment { &self.0 }

  /// Create a `FormatEnv` object, which can be used to print objects.
  /// # Safety
  /// TODO: this gives out an `&Environment`, even though it is frozen. Don't abuse it
  pub unsafe fn format_env<'a>(&'a self, source: &'a LinedString) -> FormatEnv<'a> {
    FormatEnv {source, env: self.thaw()}
  }

  /// Get the `Spans` object corrsponding to the statement that contains the given position,
  /// if one exists.
  pub fn find(&self, pos: usize) -> Option<&Spans<ObjectKind>> {
    unsafe { self.thaw() }.find(pos)
  }

  /// Accessor for [`Environment::data`](../environment/struct.Environment.html#structfield.data)
  pub fn data(&self) -> &AtomVec<FrozenAtomData> {
    unsafe { &*(&self.thaw().data as *const AtomVec<AtomData> as *const _) }
  }

  /// Accessor for [`Environment::sorts`](../environment/struct.Environment.html#structfield.sorts)
  pub fn sorts(&self) -> &SortVec<Sort> { &unsafe { self.thaw() }.sorts }
  /// Accessor for [`Environment::sorts`](../environment/struct.Environment.html#structfield.sorts)
  pub fn sort(&self, s: SortID) -> &Sort { &self.sorts()[s] }
  /// Accessor for [`Environment::terms`](../environment/struct.Environment.html#structfield.terms)
  pub fn terms(&self) -> &TermVec<Term> { &unsafe { self.thaw() }.terms }
  /// Accessor for [`Environment::terms`](../environment/struct.Environment.html#structfield.terms)
  pub fn term(&self, t: TermID) -> &Term { &self.terms()[t] }
  /// Accessor for [`Environment::thms`](../environment/struct.Environment.html#structfield.thms)
  pub fn thms(&self) -> &ThmVec<Thm> { &unsafe { self.thaw() }.thms }
  /// Accessor for [`Environment::thms`](../environment/struct.Environment.html#structfield.thms)
  pub fn thm(&self, t: ThmID) -> &Thm { &self.thms()[t] }
  /// Accessor for [`Environment::stmts`](../environment/struct.Environment.html#structfield.stmts)
  pub fn stmts(&self) -> &[StmtTrace] { &unsafe { self.thaw() }.stmts }
  /// Parse a string into an atom.
  pub fn get_atom(&self, s: &str) -> Option<AtomID> { unsafe { self.thaw() }.atoms.get(s).copied() }
  /// Accessor for [`Environment::pe`](../environment/struct.Environment.html#structfield.pe)
  pub fn pe(&self) -> &ParserEnv { &unsafe { self.thaw() }.pe }
}

/// A wrapper around an [`AtomData`](../environment/struct.AtomData.html) that is frozen.
#[derive(Debug)]
pub struct FrozenAtomData(AtomData);

impl FrozenAtomData {
  /// Accessor for [`AtomData::name`](../environment/struct.AtomData.html#structfield.name)
  pub fn name(&self) -> &ArcString { &self.0.name }
  /// Accessor for [`AtomData::sort`](../environment/struct.AtomData.html#structfield.sort)
  pub fn sort(&self) -> Option<SortID> { self.0.sort }
  /// Accessor for [`AtomData::decl`](../environment/struct.AtomData.html#structfield.decl)
  pub fn decl(&self) -> Option<DeclKey> { self.0.decl }
  /// Accessor for [`AtomData::lisp`](../environment/struct.AtomData.html#structfield.lisp)
  pub fn lisp(&self) -> &Option<(Option<(FileSpan, Span)>, FrozenLispVal)> {
    unsafe { &*(&self.0.lisp as *const Option<(_, LispVal)> as *const _) }
  }
  /// Accessor for [`AtomData::graveyard`](../environment/struct.AtomData.html#structfield.graveyard)
  pub fn graveyard(&self) -> &Option<Box<(FileSpan, Span)>> { &self.0.graveyard }
}

/// A wrapper around a [`LispVal`](../lisp/struct.LispVal.html) that is frozen.
#[derive(Debug)]
pub struct FrozenLispVal(pub LispVal);

/// A wrapper around a [`LispRef`](../lisp/struct.LispRef.html) that is frozen.
#[derive(Debug)]
pub struct FrozenLispRef(pub LispRef);

/// A wrapper around a [`Proc`](../lisp/struct.Proc.html) that is frozen.
#[derive(Debug)]
pub struct FrozenProc(pub Proc);

__mk_lisp_kind! {
  /// A wrapper around a [`LispKind`](../lisp/struct.LispKind.html) that is frozen.
  FrozenLispKind, FrozenLispVal, FrozenLispRef, FrozenProc
}

impl LispKind {
  /// Freeze a reference to a `LispKind` into a `FrozenLispKind`.
  /// # Safety
  /// The data structure should not be modified, even via clones, while this reference is alive.
  pub unsafe fn freeze(&self) -> &FrozenLispKind {
    &*(self as *const LispKind as *const _)
  }
}

impl LispVal {
  /// Freeze a reference to a `LispVal` into a `FrozenLispVal`.
  /// # Safety
  /// The data structure should not be modified, even via clones, while this reference is alive.
  pub unsafe fn freeze(&self) -> &FrozenLispVal {
    &*(self as *const LispVal as *const _)
  }
}

impl LispRef {
  /// Freeze a reference to a `LispRef` into a `FrozenLispRef`.
  /// # Safety
  /// The data structure should not be modified, even via clones, while this reference is alive.
  pub unsafe fn freeze(&self) -> &FrozenLispRef {
    &*(self as *const LispRef as *const _)
  }
}

impl Proc {
  /// Freeze a reference to a `Proc` into a `FrozenProc`.
  /// # Safety
  /// The data structure should not be modified, even via clones, while this reference is alive.
  pub unsafe fn freeze(&self) -> &FrozenProc {
    &*(self as *const Proc as *const _)
  }
}

impl FrozenLispVal {
  /// Freeze a `LispVal`, creating a new `FrozenLispVal`.
  /// # Safety
  /// The functions on the resulting `FrozenLispVal` should not be called
  /// until the value is frozen (meaning that all internal mutability stops).
  pub unsafe fn new(e: LispVal) -> Self { Self(e) }

  /// Convert a `&FrozenLispVal` into an `&LispVal`.
  /// # Safety
  /// The reference derived here is only usable for reading, so in particular
  /// `Rc::clone()` should be avoided because it could race with other readers.
  pub unsafe fn thaw(&self) -> &LispVal { &self.0 }

  /// Get a iterator over frozen lisp values, for dealing with lists.
  pub fn uncons(&self) -> FrozenUncons<'_> { FrozenUncons::New(self) }

  /// Like [`LispVal::unwrapped_arc`], but it can return a reference directly because
  /// the data structure is frozen.
  ///
  /// [`LispVal::unwrapped_arc`]: ../lisp/enum.LispVal.html#method.unwrapped_arc
  pub fn unwrap(&self) -> &Self {
    let mut ret = self;
    loop {
      match &**ret {
        FrozenLispKind::Ref(m) => ret = m,
        FrozenLispKind::Annot(_, v) => ret = v,
        _ => return ret
      }
    }
  }
}

impl FrozenLispKind {
  /// Like [`LispKind::unwrapped`], but it can return a reference directly because
  /// the data structure is frozen.
  ///
  /// [`LispKind::unwrapped`]: ../lisp/enum.LispKind.html#method.unwrapped
  pub fn unwrap(&self) -> &Self {
    let mut ret = self;
    loop {
      match ret {
        FrozenLispKind::Ref(m) => ret = m,
        FrozenLispKind::Annot(_, v) => ret = v,
        _ => return ret
      }
    }
  }

  /// Get the atom that this value stores, if applicable.
  pub fn as_atom(&self) -> Option<AtomID> {
    if let FrozenLispKind::Atom(a) = *self.unwrap() {Some(a)} else {None}
  }

  /// Returns true if this is a proper list.
  pub fn is_list(&self) -> bool {
    let mut e = self;
    loop {
      match e.unwrap() {
        FrozenLispKind::List(_) => return true,
        FrozenLispKind::DottedList(_, r) => e = r,
        _ => return false,
      }
    }
  }

  /// Returns true if this is a proper list of length `n`.
  pub fn exactly(&self, mut n: usize) -> bool {
    let mut e = self;
    loop {
      match e.unwrap() {
        FrozenLispKind::List(es) => return n == es.len(),
        FrozenLispKind::DottedList(es, _) if n < es.len() => return false,
        FrozenLispKind::DottedList(es, r) => {n -= es.len(); e = r}
        _ => return false,
      }
    }
  }

  /// Returns true if this is `()`.
  pub fn is_nil(&self) -> bool { self.exactly(0) }
  /// Returns true if this is `()`.
  pub fn is_empty(&self) -> bool { self.exactly(0) }

  /// Gets the length of the list-like prefix of this value,
  /// i.e. the number of cons-cells along the right spine before reaching something else.
  pub fn len(&self) -> usize {
    let (mut e, mut len) = (self, 0);
    loop {
      match e.unwrap() {
        FrozenLispKind::List(es) => return len + es.len(),
        FrozenLispKind::DottedList(es, r) => {len += es.len(); e = r}
        _ => return len,
      }
    }
  }

  /// Get a file span annotation associated to a lisp value, if possible.
  pub fn fspan(&self) -> Option<FileSpan> {
    let mut e = self;
    loop {
      match e.unwrap() {
        FrozenLispKind::Ref(m) => e = m,
        FrozenLispKind::Annot(Annot::Span(sp), _) => return Some(sp.clone()),
        _ => return None
      }
    }
  }
}

impl Deref for FrozenLispVal {
  type Target = FrozenLispKind;
  fn deref(&self) -> &FrozenLispKind { unsafe { self.thaw().deref().freeze() } }
}

impl Remap<LispRemapper> for FrozenLispVal {
  type Target = LispVal;
  fn remap(&self, r: &mut LispRemapper) -> LispVal {
    let ptr: *const FrozenLispKind = self.deref();
    if let Some(v) = r.lisp.get(&ptr) {return v.clone()}
    let v = match self.deref() {
      FrozenLispKind::Atom(a) => LispVal::atom(a.remap(r)),
      FrozenLispKind::List(v) => LispVal::list(v.remap(r)),
      FrozenLispKind::DottedList(v, l) => LispVal::dotted_list(v.remap(r), l.remap(r)),
      FrozenLispKind::Annot(sp, m) => LispVal::new(LispKind::Annot(sp.clone(), m.remap(r))),
      FrozenLispKind::Proc(f) => LispVal::proc(f.remap(r)),
      FrozenLispKind::AtomMap(m) => LispVal::new(LispKind::AtomMap(m.remap(r))),
      FrozenLispKind::Ref(m) => match r.refs.entry(m as *const _) {
        Entry::Occupied(e) => e.get().clone(),
        Entry::Vacant(e) => {
          let ref_ = LispVal::new(LispKind::Ref(LispRef::new(LispVal::undef())));
          e.insert(ref_.clone());
          ref_.as_ref_(|val| *val = m.remap(r)).unwrap();
          r.refs.remove(&(m as *const _));
          ref_
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
    r.lisp.entry(ptr).or_insert(v).clone()
  }
}

impl Remap<LispRemapper> for FrozenProc {
  type Target = Proc;
  fn remap(&self, r: &mut LispRemapper) -> Proc {
    match &self.0 {
      &Proc::Builtin(p) => Proc::Builtin(p),
      &Proc::Lambda {ref pos, ref env, spec, ref code} =>
        Proc::Lambda {pos: pos.remap(r), env: env.remap(r), spec, code: code.remap(r)},
      Proc::MatchCont(_) => Proc::MatchCont(Rc::new(Cell::new(false))),
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
  /// Convert a `&FrozenLispRef` into an `&LispRef`.
  /// # Safety
  /// The reference derived here is only usable for reading, so in particular
  /// `Rc::clone()` should be avoided because it could race with other readers.
  pub unsafe fn thaw(&self) -> &LispRef { &self.0 }
}

impl Deref for FrozenLispRef {
  type Target = FrozenLispVal;
  fn deref(&self) -> &FrozenLispVal {
    unsafe { self.thaw().get_unsafe().freeze() }
  }
}

/// An iterator over the contents of a `LispVal`, like [`Uncons`], but borrowing
/// from the original data instead of cloning (which is not allowed for frozen values).
///
/// [`Uncons`]: ../environment/struct.Uncons.html
#[derive(Copy, Clone, Debug)]
pub enum FrozenUncons<'a> {
  New(&'a FrozenLispVal),
  List(&'a [FrozenLispVal]),
  DottedList(&'a [FrozenLispVal], &'a FrozenLispVal),
}

impl<'a> FrozenUncons<'a> {
  /// Returns true if this is a proper list of length `n`.
  pub fn exactly(self, n: usize) -> bool {
    match self {
      FrozenUncons::New(e) => e.exactly(n),
      FrozenUncons::List(es) => es.len() == n,
      FrozenUncons::DottedList(es, r) => n.checked_sub(es.len()).map_or(false, |i| r.exactly(i)),
    }
  }

  /// Returns true if this is `()`.
  pub fn is_empty(self) -> bool { self.exactly(0) }

  /// Gets the length of the list-like prefix of this value,
  /// i.e. the number of cons-cells along the right spine before reaching something else.
  pub fn len(self) -> usize {
    match self {
      FrozenUncons::New(e) => e.len(),
      FrozenUncons::List(es) => es.len(),
      FrozenUncons::DottedList(es, r) => es.len() + r.len(),
    }
  }
}

impl<'a> Iterator for FrozenUncons<'a> {
  type Item = &'a FrozenLispVal;
  fn next(&mut self) -> Option<&'a FrozenLispVal> {
    loop {
      match self {
        FrozenUncons::New(e) => {
          let e2 = e.unwrap();
          match &**e2 {
            FrozenLispKind::List(es) => *self = FrozenUncons::List(es),
            FrozenLispKind::DottedList(es, r) => *self = FrozenUncons::DottedList(es, r),
            _ => {*e = e2; return None}
          }
        }
        FrozenUncons::List(es) => {
          let (e1, es2) = es.split_first()?;
          *es = es2;
          return Some(e1)
        }
        FrozenUncons::DottedList(es, r) => match es.split_first() {
          None => *self = FrozenUncons::New(r),
          Some((e1, es2)) => {*es = es2; return Some(e1)}
        }
      }
    }
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    match self {
      FrozenUncons::New(_) => (0, None),
      FrozenUncons::List(es) => {let n = es.len(); (n, Some(n))}
      FrozenUncons::DottedList(es, _) => (es.len(), None)
    }
  }

  fn count(self) -> usize { self.len() }
}
