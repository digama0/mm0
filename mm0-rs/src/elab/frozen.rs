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
//! [`Rc`], it is not safe to clone a [`LispVal`] during this period, and instead the
//! [`FrozenLispVal`] type is used as a read only wrapper around [`LispVal`].
//! At this point the data becomes safe to read from other threads, such as other files
//! that `import` this one and were waiting on elaboration to complete.
//!
//! There are two ways in which this strict time separation is violated. One is that
//! an elaborator may yield when it hits an `import` statement, while waiting for that
//! file to be ready, and it may restart on another thread since the executor is
//! multithreaded. To represent this we use the `FrozenElaborator` wrapper
//! (local to [`ElaborateBuilder::elab`](crate::elab::ElaborateBuilder::elab)), which
//! represents a "paused" elaboration. This object is [`Send`] but cannot be cloned,
//! and it provides no access to the data under construction (and any access to the
//! inner data by a thread that does not own the elaborator is UB).
//!
//! The other way is for a lisp object to be temporarily frozen during elaboration using
//! the [`freeze`] method. This is also unsafe in general because the [`FrozenLispVal`]
//! methods do not touch reference counts and ignore writer locks around references.
//! This is safe as long as the object is not mutated (via another shared reference,
//! or a clone) during the lifetime of the object returned by `freeze`.
//!
//! [`freeze`]: LispVal::freeze

use std::cell::{Cell, RefCell};
use std::ops::Deref;
use std::sync::Arc;
use std::rc::Rc;
use std::collections::{HashMap, hash_map::Entry};
use num::BigInt;
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;
use crate::{mk_lisp_kind, ArcString, AtomData, AtomId, AtomVec, DeclKey, DocComment, Environment,
  FileSpan, LinedString, LispData, LispKind, LispVal, MergeStrategy, MergeStrategyInner, ParserEnv, Sort,
  SortId, SortVec, Span, StmtTrace, Term, TermId, TermVec, Thm, ThmId, ThmVec,
  lisp::{print::FormatEnv, Annot, InferTarget, LispRef, LispWeak, Proc, Syntax}};
use super::{ObjectKind, Remap, Remapper, Spans};

/// A "frozen" environment, which is a thread-safe read only
/// wrapper around [`Environment`].
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[repr(transparent)]
pub struct FrozenEnv(Arc<Environment>);
#[allow(unknown_lints)] #[allow(clippy::non_send_fields_in_send_ty)]
// Safety: We protect all access through the API in this module
unsafe impl Send for FrozenEnv {}
// Safety: We protect all access through the API in this module
unsafe impl Sync for FrozenEnv {}

impl FrozenEnv {
  /// Create a new [`FrozenEnv`] from an [`Environment`].
  #[allow(clippy::arc_with_non_send_sync)]
  #[must_use] pub fn new(env: Environment) -> Self { Self(Arc::new(env)) }

  /// Convert a [`&FrozenEnv`](FrozenEnv) into an [`&Environment`](Environment).
  /// # Safety
  /// The reference derived here is only usable for reading, so in particular
  /// [`Rc::clone()`] should be avoided because it could race with other readers.
  #[must_use] pub unsafe fn thaw(&self) -> &Environment { &self.0 }

  /// Create a [`FormatEnv`] object, which can be used to print objects.
  /// # Safety
  /// TODO: this gives out an `&Environment`, even though it is frozen. Don't abuse it
  #[must_use] pub unsafe fn format_env<'a>(&'a self, source: &'a LinedString) -> FormatEnv<'a> {
    // Safety: ensured by caller
    FormatEnv { source, env: unsafe { self.thaw() } }
  }

  /// Get the list of [`Spans`] in the environment.
  #[must_use] pub fn spans(&self) -> &[Spans<ObjectKind>] {
    // Safety: ObjectKind only contains frozen data
    &unsafe { self.thaw() }.spans
  }

  /// Get the [`Spans`] object corresponding to the statement that contains the given position,
  /// if one exists.
  #[must_use] pub fn find(&self, pos: usize) -> Option<&Spans<ObjectKind>> {
    Spans::find(self.spans(), pos)
  }

  /// Accessor for [`Environment::data`]
  #[must_use] pub fn data(&self) -> &AtomVec<FrozenAtomData> {
    // Safety: Data is re-frozen, and the cast is safe because FrozenAtomData is repr(transparent)
    unsafe { &*(&raw const self.thaw().data).cast() }
  }

  /// Accessor for [`Environment::sorts`]
  #[must_use] pub fn sorts(&self) -> &SortVec<Sort> {
    // Safety: `Sort` does not have any `LispVal`s
    &unsafe { self.thaw() }.sorts
  }
  /// Accessor for [`Environment::sorts`]
  #[must_use] pub fn sort(&self, s: SortId) -> &Sort { &self.sorts()[s] }
  /// Accessor for [`Environment::terms`]
  #[must_use] pub fn terms(&self) -> &TermVec<Term> {
    // Safety: `Term` does not have any `LispVal`s
    &unsafe { self.thaw() }.terms
  }
  /// Accessor for [`Environment::terms`]
  #[must_use] pub fn term(&self, t: TermId) -> &Term { &self.terms()[t] }
  /// Accessor for [`Environment::thms`]
  #[must_use] pub fn thms(&self) -> &ThmVec<Thm> {
    // Safety: `Thm` does not have any `LispVal`s
    &unsafe { self.thaw() }.thms
  }
  /// Accessor for [`Environment::thms`]
  #[must_use] pub fn thm(&self, t: ThmId) -> &Thm { &self.thms()[t] }
  /// Accessor for [`Environment::stmts`]
  #[must_use] pub fn stmts(&self) -> &[StmtTrace] {
    // Safety: `StmtTrace` does not have any `LispVal`s
    &unsafe { self.thaw() }.stmts
  }
  /// Parse a string into an atom.
  #[must_use] pub fn get_atom(&self, s: &[u8]) -> Option<AtomId> {
    // Safety: we don't read any `LispVal`s
    unsafe { self.thaw() }.atoms.get(s).copied()
  }
  /// Accessor for [`Environment::pe`]
  #[must_use] pub fn pe(&self) -> &ParserEnv {
    // Safety: `ParserEnv` does not have any `LispVal`s
    &unsafe { self.thaw() }.pe
  }
}

/// A wrapper around an [`AtomData`] that is frozen.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[repr(transparent)]
pub struct FrozenAtomData(AtomData);

impl FrozenAtomData {
  /// Accessor for [`AtomData::name`]
  #[must_use] pub fn name(&self) -> &ArcString { &self.0.name }
  /// Accessor for [`AtomData::sort`]
  #[must_use] pub fn sort(&self) -> Option<SortId> { self.0.sort }
  /// Accessor for [`AtomData::decl`]
  #[must_use] pub fn decl(&self) -> Option<DeclKey> { self.0.decl }
  /// Accessor for [`AtomData::lisp`]
  #[must_use] pub fn lisp(&self) -> &Option<FrozenLispData> {
    // Safety: Data is re-frozen, and the cast is safe because FrozenLispData is repr(transparent)
    unsafe { &*(&raw const self.0.lisp).cast() }
  }
  /// Accessor for [`AtomData::graveyard`]
  #[must_use] pub fn graveyard(&self) -> &Option<Box<(FileSpan, Span)>> { &self.0.graveyard }
}

/// A wrapper around a [`MergeStrategyInner`] that is frozen.
#[derive(Debug)]
pub struct FrozenMergeStrategyInner(MergeStrategyInner);
/// A wrapper around a [`MergeStrategy`] that is frozen.
#[derive(Debug)]
pub struct FrozenMergeStrategy(MergeStrategy);

/// A wrapper around a [`LispData`] that is frozen.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[repr(transparent)]
pub struct FrozenLispData(LispData);

impl FrozenLispData {
  /// Accessor for [`LispData::src`]
  #[must_use] pub fn src(&self) -> &Option<(FileSpan, Span)> { &self.0.src }
  /// Accessor for [`LispData::doc`]
  #[must_use] pub fn doc(&self) -> &Option<DocComment> { &self.0.doc }
  /// Accessor for [`LispData::doc`]
  #[must_use] pub fn merge(&self) -> &FrozenMergeStrategy {
    // Safety: Input is frozen already
    unsafe { freeze_merge_strategy(&self.0.merge) }
  }
}
impl Deref for FrozenLispData {
  type Target = FrozenLispVal;
  fn deref(&self) -> &FrozenLispVal {
    // Safety: Input is frozen already
    unsafe { self.0.val.freeze() }
  }
}

/// A wrapper around a [`LispVal`] that is frozen.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[repr(transparent)]
pub struct FrozenLispVal(LispVal);

/// A wrapper around a [`LispRef`] that is frozen.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[repr(transparent)]
pub struct FrozenLispRef(LispRef);

/// A wrapper around a [`Proc`] that is frozen.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[repr(transparent)]
pub struct FrozenProc(Proc);

mk_lisp_kind! {
  /// A wrapper around a [`LispKind`] that is frozen.
  FrozenLispKind, FrozenLispVal, FrozenLispRef, FrozenProc
}

impl LispKind {
  /// Freeze a reference to a [`LispKind`] into a [`FrozenLispKind`].
  /// # Safety
  /// The data structure should not be modified, even via clones, while this reference is alive.
  #[must_use] pub unsafe fn freeze(&self) -> &FrozenLispKind {
    // Safety: The cast is safe because FrozenLispKind is repr(transparent)
    unsafe { &*<*const _>::cast(self) }
  }
}

impl LispVal {
  /// Freeze a reference to a [`LispVal`] into a [`FrozenLispVal`].
  /// # Safety
  /// The data structure should not be modified, even via clones, while this reference is alive.
  #[must_use] pub unsafe fn freeze(&self) -> &FrozenLispVal {
    // Safety: The cast is safe because FrozenLispVal is repr(transparent)
    unsafe { &*<*const _>::cast(self) }
  }
}

impl LispRef {
  /// Freeze a reference to a [`LispRef`] into a [`FrozenLispRef`].
  /// # Safety
  /// The data structure should not be modified, even via clones, while this reference is alive.
  #[must_use] pub unsafe fn freeze(&self) -> &FrozenLispRef {
    // Safety: The cast is safe because FrozenLispRef is repr(transparent)
    unsafe { &*<*const _>::cast(self) }
  }
}

/// Freeze a reference to a [`MergeStrategyInner`] into a [`FrozenMergeStrategyInner`].
/// # Safety
/// The data structure should not be modified, even via clones, while this reference is alive.
#[must_use] pub unsafe fn freeze_merge_strategy(this: &MergeStrategy) -> &FrozenMergeStrategy {
  // Safety: The cast is safe because FrozenMergeStrategy is repr(transparent)
  unsafe { &*<*const _>::cast(this) }
}

impl MergeStrategyInner {
  /// Freeze a reference to a [`MergeStrategyInner`] into a [`FrozenMergeStrategyInner`].
  /// # Safety
  /// The data structure should not be modified, even via clones, while this reference is alive.
  #[must_use] pub unsafe fn freeze(&self) -> &FrozenMergeStrategyInner {
  // Safety: The cast is safe because FrozenMergeStrategyInner is repr(transparent)
    unsafe { &*<*const _>::cast(self) }
  }
}

impl Proc {
  /// Freeze a reference to a [`Proc`] into a [`FrozenProc`].
  /// # Safety
  /// The data structure should not be modified, even via clones, while this reference is alive.
  #[must_use] pub unsafe fn freeze(&self) -> &FrozenProc {
    // Safety: The cast is safe because FrozenProc is repr(transparent)
    unsafe { &*<*const _>::cast(self) }
  }
}

impl FrozenLispVal {
  /// Freeze a [`LispVal`], creating a new [`FrozenLispVal`].
  /// # Safety
  /// The functions on the resulting [`FrozenLispVal`] should not be called
  /// until the value is frozen (meaning that all internal mutability stops).
  #[must_use] pub unsafe fn new(e: LispVal) -> Self { Self(e) }

  /// Convert a [`&FrozenLispVal`](FrozenLispVal) into an [`&LispVal`](LispVal).
  /// # Safety
  /// The reference derived here is only usable for reading, so in particular
  /// [`Rc::clone()`] should be avoided because it could race with other readers.
  #[must_use] pub unsafe fn thaw(&self) -> &LispVal { &self.0 }

  /// Get a iterator over frozen lisp values, for dealing with lists.
  pub fn uncons(&self) -> FrozenUncons<'_> { FrozenUncons::New(self) }
}

impl FrozenLispKind {
  /// Like [`LispKind::unwrapped`], but it can return a reference directly because
  /// the data structure is frozen.
  #[must_use] pub fn unwrap(&self) -> &Self {
    let mut ret = self;
    for _ in 0..20 {
      match ret {
        FrozenLispKind::Ref(m) => match m.get() {
          None => return ret,
          Some(v) => ret = v
        },
        FrozenLispKind::Annot(_, v) => ret = v,
        _ => return ret
      }
    }
    ret
  }

  /// Get the atom that this value stores, if applicable.
  #[must_use] pub fn as_atom(&self) -> Option<AtomId> {
    if let FrozenLispKind::Atom(a) = *self.unwrap() {Some(a)} else {None}
  }

  /// Returns true if this is a proper list.
  #[must_use] pub fn is_list(&self) -> bool {
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
  #[must_use] pub fn exactly(&self, mut n: usize) -> bool {
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
  #[must_use] pub fn is_nil(&self) -> bool { self.exactly(0) }
  /// Returns true if this is `()`.
  #[must_use] pub fn is_empty(&self) -> bool { self.exactly(0) }

  /// Gets the length of the list-like prefix of this value,
  /// i.e. the number of cons-cells along the right spine before reaching something else.
  #[must_use] pub fn len(&self) -> usize {
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
  #[must_use] pub fn fspan(&self) -> Option<FileSpan> {
    let mut e = self;
    for _ in 0..20 {
      match e.unwrap() {
        FrozenLispKind::Ref(m) => e = m.get()?,
        FrozenLispKind::Annot(Annot::Span(sp), _) => return Some(sp.clone()),
        _ => return None
      }
    }
    None
  }
}

impl Deref for FrozenLispVal {
  type Target = FrozenLispKind;
  fn deref(&self) -> &FrozenLispKind {
    // Safety: Input is frozen already
    unsafe { self.thaw().deref().freeze() }
  }
}

impl Remap for FrozenMergeStrategyInner {
  type Target = MergeStrategyInner;
  fn remap(&self, r: &mut Remapper) -> MergeStrategyInner {
    // Safety: Input is frozen already
    unsafe {
      match &self.0 {
        MergeStrategyInner::AtomMap(m) =>
          MergeStrategyInner::AtomMap(freeze_merge_strategy(m).remap(r)),
        MergeStrategyInner::Custom(f) =>
          MergeStrategyInner::Custom(f.freeze().remap(r))
      }
    }
  }
}

impl Remap for FrozenMergeStrategy {
  type Target = MergeStrategy;
  fn remap(&self, r: &mut Remapper) -> MergeStrategy {
    self.0.as_ref().map(|m| {
      // Safety: Input is frozen already
      Rc::new(unsafe { m.freeze() }.remap(r))
    })
  }
}

impl Remap for FrozenLispData {
  type Target = LispData;
  fn remap(&self, r: &mut Remapper) -> LispData {
    LispData {
      src: self.src().clone(),
      doc: self.doc().clone(),
      val: (**self).remap(r),
      merge: self.merge().remap(r),
    }
  }
}

impl Remap for FrozenLispVal {
  type Target = LispVal;
  fn remap(&self, r: &mut Remapper) -> LispVal { (**self).remap(r) }
}

impl Remap for FrozenLispKind {
  type Target = LispVal;
  fn remap(&self, r: &mut Remapper) -> LispVal {
    let ptr: *const FrozenLispKind = self;
    if let Some(v) = r.lisp.get(&ptr) {return v.clone()}
    let v = match self {
      FrozenLispKind::Atom(a) => LispVal::atom(a.remap(r)),
      FrozenLispKind::List(v) => LispVal::list(v.remap(r)),
      FrozenLispKind::DottedList(v, l) => LispVal::dotted_list(v.remap(r), l.remap(r)),
      FrozenLispKind::Annot(sp, m) => LispVal::new(LispKind::Annot(sp.clone(), m.remap(r))),
      FrozenLispKind::Proc(f) => LispVal::proc(f.remap(r)),
      FrozenLispKind::AtomMap(m) => LispVal::new(LispKind::AtomMap(m.remap(r))),
      FrozenLispKind::Ref(m) => match r.refs.entry(std::ptr::from_ref(m)) {
        Entry::Occupied(e) => e.get().clone(),
        Entry::Vacant(e) => {
          let ref_ = LispVal::new_ref(LispVal::undef());
          e.insert(ref_.clone());
          let w = m.remap(r);
          ref_.as_lref(|val| *val.get_mut_weak() = w).expect("impossible");
          r.refs.remove(&std::ptr::from_ref(m));
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

impl Remap for FrozenLispRef {
  type Target = LispWeak;
  fn remap(&self, r: &mut Remapper) -> LispWeak {
    // Safety: We ensure `LispWeak` are valid pointers or null, so they are safe to read
    unsafe { self.thaw().get_weak().map_unsafe(|e| e.freeze().remap(r)) }
  }
}

impl Remap for FrozenProc {
  type Target = Proc;
  fn remap(&self, r: &mut Remapper) -> Proc {
    match &self.0 {
      &Proc::Builtin(p) => Proc::Builtin(p),
      &Proc::Lambda {ref pos, ref env, spec, ref code} =>
        Proc::Lambda {pos: pos.remap(r), env: env.remap(r), spec, code: code.remap(r)},
      Proc::MatchCont(_) => Proc::MatchCont(Rc::new(Cell::new(false))),
      Proc::RefineCallback => Proc::RefineCallback,
      // Safety: the merge strategy is already frozen
      Proc::MergeMap(m) => Proc::MergeMap(unsafe {freeze_merge_strategy(m)}.remap(r)),
      Proc::ProofThunk(x, m) => Proc::ProofThunk(x.remap(r), RefCell::new(
        // Safety: the cell is frozen, so we must not change the borrow flag
        match unsafe { m.try_borrow_unguarded() }.expect("failed to deref ref") {
          Ok(e) => Ok(e.remap(r)),
          Err(v) => Err(v.remap(r)),
        }
      )),
      Proc::Dyn(c) => Proc::Dyn(c.remap(r)),
    }
  }
}

impl FrozenLispRef {
  /// Convert a [`&FrozenLispRef`](FrozenLispRef) into an [`&LispRef`](LispRef).
  /// # Safety
  /// The reference derived here is only usable for reading, so in particular
  /// [`Rc::clone()`] should be avoided because it could race with other readers.
  #[must_use] pub unsafe fn thaw(&self) -> &LispRef { &self.0 }

  /// Dereference a [`FrozenLispRef`]. This can fail if the reference
  /// is a weak reference and the target is gone.
  #[must_use] pub fn get(&self) -> Option<&FrozenLispKind> {
    // Safety: We ensure `LispWeak` are valid pointers or null, so they are safe to read
    unsafe { self.thaw().get_unsafe().map(|e| e.freeze()) }
  }
}

impl FrozenProc {
  /// Convert a [`&FrozenProc`](FrozenProc) into an [`&Proc`](Proc).
  /// # Safety
  /// The reference derived here is only usable for reading, so in particular
  /// [`Rc::clone()`] should be avoided because it could race with other readers.
  #[must_use] pub unsafe fn thaw(&self) -> &Proc { &self.0 }
}

/// An iterator over the contents of a [`LispVal`], like [`Uncons`](super::lisp::Uncons),
/// but borrowing from the original data instead of cloning
/// (which is not allowed for frozen values).
#[must_use] #[derive(Clone, Debug)]
pub enum FrozenUncons<'a> {
  /// The initial state, pointing to a lisp value.
  New(&'a FrozenLispKind),
  /// A reference to a sub-slice of a [`LispKind::List`].
  List(&'a [FrozenLispVal]),
  /// A reference to a sub-slice of a [`LispKind::DottedList`].
  DottedList(&'a [FrozenLispVal], &'a FrozenLispVal),
}

impl FrozenUncons<'_> {
  /// Returns true if this is a proper list of length `n`.
  #[must_use] pub fn exactly(&self, n: usize) -> bool {
    match self {
      FrozenUncons::New(e) => e.exactly(n),
      FrozenUncons::List(es) => es.len() == n,
      FrozenUncons::DottedList(es, r) => n.checked_sub(es.len()).is_some_and(|i| r.exactly(i)),
    }
  }

  /// Returns true if this is `()`.
  #[must_use] pub fn is_empty(&self) -> bool { self.exactly(0) }

  /// Gets the length of the list-like prefix of this value,
  /// i.e. the number of cons-cells along the right spine before reaching something else.
  #[must_use] pub fn len(&self) -> usize {
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
          match e2 {
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
