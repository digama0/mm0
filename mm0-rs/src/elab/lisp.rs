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
use std::rc::Rc;
use std::cell::{Cell, RefCell};
use std::sync::{Arc, Mutex};
use std::collections::HashMap;
use std::str::FromStr;
use num::BigInt;
use owning_ref::{OwningRef, StableAddress, CloneStableAddress};
use crate::parser::ast::Atom;
use crate::util::{ArcString, FileSpan, Span, SliceExt};
use super::{AtomID, ThmID, AtomVec, Remap, Modifiers,
  frozen::{FrozenLispKind, FrozenLispRef}};
use parser::IR;
pub use super::math_parser::{QExpr, QExprKind};

macro_rules! str_enum {
  ($(#[$doc:meta])* enum $name:ident $($rest:tt)*) => {
    str_enum!{inner concat!("Convert a `", stringify!($name), "` to a string.");
      $(#[$doc])* enum $name $($rest)*}
  };
  (inner $to_str:expr;
      $(#[$doc:meta])* enum $name:ident {$($(#[$doc2:meta])* $e:ident: $s:expr,)*}) => {
    $(#[$doc])*
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub enum $name { $($(#[$doc2])* $e),* }
    crate::deep_size_0!($name);

    impl FromStr for $name {
      type Err = ();
      fn from_str(s: &str) -> Result<Self, ()> {
        match s {
          $($s => Ok(Self::$e),)*
          _ => Err(())
        }
      }
    }
    impl $name {
      #[doc=$to_str] pub fn to_str(self) -> &'static str {
        match self {
          $($name::$e => $s),*
        }
      }
    }
  }
}

str_enum! {
  /// The `Syntax` type represents atom-like objects that are considered keywords
  /// of the language, and have special interpretations.
  enum Syntax {
    /// `def`, aka `defun` or `define` in other lisps: used to define new local or global variables
    Define: "def",
    /// `fn`, aka `lambda` in other lisps: defines a closure or anonymous procedure
    Lambda: "fn",
    /// `quote` or `'e`, aka `quasiquote` in other lisps: reinterprets most sexprs as themselves
    /// rather than as function and variable references.
    Quote: "quote",
    /// `unquote` or `,e`: splices an evaluated expression into a quotation
    Unquote: "unquote",
    /// `if`: conditional expressions
    If: "if",
    /// `focus`: a tactic that focuses on the main goal, calls a sequence of `refine` calls,
    /// and then closes the goal.
    Focus: "focus",
    /// `let`, aka `let*` in other lisps: define a sequence of variable declarations.
    Let: "let",
    /// `letrec`: define a set of mutually recursive variable declarations.
    Letrec: "letrec",
    /// `match`: perform pattern matching on an s-expression.
    Match: "match",
    /// `match-fn`: a lambda taking one argument that pattern matches on its argument.
    MatchFn: "match-fn",
    /// `match-fn*`: a lambda taking any number of arguments that pattern matches on the list of arguments.
    MatchFns: "match-fn*",
  }
}

impl Syntax {
  /// Parse a string and atom type pair into a `Syntax`.
  pub fn parse(s: &str, a: Atom) -> Result<Syntax, &str> {
    match a {
      Atom::Ident => s.parse().map_err(|_| s),
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

/// The type of a metavariable. This encodes the different types of context
/// in which a term is requested.
#[derive(Copy, Clone, Debug)]
pub enum InferTarget {
  /// This is a term that has no context. This can be created by
  /// `(have 'h _)`, for example: the type of the proof term `_` is unconstrained.
  Unknown,
  /// This is a term that should be in some provable sort. For example in
  /// `theorem foo: $ _ $;`  we know that the hole `_` represents a term that
  /// is of provable sort, but we don't know which, unless there is only one
  /// provable sort.
  Provable,
  /// This is a bound variable of sort `s`. For example, if
  /// `term all {x: var}: wff x > wff;`, in `all _ p` the `_` has type `var`
  /// and must be a variable name.
  Bound(AtomID),
  /// This is a metavariable for an expression of sort `s`. For example, if
  /// `term all {x: var}: wff x > wff;`, in `all x _` the `_` has type `wff`
  /// and can be any expression of that sort.
  Reg(AtomID),
}
crate::deep_size_0!(InferTarget);

impl InferTarget {
  /// The target sort of a metavariable. Returns `None` if the sort is unknown.
  pub fn sort(self) -> Option<AtomID> {
    match self {
      InferTarget::Bound(s) | InferTarget::Reg(s) => Some(s),
      _ => None
    }
  }
  /// Returns true if the metavariable must be a bound variable.
  pub fn bound(self) -> bool { matches!(self, InferTarget::Bound(_)) }
}

/// A lisp value. These are the "values" that are passed around by lisp code.
/// See [`LispKind`] for the list of different types of lisp object. This is
/// a wrapper around `Rc<LispKind>`, and it is cloned frequently in client code.
///
/// [`LispKind`]: enum.LispKind.html
#[derive(Default, Debug, Clone, DeepSizeOf)]
pub struct LispVal(Rc<LispKind>);

/// This macro is used to define the [`LispKind`] type, as well as the
/// [`FrozenLispKind`] type, to ensure that they have the same representation
/// and can be safely transmuted.
///
/// [`LispKind`]: enum.LispKind.html
/// [`FrozenLispKind`]: ../frozen/enum.FrozenLispKind.html
#[macro_export]
macro_rules! __mk_lisp_kind {
  ($(#[$doc:meta])* $kind:ident, $val:ident, $ref_:ident, $proc:ident) => {
    $(#[$doc])*
    #[derive(Debug, DeepSizeOf)]
    pub enum $kind {
      /// An atom like `'foo`. Atoms are internally represented as small integers,
      /// so equality comparison on atoms is fast.
      Atom(AtomID),
      /// A list of values. In lisp, this is semantically an iterated cons,
      /// `(a b c d) = (a . (b . (c . (d . ()))))`, and we don't provide any
      /// functions that distinguish these, but because lists are so common
      /// in lisp code we use arrays for this.
      List(Box<[$val]>),
      /// An improper or dotted list of values, `(a b c . d) = (a . (b . (c . d)))`.
      /// As with `List`, we chunk several cons cells into one array. We do not make
      /// any guarantee that lists and dotted lists are stored in canonical form, so
      /// all functions that deal with lists should check that `(a b . (c d . (e f g)))`
      /// is treated the same as `(a b c d e f g)`.
      DottedList(Box<[$val]>, $val),
      /// Annotates a lisp value with some information that should be invisible to the
      /// front end. Currently we primarily use it for associating file locations to
      /// lisp objects, so that client code can give targeted error messages.
      Annot(Annot, $val),
      /// A number like `123`. These use bignum arithmetic so that client code
      /// doesn't have to worry about overflow.
      Number(BigInt),
      /// An immutable string like `"foo"`.
      String(ArcString),
      /// A boolean value, `#t` or `#f`.
      Bool(bool),
      /// An atom that represents a specific syntax keyword like `'def`.
      Syntax(Syntax),
      /// The `#undef` value.
      Undef,
      /// A procedure that can be called, either built in or a user lambda.
      Proc($proc),
      /// A map from atoms to values. This can be used as a mutable map if it is behind a `Ref`.
      AtomMap(HashMap<AtomID, $val>),
      /// A mutable reference. This is the only way to have mutable values in
      /// client code.
      Ref($ref_),
      /// A metavariable. The `usize` gives the index of the metavariable in the
      /// local context, and the `InferTarget` is the expected type of the expression
      /// that should replace this metavariable.
      MVar(usize, InferTarget),
      /// A proof metavariable, also known as a goal. The argument is the expected
      /// theorem statement.
      Goal($val),
    }
  }
}
__mk_lisp_kind! {
  /// The underlying enum of types of lisp data.
  LispKind,
  LispVal,
  LispRef,
  Proc
}

/// A mutable reference to a `LispVal`, the inner type used by `ref!` and related functions.
#[derive(Debug, DeepSizeOf)]
pub struct LispRef(RefCell<LispVal>);

impl LispVal {
  /// Make a `LispVal` from the inner enum type `LispKind`.
  pub fn new(e: LispKind) -> LispVal { LispVal(Rc::new(e)) }
  /// Construct a `LispVal` for an atom.
  pub fn atom(a: AtomID) -> LispVal { LispVal::new(LispKind::Atom(a)) }
  /// Construct a `LispVal` for a list.
  pub fn list(es: impl Into<Box<[LispVal]>>) -> LispVal { LispVal::new(LispKind::List(es.into())) }
  /// Construct a `LispVal` for an improper list.
  pub fn dotted_list(es: impl Into<Box<[LispVal]>>, r: LispVal) -> LispVal {
    LispVal::new(LispKind::DottedList(es.into(), r))
  }
  /// Construct a `LispVal` for an improper list.
  pub fn number(n: BigInt) -> LispVal { LispVal::new(LispKind::Number(n)) }
  /// Construct a `LispVal` for a string.
  pub fn string(s: ArcString) -> LispVal { LispVal::new(LispKind::String(s)) }
  /// Construct a `LispVal` for a syntax element.
  pub fn syntax(s: Syntax) -> LispVal { LispVal::new(LispKind::Syntax(s)) }
  /// Construct a `LispVal` for `#undef`.
  pub fn undef() -> LispVal { LispVal::new(LispKind::Undef) }
  /// Construct a `LispVal` for `()`.
  pub fn nil() -> LispVal { LispVal::list(vec![]) }
  /// Construct a `LispVal` for a boolean.
  pub fn bool(b: bool) -> LispVal { LispVal::new(LispKind::Bool(b)) }
  /// Construct a `LispVal` for a procedure.
  pub fn proc(p: Proc) -> LispVal { LispVal::new(LispKind::Proc(p)) }
  /// Construct a `LispVal` for a mutable reference.
  pub fn new_ref(e: LispVal) -> LispVal { LispVal::new(LispKind::Ref(LispRef::new(e))) }
  /// Construct a `LispVal` for a goal.
  pub fn goal(fsp: FileSpan, ty: LispVal) -> LispVal {
    LispVal::new(LispKind::Goal(ty)).span(fsp)
  }

  /// Annotate this object with a file span.
  pub fn span(self, fsp: FileSpan) -> LispVal {
    LispVal::new(LispKind::Annot(Annot::Span(fsp), self))
  }

  /// Make a copy of this object with the given span,
  /// replacing the existing one if it has one.
  pub fn replace_span(&self, fsp: FileSpan) -> LispVal {
    match &**self {
      LispKind::Annot(_, v) => v.replace_span(fsp),
      _ => self.clone().span(fsp)
    }
  }

  /// Get a mutable reference to the inner `LispKind`, if possible, returning
  /// `None` if the value is shared and calling `f` with the inner reference if
  /// there is only one owner.
  pub fn unwrapped_mut<T>(&mut self, f: impl FnOnce(&mut LispKind) -> T) -> Option<T> {
    Rc::get_mut(&mut self.0).and_then(|e| match e {
      LispKind::Ref(m) => Self::unwrapped_mut(&mut m.get_mut(), f),
      LispKind::Annot(_, v) => Self::unwrapped_mut(v, f),
      _ => Some(f(e))
    })
  }

  /// Traverse past any `Annot` and `Ref` nodes, and return a clone of the inner data.
  pub fn unwrapped_arc(&self) -> LispVal {
    match &**self {
      LispKind::Ref(m) => Self::unwrapped_arc(&m.get()),
      LispKind::Annot(_, v) => Self::unwrapped_arc(v),
      _ => self.clone()
    }
  }

  /// Returns true if this is a clone of `e`.
  pub fn ptr_eq(&self, e: &Self) -> bool { Rc::ptr_eq(&self.0, &e.0) }
  /// Try to get at the inner data, if this value is not shared,
  /// otherwise return self.
  pub fn try_unwrap(self) -> Result<LispKind, LispVal> { Rc::try_unwrap(self.0).map_err(LispVal) }
  /// Try to get a mutable reference to the inner data, if this value is not shared.
  pub fn get_mut(&mut self) -> Option<&mut LispKind> { Rc::get_mut(&mut self.0) }

  /// Try to get a mutable reference to the inner data,
  /// unwrapping any `Annot` and `Ref` nodes, if this value is not shared.
  /// Otherwise returns the innermost shared unwrapped value.
  pub fn try_unwrapped(self) -> Result<LispKind, LispVal> {
    match Rc::try_unwrap(self.0) {
      Ok(LispKind::Annot(_, e)) => e.try_unwrapped(),
      Ok(LispKind::Ref(m)) => m.into_inner().try_unwrapped(),
      Ok(e) => Ok(e),
      Err(e) => Err(LispVal(e))
    }
  }

  /// If this is a list or improper list of length at least `n`, extends
  /// `vec` with the first `n` values in the list and returns true,
  /// otherwise it extends `vec` with as many values as are present and returns false.
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

  fn head(&self) -> Option<LispVal> {
    self.unwrapped(|e| match e {
      LispKind::List(es) => es.first().cloned(),
      LispKind::DottedList(es, r) => es.first().cloned().or_else(|| r.head()),
      _ => None
    })
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
  /// Creates a new `LispRef` initialized with value `e`.
  pub fn new(e: LispVal) -> LispRef { LispRef(RefCell::new(e)) }
  /// Get a reference to the stored value.
  pub fn get<'a>(&'a self) -> impl Deref<Target=LispVal> + 'a { self.0.borrow() }
  /// Get a mutable reference to the stored value.
  pub fn get_mut<'a>(&'a self) -> impl DerefMut<Target=LispVal> + 'a { self.0.borrow_mut() }
  /// Get a clone of the stored value.
  pub fn unref(&self) -> LispVal { self.get().clone() }
  /// Consume the reference, yielding the stored value.
  pub fn into_inner(self) -> LispVal { self.0.into_inner() }

  /// Get the value of this reference without changing the reference count.
  /// # Safety
  /// This function should not be used unless the value is frozen
  /// (in which case you should use [`FrozenLispRef::deref`] instead).
  ///
  /// [`FrozenLispRef::deref`]: ../frozen/struct.FrozenLispRef.html
  pub(crate) unsafe fn get_unsafe(&self) -> &LispVal {
    self.0.try_borrow_unguarded().unwrap()
  }
}

impl PartialEq<LispRef> for LispRef {
  fn eq(&self, other: &LispRef) -> bool { *self.get() == *other.get() }
}
impl Eq for LispRef {}

impl From<&LispKind> for bool {
  fn from(e: &LispKind) -> bool { e.truthy() }
}

impl LispKind {
  /// Unwrap `Ref` and `Annot` nodes, which are ignored by most
  /// lisp primitives, and run `f` with a reference to the inner value.
  /// (We can't directly return the value because the lifetime is too short.)
  /// See also [`LispVal::unwrapped_arc`], which returns a clone of the inner value.
  ///
  /// [`LispVal::unwrapped_arc`]: struct.LispVal.html#method.unwrapped_arc
  pub fn unwrapped<T>(&self, f: impl FnOnce(&Self) -> T) -> T {
    match self {
      LispKind::Ref(m) => m.get().unwrapped(f),
      LispKind::Annot(_, v) => v.unwrapped(f),
      _ => f(self)
    }
  }

  /// Unwrap `Ref` and `Annot` nodes, collecting a span if one is found along the way,
  /// and run `f` with a reference to the inner value and the span.
  /// `fsp` is used as the default value if no span was found.
  pub fn unwrapped_span<T>(&self, fsp: Option<&FileSpan>,
      f: impl FnOnce(Option<&FileSpan>, &Self) -> T) -> T {
    match self {
      LispKind::Ref(m) => m.get().unwrapped_span(fsp, f),
      LispKind::Annot(Annot::Span(fsp), v) => v.unwrapped_span(Some(fsp), f),
      _ => f(fsp, self)
    }
  }

  /// Returns true if this value is to be treated as true in `if` statements.
  /// Everything is truthy except `#f` and references to `#f`.
  pub fn truthy(&self) -> bool {
    self.unwrapped(|e| !matches!(e, LispKind::Bool(false)))
  }
  /// Returns true if this value is a boolean.
  pub fn is_bool(&self) -> bool {
    self.unwrapped(|e| matches!(e, LispKind::Bool(_)))
  }
  /// Get the boolean value that this value stores, if applicable.
  pub fn as_bool(&self) -> Option<bool> {
    self.unwrapped(|e| if let LispKind::Bool(b) = *e {Some(b)} else {None})
  }
  /// Returns true if this value is an atom.
  pub fn is_atom(&self) -> bool {
    self.unwrapped(|e| matches!(e, LispKind::Atom(_)))
  }
  /// Get the atom that this value stores, if applicable.
  pub fn as_atom(&self) -> Option<AtomID> {
    self.unwrapped(|e| if let LispKind::Atom(a) = *e {Some(a)} else {None})
  }
  /// Returns true if this value is a number.
  pub fn is_int(&self) -> bool {
    self.unwrapped(|e| matches!(e, LispKind::Number(_)))
  }
  /// Get the number that this value stores, if applicable.
  pub fn as_int<T>(&self, f: impl FnOnce(&BigInt) -> T) -> Option<T> {
    self.unwrapped(|e| if let LispKind::Number(n) = e {Some(f(n))} else {None})
  }
  /// Returns true if this value is a procedure.
  pub fn is_proc(&self) -> bool {
    self.unwrapped(|e| matches!(e, LispKind::Proc(_)))
  }
  /// Returns true if this value is a string.
  pub fn is_string(&self) -> bool {
    self.unwrapped(|e| matches!(e, LispKind::String(_)))
  }
  /// Returns true if this value is an atom map.
  pub fn is_map(&self) -> bool {
    self.unwrapped(|e| matches!(e, LispKind::AtomMap(_)))
  }
  /// Returns true if this value is not `#undef` or a reference to `#undef`.
  pub fn is_def(&self) -> bool {
    self.unwrapped(|e| !matches!(e, LispKind::Undef))
  }
  /// Returns true if this value is not `#undef`.
  pub fn is_def_strict(&self) -> bool {
    match self {
      LispKind::Undef => false,
      LispKind::Annot(_, v) => v.is_def_strict(),
      _ => true,
    }
  }
  /// Returns true if this value is a mutable reference.
  /// (This function, unlike most, does not auto-deref references.)
  pub fn is_ref(&self) -> bool {
    match self {
      LispKind::Ref(_) => true,
      LispKind::Annot(_, v) => v.is_ref(),
      _ => false,
    }
  }
  /// Get a mutable reference to the value stored by the reference, if it is one.
  pub fn as_ref_<T>(&self, f: impl FnOnce(&mut LispVal) -> T) -> Option<T> {
    match self {
      LispKind::Ref(m) => Some(f(&mut m.get_mut())),
      LispKind::Annot(_, e) => e.as_ref_(f),
      _ => None
    }
  }
  /// Get a file span annotation associated to a lisp value, if possible.
  pub fn fspan(&self) -> Option<FileSpan> {
    match self {
      LispKind::Ref(m) => m.get().fspan(),
      LispKind::Annot(Annot::Span(sp), _) => Some(sp.clone()),
      // LispKind::Annot(_, e) => e.fspan(),
      _ => None
    }
  }
  /// Returns true if this value is a metavariable.
  pub fn is_mvar(&self) -> bool {
    self.unwrapped(|e| matches!(e, LispKind::MVar(_, _)))
  }
  /// Get the metavariable's target type, if applicable.
  pub fn mvar_target(&self) -> Option<InferTarget> {
    self.unwrapped(|e| if let LispKind::MVar(_, is) = *e {Some(is)} else {None})
  }
  /// Returns true if this value is a goal.
  pub fn is_goal(&self) -> bool {
    self.unwrapped(|e| matches!(e, LispKind::Goal(_)))
  }
  /// Get the goal's target statement, if applicable.
  pub fn goal_type(&self) -> Option<LispVal> {
    self.unwrapped(|e| if let LispKind::Goal(e) = e {Some(e.clone())} else {None})
  }

  /// Returns true if this is a proper list of length `n`.
  pub fn exactly(&self, n: usize) -> bool {
    self.unwrapped(|e| match e {
      LispKind::List(es) => n == es.len(),
      LispKind::DottedList(es, _) if n < es.len() => false,
      LispKind::DottedList(es, r) => r.exactly(n - es.len()),
      _ => false,
    })
  }

  /// Returns true if this is `()`.
  pub fn is_nil(&self) -> bool { self.exactly(0) }
  /// Returns true if this is `()`.
  pub fn is_empty(&self) -> bool { self.exactly(0) }

  /// Returns true if this is a proper list.
  pub fn is_list(&self) -> bool {
    self.unwrapped(|e| match e {
      LispKind::List(_) => true,
      LispKind::DottedList(_, r) => r.is_list(),
      _ => false,
    })
  }

  /// Gets the length of the list-like prefix of this value,
  /// i.e. the number of cons-cells along the right spine before reaching something else.
  pub fn len(&self) -> usize {
    self.unwrapped(|e| match e {
      LispKind::List(es) => es.len(),
      LispKind::DottedList(es, r) => es.len() + r.len(),
      _ => 0,
    })
  }

  /// Returns true if this is a proper list of length at least `n`.
  pub fn list_at_least(&self, n: usize) -> bool {
    self.unwrapped(|e| match e {
      LispKind::List(es) => n <= es.len(),
      LispKind::DottedList(es, r) if n <= es.len() => r.is_list(),
      LispKind::DottedList(es, r) => r.list_at_least(n - es.len()),
      _ => false,
    })
  }

  /// Returns true if this is a proper or improper list of length at least `n`.
  pub fn at_least(&self, n: usize) -> bool {
    self.unwrapped(|e| match e {
      LispKind::List(es) => n <= es.len(),
      LispKind::DottedList(es, _) if n <= es.len() => true,
      LispKind::DottedList(es, r) => r.at_least(n - es.len()),
      _ => n == 0,
    })
  }

  /// Puts a span on this value, if `fsp` is not `None`.
  pub fn decorate_span(self, fsp: &Option<FileSpan>) -> LispVal {
    if let Some(fsp) = fsp {
      LispVal::new(self).span(fsp.clone())
    } else {LispVal::new(self)}
  }

  /// Checks if self is a proper list whose elements are equal to
  /// those yielded by the provided iterator.
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
      (LispKind::DottedList(es1, r1), LispKind::DottedList(es2, r2)) => {
        let mut it1 = es1.iter();
        let mut it2 = es2.iter();
        loop {
          match (it1.next(), it2.next()) {
            (None, None) => break r1 == r2,
            (Some(e1), Some(e2)) => if e1 != e2 {break false},
            (Some(e), None) => break r2.eq_list(Some(e).into_iter().chain(it1)),
            (None, Some(e)) => break r1.eq_list(Some(e).into_iter().chain(it2)),
          }
        }
      }
      _ => false // Goal, Proc, MVar, AtomMap all have only reference equality
    }))
  }
}
impl Eq for LispKind {}

/// An annotation, which is a tag placed on lisp values that is ignored by all
/// the basic functions.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum Annot {
  /// A span annotation marks an expression with a span from the input file.
  /// The parser will place these on all expressions it produces, and they are
  /// used to guide error reporting, but they can also be transferred to other
  /// expressions in client code using [`(copy-span)`].
  ///
  /// [`(copy-span)`]: enum.BuiltinProc.html#variant.CopySpan
  Span(FileSpan),
}

/// The location information for a procedure.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum ProcPos {
  /// A named procedure is created by `(def (foo x) ...)` or
  /// `(def foo (fn (x) ...))`. The file span is the definition block
  /// that created it, while the span is just the span of the name
  /// of the function, in this case `foo` (in the same file).
  Named(FileSpan, Span, AtomID),
  /// An unnamed procedure is a lambda like `(fn (x) ...)` that is not
  /// immediately bound to a name. It is associated only with its span
  /// in the file.
  Unnamed(FileSpan),
}

impl ProcPos {
  /// Get the file span for a procedure.
  fn fspan(&self) -> &FileSpan {
    match self {
      ProcPos::Named(fsp, _, _) => fsp,
      ProcPos::Unnamed(fsp) => fsp,
    }
  }
}

/// A callable procedure. There are several sources of procedures,
/// all of which are interactable only via function calls `(f)` and
/// printing (which shows only basic information about the procedure).
#[derive(Debug, DeepSizeOf)]
pub enum Proc {
  /// A built-in procedure (see [`BuiltinProc`] for the full list).
  /// Initially, a reference to a lisp global with a builtin procedure's name
  /// will return one of these objects, but the user can shadow builtins
  /// with global definitions of their own.
  Builtin(BuiltinProc),
  /// A lambda, created by `fn`, `match-fn`, `match-fn*` or `def`.
  Lambda {
    /// The procedure's position information
    pos: ProcPos,
    /// The local environment, that was captured at the time of the lambda's
    /// creation. This allows `fn`'s to be closures and not just named functions.
    env: Box<[LispVal]>,
    /// The procedure's specification, a poor man's function signature.
    /// As the language is untyped, the only real information we have here
    /// is how many arguments are expected.
    spec: ProcSpec,
    /// The code of the procedure.
    code: Arc<IR>
  },
  /// A match continuation, which is passed to client code in the variable `k`
  /// of `(match e [pat (=> k) code])`. It is a *delimited* continuation, which means
  /// that it is only valid while inside the scope of `code`, but it is a regular
  /// value and can be passed around, so the `Rc<Cell<bool>>` is a validity marker
  /// that is used both to identify which continuation is being jumped to, in case
  /// multiple are in scope, as well as to determine if we are still in the dynamic
  /// extent of `code`.
  MatchCont(Rc<Cell<bool>>),
  /// A callback used by `refine` when it finds a procedure in a refine script.
  /// The callback acts like `refine` as well, but it orders generated subgoals with
  /// respect to an outer invocation of `refine`. This callback also only works
  /// inside a limited extent, but unlike `MatchCont`, there cannot be multiple
  /// refine callbacks simultaneously in flight - a call to the refine callback
  /// binds to the nearest enclosing `refine` call.
  RefineCallback,
  /// A delayed proof, generated by a call to `get-decl`, which returns a lisp
  /// data structure reflecting the requested definition, but delays the proof
  /// unless forced by calling this thunk. The unevaluated form of the thunk
  /// stores `Err(args)`, where `args` is the list of variables, while the
  /// evaluated form stores `Ok(proof)`.
  ProofThunk(AtomID, RefCell<Result<LispVal, Box<[LispVal]>>>),
  /// The compiler object, which can be called as a procedure and stores its own
  /// internal state here. See [`Compiler::call`].
  ///
  /// [`Compiler::call`]: ../../mmc/struct.Compiler.html#method.call
  MMCCompiler(RefCell<crate::mmc::Compiler>) // TODO: use extern instead
}

/// A procedure specification, which defines the number of arguments expected
/// by the call. Individual procedures may have additional rules on top of
/// this for validity, but every procedure must declare its specification
/// in [`Proc::spec`].
///
/// [`Proc::spec`]: enum.Proc.html#method.spec
#[derive(Copy, Clone, Debug)]
pub enum ProcSpec {
  /// This function must be called with exactly `n` arguments.
  Exact(usize),
  /// This function must be called with at least `n` arguments.
  AtLeast(usize),
}
crate::deep_size_0!(ProcSpec);

impl ProcSpec {
  /// Returns true if `i` is a valid number of arguments given this spec.
  pub fn valid(self, i: usize) -> bool {
    match self {
      ProcSpec::Exact(n) => i == n,
      ProcSpec::AtLeast(n) => i >= n,
    }
  }
}

impl Proc {
  /// Returns the specification (number of expected arguments) for a procedure.
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
  /// The set of built in procedures. These each have names that can be shadowed
  /// but not overridden by global names in the environment.
  enum BuiltinProc {
    /// `display` takes a string and prints it. In the interactive editor mode,
    /// this appears as an info diagnostic over the word "`display`".
    /// ```text
    /// (display "hello world")         -- hello world
    /// (display 42)                    -- error, expected string
    /// ```
    Display: "display",
    /// `error` takes a string and throws an error with the given string as the message.
    Error: "error",
    /// `print` takes an arbitrary expression and pretty-prints it.
    Print: "print",
    /// `(report-at sp type msg)` will report the message `msg` at a position
    /// derived from the value `sp` (one can use `copy-span` to pass a value with the
    /// right span here), with error type `type`, which can be `'error`, `'info` or
    /// `'warn`. If `sp` is `#t`, then it will also display a stack trace.
    ReportAt: "report-at",
    /// `begin` returns its last argument, or `#undef` if it is given no arguments.
    /// In Scheme this is a syntax form, but in MM1 all functions have the same
    /// evaluation semantics as `begin`, so the only interesting thing this function
    /// does is ignore its other arguments.
    Begin: "begin",
    /// `(apply f a b '(c d))` evaluates to the result of `(f a b c d)`. That is, the
    /// first argument should be a closure and the last argument should be a list, and
    /// it applies the closure to the list, with any in between arguments added to the
    /// head of the list. `(apply)` is an error, and if `f` is a syntax form then this
    /// is also an error, i.e. `(apply def (x 5))` does not work.
    Apply: "apply",
    /// `(+ a b c)` computes the sum of the (integer) arguments. `(+)` is zero and `(+ a)` is `a`.
    Add: "+",
    /// `(* a b c)` computes the product of the (integer) arguments. `(*)` is one and `(* a)` is `a`.
    Mul: "*",
    /// `(max a b c)` computes the maximum of the (integer) arguments. `(max)` is an error.
    Max: "max",
    /// `(min a b c)` computes the minimum of the (integer) arguments. `(min)` is an error.
    Min: "min",
    /// `(- a b)` computes the subtraction `a - b`. `(- a b c)` is `a - b - c`,
    /// `(- a)` is `-a`, and `(-)` is an error.
    Sub: "-",
    /// {a // b}` computes the integer (flooring) division. More arguments associate to the left.
    Div: "//",
    /// `{a % b}` computes the integer modulus. More arguments associate to the left.
    Mod: "%",
    /// `{a < b}` is true if `a` is less than `b`. `(< a b c)` means `a < b` and `b < c`.
    Lt: "<",
    /// `{a <= b}` is true if `a` is less or equal to `b`. `(<= a b c)` means `a <= b` and `b <= c`.
    Le: "<=",
    /// `{a > b}` is true if `a` is greater than `b`. `(> a b c)` means `a > b` and `b > c`.
    Gt: ">",
    /// `{a >= b}` is true if `a` is greater or equal to `b`. `(>= a b c)` means `a >= b` and `b >= c`.
    Ge: ">=",
    /// `{a = b}` is true if `a` and `b` are equal numbers. `(= a b c)` means `a = b` and `b = c`.
    Eq: "=",
    /// `==`, distinct from `=`, is sometimes called `equal?` in other lisps, and performs
    /// recursive equality comparison.
    ///
    /// * Pointer-equal data always compare as equal.
    /// * Strings, atoms, `#t`, `#f`, `#undef` all perform structural comparison as expected
    ///   (`#t` is equal to `#t` but not equal to `#undef` or `"#t"` or `'#t`).
    /// * Two pairs are equal if their components are equal.
    /// * Procedures (both builtins and `fn` declarations), `atom-map`s, `goal`s and `mvar`s
    ///   have no structural equality; they compare equal only if they are pointer-equal.
    /// * Indirections are ignored; `(ref! 1)` is equal to `1`.
    /// * The comparison routine performs no cycle detection so equality on cyclic data structures can loop.
    /// * Like the numeric equality operator `=`, `==` can be used on more than two arguments,
    ///   in which case it will compare all elements to the first.
    Equal: "==",
    /// `(->string e)` converts an expression to a string. Numbers are converted in the usual
    /// way, strings, atoms and formulas (which are all containers for strings) get the underlying
    /// string, and other expressions are pretty printed using the same method as `print`.
    /// ```text
    /// (->string 42)     -- "42"
    /// (->string (- 42)) -- "-42"
    /// (->string "foo")  -- "foo"
    /// (->string 'foo)   -- "foo"
    /// (->string $foo$)  -- "foo"
    /// (->string '(1 . 2))  -- "(1 . 2)"
    /// ```
    ToString: "->string",
    /// `(string->atom s)` converts a string to an atom. This can be used to create atoms that
    /// violate the concrete syntax, for example if they have embedded spaces.
    /// ```text
    /// (string->atom "foo")         -- foo
    /// (string->atom "foo$bar baz") -- foo$bar baz
    /// ```
    StringToAtom: "string->atom",
    /// `(string-append s1 s2 s3)` stringifies and appends all the inputs.
    /// ```text
    /// (string-append "foo" 'bar 42) -- "foobar42"
    /// ```
    StringAppend: "string-append",
    /// `(not e1 e2 e3)` returns `#f` if any argument is truthy, and `#t` otherwise.
    /// It is not short-circuiting.
    Not: "not",
    /// `(and e1 e2 e3)` returns `#t` if every argument is truthy, and `#f` otherwise.
    /// It is not short-circuiting.
    And: "and",
    /// `(or e1 e2 e3)` returns `#t` if any argument is truthy, and `#f` otherwise.
    /// It is not short-circuiting.
    Or: "or",
    /// `(list e1 e2 e3)` returns the list `(e1 e2 e3)`. It differs from `quote`
    /// in that it evaluates its arguments.
    List: "list",
    /// `(cons e1 e2)` returns `(e1 . e2)`. With more or less arguments:
    /// * `(cons)` returns the empty list.
    /// * `(cons e1)` returns `e1`.
    /// * `(cons e1 e2 e3)` returns `(e1 e2 . e3)`.
    Cons: "cons",
    /// `(hd e)` returns the head of the list, or left element of the cons expression.
    /// It is known as `car` in most lisps.
    Head: "hd",
    /// `(tl e)` returns the tail of the list, or right element of the cons expression.
    /// It is known as `cdr` in most lisps.
    Tail: "tl",
    /// `(nth n e)` returns the `n`th element of the list, or `#undef` if out of range.
    /// It fails if the input is not a list.
    Nth: "nth",
    /// `(map f '(a1 a2) '(b1 b2))` constructs the list `(list (f a1 b1) (f a2 b2))`,
    /// calling `f` on the heads of all the arguments, then the second elements and so on.
    /// All lists must be the same length.
    Map: "map",
    /// `(bool? e)` is true if the argument is a boolean, `#t` or `#f`.
    IsBool: "bool?",
    /// `(atom? e)` is true if the argument is an atom (also known as a symbol), `'x`.
    IsAtom: "atom?",
    /// `(pair? e)` is true if its argument is a cons of something, that is,
    /// a nonempty list or improper list.
    IsPair: "pair?",
    /// `(null? e)` is true if its argument is `()`.
    IsNull: "null?",
    /// `(number? e)` is true if the argument is an integer.
    IsNumber: "number?",
    /// `(string? e)` is true if its argument is a string (not a formula or atom).
    IsString: "string?",
    /// `(fn? e)` is true if the argument is a procedure.
    IsProc: "fn?",
    /// `(def? e)` is true if the argument is not `#undef`.
    IsDef: "def?",
    /// `(ref? e)` is true if the argument is a ref-cell.
    IsRef: "ref?",
    /// * `(ref! e)` constructs a new ref-cell containing the value `e`.
    /// * `(ref!)` constructs a new ref-cell containing `#undef`.
    NewRef: "ref!",
    /// `(get! r)` dereferences the ref-cell `r` to get the value.
    GetRef: "get!",
    /// `(set! r v)` sets the value of the ref-cell `r` to `v`.
    SetRef: "set!",
    /// `(copy-span from to)` makes a copy of `to` with its position information copied from `from`.
    /// (This can be used for improved error reporting, but
    /// otherwise has no effect on program semantics.)
    CopySpan: "copy-span",
    ///  `(stack-span n)` gets the span from `n` calls up the stack (where `0` is
    /// the currently executing function). Returns `#undef` tagged with the target span,
    /// which can then be copied to a term using `(copy-span)`.
    /// (Useful for targeted error reporting in scripts.)
    StackSpan: "stack-span",
    /// `(async f args)` evaluates `(f args)` on another thread, and returns a
    /// procedure that will join on the thread to wait for the result.
    Async: "async",
    /// `(atom-map? m)` is true if the argument is an atom map.
    IsAtomMap: "atom-map?",
    /// `(atom-map! [k1 v1] [k2 v2] ...)` creates a new mutable atom map, a key-value store.
    NewAtomMap: "atom-map!",
    /// * `(lookup m k)` gets the value stored in the atom map `m` at `k`, or `#undef` if not present.
    /// * `(lookup m k v)` will return `v` instead if the key is not present,
    ///   unless `v` is a procedure, in which case it will be called with no arguments on lookup failure.
    Lookup: "lookup",
    /// * `(insert! m k v)` inserts the value `v` at key `k` in the mutable map `m`,
    ///   and returns `#undef`.
    /// * `(insert! m k)` "undefines" the value at key `k` in `m`, that is,
    ///   it erases whatever is there.
    Insert: "insert!",
    /// * `(insert m k v)` returns an immutable map based on the immutable map `m`,
    ///   with the value `v` inserted at key `k`.
    /// * `(insert m k)` returns `k` erased from `m`.
    InsertNew: "insert",
    /// `(set-timeout n)` sets the timeout for running individual theorems and
    /// `do` blocks to `n` milliseconds. The default is 5 seconds.
    SetTimeout: "set-timeout",
    /// `(mvar? e)` returns `#t` if `e` is an unsolved metavariable value.
    /// *Note:* Holes in expressions are *not* represented as raw metavariables,
    /// they are ref-cells to metavariables. So to test if a metavariable has not
    /// been assigned you can use `(mvar? (get! e))`.
    IsMVar: "mvar?",
    /// Similarly, `(goal? e)` returns `#t` if `e` is an unsolved goal expression,
    /// and `(goal? (get! e))` checks if a goal reference has not been solved.
    IsGoal: "goal?",
    /// `(mvar! s bd)` creates a new metavariable ref-cell with sort `s` and
    /// boundedness `bd` and adds it to the list of open metavariables. To emphasize:
    /// ```text
    /// (mvar? (mvar! "foo" #t))            -- #f
    /// (ref? (mvar! "foo" #t))             -- #t
    /// (mvar? (get! (mvar! "foo" #t)))     -- #t
    /// ```
    NewMVar: "mvar!",
    /// `(pp e)` pretty-prints a (fully elaborated) term expression using declared
    /// math notations. It relies on the theorem context to typecheck the formulas
    /// and provide context, and will fall back on the generic lisp printer
    /// for things it doesn't understand.
    PrettyPrint: "pp",
    /// `(goal e)` creates a new goal value given a statement expression.
    /// It will need to be wrapped with a `ref!` to be used with `set-goals`.
    NewGoal: "goal",
    /// `(goal-type g)` gets the statement of a goal (wrapped by any number of refs).
    GoalType: "goal-type",
    /// `(infer-type p)` gets the statement proven by the proof `p`.
    /// This does not perform full typechecking on `p`.
    InferType: "infer-type",
    /// `(get-mvars)` returns the current list of active metavariables.
    GetMVars: "get-mvars",
    /// `(get-goals)` returns the current goal list, a list of references to goals.
    /// Some goals may already have been assigned.
    GetGoals: "get-goals",
    /// `(set-goals g1 g2 g3)` sets the goal list to `(g1 g2 g3)`, replacing
    /// the current goal list. If any of the provided goals are already assigned
    /// they are removed from the list.
    SetGoals: "set-goals",
    /// `(set-close-fn f)` sets the "closer" for the current proof to `f`.
    /// It will be called with no arguments at the end of a `focus` block, and is
    /// responsible for reporting all unfinished goals. Passing `#undef` instead of
    /// a function will reset it to the default closer.
    SetCloseFn: "set-close-fn",
    /// `(local-ctx)` returns the list of hypothesis names (`(infer-type)`
    /// can be used to get the type of the hypotheses).
    LocalCtx: "local-ctx",
    ///`(to-expr e)` elaborates a term pre-expression into an expression,
    /// producing metavariables for `_` placeholders in the expression.
    ToExpr: "to-expr",
    /// * `(refine p)` elaborates a proof pre-expression into a proof, and unifies
    ///   its type against the first goal.
    /// * `(refine p1 p2 p3)` applies three proof pre-expressions to the first
    ///   three goals. If there are fewer than three goals the remaining proofs are ignored.
    Refine: "refine",
    /// * `(have h p)` elaborates the proof pre-expression `p` to a proof, infers
    ///   the type `e` of the proof, and adds `e` to the list of proven subproofs,
    ///   after which `h` may be referred to like any other theorem hypothesis.
    /// * `(have h e p)` is the same except that `p` is elaborated with `e` as the expected type.
    Have: "have",
    /// `(stat)` prints the current proof state, which consists of a list of
    /// subproofs, a list of goals, and a list of metavariables accompanied by their sorts.
    Stat: "stat",
    /// `(get-decl x)` returns the declaration information associated to declaration `x`.
    /// The result has one of the following forms:
    ///
    /// * `('term x bis ret)`, where `x` is the declaration name (same as the input),
    ///   `bis` is a list of binders, and `ret` is a type. A bound variable binder
    ///    `{x: set}` is represented as `'[x set]`, and a regular variable `(ph: wff x)`
    ///    is represented as `'[ph set (x)]`. The third element of the list is always present
    ///    but possibly empty for regular variables. The return type `ret` similarly has the
    ///    form `(s xs)` where `s` is the sort and `xs` is the list of dependent variables.
    ///
    /// * `('def x bis ret vis ds val)`. `x`, `bis` and `ret` have the same form as in the
    ///    `term` case. `vis` is one of  `'local`, `'abstract`, `'pub` or `()`, where the empty
    ///    list represents the default visibility. `ds` is a list of dummy variables such as
    ///    `[x set]` in the same format as the binders, or an atom map mapping `x` to `set`
    ///    and so on. `val` is either `()` indicating that a definition has not been provided,
    ///    or a term s-expression.
    ///
    /// * `('axiom x bis hyps ret)`, where `x` is the declaration name, `bis` are the bound
    ///    and regular variables, `hyps` is a list of `[h hyp]` pairs where `hyp` is a term
    ///    s-expression (`h` will always be `_`), and `ret` is also a term s-expression.
    ///
    /// * `('theorem x bis hyps ret vis vtask)`, where `x`, `bis`, `hyps` and `ret` have the
    ///    same format as in `axiom`, `vis` is the visibility in the same format as in `def`,
    ///    and `vtask` is a thunk that will return a list `(ds proof)` where `ds` is the list
    ///    or atom map of dummy variables, and `proof` is the proof s-expression. `vtask`
    ///    can also have the form `(ds proof)` itself.
    GetDecl: "get-decl",
    /// `(add-decl! decl-data ...)` adds a new declaration, as if a new `def` or `theorem`
    /// declaration was created. This does not do any elaboration - all information is
    /// expected to be fully elaborated. The input format is the same as the output format
    /// of `get-decl`. For example, `(add-decl! 'term 'foo '([_ wff ()]) 'wff)` creates a
    /// new term `term foo: wff > wff;`.
    AddDecl: "add-decl!",
    /// * `(add-term! x bis ret)` is the same as `(add-decl! 'term x bis ret)`.
    /// * `(add-term! x bis ret vis ds val)` is the same as `(add-decl! 'def x bis ret vis ds val)`.
    AddTerm: "add-term!",
    /// * `(add-thm! x bis hyps ret)` is the same as `(add-decl! 'axiom x bis hyps ret)`.
    /// * `(add-thm! x bis hyps ret vis vtask)` is the same as
    ///   `(add-decl! 'theorem x bis hyps ret vis vtask)`.
    AddThm: "add-thm!",
    /// * `(dummy! x s)` produces a new dummy variable called `x` with sort `s`, and returns `x`;
    /// * `(dummy! s)` automatically gives the variable a name like `_123` that is guaranteed to be unused.
    NewDummy: "dummy!",
    /// `(check-proofs b)` turns on (`b = #t`) or off (`b = #f`) proof checking for theorems.
    CheckProofs: "check-proofs",
    /// * `(set-reporting type b)` turns on (`b = #t`) or off (`b = #f`)
    ///   error reporting for error type `type`, which can be `'error`, `'info` or `'warn`.
    ///   (Compilation will still be aborted if there are errors, even if the
    ///   display is suppressed.)
    /// * `(set-reporting b)` will set the error reporting to `b` for all error types.
    SetReporting: "set-reporting",
    /// `refine-extra-args` can be called directly, but it simply returns an error. It is called
    /// by `refine` when elaborating a term with too many arguments, and is expected to be
    /// overridden by user code to provide a more useful behavior.
    RefineExtraArgs: "refine-extra-args",
    /// `(mmc-init)` returns a new compiler object, which is itself a procedure that can
    /// be called to compile MMC functions. See [`Compiler::call`].
    ///
    /// [`Compiler::call`]: ../../mmc/struct.Compiler.html#method.call
    MMCInit: "mmc-init",
  }
}

impl std::fmt::Display for BuiltinProc {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.to_str().fmt(f)
  }
}

/// An iterator over lisp values, for dealing with lists. Semantically this is
/// the same as a `LispVal`, but in order to decrease allocations this allows
/// holding on to incomplete subparts of the arrays used in `LispKind::List`
/// and `LispKind::DottedList`.
#[derive(Debug, DeepSizeOf)]
pub enum Uncons {
  /// The initial state, pointing to a lisp value.
  New(LispVal),
  /// A reference to a sub-slice of a `LispKind::List`.
  List(OwningRef<LispVal, [LispVal]>),
  /// A reference to a sub-slice of a `LispKind::DottedList`.
  DottedList(OwningRef<LispVal, [LispVal]>, LispVal),
}

impl From<LispVal> for Uncons {
  fn from(e: LispVal) -> Uncons { Uncons::New(e) }
}

impl Uncons {
  /// Create an empty `Uncons`.
  pub fn nil() -> Uncons { Uncons::New(LispVal::nil()) }

  /// Returns true if this is a proper list of length `n`.
  pub fn exactly(&self, n: usize) -> bool {
    match self {
      Uncons::New(e) => e.exactly(n),
      Uncons::List(es) => es.len() == n,
      Uncons::DottedList(es, r) => n.checked_sub(es.len()).map_or(false, |i| r.exactly(i)),
    }
  }

  /// Convert an `Uncons` back into a `LispVal`.
  pub fn as_lisp(&self) -> LispVal {
    match self {
      Uncons::New(e) => e.clone(),
      Uncons::List(es) if es.is_empty() => LispVal::nil(),
      Uncons::List(es) => LispVal::list(es.cloned_box()),
      Uncons::DottedList(es, r) if es.is_empty() => r.clone(),
      Uncons::DottedList(es, r) => LispVal::dotted_list(es.cloned_box(), r.clone()),
    }
  }

  /// Returns true if this is `()`.
  pub fn is_empty(&self) -> bool { self.exactly(0) }

  /// Returns true if this is a proper or improper list of length at least `n`.
  pub fn at_least(&self, n: usize) -> bool {
    n == 0 || match self {
      Uncons::New(e) => e.at_least(n),
      Uncons::List(es) => es.len() >= n,
      Uncons::DottedList(es, r) => n.checked_sub(es.len()).map_or(true, |i| r.at_least(i)),
    }
  }

  /// Returns true if this is a proper list of length at least `n`.
  pub fn list_at_least(&self, n: usize) -> bool {
    n == 0 || match self {
      Uncons::New(e) => e.list_at_least(n),
      Uncons::List(es) => es.len() >= n,
      Uncons::DottedList(es, r) => n.checked_sub(es.len()).map_or(true, |i| r.list_at_least(i)),
    }
  }

  /// Gets the length of the list-like prefix of this value,
  /// i.e. the number of cons-cells along the right spine before reaching something else.
  pub fn len(&self) -> usize {
    match self {
      Uncons::New(e) => e.len(),
      Uncons::List(es) => es.len(),
      Uncons::DottedList(es, r) => es.len() + r.len(),
    }
  }

  /// This is the same as `next()`, but it does not advance the iterator.
  /// (This could almost be a `Peekable` implementation, but the reference
  /// may not be derived from `self`, so it has to clone the value.)
  pub fn head(&self) -> Option<LispVal> {
    match self {
      Uncons::New(e) => e.head(),
      Uncons::List(es) => es.first().cloned(),
      Uncons::DottedList(es, r) => es.first().cloned().or_else(|| r.head()),
    }
  }

  /// If this is a list or improper list of length at least `n`, extends
  /// `vec` with the first `n` values in the list and returns true,
  /// otherwise it extends `vec` with as many values as are present and returns false.
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

impl From<Uncons> for LispVal {
  fn from(u: Uncons) -> LispVal {
    match u {
      Uncons::New(e) => e,
      Uncons::List(es) if es.is_empty() => LispVal::nil(),
      Uncons::List(es) => LispVal::list(es.cloned_box()),
      Uncons::DottedList(es, r) if es.is_empty() => r,
      Uncons::DottedList(es, r) => LispVal::dotted_list(es.cloned_box(), r),
    }
  }
}

impl Clone for Uncons {
  fn clone(&self) -> Self { Uncons::New(self.as_lisp()) }
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

  fn size_hint(&self) -> (usize, Option<usize>) {
    match self {
      Uncons::New(_) => (0, None),
      Uncons::List(es) => {let n = es.len(); (n, Some(n))}
      Uncons::DottedList(es, _) => (es.len(), None)
    }
  }

  fn count(self) -> usize { self.len() }
}

/// A `LispRemapper` is the context required to copy a foreign lisp environment into
/// the current environment. This is used to implement [`Environment::merge`],
/// used for `import` commands.
///
/// [`Environment::merge`]: ../environment/struct.Environment.html#method.merge
#[derive(Default, Debug)]
pub(crate) struct LispRemapper {
  /// A mapping of foreign atoms into local atom IDs
  pub(crate) atom: AtomVec<AtomID>,
  /// A mapping of foreign `FrozenLispVal`s into local `LispVal`s.
  /// It uses a pointer to the underlying allocation as an identifier so that
  /// we don't remap the same lisp values many times.
  pub(crate) lisp: HashMap<*const FrozenLispKind, LispVal>,
  /// A stack of references that are currently being constructed. It is stored
  /// as a hashmap, indexed on the source lisp ref-cell, for fast lookup.
  ///
  /// When a `Ref` is remapped, we initially create a `(ref! #undef)` and put it
  /// in `refs` (if it is not already present), then we remap the contents of
  /// the ref, and finally we assign the result to the ref we created and
  /// remove the newly assigned ref-cell from `refs`. That way, a mutable cell
  /// is remapped to another mutable cell, but we can detect cycles and correctly
  /// remap them into cycles.
  pub(crate) refs: HashMap<*const FrozenLispRef, LispVal>,
}
impl Remap<LispRemapper> for AtomID {
  type Target = Self;
  fn remap(&self, r: &mut LispRemapper) -> Self { *r.atom.get(*self).unwrap_or(self) }
}
impl<R, K: Clone + Hash + Eq, V: Remap<R>> Remap<R> for HashMap<K, V> {
  type Target = HashMap<K, V::Target>;
  fn remap(&self, r: &mut R) -> Self::Target { self.iter().map(|(k, v)| (k.clone(), v.remap(r))).collect() }
}
impl<R, A: Remap<R>> Remap<R> for RefCell<A> {
  type Target = RefCell<A::Target>;
  fn remap(&self, r: &mut R) -> Self::Target { RefCell::new(self.borrow().remap(r)) }
}
impl<R, A: Remap<R>> Remap<R> for Mutex<A> {
  type Target = Mutex<A::Target>;
  fn remap(&self, r: &mut R) -> Self::Target { Mutex::new(self.lock().unwrap().remap(r)) }
}
impl Remap<LispRemapper> for LispVal {
  type Target = Self;
  fn remap(&self, r: &mut LispRemapper) -> Self { unsafe { self.freeze() }.remap(r) }
}

impl Remap<LispRemapper> for InferTarget {
  type Target = Self;
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
  type Target = Self;
  fn remap(&self, r: &mut LispRemapper) -> Self {
    match self {
      ProcPos::Named(fsp, sp, a) => ProcPos::Named(fsp.clone(), *sp, a.remap(r)),
      ProcPos::Unnamed(fsp) => ProcPos::Unnamed(fsp.clone()),
    }
  }
}

impl Remap<LispRemapper> for Proc {
  type Target = Self;
  fn remap(&self, r: &mut LispRemapper) -> Self { unsafe { self.freeze() }.remap(r) }
}
