//! Implementation of the Scheme-like metaprogramming language of MM1.
//!
//! See [`mm1.md`] for a description of the MM1 metaprogramming language.
//!
//! [`mm1.md`]: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#evaluation

pub mod parser;
pub mod eval;
pub mod debug;
pub mod print;
pub mod pretty;

use std::ops::{Deref, DerefMut};
use std::hash::Hash;
use std::rc::{Rc, Weak};
use std::cell::{Cell, RefCell};
use std::sync::{Arc, Mutex};
use std::collections::HashMap;
use num::BigInt;
use crate::{ast::Atom, ArcString, AtomId, FileSpan, MergeStrategy, MergeStrategyInner, Modifiers,
  MutexExt, Remap, Remapper, SliceExt, Span, StackList};
use parser::Ir;
pub use super::math_parser::{QExpr, QExprKind};

macro_rules! str_enum {
  ($(#[$doc:meta])* enum $name:ident $($rest:tt)*) => {
    str_enum!{@inner
      concat!("Convert a `", stringify!($name), "` to a string."),
      concat!("Convert a string into a `", stringify!($name), "`."),
      concat!("Convert a byte string into a `", stringify!($name), "`.");
      $(#[$doc])* enum $name $($rest)*}
  };
  (@inner $to_str:expr, $from_str:expr, $from_bytes:expr;
      $(#[$doc:meta])* enum $name:ident {$($(#[doc=$doc2:expr])* $(#[cfg($($cfgs:tt)*)])* $e:ident: $s:expr,)*}) => {
    $(#[$doc])*
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub enum $name { $($(#[doc=$doc2])* $(#[cfg($($cfgs)*)])* $e),* }
    crate::deep_size_0!($name);

    impl $name {
      #[doc=$to_str]
      #[must_use] pub fn to_str(self) -> &'static str {
        match self {
          $($(#[cfg($($cfgs)*)])* Self::$e => $s),*
        }
      }
      #[doc=$to_str]
      #[must_use] pub fn to_byte_str(self) -> &'static [u8] {
        self.to_str().as_bytes()
      }
      #[doc=$from_str]
      #[allow(clippy::should_implement_trait)]
      #[must_use] pub fn from_str(s: &str) -> Option<Self> {
        match s {
          $($(#[cfg($($cfgs)*)])* $s => Some(Self::$e),)*
          _ => None
        }
      }
      #[doc=$from_bytes]
      #[must_use] pub fn from_bytes(s: &[u8]) -> Option<Self> {
        // Safety: the function we defined just above doesn't do anything
        // dangerous with the &str
        Self::from_str(unsafe { std::str::from_utf8_unchecked(s) })
      }

      /// Iterate over all the elements in the enum.
      pub fn for_each(mut f: impl FnMut(Self, &'static str)) {
        $($(#[cfg($($cfgs)*)])* {f(Self::$e, $s);})*
      }

      /// The documentation comment on this item.
      #[must_use] pub fn doc(self) -> &'static str {
        match self {
          $($(#[cfg($($cfgs)*)])* $name::$e => concat!($($doc2,"\n"),*)),*
        }
      }
    }
  }
}

str_enum! {
  /// The [`Syntax`] type represents atom-like objects that are considered keywords
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
    /// `begin`: a sequence of expressions
    Begin: "begin",
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
    /// `(set-merge-strategy foo strat)` will set the *merge strategy* for global definition `foo`
    /// to `strat`. This determines what happens when `foo` is declared twice, either explicitly or
    /// because the file containing the declaration of `foo` was imported twice in a diamond pattern.
    ///
    /// * The default strategy is `#undef`, which means that the new declaration will replace the old.
    /// * If a function `f` is passed as the strategy, it will be called as `(f old new)` where
    ///   `old` is the previous definition and `new` is the new definition, and the result of the function
    ///   will be what is stored.
    /// * A commonly useful strategy is `merge-map`, which will add any keys in `new` to `old`,
    ///   overwriting the originals but preserving any keys not in `new`.
    ///   * This can also be used as `(merge-map strat)` where `strat` is a subsidiary merge strategy.
    SetMergeStrategy: "set-merge-strategy",
  }
}

impl Syntax {
  /// Parse a string and atom type pair into a [`Syntax`].
  pub fn parse(s: &[u8], a: Atom) -> Result<Syntax, &[u8]> {
    match a {
      Atom::Ident => Syntax::from_bytes(s).ok_or(s),
      Atom::Quote => Ok(Syntax::Quote),
      Atom::Unquote => Ok(Syntax::Unquote),
      Atom::Nfx => Err(b":nfx"),
    }
  }
}

impl std::fmt::Display for Syntax {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.to_str().fmt(f)
  }
}

str_enum! {
  /// The [`PatternSyntax`] type represents additional syntax elements that are only parsed
  /// inside patterns.
  enum PatternSyntax {
    /// * `(mvar s bd)` matches a metavariable with sort `s` and boundedness `bd`
    ///   (see the arguments to `mvar!`)
    /// * `(mvar)` matches a metavariable with unconstrained target.
    /// * `(mvar ...)` with literal `...` will match either kind of metavariable.
    MVar: "mvar",
    /// `(goal p)` matches a goal with target `p`.
    Goal: "goal",
    /// `(and p1 ... pn)` will match the input against all the patterns `p1` through `pn`,
    /// and using all the resulting bindings. It succeeds if all the patterns match.
    And: "and",
    /// `(or p1 ... pn)` succeeds if any of the patterns match, and it uses all bindings from the
    /// successes. Results are unspecified if the patterns do not all bind the same variables.
    Or: "or",
    /// `(not p1 ... pn)` succeeds if none of the patterns match, and binds nothing.
    Not: "not",
    /// `(? pred p1 ... pn)` succeeds if all of the patterns `p1`, ..., `pn` match,
    /// and `(pred v)` evaluates to a truthy value where `v` is the value being matched.
    ///
    /// `pred` should evaluate to a unary predicate *in the context of the match expression*;
    /// bindings from the match are not available when the predicate is evaluated.
    Test: "?",
    /// `(cons p1 ... pn p)` or `(p1 ... pn . p)` ensures the input is a proper or improper list
    /// of length at least `n`, and matches the first `n` patterns with the `n` input values
    /// and matches the tail against the pattern `p`.
    Cons: "cons",
    /// `(p1 ... pn "...")` (with a literal `...` at the end) ensures the input is a proper list
    /// of length at least `n`, and matches the first `n` patterns with the `n` input values.
    /// You can also use `___` in place of `...`.
    Rest: "...",
    /// `(p1 ... pn __ k)`, where `k` is a number, ensures the input is a proper list
    /// of length at least `n + k`, and matches the first `n` patterns with the `n` input values.
    RestN: "__",
  }
}

str_enum! {
  /// The `RefineSyntax` type represents atom-like objects that are considered keywords
  /// in the refine tactic, and have special interpretations.
  enum RefineSyntax {
    /// `!`: A modifier on theorem application, for explicitly passing all variables
    /// (both bound and regular). For example, given
    /// ```metamath-zero
    /// axiom ax_gen {x: nat} (p: wff x): $ p $ > $ A. x p $;
    /// ```
    /// the application `(! ax_gen y $ 0 < 1 $ h)` is a proof of `$ A. y 0 < 1 $` if
    /// `h` is a proof of `$ 0 < 1 $`.
    Explicit: "!",
    /// `!!`: A modifier on theorem application, for explicitly passing all bound variables.
    /// For example, given
    /// ```metamath-zero
    /// axiom ax_gen {x: nat} (p: wff x): $ p $ > $ A. x p $;
    /// ```
    /// the application `(! ax_gen y h)` is a proof of `$ A. y ?p $` if
    /// `h` is a proof of `?p` for some expression `?p`.
    BoundOnly: "!!",
    /// `:verb`, for "verbatim": Interpolate an already elaborated proof term into a
    /// refine script. Elaborated proof terms have all arguments explicit, equivalent to `!`
    /// on every application, and also include terms for conversion proofs, whereas refine
    /// scripts can unfold definitions implicitly by unification.
    ///
    /// This construct is most useful for tactics, that produce full proofs but want to be
    /// interpolated into a user's refine script without re-interpreting the proof as a
    /// refine script. For example, `(:verb (a1i p q h))` is a proof of `$ p -> q $` if
    /// `h` proves `$ q $`, but simply `(a1i p q h)` is ill-formed because it has too many
    /// arguments; the equivalent refine script would be `(a1i h)` or `(! a1i p q h)` where
    /// the former performs unification to find `p` and `q`.
    ///
    /// *Warning*: `refine` will perform no unification on verbatim proofs, so it is possible
    /// to give ill formed terms to `refine` this way. The error resulting from this will
    /// not be caught until the theorem is finalized, possibly long after the bad `refine`
    /// call, leading to a poor user experience. So tactic authors should be careful not
    /// to supply bad proofs.
    Verb: ":verb",
    /// The expression `{p : $ t $}` asserts that the current goal is `$ t $`, where `p` is
    /// the proof. Besides the documentation use of asserting what the statement to be proved
    /// is, this can also be used to unify metavariables in the goal, as well as force unfolding
    /// or re-folding of definitions. In any case, `p` will be elaborated with goal exactly `t`
    /// regardless of the original goal.
    Typed: ":",
  }
}

/// The type of a metavariable. This encodes the different types of context
/// in which a term is requested.
#[derive(Copy, Clone, Debug, EnvDebug)]
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
  Bound(AtomId),
  /// This is a metavariable for an expression of sort `s`. For example, if
  /// `term all {x: var}: wff x > wff;`, in `all x _` the `_` has type `wff`
  /// and can be any expression of that sort.
  Reg(AtomId),
}
crate::deep_size_0!(InferTarget);

impl InferTarget {
  /// The target sort of a metavariable. Returns [`None`] if the sort is unknown.
  #[must_use] pub fn sort(self) -> Option<AtomId> {
    match self {
      InferTarget::Bound(s) | InferTarget::Reg(s) => Some(s),
      _ => None
    }
  }
  /// Returns true if the metavariable must be a bound variable.
  #[must_use] pub fn bound(self) -> bool { matches!(self, InferTarget::Bound(_)) }
}

/// A lisp value. These are the "values" that are passed around by lisp code.
/// See [`LispKind`] for the list of different types of lisp object. This is
/// a wrapper around `Rc<LispKind>`, and it is cloned frequently in client code.
#[derive(Default, Debug, EnvDebug, Clone)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct LispVal(Rc<LispKind>);

/// This macro is used to define the [`LispKind`] type, as well as the
/// [`FrozenLispKind`] type, to ensure that they have the same representation
/// and can be safely transmuted.
///
/// [`FrozenLispKind`]: super::frozen::FrozenLispKind
#[macro_export]
macro_rules! mk_lisp_kind {
  ($(#[$doc:meta])* $kind:ident, $val:ident, $ref_:ident, $proc:ident) => {
    $(#[$doc])*
    #[derive(Debug)]
    #[cfg_attr(feature = "memory", derive(DeepSizeOf))]
    pub enum $kind {
      /// An atom like `'foo`. Atoms are internally represented as small integers,
      /// so equality comparison on atoms is fast.
      Atom(AtomId),
      /// A list of values. In lisp, this is semantically an iterated cons,
      /// `(a b c d) = (a . (b . (c . (d . ()))))`, and we don't provide any
      /// functions that distinguish these, but because lists are so common
      /// in lisp code we use arrays for this.
      List(Box<[$val]>),
      /// An improper or dotted list of values, `(a b c . d) = (a . (b . (c . d)))`.
      /// As with [`List`](Self::List), we chunk several cons cells into one array. We do not make
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
      /// A map from atoms to values. This can be used as a mutable map if it is behind a
      /// [`Ref`](Self::Ref).
      AtomMap(HashMap<AtomId, $val>),
      /// A mutable reference. This is the only way to have mutable values in
      /// client code.
      Ref($ref_),
      /// A metavariable. The `usize` gives the index of the metavariable in the
      /// local context, and the [`InferTarget`] is the expected type of the expression
      /// that should replace this metavariable.
      MVar(usize, InferTarget),
      /// A proof metavariable, also known as a goal. The argument is the expected
      /// theorem statement.
      Goal($val),
    }
  }
}
mk_lisp_kind! {
  /// The underlying enum of types of lisp data.
  #[derive(EnvDebug)]
  LispKind,
  LispVal,
  LispRef,
  Proc
}

impl LispVal {
  /// Make a [`LispVal`] from the inner enum type [`LispKind`].
  #[must_use] pub fn new(e: LispKind) -> LispVal { LispVal(Rc::new(e)) }
  /// Construct a [`LispVal`] for an atom.
  #[must_use] pub fn atom(a: AtomId) -> LispVal { LispVal::new(LispKind::Atom(a)) }
  /// Construct a [`LispVal`] for a list.
  #[must_use] pub fn list(es: impl Into<Box<[LispVal]>>) -> LispVal { LispVal::new(LispKind::List(es.into())) }
  /// Construct a [`LispVal`] for an improper list.
  #[must_use] pub fn dotted_list(es: impl Into<Box<[LispVal]>>, r: LispVal) -> LispVal {
    LispVal::new(LispKind::DottedList(es.into(), r))
  }
  /// Construct a [`LispVal`] for an improper list.
  #[must_use] pub fn number(n: BigInt) -> LispVal { LispVal::new(LispKind::Number(n)) }
  /// Construct a [`LispVal`] for a string.
  #[must_use] pub fn string(s: ArcString) -> LispVal { LispVal::new(LispKind::String(s)) }
  /// Construct a [`LispVal`] for a syntax element.
  #[must_use] pub fn syntax(s: Syntax) -> LispVal { LispVal::new(LispKind::Syntax(s)) }
  /// Construct a [`LispVal`] for `#undef`.
  #[must_use] pub fn undef() -> LispVal { LispVal::new(LispKind::Undef) }
  /// Construct a [`LispVal`] for `()`.
  #[must_use] pub fn nil() -> LispVal { LispVal::list(vec![]) }
  /// Construct a [`LispVal`] for a boolean.
  #[must_use] pub fn bool(b: bool) -> LispVal { LispVal::new(LispKind::Bool(b)) }
  /// Construct a [`LispVal`] for a procedure.
  #[must_use] pub fn proc(p: Proc) -> LispVal { LispVal::new(LispKind::Proc(p)) }
  /// Construct a [`LispVal`] for a mutable reference.
  #[must_use] pub fn new_ref(e: LispVal) -> LispVal { LispRef::new_as_val(LispWeak::Strong(e)) }
  /// Construct a [`LispVal`] for a weak reference.
  #[must_use] pub fn weak_ref(e: &LispVal) -> LispVal { LispRef::new_as_val(LispWeak::Weak(Rc::downgrade(&e.0))) }
  /// Construct a [`LispVal`] for a goal.
  #[must_use] pub fn goal(fsp: FileSpan, ty: LispVal) -> LispVal {
    LispVal::new(LispKind::Goal(ty)).span(fsp)
  }

  /// Annotate this object with a file span.
  #[must_use] pub fn span(self, fsp: FileSpan) -> LispVal {
    LispVal::new(LispKind::Annot(Annot::Span(fsp), self))
  }

  /// Make a copy of this object with the given span,
  /// replacing the existing one if it has one.
  #[must_use] pub fn replace_span(&self, fsp: FileSpan) -> LispVal {
    match &**self {
      LispKind::Annot(_, v) => v.replace_span(fsp),
      _ => self.clone().span(fsp)
    }
  }

  /// Get a mutable reference to the inner [`LispKind`], if possible, returning
  /// [`None`] if the value is shared and calling `f` with the inner reference if
  /// there is only one owner.
  pub fn unwrapped_mut<T>(&mut self, f: impl FnOnce(&mut LispKind) -> T) -> Option<T> {
    Rc::get_mut(&mut self.0).and_then(|e| match e {
      LispKind::Ref(m) => m.get_mut(|e| Self::unwrapped_mut(e, f)),
      LispKind::Annot(_, v) => Self::unwrapped_mut(v, f),
      _ => Some(f(e))
    })
  }

  /// Traverse past any [`Annot`](LispKind::Annot) and [`Ref`](LispKind::Ref) nodes,
  /// and return a clone of the inner data.
  #[must_use] pub fn unwrapped_arc(&self) -> LispVal {
    match &**self {
      LispKind::Ref(m) => m.get(Self::unwrapped_arc),
      LispKind::Annot(_, v) => Self::unwrapped_arc(v),
      _ => self.clone()
    }
  }

  /// Returns true if this is a clone of `e`.
  #[must_use] pub fn ptr_eq(&self, e: &Self) -> bool { Rc::ptr_eq(&self.0, &e.0) }
  /// Try to get at the inner data, if this value is not shared,
  /// otherwise return self.
  pub fn try_unwrap(self) -> Result<LispKind, LispVal> { Rc::try_unwrap(self.0).map_err(LispVal) }
  /// Try to get a mutable reference to the inner data, if this value is not shared.
  #[must_use] pub fn get_mut(&mut self) -> Option<&mut LispKind> { Rc::get_mut(&mut self.0) }

  /// Try to get a mutable reference to the inner data,
  /// unwrapping any [`Annot`](LispKind::Annot) and [`Ref`](LispKind::Ref) nodes,
  /// if this value is not shared.
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
        LispKind::List(es) => {vec.extend_from_slice(es); return false},
        LispKind::DottedList(es, r) => {
          vec.extend_from_slice(es);
          n -= es.len();
          self = r.clone()
        }
        _ => return false
      }
    }
  }

  /// Get the head of the cons cell, if it is one.
  #[must_use] pub fn head(&self) -> Option<LispVal> {
    self.unwrapped(|e| match e {
      LispKind::List(es) => es.first().cloned(),
      LispKind::DottedList(es, r) => es.first().cloned().or_else(|| r.head()),
      _ => None
    })
  }

  /// Make a [`MergeStrategy`] from a lisp value. (This is a best effort attempt to
  /// recognize the `#undef` and `merge-map` merge strategies, with everything else
  /// counted as [`Custom`](MergeStrategyInner::Custom).)
  #[must_use] pub fn into_merge_strategy(self) -> MergeStrategy {
    self.unwrapped(|e| match e {
      LispKind::Undef => Some(None),
      LispKind::Proc(Proc::Builtin(BuiltinProc::MergeMap)) =>
        Some(Some(Rc::new(MergeStrategyInner::AtomMap(None)))),
      LispKind::Proc(Proc::MergeMap(strat)) =>
        Some(Some(Rc::new(MergeStrategyInner::AtomMap(strat.clone())))),
      _ => None,
    }).unwrap_or_else(|| Some(Rc::new(MergeStrategyInner::Custom(self))))
  }
}

impl Deref for LispVal {
  type Target = LispKind;
  fn deref(&self) -> &LispKind { &self.0 }
}

impl PartialEq<LispVal> for LispVal {
  fn eq(&self, other: &LispVal) -> bool {
    self.ptr_eq(other) || **self == **other
  }
}
impl Eq for LispVal {}

#[derive(Default)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub(crate) struct LispArena(typed_arena::Arena<Weak<LispKind>>);

thread_local!(static REFS: Cell<Option<*const LispArena>> = Cell::new(None));

impl LispArena {
  pub(crate) fn install_thread_local(&self) { REFS.with(|refs| refs.set(Some(self))) }
  pub(crate) fn uninstall_thread_local() { REFS.with(|refs| refs.set(None)) }

  #[allow(clippy::unused_self)]
  pub(crate) fn clear(self) {
    // for e in self.0.iter_mut() {
      // if let Some(e) = e.upgrade() { e.as_ref_(|r| *r = LispVal::undef()); }
    // }
  }
}

impl std::fmt::Debug for LispArena {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "LispArena") }
}

/// The target of a reference can be either a weak reference or a strong reference.
/// Weak references are used to break cycles.
#[derive(Debug, EnvDebug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum LispWeak {
  /// A regular (strong) reference.
  Strong(LispVal),
  /// A weak reference, generated via `(set-weak!)` or function references in a `letrec`.
  Weak(Weak<LispKind>),
}

impl LispWeak {
  fn get<T>(&self, f: impl FnOnce(&LispVal) -> T) -> T {
    match self {
      LispWeak::Strong(e) => f(e),
      LispWeak::Weak(e) => match e.upgrade() {
        None => f(&LispVal::undef()),
        Some(e) => f(&LispVal(e))
      }
    }
  }
  fn get_mut<T>(&mut self, f: impl FnOnce(&mut LispVal) -> T) -> T {
    match self {
      LispWeak::Strong(e) => f(e),
      LispWeak::Weak(e) => {
        let e = match e.upgrade() {
          None => LispVal::undef(),
          Some(e) => LispVal(e)
        };
        *self = LispWeak::Strong(e);
        let LispWeak::Strong(e) = self else { unreachable!() };
        f(e)
      }
    }
  }
  fn upgrade(self) -> LispVal {
    match self {
      Self::Weak(e) => match e.upgrade() {
        None => LispVal::undef(),
        Some(e) => LispVal(e)
      }
      Self::Strong(e) => e
    }
  }

  /// # Safety
  /// If the pointer is a weak pointer it must point to valid memory
  pub(crate) unsafe fn map_unsafe(&self, f: impl FnOnce(&LispKind) -> LispVal) -> LispWeak {
    match self {
      LispWeak::Strong(e) => LispWeak::Strong(f(e)),
      LispWeak::Weak(e) if e.strong_count() == 0 => LispWeak::Weak(Weak::new()),
      // Safety: The pointer must be valid
      LispWeak::Weak(e) => LispWeak::Weak(Rc::downgrade(&f(unsafe { &*e.as_ptr() }).0)),
    }
  }
}
/// A mutable reference to a [`LispVal`], the inner type used by `ref!` and related functions.
#[derive(Debug, EnvDebug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct LispRef(RefCell<LispWeak>);

impl LispRef {
  /// Construct a [`LispVal`] for a mutable reference.
  fn new_as_val(w: LispWeak) -> LispVal {
    LispVal::new(LispKind::Ref(LispRef(RefCell::new(w))))
    // REFS.with(|refs| {unsafe{&*refs.get().unwrap()}.0.alloc(Rc::downgrade(&r.0));});
  }
  /// Get a reference to the stored value.
  pub fn get<T>(&self, f: impl FnOnce(&LispVal) -> T) -> T {
    self.0.borrow().get(f)
  }
  /// Get a mutable reference to the stored value.
  pub fn get_mut<T>(&self, f: impl FnOnce(&mut LispVal) -> T) -> T {
    self.0.borrow_mut().get_mut(f)
  }
  /// Get a reference to the stored value.
  pub fn get_weak(&self) -> impl Deref<Target=LispWeak> + '_ {
    self.0.try_borrow().unwrap_or_else(|_| {
      panic!("not frozen")
    })
  }
  /// Attempt to mutate the stored value, or return `None`.
  pub fn try_get_mut<T>(&self, f: impl FnOnce(&mut LispVal) -> T) -> Option<T> {
    Some(self.0.try_borrow_mut().ok()?.get_mut(f))
  }
  /// Get a mutable reference to the stored value.
  pub fn get_mut_weak(&self) -> impl DerefMut<Target=LispWeak> + '_ { self.0.borrow_mut() }
  /// Set this reference to a weak reference to `e`.
  pub fn set_weak(&self, e: &LispVal) {
    *self.0.borrow_mut() = LispWeak::Weak(Rc::downgrade(&e.0))
  }
  /// Get a clone of the stored value.
  pub fn unref(&self) -> LispVal { self.get(Clone::clone) }
  /// Consume the reference, yielding the stored value.
  pub fn into_inner(self) -> LispVal { self.0.into_inner().upgrade() }

  /// Returns true if this refcell has suspciously many readers
  pub(crate) fn too_many_readers(&self) -> bool {
    struct RefCell2<T: ?Sized> {
      borrow: Cell<isize>,
      _value: std::cell::UnsafeCell<T>,
    }
    // Safety: This ties us to the representation of RefCell, but I don't think
    // that is going to change.
    unsafe { &*<*const _>::cast::<RefCell2<LispWeak>>(&self.0) }.borrow.get() > 30
  }

  /// Get the value of this reference without changing the reference count.
  /// # Safety
  /// This function should not be used unless the value is frozen
  /// (in which case you should use [`FrozenLispRef::get`] instead).
  ///
  /// [`FrozenLispRef::get`]: super::frozen::FrozenLispRef::get
  pub(crate) unsafe fn get_unsafe(&self) -> Option<&LispKind> {
    // Safety: we can't modify the borrow flag because the data is frozen
    match unsafe { self.0.try_borrow_unguarded() }.unwrap_or_else(|_| {
      std::sync::atomic::fence(std::sync::atomic::Ordering::SeqCst);
      // Safety: we can't modify the borrow flag because the data is frozen
      unsafe { self.0.try_borrow_unguarded() }.expect("could not deref refcell")
    }) {
      LispWeak::Strong(e) => Some(e),
      LispWeak::Weak(e) if e.strong_count() == 0 => None,
      // Safety: `LispWeak` are null or valid so `as_ptr` is safe
      LispWeak::Weak(e) => Some(unsafe { &*e.as_ptr() })
    }
  }
}

impl PartialEq<LispRef> for LispRef {
  fn eq(&self, other: &LispRef) -> bool { self.get(|a| other.get(|b| *a == *b)) }
}
impl Eq for LispRef {}

impl From<&LispKind> for bool {
  fn from(e: &LispKind) -> bool { e.truthy() }
}

impl LispKind {
  /// Unwrap [`Ref`](Self::Ref) and [`Annot`](Self::Annot) nodes,
  /// which are ignored by most lisp primitives, and run `f`
  /// with a reference to the inner value.
  /// (We can't directly return the value because the lifetime is too short.)
  /// See also [`LispVal::unwrapped_arc`], which returns a clone of the inner value.
  pub fn unwrapped<T>(&self, f: impl FnOnce(&Self) -> T) -> T {
    fn rec<T>(e: &LispKind, stack: StackList<'_, *const LispRef>, f: impl FnOnce(&LispKind) -> T) -> T {
      match e {
        LispKind::Ref(m) if !stack.contains(&(m as *const _)) => m.get(|e| rec(e, StackList(Some(&(stack, m))), f)),
        LispKind::Annot(_, v) => rec(v, stack, f),
        _ => f(e)
      }
    }
    rec(self, StackList(None), f)
  }

  /// Unwrap [`Ref`](Self::Ref) and [`Annot`](Self::Annot) nodes,
  /// collecting a span if one is found along the way,
  /// and run `f` with a reference to the inner value and the span.
  /// `fsp` is used as the default value if no span was found.
  pub fn unwrapped_span<T>(&self, fsp: Option<&FileSpan>,
      f: impl FnOnce(Option<&FileSpan>, &Self) -> T) -> T {
    fn rec<T>(e: &LispKind,
      stack: StackList<'_, *const LispRef>,
      fsp: Option<&FileSpan>,
      f: impl FnOnce(Option<&FileSpan>, &LispKind) -> T
    ) -> T {
      match e {
        LispKind::Ref(m) if !stack.contains(&(m as *const _)) =>
          m.get(|e| rec(e, StackList(Some(&(stack, m))), fsp, f)),
        LispKind::Annot(Annot::Span(fsp), v) => rec(v, stack, Some(fsp), f),
        _ => f(fsp, e)
      }
    }
    rec(self, StackList(None), fsp, f)
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
  pub fn as_atom(&self) -> Option<AtomId> {
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
  pub fn as_lref<T>(&self, f: impl FnOnce(&LispRef) -> T) -> Option<T> {
    match self {
      LispKind::Ref(m) => Some(f(m)),
      LispKind::Annot(_, e) => e.as_lref(f),
      _ => None
    }
  }
  /// Get a mutable reference to the value stored by the reference, if it is one.
  pub fn as_ref_<T>(&self, f: impl FnOnce(&mut LispVal) -> T) -> Option<T> {
    self.as_lref(|m| m.get_mut(f))
  }

  /// Get a file span annotation associated to a lisp value, if possible.
  pub fn fspan(&self) -> Option<FileSpan> {
    match self {
      LispKind::Ref(m) => m.get(|e| e.fspan()),
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

  /// Puts a span on this value, if `fsp` is not [`None`].
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
            (Some(e), None) => break r2.eq_list(std::iter::once(e).chain(it1)),
            (None, Some(e)) => break r1.eq_list(std::iter::once(e).chain(it2)),
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
#[derive(Clone, Debug, EnvDebug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum Annot {
  /// A span annotation marks an expression with a span from the input file.
  /// The parser will place these on all expressions it produces, and they are
  /// used to guide error reporting, but they can also be transferred to other
  /// expressions in client code using [`(copy-span)`].
  ///
  /// [`(copy-span)`]: BuiltinProc::CopySpan
  Span(FileSpan),
}

/// The location information for a procedure.
#[derive(Clone, Debug, EnvDebug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum ProcPos {
  /// A named procedure is created by `(def (foo x) ...)` or
  /// `(def foo (fn (x) ...))`. The file span is the definition block
  /// that created it, while the span is just the span of the name
  /// of the function, in this case `foo` (in the same file).
  Named(FileSpan, Span, AtomId),
  /// An unnamed procedure is a lambda like `(fn (x) ...)` that is not
  /// immediately bound to a name. It is associated only with its span
  /// in the file.
  Unnamed(FileSpan),
  /// A builtin procedure.
  Builtin(BuiltinProc),
}

impl ProcPos {
  /// Get the file span for a procedure.
  fn fspan(&self) -> Option<&FileSpan> {
    match self {
      ProcPos::Named(fsp, _, _) | ProcPos::Unnamed(fsp) => Some(fsp),
      ProcPos::Builtin(_) => None,
    }
  }
}

/// A callable procedure. There are several sources of procedures,
/// all of which are interactable only via function calls `(f)` and
/// printing (which shows only basic information about the procedure).
#[derive(Debug, EnvDebug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
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
    code: Arc<[Ir]>
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
  /// inside a limited extent, but unlike [`MatchCont`](Self::MatchCont),
  /// there cannot be multiple refine callbacks simultaneously in flight -
  /// a call to the refine callback binds to the nearest enclosing `refine` call.
  RefineCallback,
  /// A partially applied `(merge-map f)` invocation.
  MergeMap(MergeStrategy),
  /// A delayed proof, generated by a call to `get-decl`, which returns a lisp
  /// data structure reflecting the requested definition, but delays the proof
  /// unless forced by calling this thunk. The unevaluated form of the thunk
  /// stores `Err(args)`, where `args` is the list of variables, while the
  /// evaluated form stores `Ok(proof)`.
  ProofThunk(AtomId, RefCell<Result<LispVal, Box<[LispVal]>>>),
  /// The compiler object, which can be called as a procedure and stores its own
  /// internal state here. See [`Compiler::call`].
  ///
  /// [`Compiler::call`]: crate::mmc::Compiler::call
  Dyn(RefCell<Box<dyn LispProc>>) // TODO: use extern instead
}

/// A procedure specification, which defines the number of arguments expected
/// by the call. Individual procedures may have additional rules on top of
/// this for validity, but every procedure must declare its specification
/// in [`Proc::spec`].
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
  #[must_use] pub fn valid(self, i: usize) -> bool {
    match self {
      ProcSpec::Exact(n) => i == n,
      ProcSpec::AtLeast(n) => i >= n,
    }
  }

  fn arity_error(self) -> String {
    match self {
      ProcSpec::Exact(n) => format!("expected {n} argument(s)"),
      ProcSpec::AtLeast(n) => format!("expected at least {n} argument(s)"),
    }
  }
}

impl Proc {
  /// Returns the specification (number of expected arguments) for a procedure.
  #[allow(clippy::match_same_arms)]
  pub fn spec(&self) -> ProcSpec {
    match self {
      Proc::Builtin(p) => p.spec(),
      &Proc::Lambda {spec, ..} => spec,
      Proc::MatchCont(_) |
      Proc::ProofThunk(_, _) => ProcSpec::AtLeast(0),
      Proc::MergeMap(_) => ProcSpec::Exact(2),
      Proc::RefineCallback => ProcSpec::AtLeast(1),
      Proc::Dyn(proc) => proc.borrow().spec(),
    }
  }
}

str_enum! {
  /// The set of built in procedures. These each have names that can be shadowed
  /// but not overridden by global names in the environment.
  enum BuiltinProc {
    /// `display` takes a string and prints it. In the interactive editor mode,
    /// this appears as an info diagnostic over the word "`display`".
    /// ```metamath-zero
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
    /// `{a ^ b}` computes `a` to the power of `b`. It gives an error if `b` is negative.
    /// Additional arguments are right associative.
    Pow: "^",
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
    /// `{a shl b}` performs a left shift `a << b`, equivalent to `a * 2 ^ b`.
    /// Negative `b` causes a right shift. Additional arguments are left associative;
    /// `3 << -1 << 1 = 2`.
    Shl: "shl",
    /// `{a shr b}` performs a right shift `a >> b`, equivalent to `a // 2 ^ b`.
    /// Negative `b` causes a left shift. Additional arguments are left associative;
    /// `3 >> 1 >> -1 = 2`.
    Shr: "shr",
    /// `{a band b band ...}` performs a bitwise AND of the arguments.
    BAnd: "band",
    /// `{a bor b bor ...}` performs a bitwise OR of the arguments.
    BOr: "bor",
    /// `{a bxor b bxor ...}` performs a bitwise XOR of the arguments.
    BXor: "bxor",
    /// `(bnot a)` performs a bitwise NOT of the argument; additional arguments act like NAND.
    BNot: "bnot",
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
    /// ```metamath-zero
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
    /// ```metamath-zero
    /// (string->atom "foo")         -- foo
    /// (string->atom "foo$bar baz") -- foo$bar baz
    /// ```
    StringToAtom: "string->atom",
    /// `(string-append s1 s2 s3)` stringifies and appends all the inputs.
    /// ```metamath-zero
    /// (string-append "foo" 'bar 42) -- "foobar42"
    /// ```
    StringAppend: "string-append",
    /// `(string-len s)` returns the length of the string (number of bytes).
    /// ```metamath-zero
    /// (string-len "foo") -- 3
    /// ```
    StringLen: "string-len",
    /// `(string-nth n s)` returns the character code of the nth byte (zero-indexed) in the string.
    /// ```metamath-zero
    /// (string-nth 1 "bar") -- 97, ascii 'a'
    /// ```
    StringNth: "string-nth",
    /// `(substr start end s)` returns a newly allocated substring `s[start..end]`, the substring
    /// starting at `start` (inclusive) and ending at `end` (exclusive), where
    /// `0 <= start <= end <= (string-len s)`.
    /// ```metamath-zero
    /// (substr 6 11 "hello world!") -- "world"
    /// ```
    Substr: "substr",
    /// `(string->list s)` converts a string to a list of character codes.
    /// ```metamath-zero
    /// (string->list "bar") -- (98 97 114)
    /// ```
    StringToList: "string->list",
    /// `(list->string s)` constructs a string from a list of character codes.
    /// ```metamath-zero
    /// (list->string '(98 97 114)) -- "bar"
    /// ```
    ListToString: "list->string",
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
    /// `(set-weak! r v)` sets the value of the ref-cell `r` to a weak reference to `v`.
    /// It returns (a strong reference to) `v`.
    SetWeak: "set-weak!",
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
    /// This function is intended for use in `set-merge-strategy`, and will merge atom-maps.
    ///
    /// * `(merge-map old new)` will add all keys in the atom-map `new` to `old`, returning
    ///   a composite map. If `old` is a mutable atom-map, it will be modified and returned,
    ///   otherwise if `old` is an immutable atom-map, a new immutable atom-map will be returned.
    /// * `(merge-map f old new)` or `((merge-map f) old new)` will use
    ///   `(f oldval newval)` to resolve keys that are present in both maps.
    MergeMap: "merge-map",
    /// `(set-timeout n)` sets the timeout for running individual theorems and
    /// `do` blocks to `n` milliseconds. The default is 5 seconds.
    SetTimeout: "set-timeout",
    /// `(set-stack-limit n)` sets the maximum number of stack frames used during
    /// evaluation of theorems and `do` blocks to `n`. The default is 1024.
    SetStackLimit: "set-stack-limit",
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
    /// ```metamath-zero
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
    /// `(infer-sort e)` returns the sort and boundedness of the expression.
    InferSort: "infer-sort",
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
    /// * `(get-doc 'sort x)` returns the documentation comment on sort `x`.
    /// * `(get-doc 'term x)` returns the documentation comment on term/def/axiom/theorem `x`.
    /// * `(get-doc 'lisp x)` returns the documentation comment on lisp declaration `x`.
    /// * `(get-doc x)` returns the documentation comment on an item named `x`
    ///   (prefers lisp items, then declarations, then sorts).
    GetDoc: "get-doc",
    /// * `(set-doc! x "doc")` sets the documentation comment on item `x` to `"doc"`
    ///   (prefers lisp items, then declarations, then sorts).
    /// * `(set-doc 'sort x "doc")` sets the documentation comment on sort `x`.
    /// * `(set-doc 'term x "doc")` sets the documentation comment on term/def/axiom/theorem `x`.
    /// * `(set-doc 'lisp x "doc")` sets the documentation comment on lisp declaration `x`.
    SetDoc: "set-doc!",
    /// * `(dummy! x s)` produces a new dummy variable called `x` with sort `s`, and returns `x`;
    /// * `(dummy! s)` automatically gives the variable a name like `_123` that is guaranteed to be unused.
    NewDummy: "dummy!",
    /// `(check-proofs b)` turns on (`b = #t`) or off (`b = #f`) proof checking for theorems.
    /// Enabled by default.
    CheckProofs: "check-proofs",
    /// `(warn-unnecessary-parens b)` turns on (`b = #t`) or off (`b = #f`)
    /// the warning for using unnecessary parentheses in math expressions.
    /// Disabled by default.
    WarnUnnecessaryParens: "warn-unnecessary-parens",
    /// `(warn-unused-vars b)` turns on (`b = #t`) or off (`b = #f`)
    /// the warning for unused variables in definitions and theorems.
    /// Enabled by default.
    WarnUnusedVars: "warn-unused-vars",
    /// * `(set-reporting type b)` turns on (`b = #t`) or off (`b = #f`)
    ///   error reporting for error type `type`, which can be `'error`, `'info` or `'warn`.
    ///   (Compilation will still be aborted if there are errors, even if the
    ///   display is suppressed.)
    /// * `(set-reporting b)` will set the error reporting to `b` for all error types.
    SetReporting: "set-reporting",
    /// * `(set-backtrace b)` turns on (`b = #t`) or off (`b = #f`) backtraces in lisp for theorems.
    /// * `(set-backtrace type b)` does the same but for specific error type `type`,
    ///   which can be `'error`, `'info` or `'warn`.
    SetBacktrace: "set-backtrace",
    /// `refine-extra-args` can be called directly, but it simply returns an error. It is called
    /// by `refine` when elaborating a term with too many arguments, and is expected to be
    /// overridden by user code to provide a more useful behavior.
    RefineExtraArgs: "refine-extra-args",
    /// `(eval-string e1 e2 ...)` takes as input zero or more expressions which are elaborated
    /// as type `string`, and then evaluates them to an actual lisp string. This has the same
    /// effect as the top level command `output string: e1 e2 ...;` but this command is only
    /// triggered on a compile, while `eval-string` works also in server mode.
    EvalString: "eval-string",
    /// `(mmc-init)` returns a new compiler object, which is itself a procedure that can
    /// be called to compile MMC functions. See [`Compiler::call`].
    ///
    /// [`Compiler::call`]: crate::mmc::Compiler::call
    #[cfg(feature = "mmc")]
    MmcInit: "mmc-init",
  }
}

impl std::fmt::Display for BuiltinProc {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.to_str().fmt(f)
  }
}

macro_rules! def_lisp_proc {
  ($($extra:path)?) => {
    /// A trait for external objects that can be called like functions.
    pub trait LispProc:
      std::fmt::Debug + crate::EnvDebug + crate::EnvDisplay $(+ $extra)?
    {
      /// Returns the procedure specification (number of arguments).
      /// `call` is guaranteed to be called only with `args` matching this specification.
      fn spec(&self) -> ProcSpec;

      /// Call the function object, given mutable access to its own state,
      /// as well as the elaborator state. The span and function arguments are also passed.
      fn call(&mut self,
        elab: &mut crate::Elaborator, sp: Span, args: Vec<LispVal>
      ) -> super::Result<LispVal>;

      /// Morally `LispProc: Remap<Target=Self>`, but this would make the trait not object-safe
      /// so we have to provide the remap function via an indirection here.
      /// The implementation should just be `Box::new(self.remap(r))`.
      fn box_remap(&self, r: &mut Remapper) -> Box<dyn LispProc>;
    }
  }
}

#[cfg(feature = "memory")] def_lisp_proc! { mm0_deepsize::DeepSizeOf }
#[cfg(not(feature = "memory"))] def_lisp_proc! {}

impl Remap for Box<dyn LispProc> {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self::Target { self.box_remap(r) }
}

/// An iterator over lisp values, for dealing with lists. Semantically this is
/// the same as a [`LispVal`], but in order to decrease allocations this allows
/// holding on to incomplete subparts of the arrays used in [`LispKind::List`]
/// and [`LispKind::DottedList`].
#[must_use] #[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Uncons {
  /// The initial state, pointing to a lisp value.
  e: LispVal,
  /// A reference to a sub-slice of a [`LispKind::List`] or [`LispKind::DottedList`].
  /// (It is an invariant of the type that if `offset` is nonzero then `e` is
  /// directly a `List(es)` or `DottedList(es, _)`, not a `Ref` or `Annot` thereof,
  /// and `offset <= es.len()`.)
  offset: u32,
}

impl From<LispVal> for Uncons {
  fn from(e: LispVal) -> Uncons { Uncons::new(e) }
}

impl Uncons {
  /// Create a new [`Uncons`] to destruct a [`LispVal`].
  pub fn new(e: LispVal) -> Uncons { Uncons { e, offset: 0 } }

  /// Create an empty [`Uncons`].
  pub fn nil() -> Uncons { Uncons::new(LispVal::nil()) }

  /// Returns true if this is a proper list of length `n`.
  #[must_use] pub fn exactly(&self, n: usize) -> bool {
    self.e.exactly(n + self.offset as usize)
  }

  /// Reconstruct a file span for an [`Uncons`]. Note that this may not be a well formed
  /// substring, for example in `(a b c)` after the first iteration the span will refer
  /// to `b c)` and at the last iteration the span will cover only `)`.
  #[must_use] pub fn fspan(&self) -> Option<FileSpan> {
    if self.offset == 0 { return self.e.fspan() }
    match &*self.e {
      LispKind::DottedList(es, r) if es.len() == self.offset as usize => r.fspan(),
      LispKind::List(es) |
      LispKind::DottedList(es, _) => self.e.fspan().map(|mut fsp| {
        fsp.span.start = match es[self.offset as usize..].last().and_then(|e| e.fspan()) {
          Some(fsp2) => fsp2.span.start,
          None => fsp.span.end.saturating_sub(1),
        };
        fsp
      }),
      _ => self.e.fspan(),
    }
  }

  /// Convert an [`Uncons`] back into a [`LispVal`].
  #[must_use] pub fn as_lisp(&self) -> LispVal {
    if self.offset == 0 { return self.e.clone() }
    match &*self.e {
      LispKind::List(es) =>
        LispKind::List(es[self.offset as usize..].cloned_box()).decorate_span(&self.fspan()),
      LispKind::DottedList(es, r) if es.len() == self.offset as usize => r.clone(),
      LispKind::DottedList(es, r) =>
        LispKind::DottedList(es[self.offset as usize..].cloned_box(), r.clone())
          .decorate_span(&self.fspan()),
      _ => self.e.clone(),
    }
  }

  /// Returns true if this is `()`.
  #[must_use] pub fn is_empty(&self) -> bool { self.exactly(0) }

  /// Returns true if this is a proper or improper list of length at least `n`.
  #[must_use] pub fn at_least(&self, n: usize) -> bool {
    n == 0 || match &*self.e {
      LispKind::List(es) => es.len() >= n + self.offset as usize,
      LispKind::DottedList(es, r) =>
        (n + self.offset as usize).checked_sub(es.len()).map_or(true, |i| r.at_least(i)),
      _ => self.e.at_least(n),
    }
  }

  /// Returns true if this is a proper list of length at least `n`.
  #[must_use] pub fn list_at_least(&self, n: usize) -> bool {
    n == 0 || match &*self.e {
      LispKind::List(es) => es.len() >= n + self.offset as usize,
      LispKind::DottedList(es, r) =>
        (n + self.offset as usize).checked_sub(es.len()).map_or(true, |i| r.list_at_least(i)),
      _ => self.e.list_at_least(n),
    }
  }

  /// Gets the length of the list-like prefix of this value,
  /// i.e. the number of cons-cells along the right spine before reaching something else.
  #[must_use] pub fn len(&self) -> usize {
    match &*self.e {
      LispKind::List(es) => es.len() - self.offset as usize,
      LispKind::DottedList(es, r) => (es.len() - self.offset as usize) + r.len(),
      _ => self.e.len(),
    }
  }

  /// This is the same as `next()`, but it does not advance the iterator.
  /// (This could almost be a [`Peekable`](std::iter::Peekable) implementation,
  /// but the reference may not be derived from `self`, so it has to clone the value.)
  #[must_use] pub fn head(&self) -> Option<LispVal> {
    match &*self.e {
      LispKind::List(es) => es[self.offset as usize..].first().cloned(),
      LispKind::DottedList(es, r) =>
        es[self.offset as usize..].first().cloned().or_else(|| r.head()),
      _ => self.e.head(),
    }
  }

  /// If this is a list or improper list of length at least `n`, extends
  /// `vec` with the first `n` values in the list and returns true,
  /// otherwise it extends `vec` with as many values as are present and returns false.
  pub fn extend_into(&self, n: usize, vec: &mut Vec<LispVal>) -> bool {
    match &*self.e {
      LispKind::List(es) | LispKind::DottedList(es, _) if n <= es[self.offset as usize..].len() =>
        {vec.extend_from_slice(&es[self.offset as usize..][..n]); true}
      LispKind::List(es) => {vec.extend_from_slice(&es[self.offset as usize..]); false}
      LispKind::DottedList(es, r) => {
        vec.extend_from_slice(&es[self.offset as usize..]);
        r.clone().extend_into(n - es[self.offset as usize..].len(), vec)
      }
      _ => self.e.clone().extend_into(n, vec),
    }
  }
}

impl From<Uncons> for LispVal {
  fn from(u: Uncons) -> LispVal { u.as_lisp() }
}

impl Clone for Uncons {
  fn clone(&self) -> Self { Uncons::new(self.as_lisp()) }
}

impl Iterator for Uncons {
  type Item = LispVal;
  fn next(&mut self) -> Option<LispVal> {
    loop {
      match &*self.e {
        LispKind::List(es) => {
          let e = es.get(self.offset as usize)?;
          self.offset += 1;
          return Some(e.clone())
        }
        LispKind::DottedList(es, r) => {
          if let Some(e) = es.get(self.offset as usize) {
            self.offset += 1;
            return Some(e.clone())
          }
          *self = Uncons::new(r.clone())
        }
        LispKind::Ref(m) => self.e = m.unref(),
        LispKind::Annot(_, v) => self.e = v.clone(),
        _ => return None,
      }
    }
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    match &*self.e {
      LispKind::List(es) => {let n = es.len() - self.offset as usize; (n, Some(n))}
      LispKind::DottedList(es, _) => (es.len() - self.offset as usize, None),
      _ => (0, None),
    }
  }

  fn count(self) -> usize { self.len() }
}

impl<K: Clone + Hash + Eq, V: Remap, S> Remap for HashMap<K, V, S> {
  type Target = HashMap<K, V::Target>;
  fn remap(&self, r: &mut Remapper) -> Self::Target { self.iter().map(|(k, v)| (k.clone(), v.remap(r))).collect() }
}
impl<A: Remap> Remap for RefCell<A> {
  type Target = RefCell<A::Target>;
  fn remap(&self, r: &mut Remapper) -> Self::Target { RefCell::new(self.borrow().remap(r)) }
}
impl<A: Remap> Remap for Mutex<A> {
  type Target = Mutex<A::Target>;
  fn remap(&self, r: &mut Remapper) -> Self::Target { Mutex::new(self.ulock().remap(r)) }
}
impl Remap for LispVal {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    // Safety: Remapping is only done to frozen databases
    unsafe { self.freeze() }.remap(r)
  }
}

impl Remap for InferTarget {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      InferTarget::Unknown => InferTarget::Unknown,
      InferTarget::Provable => InferTarget::Provable,
      InferTarget::Bound(a) => InferTarget::Bound(a.remap(r)),
      InferTarget::Reg(a) => InferTarget::Reg(a.remap(r)),
    }
  }
}
impl Remap for ProcPos {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      ProcPos::Named(fsp, sp, a) => ProcPos::Named(fsp.clone(), *sp, a.remap(r)),
      ProcPos::Unnamed(fsp) => ProcPos::Unnamed(fsp.clone()),
      &ProcPos::Builtin(p) => ProcPos::Builtin(p),
    }
  }
}

impl Remap for Proc {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    // Safety: Remapping is only done to frozen databases
    unsafe { self.freeze() }.remap(r)
  }
}
