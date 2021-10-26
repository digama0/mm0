//! Types used in the rest of the compiler.

use std::{fmt::Display, ops::BitOrAssign};
use num::BigInt;
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;
use crate::{FileSpan, Symbol};
use super::{Binop, IntTy, LambdaId, Unop, VarId, ast::TyVarId};
pub use super::ast::ArgAttr;

/// A trait for displaying with a "context" struct. This is a generalization of [`EnvDisplay`] to
/// other forms of context.
pub trait CtxDisplay<C> where C: ?Sized {
  /// Display this object, using the given context and printing into the given formatter.
  fn fmt(&self, ctx: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
}

/// A printing struct for printing a [`CtxDisplay`] type.
#[derive(Debug)]
pub struct CtxPrint<'a, C: ?Sized, A: ?Sized>(pub &'a C, pub &'a A);

impl<C: ?Sized, A: CtxDisplay<C> + ?Sized> Display for CtxPrint<'_, C, A> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.1.fmt(self.0, f)
  }
}

/// A display context sufficient to print the types in this module.
pub trait DisplayCtx<'a> {
  /// Print a variable.
  fn fmt_var(&self, v: VarId, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
  /// Print a lifetime metavariable.
  fn fmt_lft_mvar(&self, v: LftMVarId, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
  /// Print an expression metavariable.
  fn fmt_expr_mvar(&self, v: ExprMVarId, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
  /// Print a type metavariable.
  fn fmt_ty_mvar(&self, v: TyMVarId, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
  /// Print a lambda with given substitutions.
  fn fmt_lambda(&self, v: LambdaId, subst: &[Expr<'a>], f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
}

impl<'a, C: DisplayCtx<'a>> CtxDisplay<C> for VarId {
  fn fmt(&self, ctx: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    ctx.fmt_var(*self, f)
  }
}

bitflags! {
  /// A list of flags that are propagated on type/expr construction
  /// for quick answers to some basic questions.
  pub struct Flags: u8 {
    /// Does this type/expr have a type metavariable?
    const HAS_TY_MVAR   = 1 << 0;
    /// Does this type/expr have a proposition metavariable?
    const HAS_PROP_MVAR = 1 << 1;
    /// Does this type/expr have a expr metavariable?
    const HAS_EXPR_MVAR = 1 << 2;
    /// Does this type/expr have a lifetime metavariable?
    const HAS_LFT_MVAR  = 1 << 3;
    /// Does this type/expr contain a variable (not in pattern position)?
    const HAS_VAR       = 1 << 4;
    /// Does this type/expr have an `Error` subexpression?
    const HAS_ERROR     = 1 << 5;
    /// Does this type/expr have a metavariable?
    const HAS_MVAR =
      Self::HAS_TY_MVAR.bits | Self::HAS_PROP_MVAR.bits |
      Self::HAS_EXPR_MVAR.bits | Self::HAS_LFT_MVAR.bits;
    /// (For Ty:) Is this type not (necessarily) a copy type?
    const IS_NON_COPY   = 1 << 6;
    /// (For Ty:) Is this a computationally relevant type?
    const IS_RELEVANT   = 1 << 7;
  }
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(Flags);

/// A trait for types that can accumulate flag data.
/// (We use `T: AddFlags` roughly interchangeably with
/// `for<'a> Flags: BitOrAssign<&'a T>`; the latter sometimes gives Rust trouble
/// due to syntax restrictions around higher-order type bounds.)
pub trait AddFlags {
  /// Accumulate the data from this type into `flags`.
  fn add(&self, flags: &mut Flags);
}

impl<'a, T: AddFlags + ?Sized> BitOrAssign<&'a T> for Flags {
  #[inline] fn bitor_assign(&mut self, t: &'a T) { t.add(self) }
}

impl BitOrAssign<VarId> for Flags {
  #[inline] fn bitor_assign(&mut self, _: VarId) {}
}

impl<'a, T: Copy> BitOrAssign<&'a [T]> for Flags
where Flags: BitOrAssign<T> {
  #[inline] fn bitor_assign(&mut self, rhs: &'a [T]) {
    for &t in rhs { *self |= t }
  }
}

impl<A, B> BitOrAssign<(A, B)> for Flags
where Flags: BitOrAssign<A> + BitOrAssign<B> {
  #[inline] fn bitor_assign(&mut self, (a, b): (A, B)) {
    *self |= a; *self |= b
  }
}

impl<A, B, C> BitOrAssign<(A, B, C)> for Flags
where Flags: BitOrAssign<A> + BitOrAssign<B> + BitOrAssign<C> {
  #[inline] fn bitor_assign(&mut self, (a, b, c): (A, B, C)) {
    *self |= a; *self |= b; *self |= c
  }
}

/// A `T` together with precomputed flag data for it. If `T: AddFlags`,
/// then the [`WithMeta::new`] function can be used to perform the precomputation.
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct WithMeta<T> {
  /// The flags.
  pub flags: Flags,
  /// The kind data.
  pub k: T
}
impl<T: std::fmt::Debug> std::fmt::Debug for WithMeta<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.k.fmt(f)
    }
}
impl<T> std::hash::Hash for WithMeta<T> {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    (self as *const Self).hash(state)
  }
}
impl<T> PartialEq for WithMeta<T> {
  fn eq(&self, other: &Self) -> bool { std::ptr::eq(self, other) }
}
impl<T> Eq for WithMeta<T> {}

impl<T: std::fmt::Display> std::fmt::Display for WithMeta<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.k.fmt(f)
  }
}

impl<C, T: CtxDisplay<C>> CtxDisplay<C> for WithMeta<T> {
  fn fmt(&self, ctx: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.k.fmt(ctx, f)
  }
}

impl<T> AddFlags for WithMeta<T> {
  #[inline] fn add(&self, f: &mut Flags) { *f |= self.flags }
}

impl<T: AddFlags> WithMeta<T> {
  /// Create a new `WithMeta<T>` by calculating the flag data using the method from `T: AddFlags`.
  pub fn new(k: T) -> WithMeta<T> {
    let mut flags = Flags::empty();
    flags |= &k;
    WithMeta {flags, k}
  }
}

mk_id! {
  /** A type metavariable. */ TyMVarId(Debug("?t")),
  /** An expression metavariable. */ ExprMVarId(Debug("?e")),
  /** A lifetime metavariable. */ LftMVarId(Debug("?l"))
}

/// A "lifetime" in MMC is a variable or place from which references can be derived.
/// For example, if we `let y = &x[1]` then `y` has the type `(& x T)`. As long as
/// heap variables referring to lifetime `x` exist, `x` cannot be modified or dropped.
/// There is a special lifetime `extern` that represents inputs to the current function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Lifetime {
  /// The `extern` lifetime is the inferred lifetime for function arguments such as
  /// `fn f(x: &T)`.
  Extern,
  /// A variable lifetime `x` is the annotation on references derived from `x`
  /// (or derived from other references derived from `x`).
  Place(VarId),
  /// A lifetime that has not been inferred yet.
  Infer(LftMVarId),
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(Lifetime);

impl<'a, C: DisplayCtx<'a>> CtxDisplay<C> for Lifetime {
  fn fmt(&self, ctx: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match *self {
      Lifetime::Extern => "extern".fmt(f),
      Lifetime::Place(v) => ctx.fmt_var(v, f),
      Lifetime::Infer(v) => ctx.fmt_lft_mvar(v, f),
    }
  }
}

impl BitOrAssign<Lifetime> for Flags {
  fn bitor_assign(&mut self, rhs: Lifetime) {
    match rhs {
      Lifetime::Extern |
      Lifetime::Place(_) => {}
      Lifetime::Infer(_) => *self |= Flags::HAS_LFT_MVAR,
    }
  }
}

/// An adjustment to an expr that can happen with no syntax,
/// simply because types don't line up.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum Coercion<'a> {
  /// The value can be typed at the target type, without regard for the source.
  TypedPure(Ty<'a>),
  /// An error coercion maps `X -> Y` for any `X, Y`. To use this variant,
  /// an error must have been previously reported regarding this type error.
  Error,
}

impl<'a> BitOrAssign<Coercion<'a>> for Flags {
  fn bitor_assign(&mut self, coe: Coercion<'a>) {
    match coe {
      Coercion::TypedPure(_) => {}
      Coercion::Error => *self |= Flags::HAS_ERROR,
    }
  }
}

/// A strongly typed tuple pattern.
pub type TuplePattern<'a> = &'a TuplePatternS<'a>;
/// A strongly typed tuple pattern.
pub type TuplePatternS<'a> = WithMeta<TuplePatternKind<'a>>;

/// A strongly typed tuple pattern.
#[derive(PartialEq, Eq, Hash)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum TuplePatternKind<'a> {
  /// A variable binding.
  Name(Symbol, VarId, Ty<'a>),
  /// A tuple destructuring pattern.
  Tuple(&'a [TuplePattern<'a>], TupleMatchKind, Ty<'a>),
  /// An error that has been reported.
  /// (We keep the original tuple pattern so that name scoping still works.)
  Error(TuplePattern<'a>, Ty<'a>),
}

impl std::fmt::Debug for TuplePatternKind<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    match *self {
      TuplePatternKind::Name(name, v, ty) => write!(f, "{:?}{{{}}}: {:?}", v, name, ty),
      TuplePatternKind::Tuple(args, mk, _) => match mk {
        TupleMatchKind::Unit => write!(f, "()"),
        TupleMatchKind::True => write!(f, "itrue"),
        TupleMatchKind::List |
        TupleMatchKind::Struct |
        TupleMatchKind::Sn |
        TupleMatchKind::Own => write!(f, "({:?})", args.iter().format(", ")),
        TupleMatchKind::Array => write!(f, "[{:?}]", args.iter().format(", ")),
        TupleMatchKind::And => write!(f, "<{:?}>", args.iter().format(", ")),
      }
      TuplePatternKind::Error(pat, ty) => write!(f, "{:?} ??as {:?}", pat, ty),
    }
  }
}

/// Defines the kind of pattern match being performed by a [`TuplePatternKind::Tuple`]. The [`Ty`]
/// part defines this uniquely, but there is some weak head normalization required to determine
/// this, so it is easier to have an enum to quickly match against.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum TupleMatchKind {
  /// A unit pattern match just returns `()`.
  Unit,
  /// A true pattern match just returns `()`.
  True,
  /// A list pattern match constructs `(e1, ..., en)`.
  List,
  /// A dependent list pattern match constructs `(e1, ..., en)`.
  Struct,
  /// An array pattern match constructs an array literal `[e1, ..., en]`.
  Array,
  /// An and pattern match uses the first element in the list. (All elements should be the
  /// same, although we don't check this here.)
  And,
  /// A singleton pattern match `(x, h): sn {a : T}` returns `x`.
  /// (It could also soundly return `a`, but `x` seems more useful here.)
  Sn,
  /// An `own` pattern match `(x, h): own T` returns `& x`.
  Own,
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(TupleMatchKind);

impl<'a> TuplePatternKind<'a> {
  /// The type of values that will be matched by the pattern.
  #[must_use] pub fn ty(&self) -> Ty<'a> {
    match *self {
      TuplePatternKind::Name(_, _, ty) |
      TuplePatternKind::Error(_, ty) |
      TuplePatternKind::Tuple(_, _, ty) => ty
    }
  }

  /// Calls function `f` on all variables in the pattern.
  pub fn on_vars(&self, f: &mut impl FnMut(Symbol, VarId)) {
    match *self {
      TuplePatternKind::Name(n, v, _) => f(n, v),
      TuplePatternKind::Error(pat, _) => pat.k.on_vars(f),
      TuplePatternKind::Tuple(pats, _, _) => for pat in pats { pat.k.on_vars(f) }
    }
  }

  /// Returns the variable of this pattern, if it is a simple (non-tuple) pattern.
  #[must_use] pub fn var(&self) -> Option<VarId> {
    if let TuplePatternKind::Name(_, v, _) = *self { Some(v) } else { None }
  }

  fn find_field(&self, f: Symbol, idxs: &mut Vec<u32>) -> bool {
    match *self {
      TuplePatternKind::Name(a, _, _) => a == f,
      TuplePatternKind::Error(pat, _) => pat.k.find_field(f, idxs),
      TuplePatternKind::Tuple(pats, _, _) =>
        pats.iter().enumerate().any(|(i, &pat)| {
          pat.k.find_field(f, idxs) && {
            idxs.push(i.try_into().expect("overflow"));
            true
          }
        }),
    }
  }
}

impl AddFlags for TuplePatternKind<'_> {
  fn add(&self, f: &mut Flags) {
    match *self {
      TuplePatternKind::Name(_, _, ty) => *f |= ty,
      TuplePatternKind::Error(pat, ty) => *f |= (Flags::HAS_ERROR, pat, ty),
      TuplePatternKind::Tuple(pats, _, ty) => *f |= (pats, ty),
    }
  }
}

impl<'a, C: DisplayCtx<'a>> CtxDisplay<C> for TuplePatternKind<'a> {
  fn fmt(&self, ctx: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    match *self {
      TuplePatternKind::Name(_, v, _) => ctx.fmt_var(v, f),
      TuplePatternKind::Error(pat, _) => write!(f, "??{}", CtxPrint(ctx, pat)),
      TuplePatternKind::Tuple(pats, _, _) =>
        write!(f, "({})", pats.iter().map(|&pat| CtxPrint(ctx, pat)).format(" ")),
    }
  }
}

/// An argument declaration for a function.
pub type Arg<'a> = &'a WithMeta<ArgS<'a>>;
/// An argument declaration for a function.
pub type ArgS<'a> = (ArgAttr, ArgKind<'a>);

/// An argument declaration for a function.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum ArgKind<'a> {
  /// A standard argument of the form `{x : T}`, a "lambda binder"
  Lam(TuplePattern<'a>),
  /// A substitution argument of the form `{{x : T} := val}`. (These are not supplied in
  /// invocations, they act as let binders in the remainder of the arguments.)
  Let(TuplePattern<'a>, Expr<'a>),
}

impl<'a> ArgKind<'a> {
  /// Get the argument pattern of the argument.
  #[must_use] pub fn var(&self) -> TuplePattern<'a> {
    match *self {
      ArgKind::Lam(pat) |
      ArgKind::Let(pat, _) => pat,
    }
  }

  /// Try to find a field specified by name in the list of arguments.
  /// On success, returns a pair `(n, path)` where `n` is the first argument
  /// with a matching field name and `path` is the sub-indexing path required
  /// to get to the field (since the name could be in a tuple pattern).
  #[must_use] pub fn find_field(args: &'a [Arg<'a>], f: Symbol) -> Option<(u32, Vec<u32>)> {
    let mut path = vec![];
    for (i, &arg) in args.iter().enumerate() {
      if arg.k.1.var().k.find_field(f, &mut path) {
        return Some((i.try_into().expect("overflow"), path))
      }
    }
    None
  }
}

impl AddFlags for ArgS<'_> {
  fn add(&self, f: &mut Flags) {
    match self.1 {
      ArgKind::Lam(pat) => *f |= pat,
      ArgKind::Let(pat, e) => *f |= (pat, e),
    }
    if self.0.contains(ArgAttr::GHOST) { f.remove(Flags::IS_RELEVANT) }
  }
}

impl<'a, C: DisplayCtx<'a>> CtxDisplay<C> for ArgS<'a> {
  fn fmt(&self, ctx: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self.1 {
      ArgKind::Lam(pat) =>
        write!(f, "{}: {}", CtxPrint(ctx, pat), CtxPrint(ctx, pat.k.ty())),
      ArgKind::Let(pat, e) =>
        write!(f, "{}: {} := {}", CtxPrint(ctx, pat), CtxPrint(ctx, pat.k.ty()), CtxPrint(ctx, e)),
    }
  }
}

/// An embedded MM0 expression inside MMC. All free variables have been replaced by indexes,
/// with `subst` holding the internal names of these variables.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Mm0Expr<'a> {
  /// The mapping from indexes in the `expr` to internal names.
  /// (The user-facing names have been erased.)
  pub subst: &'a [Expr<'a>],
  /// The root node of the expression.
  pub expr: LambdaId,
}

impl<'a, C: DisplayCtx<'a>> CtxDisplay<C> for Mm0Expr<'a> {
  fn fmt(&self, ctx: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    ctx.fmt_lambda(self.expr, self.subst, f)
  }
}

/// A type, which classifies regular variables (not type variables, not hypotheses).
pub type Ty<'a> = &'a TyS<'a>;
/// A type, which classifies regular variables (not type variables, not hypotheses).
pub type TyS<'a> = WithMeta<TyKind<'a>>;

/// A type, which classifies regular variables (not type variables, not hypotheses).
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum TyKind<'a> {
  /// `()` is the type with one element; `sizeof () = 0`.
  Unit,
  /// A true proposition.
  True,
  /// A false proposition.
  False,
  /// `bool` is the type of booleans, that is, bytes which are 0 or 1; `sizeof bool = 1`.
  Bool,
  /// A type variable.
  Var(TyVarId),
  /// The integral types:
  /// * `i(8*N)` is the type of N byte signed integers `sizeof i(8*N) = N`.
  /// * `u(8*N)` is the type of N byte unsigned integers; `sizeof u(8*N) = N`.
  Int(IntTy),
  /// The type `[T; n]` is an array of `n` elements of type `T`;
  /// `sizeof [T; n] = sizeof T * n`.
  Array(Ty<'a>, Expr<'a>),
  /// `own T` is a type of owned pointers. The typehood predicate is
  /// `x :> own T` iff `E. v (x |-> v) * v :> T`.
  Own(Ty<'a>),
  /// `(ref T)` is a type of borrowed values. This type is elaborated to
  /// `(ref a T)` where `a` is a lifetime; this is handled a bit differently than rust
  /// (see [`Lifetime`]).
  Ref(Lifetime, Ty<'a>),
  /// `&sn x` is the type of pointers to the place `x` (a variable or indexing expression).
  RefSn(Place<'a>),
  /// `(A, B, C)` is a tuple type with elements `A, B, C`;
  /// `sizeof (list A B C) = sizeof A + sizeof B + sizeof C`.
  List(&'a [Ty<'a>]),
  /// `(sn {a : T})` the type of values of type `T` that are equal to `a`.
  /// This is useful for asserting that a computationally relevant value can be
  /// expressed in terms of computationally irrelevant parts.
  Sn(Expr<'a>, Ty<'a>),
  /// `{x : A, y : B, z : C}` is the dependent version of `list`;
  /// it is a tuple type with elements `A, B, C`, but the types `A, B, C` can
  /// themselves refer to `x, y, z`.
  /// `sizeof {x : A, _ : B x} = sizeof A + max_x (sizeof (B x))`.
  ///
  /// The top level declaration `(struct foo {x : A} {y : B})` desugars to
  /// `(typedef foo {x : A, y : B})`.
  Struct(&'a [Arg<'a>]),
  /// A universally quantified proposition.
  All(TuplePattern<'a>, Ty<'a>),
  /// Implication (plain, non-separating).
  Imp(Ty<'a>, Ty<'a>),
  /// Separating implication.
  Wand(Ty<'a>, Ty<'a>),
  /// Negation.
  Not(Ty<'a>),
  /// `(and A B C)` is an intersection type of `A, B, C`;
  /// `sizeof (and A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (and A B C)` iff
  /// `x :> A /\ x :> B /\ x :> C`. (Note that this is regular conjunction,
  /// not separating conjunction.)
  And(&'a [Ty<'a>]),
  /// `(or A B C)` is an undiscriminated anonymous union of types `A, B, C`.
  /// `sizeof (or A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (or A B C)` iff
  /// `x :> A \/ x :> B \/ x :> C`.
  Or(&'a [Ty<'a>]),
  /// `(if cond A B)` is a type that is `A` if `cond` is true and `B` if cond is false.
  /// `sizeof (if cond A B) = max (sizeof A, sizeof B)`, and
  /// the typehood predicate is `x :> (if cond A B)` iff
  /// `if cond (x :> A) (x :> B)`.
  If(Expr<'a>, Ty<'a>, Ty<'a>),
  /// `(ghost A)` is a computationally irrelevant version of `A`, which means
  /// that the logical storage of `(ghost A)` is the same as `A` but the physical storage
  /// is the same as `()`. `sizeof (ghost A) = 0`.
  Ghost(Ty<'a>),
  /// `(? T)` is the type of possibly-uninitialized `T`s. The typing predicate
  /// for this type is vacuous, but it has the same size as `T`, so overwriting with
  /// a `T` is possible.
  Uninit(Ty<'a>),
  /// A boolean expression, interpreted as a pure proposition
  Pure(Expr<'a>),
  /// A user-defined type-former.
  User(Symbol, &'a [Ty<'a>], &'a [Expr<'a>]),
  /// A heap assertion `l |-> (v: |T|)`.
  Heap(Expr<'a>, Expr<'a>, Ty<'a>),
  /// An explicit typing assertion `[v : T]`.
  HasTy(Expr<'a>, Ty<'a>),
  /// The input token.
  Input,
  /// The output token.
  Output,
  /// A moved-away type.
  Moved(Ty<'a>),
  /// An inference variable.
  Infer(TyMVarId),
  /// A type error that has been reported.
  Error,
}

/// A visitor trait for the `Ty` type.
/// This is used as the callback type of [`Ty::visit`].
///
/// [`Ty::visit`]: struct.WithMeta.html#method.visit
pub trait TyVisit<'a> {
  /// Called on `Expr` subexpressions.
  fn visit_expr(&mut self, _: Expr<'a>) {}
  /// Called on `Place` subexpressions.
  fn visit_place(&mut self, _: Place<'a>) {}
  /// Called on type `MVar` subexpressions.
  fn visit_mvar(&mut self, _: TyMVarId) {}
}
impl<'a> TyS<'a> {
  /// If this type is an integral type, return the underlying [`IntTy`], otherwise `None`.
  #[must_use] pub fn as_int_ty(&self) -> Option<IntTy> {
    if let TyKind::Int(ity) = self.k { Some(ity) } else { None }
  }

  /// Calls `f` on all leaf subterms of interest, using methods in the [`TyVisit`] trait.
  pub fn visit(&self, f: &mut impl TyVisit<'a>) {
    match self.k {
      TyKind::Unit |
      TyKind::True |
      TyKind::False |
      TyKind::Bool |
      TyKind::Var(_) |
      TyKind::Int(_) |
      TyKind::Input |
      TyKind::Output |
      TyKind::Error => {}
      TyKind::Array(ty, e) |
      TyKind::Sn(e, ty) => {ty.visit(f); f.visit_expr(e)}
      TyKind::All(pat, p) => {pat.k.ty().visit(f); p.visit(f)}
      TyKind::Imp(p, q) |
      TyKind::Wand(p, q) => {p.visit(f); q.visit(f)}
      TyKind::Own(ty) |
      TyKind::Ref(_, ty) |
      TyKind::Ghost(ty) |
      TyKind::Uninit(ty) |
      TyKind::Not(ty) |
      TyKind::Moved(ty) => ty.visit(f),
      TyKind::RefSn(p) => f.visit_place(p),
      TyKind::Pure(e) => f.visit_expr(e),
      TyKind::List(tys) |
      TyKind::And(tys) |
      TyKind::Or(tys) => for &ty in tys { ty.visit(f) },
      TyKind::Struct(args) => for &arg in args {
        match arg.k.1 {
          ArgKind::Lam(pat) => pat.k.ty().visit(f),
          ArgKind::Let(pat, e) => {pat.k.ty().visit(f); f.visit_expr(e)}
        }
      },
      TyKind::If(e, ty1, ty2) => {f.visit_expr(e); ty1.visit(f); ty2.visit(f)}
      TyKind::User(_, tys, es) => {
        for &ty in tys { ty.visit(f) }
        for &e in es { f.visit_expr(e) }
      }
      TyKind::Heap(e1, e2, ty) => {f.visit_expr(e1); f.visit_expr(e2); ty.visit(f)}
      TyKind::HasTy(x, ty) => {f.visit_expr(x); ty.visit(f)}
      TyKind::Infer(e) => f.visit_mvar(e),
    }
  }

  /// Calls function `f` on all type metavariables.
  pub fn on_mvars(&self, f: impl FnMut(TyMVarId)) {
    struct Visitor<F>(F);
    impl<'a, F: FnMut(TyMVarId)> TyVisit<'a> for Visitor<F> {
      fn visit_mvar(&mut self, v: TyMVarId) { self.0(v) }
    }
    impl<'a, F: FnMut(TyMVarId)> ExprVisit<'a> for Visitor<F> {
      fn visit_ty(&mut self, ty: Ty<'a>) { ty.visit(self) }
    }
    self.visit(&mut Visitor(f));
  }

  /// Calls function `f` on all expression variables (not type variables).
  pub fn on_vars(&self, f: impl FnMut(VarId)) { self.visit(&mut OnVars(f)) }
}

impl AddFlags for TyKind<'_> {
  fn add(&self, f: &mut Flags) {
    match *self {
      TyKind::Unit |
      TyKind::True |
      TyKind::False => {}
      TyKind::Bool |
      TyKind::Var(_) |
      TyKind::Int(_) => *f |= Flags::IS_RELEVANT,
      TyKind::Input |
      TyKind::Output => *f |= Flags::IS_NON_COPY,
      TyKind::Array(ty, e) |
      TyKind::Sn(e, ty) => {
        *f |= e;
        f.remove(Flags::IS_NON_COPY | Flags::IS_RELEVANT);
        *f |= ty;
      }
      TyKind::Own(ty) => *f |= (Flags::IS_NON_COPY | Flags::IS_RELEVANT, ty),
      TyKind::Not(ty) => *f |= ty,
      TyKind::Ghost(ty) => {*f |= ty; f.remove(Flags::IS_RELEVANT)}
      TyKind::Uninit(ty) |
      TyKind::Moved(ty) => {*f |= ty; f.remove(Flags::IS_NON_COPY)}
      TyKind::Ref(lft, ty) => {*f |= (lft, ty); f.remove(Flags::IS_NON_COPY)}
      TyKind::RefSn(p) => {
        *f |= p;
        f.remove(Flags::IS_NON_COPY);
        *f |= Flags::IS_RELEVANT;
      }
      TyKind::Pure(e) => {*f |= e; f.remove(Flags::IS_NON_COPY | Flags::IS_RELEVANT)}
      TyKind::Struct(args) => *f |= args,
      TyKind::All(pat, p) => {*f |= pat; f.remove(Flags::IS_RELEVANT); *f |= p}
      TyKind::Imp(p, q) |
      TyKind::Wand(p, q) => {*f |= p; f.remove(Flags::IS_RELEVANT); *f |= q}
      TyKind::List(tys) |
      TyKind::And(tys) |
      TyKind::Or(tys) => *f |= tys,
      TyKind::If(e, tru, fal) => {
        *f |= e;
        f.remove(Flags::IS_NON_COPY | Flags::IS_RELEVANT);
        *f |= (tru, fal);
      }
      TyKind::User(_, tys, es) => *f |= (Flags::IS_NON_COPY | Flags::IS_RELEVANT, tys, es),
      TyKind::Heap(e, v, ty) => {
        *f |= (Flags::IS_NON_COPY, (e, v, ty));
        f.remove(Flags::IS_RELEVANT);
      }
      TyKind::HasTy(v, ty) => {
        *f |= v;
        f.remove(Flags::IS_NON_COPY);
        *f |= ty;
        f.remove(Flags::IS_RELEVANT);
      }
      TyKind::Infer(_) => *f |= Flags::IS_NON_COPY | Flags::IS_RELEVANT | Flags::HAS_TY_MVAR,
      TyKind::Error => *f |= Flags::HAS_ERROR,
    }
  }
}

impl<'a, C: DisplayCtx<'a>> CtxDisplay<C> for TyKind<'a> {
  fn fmt(&self, ctx: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    macro_rules! p {($e:expr) => {CtxPrint(ctx, $e)}}
    match *self {
      TyKind::Var(v) => v.fmt(f),
      TyKind::Unit => "()".fmt(f),
      TyKind::True => "true".fmt(f),
      TyKind::False => "false".fmt(f),
      TyKind::Bool => "bool".fmt(f),
      TyKind::Int(ity) => ity.fmt(f),
      TyKind::Array(ty, n) => write!(f, "(array {} {})", p!(ty), p!(n)),
      TyKind::Own(ty) => match ty.k {
        TyKind::Ref(lft, ty) => write!(f, "(& {} {})", p!(&lft), p!(ty)),
        _ => write!(f, "(own {})", p!(ty))
      },
      TyKind::Ref(lft, ty) => write!(f, "(ref {} {})", p!(&lft), p!(ty)),
      TyKind::RefSn(x) => write!(f, "(&sn {})", p!(x)),
      TyKind::List(tys) => write!(f, "(list {})", tys.iter().map(|&ty| p!(ty)).format(" ")),
      TyKind::Sn(e, ty) => write!(f, "(sn {{{}: {}}})", p!(e), p!(ty)),
      TyKind::Struct(args) => {
        "(struct".fmt(f)?;
        for &arg in args { write!(f, " {{{}}}", p!(arg))? }
        ")".fmt(f)
      }
      TyKind::All(a, pr) => write!(f, "A. {} {}", p!(a), p!(pr)),
      TyKind::Imp(p, q) => write!(f, "({} -> {})", p!(p), p!(q)),
      TyKind::Wand(p, q) => write!(f, "({} -* {})", p!(p), p!(q)),
      TyKind::Not(pr) => write!(f, "~{}", p!(pr)),
      TyKind::And(tys) => write!(f, "({})", tys.iter().map(|&p| p!(p)).format(" /\\ ")),
      TyKind::Or(tys) => write!(f, "({})", tys.iter().map(|&p| p!(p)).format(" \\/ ")),
      TyKind::If(cond, then, els) => write!(f, "(if {} {} {})", p!(cond), p!(then), p!(els)),
      TyKind::Ghost(ty) => write!(f, "(ghost {})", p!(ty)),
      TyKind::Uninit(ty) => write!(f, "(? {})", p!(ty)),
      TyKind::Pure(e) => e.fmt(ctx, f),
      TyKind::User(name, tys, es) => {
        write!(f, "({}", name)?;
        for &ty in tys { " ".fmt(f)?; ty.fmt(ctx, f)? }
        for &e in es { " ".fmt(f)?; e.fmt(ctx, f)? }
        ")".fmt(f)
      }
      TyKind::Heap(x, v, t) => write!(f, "{} => {}: {}", p!(x), p!(v), p!(t)),
      TyKind::HasTy(v, t) => write!(f, "[{}: {}]", p!(v), p!(t)),
      TyKind::Input => "Input".fmt(f),
      TyKind::Output => "Output".fmt(f),
      TyKind::Moved(ty) => write!(f, "|{}|", p!(ty)),
      TyKind::Infer(v) => write!(f, "?T{}", v.0),
      TyKind::Error => "??".fmt(f),
    }
  }
}

impl std::fmt::Debug for TyKind<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    match *self {
      TyKind::Var(v) => write!(f, "{:?}", v),
      TyKind::Unit => write!(f, "()"),
      TyKind::True => write!(f, "true"),
      TyKind::False => write!(f, "false"),
      TyKind::Bool => write!(f, "bool"),
      TyKind::Int(ity) => write!(f, "{}", ity),
      TyKind::Array(ty, n) => write!(f, "[{:?}; {:?}]", ty, n),
      TyKind::Own(ty) => match ty.k {
        TyKind::Ref(lft, ty) => write!(f, "&'{:?} {:?}", &lft, ty),
        _ => write!(f, "own {:?}", ty)
      },
      TyKind::Ref(lft, ty) => write!(f, "ref '{:?} {:?})", &lft, ty),
      TyKind::RefSn(x) => write!(f, "&sn {:?}", x),
      TyKind::List(tys) => write!(f, "[{:?}]", tys.iter().format(", ")),
      TyKind::Sn(e, ty) => write!(f, "sn({:?}: {:?})", e, ty),
      TyKind::Struct(args) => write!(f, "[{:?}]", args.iter().format(", ")),
      TyKind::All(a, pr) => write!(f, "A. {:?} {:?}", a, pr),
      TyKind::Imp(p, q) => write!(f, "({:?} -> {:?})", p, q),
      TyKind::Wand(p, q) => write!(f, "({:?} -* {:?})", p, q),
      TyKind::Not(pr) => write!(f, "~{:?}", pr),
      TyKind::And(tys) => write!(f, "({:?})", tys.iter().format(" /\\ ")),
      TyKind::Or(tys) => write!(f, "({:?})", tys.iter().format(" \\/ ")),
      TyKind::If(cond, then, els) =>
        write!(f, "if {:?} {{ {:?} }} else {{ {:?} }}", cond, then, els),
      TyKind::Ghost(ty) => write!(f, "ghost({:?})", ty),
      TyKind::Uninit(ty) => write!(f, "Uninit({:?})", ty),
      TyKind::Pure(e) => write!(f, "{:?}", e),
      TyKind::User(name, tys, es) => {
        use itertools::Itertools;
        write!(f, "{}", name)?;
        if !tys.is_empty() { write!(f, "<{:?}>", tys.iter().format(", "))? }
        write!(f, "({:?})", es.iter().format(", "))
      }
      TyKind::Heap(x, v, t) => write!(f, "({:?} => {:?}: {:?})", x, v, t),
      TyKind::HasTy(v, t) => write!(f, "[{:?}: {:?}]", v, t),
      TyKind::Input => write!(f, "Input"),
      TyKind::Output => write!(f, "Output"),
      TyKind::Moved(ty) => write!(f, "|{:?}|", ty),
      TyKind::Infer(v) => write!(f, "?T{:?}", v.0),
      TyKind::Error => write!(f, "??"),
    }
  }
}

impl<'a> TyS<'a> {
  /// Returns true if this is a copy type (i.e. `|T| = T`).
  #[inline] #[must_use] pub fn is_copy(&self) -> bool {
    !self.flags.contains(Flags::IS_NON_COPY)
  }

  /// A type is ghostly if elements of this type can be obtained from the logical assertion that
  /// the element exists in the type, without any actual computation or bit representation.
  ///
  /// This includes types with at most one element like `()`, `true` and `false`, as well as pure
  /// (separating) propositions like `[v: T]`, as well as `(ghost T)` for any `T`, and structs made
  /// up from these pieces.
  #[inline] #[must_use] pub fn ghostly(&self) -> bool {
    !self.flags.contains(Flags::IS_RELEVANT)
  }
}

struct OnVars<F>(F);

impl<'a, F: FnMut(VarId)> TyVisit<'a> for OnVars<F> {
  fn visit_expr(&mut self, e: Expr<'a>) { e.visit(self) }
}
impl<'a, F: FnMut(VarId)> ExprVisit<'a> for OnVars<F> {
  fn visit_ty(&mut self, ty: Ty<'a>) { ty.visit(self) }
  fn visit_var(&mut self, v: VarId) { self.0(v) }
}

/// A place expression.
pub type Place<'a> = &'a PlaceS<'a>;
/// A place expression.
pub type PlaceS<'a> = WithMeta<PlaceKind<'a>>;
/// A place expression, or a "place to blame" for why it's not pure.
pub type RPlace<'a> = Result<Place<'a>, &'a FileSpan>;
/// A pair of an optional place expression and a type, used to classify the result
/// of expressions that may or may not be pure.
pub type RPlaceTy<'a> = (RPlace<'a>, Ty<'a>);

/// A place expression.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum PlaceKind<'a> {
  /// A variable reference.
  Var(VarId),
  /// An index operation `(index a i): T` where `a: (array T n)` and `i: nat`.
  Index(Place<'a>, Ty<'a>, Expr<'a>),
  /// If `x: (array T n)`, then `(slice x a b h): (array T b)` if
  /// `h` is a proof that `a + b <= n`.
  /// If `h` is the `Err` variant, then it is an expr evaluating to `n`.
  Slice(Place<'a>, Ty<'a>, [Expr<'a>; 2]),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(Place<'a>, Ty<'a>, u32),
  /// A type error that has been reported.
  Error,
}

impl std::fmt::Debug for PlaceKind<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      PlaceKind::Var(v) => write!(f, "{}", v),
      PlaceKind::Index(arr, _, idx) => write!(f, "{:?}[{:?}]", arr, idx),
      PlaceKind::Slice(arr, _, [idx, len]) => write!(f, "{:?}[{:?}..+{:?}]", arr, idx, len),
      PlaceKind::Proj(e, _, j) => write!(f, "{:?}.{}", e, j),
      PlaceKind::Error => write!(f, "??"),
    }
  }
}

impl<'a> PlaceS<'a> {
  /// Calls `f` on all leaf subterms of interest, using methods in the [`ExprVisit`] trait.
  pub fn visit(&self, f: &mut impl ExprVisit<'a>) {
    match self.k {
      PlaceKind::Error => {}
      PlaceKind::Var(v) => f.visit_var(v),
      PlaceKind::Index(a, ty, i) => {a.visit(f); f.visit_ty(ty); i.visit(f)}
      PlaceKind::Slice(a, ty, [i, n]) => {a.visit(f); f.visit_ty(ty); i.visit(f); n.visit(f)}
      PlaceKind::Proj(e, ty, _) => {e.visit(f); f.visit_ty(ty)},
    }
  }

  /// Calls function `f` on all expression variables (not type variables).
  pub fn on_vars(&self, f: impl FnMut(VarId)) { self.visit(&mut OnVars(f)) }
}

impl AddFlags for PlaceKind<'_> {
  fn add(&self, f: &mut Flags) {
    match *self {
      PlaceKind::Var(_) => *f |= Flags::HAS_VAR,
      PlaceKind::Proj(e, ty,  _) => *f |= (e, ty),
      PlaceKind::Index(a, ty, i) => *f |= (a, ty, i),
      PlaceKind::Slice(a, ty, [i, n]) => *f |= ((a, ty), i, n),
      PlaceKind::Error => *f |= Flags::HAS_ERROR,
    }
  }
}

impl<'a, C: DisplayCtx<'a>> CtxDisplay<C> for PlaceKind<'a> {
  fn fmt(&self, ctx: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    macro_rules! p {($e:expr) => {CtxPrint(ctx, $e)}}
    match *self {
      PlaceKind::Var(v) => ctx.fmt_var(v, f),
      PlaceKind::Index(a, _, i) => write!(f, "(index {} {})", p!(a), p!(i)),
      PlaceKind::Slice(a, _, [i, n]) => write!(f, "(slice {} {} {})", p!(a), p!(i), p!(n)),
      PlaceKind::Proj(a, _, i) => write!(f, "({} . {})", p!(a), i),
      PlaceKind::Error => "??".fmt(f),
    }
  }
}

/// A pure expression. (Regular expressions are not manipulated like types,
/// i.e. copied and substituted around, so they are in the [`hir`](super::hir) module.)
pub type Expr<'a> = &'a ExprS<'a>;
/// A pure expression.
pub type ExprS<'a> = WithMeta<ExprKind<'a>>;

/// A pure expression, or `None` if it's not pure.
pub type OExpr<'a> = Option<Expr<'a>>;

/// A pure expression, or a "place to blame" for why it's not pure.
pub type RExpr<'a> = Result<Expr<'a>, &'a FileSpan>;

/// A pair of an optional pure expression and a type, used to classify the result
/// of expressions that may or may not be pure.
pub type RExprTy<'a> = (RExpr<'a>, Ty<'a>);

/// A pair of an optional pure expression and a type, used to classify the result
/// of expressions that may or may not be pure.
pub type ExprTy<'a> = (OExpr<'a>, Ty<'a>);

/// A pure expression.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum ExprKind<'a> {
  /// A `()` literal.
  Unit,
  /// A variable reference.
  Var(VarId),
  /// A user constant.
  Const(Symbol),
  /// A number literal.
  Bool(bool),
  /// A number literal.
  Int(&'a BigInt),
  /// A unary operation.
  Unop(Unop, Expr<'a>),
  /// A binary operation.
  Binop(Binop, Expr<'a>, Expr<'a>),
  /// An index operation `a[i]: T` where `a: (array T n)`
  /// and `i: nat`.
  Index(Expr<'a>, Expr<'a>),
  /// If `x: (array T n)`, then `x[a..a+b]: (array T b)`.
  Slice([Expr<'a>; 3]),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(Expr<'a>, u32),
  /// `(update-index a i e)` is the result of `a` after `a[i] = e`.
  UpdateIndex([Expr<'a>; 3]),
  /// `(update-slice x a b e)` is the result of assigning `x[a..a+b] = e`.
  UpdateSlice([Expr<'a>; 4]),
  /// `(update-proj x i)` is the result of assigning `x.i = e`.
  UpdateProj(Expr<'a>, u32, Expr<'a>),
  /// `(e1, ..., en)` returns a tuple of the arguments.
  List(&'a [Expr<'a>]),
  /// `[e1, ..., en]`, an array literal.
  Array(&'a [Expr<'a>]),
  /// Return the size of a type.
  Sizeof(Ty<'a>),
  /// A place result.
  Ref(Place<'a>),
  /// `(pure $e$)` embeds an MM0 expression `$e$` as the target type,
  /// one of the numeric types
  Mm0(Mm0Expr<'a>),
  /// A function call
  Call {
    /// The function to call.
    f: Symbol,
    /// The type arguments.
    tys: &'a [Ty<'a>],
    /// The function arguments.
    args: &'a [Expr<'a>],
  },
  /// An if-then-else expression (at either block or statement level). The initial atom names
  /// a hypothesis that the expression is true in one branch and false in the other.
  If {
    /// The if condition.
    cond: Expr<'a>,
    /// The then case.
    then: Expr<'a>,
    /// The else case.
    els: Expr<'a>
  },
  /// An inference variable.
  Infer(ExprMVarId),
  /// A type error that has been reported.
  Error,
}

/// A visitor trait for the `Expr` type.
/// This is used as the callback type of [`Expr::visit`] and [`Place::visit`].
///
/// [`Expr::visit`]: struct.WithMeta.html#method.visit-2
/// [`Place::visit`]: struct.WithMeta.html#method.visit-1
pub trait ExprVisit<'a> {
  /// Called on `Ty` subexpressions.
  fn visit_ty(&mut self, _: Ty<'a>) {}
  /// Called on variable subexpressions.
  fn visit_var(&mut self, _: VarId) {}
  /// Called on expression `MVar` subexpressions.
  fn visit_mvar(&mut self, _: ExprMVarId) {}
}

impl<'a> ExprS<'a> {
  /// Calls `f` on all leaf subterms of interest, using methods in the [`ExprVisit`] trait.
  pub fn visit(&self, f: &mut impl ExprVisit<'a>) {
    match self.k {
      ExprKind::Unit |
      ExprKind::Const(_) |
      ExprKind::Bool(_) |
      ExprKind::Int(_) |
      ExprKind::Error => {}
      ExprKind::Var(v) => f.visit_var(v),
      ExprKind::Unop(_, e) |
      ExprKind::Proj(e, _) => e.visit(f),
      ExprKind::Ref(e) => e.visit(f),
      ExprKind::Binop(_, e1, e2) => {e1.visit(f); e2.visit(f)}
      ExprKind::Index(a, i) => {a.visit(f); i.visit(f)}
      ExprKind::Slice([a, i, n]) => {a.visit(f); i.visit(f); n.visit(f)}
      ExprKind::UpdateIndex([a, i, val]) => {a.visit(f); i.visit(f); val.visit(f)}
      ExprKind::UpdateSlice([a, i, n, val]) => {a.visit(f); i.visit(f); n.visit(f); val.visit(f)}
      ExprKind::UpdateProj(a, _, val) => {a.visit(f); val.visit(f)}
      ExprKind::Sizeof(e) => f.visit_ty(e),
      ExprKind::List(es) |
      ExprKind::Array(es) => for e in es {e.visit(f)},
      ExprKind::Mm0(ref e) => for e in e.subst {e.visit(f)},
      ExprKind::Call {tys, args, ..} => {
        for &ty in tys { f.visit_ty(ty) }
        for &arg in args { arg.visit(f) }
      }
      ExprKind::If {cond, then, els} => {cond.visit(f); then.visit(f); els.visit(f)}
      ExprKind::Infer(v) => f.visit_mvar(v),
    }
  }

  /// Calls function `f` on all expression metavariables.
  pub fn on_mvars(&self, f: impl FnMut(ExprMVarId)) {
    struct Visitor<F>(F);
    impl<'a, F: FnMut(ExprMVarId)> ExprVisit<'a> for Visitor<F> {
      fn visit_mvar(&mut self, e: ExprMVarId) { self.0(e) }
    }
    self.visit(&mut Visitor(f));
  }

  /// Calls function `f` on all expression variables (not type variables).
  pub fn on_vars(&self, f: impl FnMut(VarId)) { self.visit(&mut OnVars(f)) }
}

impl AddFlags for ExprKind<'_> {
  fn add(&self, f: &mut Flags) {
    match *self {
      ExprKind::Unit |
      ExprKind::Const(_) |
      ExprKind::Bool(_) |
      ExprKind::Int(_) |
      ExprKind::Sizeof(_) => {}
      ExprKind::Var(_) => *f |= Flags::HAS_VAR,
      ExprKind::Unop(_, e) |
      ExprKind::Proj(e, _) => *f |= e,
      ExprKind::Ref(e) => *f |= e,
      ExprKind::Binop(_, e1, e2) => *f |= (e1, e2),
      ExprKind::Index(a, i) => *f |= (a, i),
      ExprKind::Slice([a, i, n]) => *f |= (a, i, n),
      ExprKind::UpdateIndex([a, i, val]) => *f |= (a, i, val),
      ExprKind::UpdateSlice([a, i, n, val]) => *f |= ((a, i, n), val),
      ExprKind::UpdateProj(a, _, val) => *f |= (a, val),
      ExprKind::List(es) |
      ExprKind::Array(es) => *f |= es,
      ExprKind::Mm0(ref e) => *f |= e.subst,
      ExprKind::Call {tys, args, ..} => *f |= (tys, args),
      ExprKind::If {cond, then, els} => *f |= (cond, then, els),
      ExprKind::Infer(_) => *f |= Flags::HAS_EXPR_MVAR,
      ExprKind::Error => *f |= Flags::HAS_ERROR,
    }
  }
}

impl<'a, C: DisplayCtx<'a>> CtxDisplay<C> for ExprKind<'a> {
  fn fmt(&self, ctx: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    macro_rules! p {($e:expr) => {CtxPrint(ctx, $e)}}
    match *self {
      ExprKind::Unit => "()".fmt(f),
      ExprKind::Var(v) => ctx.fmt_var(v, f),
      ExprKind::Const(c) => c.fmt(f),
      // ExprKind::Global(v) => v.fmt(fe, f),
      ExprKind::Bool(b) => b.fmt(f),
      ExprKind::Int(n) => n.fmt(f),
      ExprKind::Unop(Unop::As(ity), e) => write!(f, "{{{} as {}}}", p!(e), ity),
      ExprKind::Unop(op, e) => write!(f, "({} {})", op, p!(e)),
      ExprKind::Binop(op, e1, e2) => write!(f, "{{{} {} {}}}", p!(e1), op, p!(e2)),
      ExprKind::List(es) |
      ExprKind::Array(es) => write!(f, "(list {})", es.iter().map(|&e| p!(e)).format(" ")),
      ExprKind::Index(a, i) => write!(f, "(index {} {})", p!(a), p!(i)),
      ExprKind::Slice([a, i, n]) => write!(f, "(slice {} {} {})", p!(a), p!(i), p!(n)),
      ExprKind::Proj(a, i) => write!(f, "({} . {})", p!(a), i),
      ExprKind::UpdateIndex([a, i, val]) => write!(f,
        "(update-index {} {} {})", p!(a), p!(i), p!(val)),
      ExprKind::UpdateSlice([a, i, l, val]) => write!(f,
        "(update-slice {} {} {} {})", p!(a), p!(i), p!(l), p!(val)),
      ExprKind::UpdateProj(a, n, val) => write!(f,
        "(update-proj {} {} {})", p!(a), n, p!(val)),
      ExprKind::Ref(e) => write!(f, "(& {})", p!(e)),
      ExprKind::Sizeof(ty) => write!(f, "(sizeof {})", p!(ty)),
      ExprKind::Mm0(ref e) => e.fmt(ctx, f),
      ExprKind::Call {f: x, tys, args} => {
        write!(f, "({}", x)?;
        for &ty in tys { write!(f, " {}", p!(ty))? }
        for &arg in args { write!(f, " {}", p!(arg))? }
        ")".fmt(f)
      }
      ExprKind::If {cond, then, els} => write!(f, "(if {} {} {})", p!(cond), p!(then), p!(els)),
      ExprKind::Infer(v) => write!(f, "?v{}", v.0),
      ExprKind::Error => "??".fmt(f),
    }
  }
}

impl std::fmt::Debug for ExprKind<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      ExprKind::Unit => write!(f, "()"),
      ExprKind::Var(v) => write!(f, "{}", v),
      ExprKind::Const(c) => write!(f, "{}", c),
      ExprKind::Bool(b) => write!(f, "{}", b),
      ExprKind::Int(n) => write!(f, "{}", n),
      ExprKind::Unop(op, e) => { write!(f, "{} {:?}", op, e) }
      ExprKind::Binop(op, e1, e2) => write!(f, "({:?} {} {:?})", e1, op, e2),
      ExprKind::Index(arr, idx) => write!(f, "{:?}[{:?}]", arr, idx),
      ExprKind::Slice([arr, idx, len]) => write!(f, "{:?}[{:?}..+{:?}]", arr, idx, len),
      ExprKind::Proj(e, j) => write!(f, "{:?}.{}", e, j),
      ExprKind::UpdateIndex([a, i, val]) => write!(f, "({:?}[{:?}] .= {:?})", a, i, val),
      ExprKind::UpdateSlice([a, i, l, val]) =>
        write!(f, "({:?}[{:?}..+{:?}] .= {:?})", a, i, l, val),
      ExprKind::UpdateProj(a, n, val) => write!(f, "({:?}.{:?} .= {:?})", a, n, val),
      ExprKind::List(es) => {
        use itertools::Itertools;
        writeln!(f, "({:?})", es.iter().format(", "))
      }
      ExprKind::Array(es) => {
        use itertools::Itertools;
        writeln!(f, "[{:?}]", es.iter().format(", "))
      }
      ExprKind::Ref(e) => write!(f, "ref {:?}", e),
      ExprKind::Mm0(e) => {
        write!(f, "{:?}", e.expr)?;
        if !e.subst.is_empty() {
          write!(f, "[")?;
          for e in e.subst {
            write!(f, "{:?},", e)?;
          }
          writeln!(f, "]")?;
        }
        Ok(())
      }
      ExprKind::Sizeof(ty) => {
        write!(f, "sizeof({:?})", ty)
      }
      ExprKind::Call {f: func, tys, args} => {
        use itertools::Itertools;
        write!(f, "{}", func)?;
        if !tys.is_empty() { write!(f, "<{:?}>", tys.iter().format(", "))? }
        write!(f, "({:?})", args.iter().format(", "))
      }
      ExprKind::If { cond, then, els } =>
        write!(f, "if {:?} {{ {:?} }} else {{ {:?} }}", cond, then, els),
      ExprKind::Infer(v) => write!(f, "{:?}", v),
      ExprKind::Error => write!(f, "??"),
    }
  }
}
