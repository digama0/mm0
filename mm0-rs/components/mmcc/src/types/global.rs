//! An owning version of the types in `ty` module, for use in globals.

use std::{collections::HashMap, rc::Rc};
use num::BigInt;
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;
use crate::Symbol;
use super::{ty, super::infer::MVars};
pub use ty::{WithMeta, TupleMatchKind, Lifetime, ArgAttr};
use super::{Binop, IntTy, LambdaId, Unop, VarId, ast::TyVarId, hir};

type Mapper<'a, T> = HashMap<&'a WithMeta<T>, <&'a WithMeta<T> as ToGlobal<'a>>::Output>;

pub(crate) trait Internable<'a>: Sized + 'a where &'a WithMeta<Self>: ToGlobal<'a> {
  type Inner;
  fn interner<'s>(_: &'s mut ToGlobalCtx<'a, '_>) -> &'s mut Mapper<'a, Self>;
}

#[derive(Debug)]
pub(crate) struct ToGlobalCtx<'a, 'n> {
  mvars: &'n mut MVars<'a>,
  tpat: Mapper<'a, ty::TuplePatternKind<'a>>,
  arg: Mapper<'a, ty::ArgS<'a>>,
  expr: Mapper<'a, ty::ExprKind<'a>>,
  place: Mapper<'a, ty::PlaceKind<'a>>,
  ty: Mapper<'a, ty::TyKind<'a>>,
  errors: &'n mut Vec<hir::Spanned<'a, crate::infer::TypeError<'a>>>,
  t_error: ty::Ty<'a>,
  e_error: ty::Expr<'a>,
}

impl<'a, 'n> ToGlobalCtx<'a, 'n> {
  pub(crate) fn new(
    mvars: &'n mut MVars<'a>,
    errors: &'n mut Vec<hir::Spanned<'a, crate::infer::TypeError<'a>>>,
    t_error: ty::Ty<'a>,
    e_error: ty::Expr<'a>
  ) -> Self {
    Self {
      mvars,
      errors,
      t_error,
      e_error,
      tpat: Default::default(),
      arg: Default::default(),
      expr: Default::default(),
      place: Default::default(),
      ty: Default::default(),
    }
  }
}

impl<'a> Internable<'a> for ty::TuplePatternKind<'a> {
  type Inner = TuplePatternKind;
  fn interner<'s>(ctx: &'s mut ToGlobalCtx<'a, '_>) -> &'s mut Mapper<'a, Self> { &mut ctx.tpat }
}
impl<'a> Internable<'a> for ty::ArgS<'a> {
  type Inner = ArgS;
  fn interner<'s>(ctx: &'s mut ToGlobalCtx<'a, '_>) -> &'s mut Mapper<'a, Self> { &mut ctx.arg }
}
impl<'a> Internable<'a> for ty::ExprKind<'a> {
  type Inner = ExprKind;
  fn interner<'s>(ctx: &'s mut ToGlobalCtx<'a, '_>) -> &'s mut Mapper<'a, Self> { &mut ctx.expr }
}
impl<'a> Internable<'a> for ty::PlaceKind<'a> {
  type Inner = PlaceKind;
  fn interner<'s>(ctx: &'s mut ToGlobalCtx<'a, '_>) -> &'s mut Mapper<'a, Self> { &mut ctx.place }
}
impl<'a> Internable<'a> for ty::TyKind<'a> {
  type Inner = TyKind;
  fn interner<'s>(ctx: &'s mut ToGlobalCtx<'a, '_>) -> &'s mut Mapper<'a, Self> { &mut ctx.ty }
}

pub(crate) trait ToGlobal<'a> {
  type Output;
  fn to_global(&self, ctx: &mut ToGlobalCtx<'a, '_>) -> Self::Output;
}

impl<'a, T> ToGlobal<'a> for &'a WithMeta<T>
where T: Internable<'a> + ToGlobal<'a, Output=Rc<<T as Internable<'a>>::Inner>> {
  type Output = Rc<T::Inner>;
  fn to_global(&self, ctx: &mut ToGlobalCtx<'a, '_>) -> Rc<T::Inner> {
    if let Some(e) = T::interner(ctx).get(self) { return e.clone() }
    let rc = self.k.to_global(ctx);
    T::interner(ctx).insert(self, rc.clone());
    rc
  }
}

impl<'a, T: ToGlobal<'a>> ToGlobal<'a> for &[T] {
  type Output = Box<[T::Output]>;
  fn to_global(&self, ctx: &mut ToGlobalCtx<'a, '_>) -> Box<[T::Output]> {
    self.iter().map(|t| t.to_global(ctx)).collect()
  }
}

impl<'a, T: ToGlobal<'a>> ToGlobal<'a> for [T; 2] {
  type Output = [T::Output; 2];
  fn to_global(&self, ctx: &mut ToGlobalCtx<'a, '_>) -> [T::Output; 2] {
    [self[0].to_global(ctx), self[1].to_global(ctx)]
  }
}

impl<'a, T: ToGlobal<'a>> ToGlobal<'a> for Option<T> {
  type Output = Option<T::Output>;
  fn to_global(&self, ctx: &mut ToGlobalCtx<'a, '_>) -> Option<T::Output> {
    self.as_ref().map(|t| t.to_global(ctx))
  }
}

/// A strongly typed tuple pattern.
pub type TuplePattern = Rc<TuplePatternKind>;

/// A strongly typed tuple pattern.
#[derive(Hash, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum TuplePatternKind {
  /// A variable binding.
  Name(Symbol, VarId, Ty),
  /// A tuple destructuring pattern.
  Tuple(Box<[TuplePattern]>, TupleMatchKind, Ty),
  /// An error that has been reported.
  /// (We keep the original tuple pattern so that name scoping still works.)
  Error(TuplePattern, Ty),
}

impl TuplePatternKind {
  /// Get the type of this tuple pattern.
  #[must_use] pub fn ty(&self) -> &Ty {
    match self { Self::Name(_, _, ty) | Self::Tuple(_, _, ty) | Self::Error(_, ty) => ty }
  }
}

impl<'a> ToGlobal<'a> for ty::TuplePatternKind<'a> {
  type Output = Rc<TuplePatternKind>;
  fn to_global(&self, ctx: &mut ToGlobalCtx<'a, '_>) -> Self::Output {
    Rc::new(match *self {
      ty::TuplePatternKind::Name(a, v, ty) => TuplePatternKind::Name(a, v, ty.to_global(ctx)),
      ty::TuplePatternKind::Tuple(pats, mk, ty) =>
        TuplePatternKind::Tuple(pats.to_global(ctx), mk, ty.to_global(ctx)),
      ty::TuplePatternKind::Error(pat, ty) =>
        TuplePatternKind::Error(pat.to_global(ctx), ty.to_global(ctx)),
    })
  }
}

/// An argument declaration for a function.
pub type Arg = Rc<ArgS>;
/// An argument declaration for a function.
pub type ArgS = (ArgAttr, ArgKind);

/// An argument declaration for a function.
#[derive(Hash, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum ArgKind {
  /// A standard argument of the form `{x : T}`, a "lambda binder"
  Lam(TuplePattern),
  /// A substitution argument of the form `{{x : T} := val}`. (These are not supplied in
  /// invocations, they act as let binders in the remainder of the arguments.)
  Let(TuplePattern, Expr),
}

impl ArgKind {
  /// Get the type of this tuple pattern.
  #[must_use] pub fn ty(&self) -> &Ty {
    match self { Self::Lam(arg) | Self::Let(arg, _) => arg.ty() }
  }
}

impl<'a> ToGlobal<'a> for ty::ArgS<'a> {
  type Output = Rc<ArgS>;
  fn to_global(&self, ctx: &mut ToGlobalCtx<'a, '_>) -> Self::Output {
    Rc::new((self.0, match self.1 {
      ty::ArgKind::Lam(arg) => ArgKind::Lam(arg.to_global(ctx)),
      ty::ArgKind::Let(arg, e) => ArgKind::Let(arg.to_global(ctx), e.to_global(ctx)),
    }))
  }
}

/// An embedded MM0 expression inside MMC. All free variables have been replaced by indexes,
/// with `subst` holding the internal names of these variables.
#[derive(PartialEq, Eq, Hash)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Mm0Expr<T=Expr> {
  /// The mapping from indexes in the `expr` to internal names.
  /// (The user-facing names have been erased.)
  pub subst: Box<[T]>,
  /// The root node of the expression.
  pub expr: LambdaId,
}

impl<T: std::fmt::Debug> std::fmt::Debug for Mm0Expr<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    write!(f, "{:?}", self.expr)?;
    if !self.subst.is_empty() { write!(f, "[{:?}]", self.subst.iter().format(", "))? }
    Ok(())
  }
}

impl<'a> ToGlobal<'a> for ty::Mm0Expr<'a> {
  type Output = Mm0Expr<Expr>;
  fn to_global(&self, ctx: &mut ToGlobalCtx<'a, '_>) -> Self::Output {
    Mm0Expr { subst: self.subst.to_global(ctx), expr: self.expr }
  }
}

impl<'a> ToGlobal<'a> for Lifetime {
  type Output = Lifetime;
  fn to_global(&self, ctx: &mut ToGlobalCtx<'a, '_>) -> Self::Output {
    match *self {
      Lifetime::Infer(v) => ctx.mvars.get_lft_or_assign_extern(v),
      lft => lft
    }
  }
}

/// A type, which classifies regular variables (not type variables, not hypotheses).
pub type Ty = Rc<TyKind>;

/// A type, which classifies regular variables (not type variables, not hypotheses).
#[derive(Hash, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum TyKind {
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
  Array(Ty, Expr),
  /// `own T` is a type of owned pointers. The typehood predicate is
  /// `x :> own T` iff `E. v (x |-> v) * v :> T`.
  Own(Ty),
  /// `(ref T)` is a type of borrowed values. This type is elaborated to
  /// `(ref a T)` where `a` is a lifetime; this is handled a bit differently than rust
  /// (see [`Lifetime`]).
  Ref(Lifetime, Ty),
  /// `&sn x` is the type of pointers to the place `x` (a variable or indexing expression).
  RefSn(Place),
  /// `(A, B, C)` is a tuple type with elements `A, B, C`;
  /// `sizeof (list A B C) = sizeof A + sizeof B + sizeof C`.
  List(Box<[Ty]>),
  /// `(sn {a : T})` the type of values of type `T` that are equal to `a`.
  /// This is useful for asserting that a computationally relevant value can be
  /// expressed in terms of computationally irrelevant parts.
  Sn(Expr, Ty),
  /// `{x : A, y : B, z : C}` is the dependent version of `list`;
  /// it is a tuple type with elements `A, B, C`, but the types `A, B, C` can
  /// themselves refer to `x, y, z`.
  /// `sizeof {x : A, _ : B x} = sizeof A + max_x (sizeof (B x))`.
  ///
  /// The top level declaration `(struct foo {x : A} {y : B})` desugars to
  /// `(typedef foo {x : A, y : B})`.
  Struct(Box<[Arg]>),
  /// A universally quantified proposition.
  All(TuplePattern, Ty),
  /// Implication (plain, non-separating).
  Imp(Ty, Ty),
  /// Separating implication.
  Wand(Ty, Ty),
  /// Negation.
  Not(Ty),
  /// `(and A B C)` is an intersection type of `A, B, C`;
  /// `sizeof (and A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (and A B C)` iff
  /// `x :> A /\ x :> B /\ x :> C`. (Note that this is regular conjunction,
  /// not separating conjunction.)
  And(Box<[Ty]>),
  /// `(or A B C)` is an undiscriminated anonymous union of types `A, B, C`.
  /// `sizeof (or A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (or A B C)` iff
  /// `x :> A \/ x :> B \/ x :> C`.
  Or(Box<[Ty]>),
  /// `(or A B C)` is an undiscriminated anonymous union of types `A, B, C`.
  /// `sizeof (or A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (or A B C)` iff
  /// `x :> A \/ x :> B \/ x :> C`.
  If(Expr, Ty, Ty),
  /// `(ghost A)` is a computationally irrelevant version of `A`, which means
  /// that the logical storage of `(ghost A)` is the same as `A` but the physical storage
  /// is the same as `()`. `sizeof (ghost A) = 0`.
  Ghost(Ty),
  /// `(? T)` is the type of possibly-uninitialized `T`s. The typing predicate
  /// for this type is vacuous, but it has the same size as `T`, so overwriting with
  /// a `T` is possible.
  Uninit(Ty),
  /// A boolean expression, interpreted as a pure proposition
  Pure(Expr),
  /// A user-defined type-former.
  User(Symbol, Box<[Ty]>, Box<[Expr]>),
  /// A heap assertion `l |-> (v: |T|)`.
  Heap(Expr, Expr, Ty),
  /// An explicit typing assertion `[v : T]`.
  HasTy(Expr, Ty),
  /// The input token.
  Input,
  /// The output token.
  Output,
  /// A moved-away type.
  Moved(Ty),
  /// A type error that has been reported.
  Error,
}

impl<'a> ToGlobal<'a> for ty::TyKind<'a> {
  type Output = Rc<TyKind>;
  fn to_global(&self, ctx: &mut ToGlobalCtx<'a, '_>) -> Rc<TyKind> {
    Rc::new(match *self {
      ty::TyKind::Unit => TyKind::Unit,
      ty::TyKind::True => TyKind::True,
      ty::TyKind::False => TyKind::False,
      ty::TyKind::Bool => TyKind::Bool,
      ty::TyKind::Var(v) => TyKind::Var(v),
      ty::TyKind::Int(ity) => TyKind::Int(ity),
      ty::TyKind::Array(ty, n) => TyKind::Array(ty.to_global(ctx), n.to_global(ctx)),
      ty::TyKind::Own(ty) => TyKind::Own(ty.to_global(ctx)),
      ty::TyKind::Ref(lft, ty) => TyKind::Ref(lft.to_global(ctx), ty.to_global(ctx)),
      ty::TyKind::RefSn(e) => TyKind::RefSn(e.to_global(ctx)),
      ty::TyKind::List(tys) => TyKind::List(tys.to_global(ctx)),
      ty::TyKind::Sn(a, ty) => TyKind::Sn(a.to_global(ctx), ty.to_global(ctx)),
      ty::TyKind::Struct(args) => TyKind::Struct(args.to_global(ctx)),
      ty::TyKind::All(pat, ty) => TyKind::All(pat.to_global(ctx), ty.to_global(ctx)),
      ty::TyKind::Imp(p, q) => TyKind::Imp(p.to_global(ctx), q.to_global(ctx)),
      ty::TyKind::Wand(p, q) => TyKind::Wand(p.to_global(ctx), q.to_global(ctx)),
      ty::TyKind::Not(p) => TyKind::Not(p.to_global(ctx)),
      ty::TyKind::And(ps) => TyKind::And(ps.to_global(ctx)),
      ty::TyKind::Or(ps) => TyKind::Or(ps.to_global(ctx)),
      ty::TyKind::If(c, t, e) => TyKind::If(c.to_global(ctx), t.to_global(ctx), e.to_global(ctx)),
      ty::TyKind::Ghost(ty) => TyKind::Ghost(ty.to_global(ctx)),
      ty::TyKind::Uninit(ty) => TyKind::Uninit(ty.to_global(ctx)),
      ty::TyKind::Pure(e) => TyKind::Pure(e.to_global(ctx)),
      ty::TyKind::User(f, tys, es) => TyKind::User(f, tys.to_global(ctx), es.to_global(ctx)),
      ty::TyKind::Heap(e, v, ty) =>
        TyKind::Heap(e.to_global(ctx), v.to_global(ctx), ty.to_global(ctx)),
      ty::TyKind::HasTy(e, ty) => TyKind::HasTy(e.to_global(ctx), ty.to_global(ctx)),
      ty::TyKind::Input => TyKind::Input,
      ty::TyKind::Output => TyKind::Output,
      ty::TyKind::Moved(ty) => TyKind::Moved(ty.to_global(ctx)),
      ty::TyKind::Infer(v) =>
        return ctx.mvars.err_if_not_assigned_ty(v, ctx.errors, ctx.t_error).to_global(ctx),
      ty::TyKind::Error => TyKind::Error,
    })
  }
}

/// The type of variant, or well founded order that recursions decrease.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum VariantType {
  /// This variant is a nonnegative natural number which decreases to 0.
  Down,
  /// This variant is a natural number or integer which increases while
  /// remaining less than this constant.
  UpLt(Expr),
  /// This variant is a natural number or integer which increases while
  /// remaining less than or equal to this constant.
  UpLe(Expr),
}

impl<'a> ToGlobal<'a> for hir::VariantType<'a> {
  type Output = VariantType;
  fn to_global(&self, ctx: &mut ToGlobalCtx<'a, '_>) -> Self::Output {
    match self {
      hir::VariantType::Down => VariantType::Down,
      hir::VariantType::UpLt(e) => VariantType::UpLt(e.to_global(ctx)),
      hir::VariantType::UpLe(e) => VariantType::UpLe(e.to_global(ctx)),
    }
  }
}

/// A variant is a pure expression, together with a
/// well founded order that decreases on all calls.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Variant(pub Expr, pub VariantType);

impl<'a> ToGlobal<'a> for hir::Variant<'a> {
  type Output = Variant;
  fn to_global(&self, ctx: &mut ToGlobalCtx<'a, '_>) -> Self::Output {
    Variant(self.0.to_global(ctx), self.1.to_global(ctx))
  }
}

/// A pure expression. (Regular expressions are not manipulated like types,
/// i.e. copied and substituted around, so they are in the [`hir`](super::hir) module.)
pub type Place = Rc<PlaceKind>;

/// A pure expression.
#[derive(Hash, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum PlaceKind {
  /// A variable reference.
  Var(VarId),
  /// An index operation `a[i]: T` where `a: (array T n)`
  /// and `i: nat`.
  Index(Place, Ty, Expr),
  /// If `x: (array T n)`, then `x[a..a+b]: (array T b)`.
  Slice(Place, Ty, [Expr; 2]),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(Place, Ty, u32),
  /// A type error that has been reported.
  Error,
}

impl<'a> ToGlobal<'a> for ty::PlaceKind<'a> {
  type Output = Rc<PlaceKind>;
  fn to_global(&self, ctx: &mut ToGlobalCtx<'a, '_>) -> Self::Output {
    Rc::new(match *self {
      ty::PlaceKind::Var(v) => PlaceKind::Var(v),
      ty::PlaceKind::Index(a, ty, i) =>
        PlaceKind::Index(a.to_global(ctx), ty.to_global(ctx), i.to_global(ctx)),
      ty::PlaceKind::Slice(a, ty, il) =>
        PlaceKind::Slice(a.to_global(ctx), ty.to_global(ctx), il.to_global(ctx)),
      ty::PlaceKind::Proj(a, ty, i) => PlaceKind::Proj(a.to_global(ctx), ty.to_global(ctx), i),
      ty::PlaceKind::Error => PlaceKind::Error,
    })
  }
}

/// A pure expression. (Regular expressions are not manipulated like types,
/// i.e. copied and substituted around, so they are in the [`hir`](super::hir) module.)
pub type Expr = Rc<ExprKind>;

/// A pure expression.
#[derive(Hash, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum ExprKind {
  /// A `()` literal.
  Unit,
  /// A variable reference.
  Var(VarId),
  /// A user constant.
  Const(Symbol),
  /// A number literal.
  Bool(bool),
  /// A number literal.
  Int(BigInt),
  /// A unary operation.
  Unop(Unop, Expr),
  /// A binary operation.
  Binop(Binop, Expr, Expr),
  /// An index operation `a[i]: T` where `a: (array T n)`
  /// and `i: nat`.
  Index(Expr, Expr),
  /// If `x: (array T n)`, then `x[a..a+b]: (array T b)`.
  Slice([Expr; 3]),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(Expr, u32),
  /// `(update-index a i e)` is the result of `a` after `a[i] = e`.
  UpdateIndex([Expr; 3]),
  /// `(update-slice x a b e)` is the result of assigning `x[a..a+b] = e`.
  UpdateSlice([Expr; 4]),
  /// `(update-proj x i)` is the result of assigning `x.i = e`.
  UpdateProj(Expr, u32, Expr),
  /// `(e1, ..., en)` returns a tuple of the arguments.
  List(Box<[Expr]>),
  /// `[e1, ..., en]`, an array literal.
  Array(Box<[Expr]>),
  /// Return the size of a type.
  Sizeof(Ty),
  /// A pointer to a place.
  Ref(Place),
  /// `(pure $e$)` embeds an MM0 expression `$e$` as the target type,
  /// one of the numeric types
  Mm0(Mm0Expr),
  /// A function call
  Call {
    /// The function to call.
    f: Symbol,
    /// The type arguments.
    tys: Box<[Ty]>,
    /// The function arguments.
    args: Box<[Expr]>,
  },
  /// An if-then-else expression (at either block or statement level). The initial atom names
  /// a hypothesis that the expression is true in one branch and false in the other.
  If {
    /// The if condition.
    cond: Expr,
    /// The then case.
    then: Expr,
    /// The else case.
    els: Expr
  },
  /// A type error that has been reported.
  Error,
}

impl<'a> ToGlobal<'a> for ty::ExprKind<'a> {
  type Output = Rc<ExprKind>;
  fn to_global(&self, ctx: &mut ToGlobalCtx<'a, '_>) -> Self::Output {
    Rc::new(match *self {
      ty::ExprKind::Unit => ExprKind::Unit,
      ty::ExprKind::Var(v) => ExprKind::Var(v),
      ty::ExprKind::Const(c) => ExprKind::Const(c),
      ty::ExprKind::Bool(b) => ExprKind::Bool(b),
      ty::ExprKind::Int(n) => ExprKind::Int(n.clone()),
      ty::ExprKind::Unop(op, e) => ExprKind::Unop(op, e.to_global(ctx)),
      ty::ExprKind::Binop(op, e1, e2) => ExprKind::Binop(op, e1.to_global(ctx), e2.to_global(ctx)),
      ty::ExprKind::Index(a, i) => ExprKind::Index(a.to_global(ctx), i.to_global(ctx)),
      ty::ExprKind::Slice([a, i, l]) =>
        ExprKind::Slice([a.to_global(ctx), i.to_global(ctx), l.to_global(ctx)]),
      ty::ExprKind::Proj(a, i) => ExprKind::Proj(a.to_global(ctx), i),
      ty::ExprKind::UpdateIndex([a, i, v]) =>
        ExprKind::UpdateIndex([a.to_global(ctx), i.to_global(ctx), v.to_global(ctx)]),
      ty::ExprKind::UpdateSlice([a, i, l, v]) => ExprKind::UpdateSlice(
        [a.to_global(ctx), i.to_global(ctx), l.to_global(ctx), v.to_global(ctx)]),
      ty::ExprKind::UpdateProj(a, i, v) =>
        ExprKind::UpdateProj(a.to_global(ctx), i, v.to_global(ctx)),
      ty::ExprKind::List(es) => ExprKind::List(es.to_global(ctx)),
      ty::ExprKind::Array(es) => ExprKind::Array(es.to_global(ctx)),
      ty::ExprKind::Sizeof(ty) => ExprKind::Sizeof(ty.to_global(ctx)),
      ty::ExprKind::Ref(e) => ExprKind::Ref(e.to_global(ctx)),
      ty::ExprKind::Mm0(e) => ExprKind::Mm0(e.to_global(ctx)),
      ty::ExprKind::Call {f, tys, args} =>
        ExprKind::Call {f, tys: tys.to_global(ctx), args: args.to_global(ctx)},
      ty::ExprKind::If {cond, then, els} => ExprKind::If {
        cond: cond.to_global(ctx), then: then.to_global(ctx), els: els.to_global(ctx)},
      ty::ExprKind::Infer(v) =>
        return ctx.mvars.err_if_not_assigned_expr(v, ctx.errors, ctx.e_error).to_global(ctx),
      ty::ExprKind::Error => ExprKind::Error,
    })
  }
}
