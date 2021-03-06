//! The mid level IR, a basic block based representation used for most optimizations.

use std::{collections::HashMap, ops::{Index, IndexMut}, rc::Rc};
use std::convert::{TryFrom, TryInto};
use std::mem;
use bit_vec::BitVec;
use num::BigInt;
use smallvec::SmallVec;
use crate::{AtomId, LispVal, Remap, Remapper, u32_as_usize};
use super::{IntTy, IdxVec, Spanned, ast::ProcKind, ast, global, hir,
  super::mir_opt::DominatorTree};
pub use {ast::TyVarId, hir::{Unop, Binop}};

/// The alpha conversion struct is a mapping from variables to variables.
#[derive(Debug, Default)]
pub struct Alpha(HashMap<VarId, VarId>);

impl Alpha {
  /// Insert a new variable mapping into the alpha conversion struct.
  pub fn push(&mut self, v: VarId, w: VarId) {
    if v != w { assert!(self.0.insert(v, w).is_none()) }
  }

  /// Enter a binder during alpha conversion. This suppresses substitution for a bound variable
  /// within its scope.
  fn enter<R>(&mut self, v: VarId, f: impl FnOnce(&mut Self) -> R) -> R {
    if let Some(w) = self.0.remove(&v) {
      let r = f(self);
      self.0.insert(v, w);
      r
    } else {
      f(self)
    }
  }

  /// Performs alpha conversion (var-var substitution) on a type or expression.
  pub fn alpha<T: HasAlpha + Clone>(&mut self, t: &T) -> T {
    if self.0.is_empty() { t.clone() } else { t.alpha(self) }
  }
}

/// A trait for the alpha conversion operation on subparts of a type.
pub trait HasAlpha {
  /// Applies the alpha conversion operation, producing a copy of the value.
  fn alpha(&self, a: &mut Alpha) -> Self;
}

impl<T: HasAlpha> HasAlpha for Rc<T> {
  fn alpha(&self, a: &mut Alpha) -> Self {
    Rc::new((**self).alpha(a))
  }
}

impl<T: HasAlpha> HasAlpha for Box<[T]> {
  fn alpha(&self, a: &mut Alpha) -> Self {
    self.iter().map(|e| e.alpha(a)).collect()
  }
}

impl<T: HasAlpha> HasAlpha for global::Mm0Expr<T> {
  fn alpha(&self, a: &mut Alpha) -> Self {
    Self { subst: self.subst.alpha(a), expr: self.expr.clone() }
  }
}

mk_id! {
  /// A variable ID. We use a different numbering here to avoid confusion with `VarId`s from HIR.
  VarId
}

impl std::fmt::Display for VarId {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "_{}", self.0)
  }
}

impl HasAlpha for VarId {
  fn alpha(&self, a: &mut Alpha) -> Self { *a.0.get(self).unwrap_or(self) }
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
}
crate::deep_size_0!(Lifetime);

impl HasAlpha for Lifetime {
  fn alpha(&self, a: &mut Alpha) -> Self {
    match self {
      Lifetime::Extern => Lifetime::Extern,
      Lifetime::Place(v) => Lifetime::Place(v.alpha(a))
    }
  }
}

bitflags! {
  /// Attributes on arguments in a `(struct)` dependent tuple type.
  pub struct ArgAttr: u8 {
    /// An argument is nondependent if the remainder of the type does not depend on this variable.
    const NONDEP = 1 << 0;
    /// An existential argument represents `exists x. p(x)` instead of `sigma x. p(x)`; the
    /// difference is that a witness to `exists x. p(x)` is `a` such that `a: p(x)` for some `x`,
    /// while a witness to `sigma x. p(x)` is a tuple `(x, a)` such that `a: p(x)`. Thus we cannot
    /// project out existential arguments (nor can we get the type of arguments depending on an
    /// existential argument).
    const EXISTENTIAL = 1 << 1;
    /// An singleton argument is a special case where an existential argument can support
    /// projections, because it has a singleton type (for example `()`, `sn x`, or a proposition).
    const SINGLETON = 1 << 2;
    /// A ghost argument is one that has no bit-representation; a representative of
    /// `sigma x: ghost T. p(x)` is just a representative of `p(x)`, while a representative of
    /// `sigma x: T. p(x)` is the concatenation of a representative of `T` and a representative of
    /// `p(x)`. (In other words, this is like `EXISTENTIAL` but at the computation level instead of
    /// the logical level.)
    const GHOST = 1 << 3;
  }
}
crate::deep_size_0!(ArgAttr);

impl ArgAttr {
  /// The [`GHOST`](Self::GHOST) flag modulated by a boolean.
  #[inline] #[must_use] pub fn ghost(b: bool) -> ArgAttr {
    if b { ArgAttr::GHOST } else { ArgAttr::empty() }
  }
}

impl Remap for ArgAttr {
  type Target = Self;
  fn remap(&self, _: &mut Remapper) -> Self { *self }
}

/// An argument in a struct (dependent tuple).
#[derive(Debug, DeepSizeOf)]
pub struct Arg {
  /// Extra properties of the binding
  pub attr: ArgAttr,
  /// The variable to bind
  pub var: VarId,
  /// The type of the variable
  pub ty: Ty,
}

impl Remap for Arg {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Self {
      attr: self.attr,
      var: self.var,
      ty: self.ty.remap(r),
    }
  }
}

/// The type of embedded MM0 expressions.
pub type Mm0Expr = global::Mm0Expr<Expr>;

/// A type, which classifies regular variables (not type variables, not hypotheses).
pub type Ty = Rc<TyKind>;

/// A type, which classifies regular variables (not type variables, not hypotheses).
#[derive(Debug, DeepSizeOf)]
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
  RefSn(EPlace),
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
  All(VarId, Ty, Ty),
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
  User(AtomId, Box<[Ty]>, Box<[Expr]>),
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
}

impl TyKind {
  /// Get this type as an [`IntTy`].
  #[must_use] pub fn as_int_ty(&self) -> Option<IntTy> {
    if let TyKind::Int(ity) = *self { Some(ity) } else { None }
  }
}

impl Remap for TyKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      TyKind::Unit => TyKind::Unit,
      TyKind::True => TyKind::True,
      TyKind::False => TyKind::False,
      TyKind::Bool => TyKind::Bool,
      &TyKind::Var(v) => TyKind::Var(v),
      &TyKind::Int(ity) => TyKind::Int(ity),
      TyKind::Array(ty, n) => TyKind::Array(ty.remap(r), n.remap(r)),
      TyKind::Own(ty) => TyKind::Own(ty.remap(r)),
      TyKind::Ref(lft, ty) => TyKind::Ref(*lft, ty.remap(r)),
      TyKind::RefSn(e) => TyKind::RefSn(e.remap(r)),
      TyKind::Sn(a, ty) => TyKind::Sn(a.remap(r), ty.remap(r)),
      TyKind::Struct(args) => TyKind::Struct(args.remap(r)),
      TyKind::All(v, pat, ty) => TyKind::All(*v, pat.remap(r), ty.remap(r)),
      TyKind::Imp(p, q) => TyKind::Imp(p.remap(r), q.remap(r)),
      TyKind::Wand(p, q) => TyKind::Wand(p.remap(r), q.remap(r)),
      TyKind::Not(p) => TyKind::Not(p.remap(r)),
      TyKind::And(ps) => TyKind::And(ps.remap(r)),
      TyKind::Or(ps) => TyKind::Or(ps.remap(r)),
      TyKind::If(c, t, e) => TyKind::If(c.remap(r), t.remap(r), e.remap(r)),
      TyKind::Ghost(ty) => TyKind::Ghost(ty.remap(r)),
      TyKind::Uninit(ty) => TyKind::Uninit(ty.remap(r)),
      TyKind::Pure(e) => TyKind::Pure(e.remap(r)),
      TyKind::User(f, tys, es) => TyKind::User(*f, tys.remap(r), es.remap(r)),
      TyKind::Heap(e, v, ty) =>
        TyKind::Heap(e.remap(r), v.remap(r), ty.remap(r)),
      TyKind::HasTy(e, ty) => TyKind::HasTy(e.remap(r), ty.remap(r)),
      TyKind::Input => TyKind::Input,
      TyKind::Output => TyKind::Output,
      TyKind::Moved(ty) => TyKind::Moved(ty.remap(r)),
    }
  }
}

impl HasAlpha for TyKind {
  fn alpha(&self, a: &mut Alpha) -> Self {
    macro_rules! a {($e:expr) => {$e.alpha(a)}}
    match self {
      TyKind::Unit => TyKind::Unit,
      TyKind::True => TyKind::True,
      TyKind::False => TyKind::False,
      TyKind::Bool => TyKind::Bool,
      &TyKind::Var(v) => TyKind::Var(v),
      &TyKind::Int(ity) => TyKind::Int(ity),
      TyKind::Array(ty, n) => TyKind::Array(a!(ty), a!(n)),
      TyKind::Own(ty) => TyKind::Own(a!(ty)),
      TyKind::Ref(lft, ty) => TyKind::Ref(a!(lft), a!(ty)),
      TyKind::RefSn(e) => TyKind::RefSn(a!(e)),
      TyKind::Sn(a, ty) => TyKind::Sn(a!(a), a!(ty)),
      TyKind::Struct(args) => {
        fn rec(args: &mut std::slice::Iter<'_, Arg>, a: &mut Alpha, vec: &mut Vec<Arg>) {
          loop {
            if let Some(&Arg {attr, var, ref ty}) = args.next() {
              let ty = ty.alpha(a);
              vec.push(Arg {attr, var, ty});
              if attr.contains(ArgAttr::NONDEP) { continue }
              a.enter(var, |a| rec(args, a, vec))
            }
            break
          }
        }
        let mut vec = Vec::with_capacity(args.len());
        rec(&mut args.iter(), a, &mut vec);
        TyKind::Struct(vec.into_boxed_slice())
      }
      &TyKind::All(v, ref pat, ref ty) => {
        let pat = a!(pat);
        a.enter(v, |a| TyKind::All(v, pat, ty.alpha(a)))
      }
      TyKind::Imp(p, q) => TyKind::Imp(a!(p), a!(q)),
      TyKind::Wand(p, q) => TyKind::Wand(a!(p), a!(q)),
      TyKind::Not(p) => TyKind::Not(a!(p)),
      TyKind::And(ps) => TyKind::And(a!(ps)),
      TyKind::Or(ps) => TyKind::Or(a!(ps)),
      TyKind::If(c, t, e) => TyKind::If(a!(c), a!(t), a!(e)),
      TyKind::Ghost(ty) => TyKind::Ghost(a!(ty)),
      TyKind::Uninit(ty) => TyKind::Uninit(a!(ty)),
      TyKind::Pure(e) => TyKind::Pure(a!(e)),
      TyKind::User(f, tys, es) => TyKind::User(*f, tys.clone(), a!(es)),
      TyKind::Heap(e, v, ty) =>
        TyKind::Heap(a!(e), a!(v), a!(ty)),
      TyKind::HasTy(e, ty) => TyKind::HasTy(a!(e), a!(ty)),
      TyKind::Input => TyKind::Input,
      TyKind::Output => TyKind::Output,
      TyKind::Moved(ty) => TyKind::Moved(a!(ty)),
    }
  }
}

/// The type of variant, or well founded order that recursions decrease.
#[derive(Debug, DeepSizeOf)]
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

/// A variant is a pure expression, together with a
/// well founded order that decreases on all calls.
#[derive(Debug, DeepSizeOf)]
pub struct Variant(pub Expr, pub VariantType);

/// A place expression.
pub type EPlace = Rc<EPlaceKind>;

/// A place expression, with its type. If this is `None` then it involves creating a new
/// temporary, i.e. it refers to an anonymous place.
pub type EPlaceTy = (Option<EPlace>, Ty);

/// A place expression.
#[derive(Debug, DeepSizeOf)]
pub enum EPlaceKind {
  /// A variable reference.
  Var(VarId),
  /// An index operation `(index _ i): T` where `_: (array T n)`,
  /// `i: nat`, and `h: i < n`.
  /// If `h` is the `Err` variant, then it is an expr evaluating to `n`.
  Index(EPlace, Ty, Expr),
  /// If `x: (array T n)`, then `(slice x a b): (array T b)`.
  Slice(EPlace, Ty, [Expr; 2]),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(EPlace, Ty, u32),
}

impl Remap for EPlaceKind {
  type Target = Self;
  #[allow(clippy::many_single_char_names)]
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      &EPlaceKind::Var(v) => EPlaceKind::Var(v),
      EPlaceKind::Index(a, ty, i) => EPlaceKind::Index(a.remap(r), ty.remap(r), i.remap(r)),
      EPlaceKind::Slice(a, ty, il) => EPlaceKind::Slice(a.remap(r), ty.remap(r), il.remap(r)),
      EPlaceKind::Proj(a, ty, i) => EPlaceKind::Proj(a.remap(r), ty.remap(r), *i),
    }
  }
}

impl HasAlpha for EPlaceKind {
  fn alpha(&self, a: &mut Alpha) -> Self {
    macro_rules! a {($e:expr) => {$e.alpha(a)}}
    match self {
      &EPlaceKind::Var(v) => EPlaceKind::Var(a!(v)),
      EPlaceKind::Index(a, ty, i) => EPlaceKind::Index(a!(a), a!(ty), a!(i)),
      EPlaceKind::Slice(a, ty, [i, l]) => EPlaceKind::Slice(a!(a), a!(ty), [a!(i), a!(l)]),
      EPlaceKind::Proj(a, ty, i) => EPlaceKind::Proj(a!(a), a!(ty), *i),
    }
  }
}

/// A pure expression. (Regular expressions are not manipulated like types,
/// i.e. copied and substituted around, so they are in the [`hir`](super::hir) module.)
pub type Expr = Rc<ExprKind>;

/// A pure expression. (Regular expressions are not manipulated like types,
/// i.e. copied and substituted around, so they are in the [`hir`](super::hir) module.)
pub type ExprTy = (Option<Expr>, Ty);

/// A pure expression.
#[derive(Debug, DeepSizeOf)]
pub enum ExprKind {
  /// A `()` literal.
  Unit,
  /// A variable reference.
  Var(VarId),
  /// A user constant.
  Const(AtomId),
  /// A number literal.
  Bool(bool),
  /// A number literal.
  Int(BigInt),
  /// A unary operation.
  Unop(super::Unop, Expr),
  /// A binary operation.
  Binop(super::Binop, Expr, Expr),
  /// An index operation `a[i]: T` where `a: (array T n)` and `i: nat`.
  Index(Expr, Expr),
  /// If `x: (array T n)`, then `x[a..a+b]: (array T b)`.
  Slice(Expr, Expr, Expr),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(Expr, u32),
  /// `(update-index a i e)` is the result of `a` after `a[i] = e`.
  UpdateIndex(Expr, Expr, Expr),
  /// `(update-slice x a b e)` is the result of assigning `x[a..a+b] = e`.
  UpdateSlice(Expr, Expr, Expr, Expr),
  /// `(update-proj x i)` is the result of assigning `x.i = e`.
  UpdateProj(Expr, u32, Expr),
  /// `(e1, ..., en)` returns a tuple of the arguments.
  List(Box<[Expr]>),
  /// `[e1, ..., en]`, an array literal.
  Array(Box<[Expr]>),
  /// Return the size of a type.
  Sizeof(Ty),
  /// A pointer to a place.
  Ref(EPlace),
  /// `(pure $e$)` embeds an MM0 expression `$e$` as the target type,
  /// one of the numeric types
  Mm0(Mm0Expr),
  /// A function call
  Call {
    /// The function to call.
    f: AtomId,
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
}

impl Remap for ExprKind {
  type Target = Self;
  #[allow(clippy::many_single_char_names)]
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      ExprKind::Unit => ExprKind::Unit,
      &ExprKind::Var(v) => ExprKind::Var(v),
      &ExprKind::Const(c) => ExprKind::Const(c),
      &ExprKind::Bool(b) => ExprKind::Bool(b),
      ExprKind::Int(n) => ExprKind::Int(n.clone()),
      ExprKind::Unop(op, e) => ExprKind::Unop(*op, e.remap(r)),
      ExprKind::Binop(op, e1, e2) => ExprKind::Binop(*op, e1.remap(r), e2.remap(r)),
      ExprKind::Index(a, i) => ExprKind::Index(a.remap(r), i.remap(r)),
      ExprKind::Slice(a, i, l) => ExprKind::Slice(a.remap(r), i.remap(r), l.remap(r)),
      ExprKind::Proj(a, i) => ExprKind::Proj(a.remap(r), *i),
      ExprKind::UpdateIndex(a, i, v) => ExprKind::UpdateIndex(a.remap(r), i.remap(r), v.remap(r)),
      ExprKind::UpdateSlice(a, i, l, v) =>
        ExprKind::UpdateSlice(a.remap(r), i.remap(r), l.remap(r), v.remap(r)),
      ExprKind::UpdateProj(a, i, v) => ExprKind::UpdateProj(a.remap(r), *i, v.remap(r)),
      ExprKind::List(es) => ExprKind::List(es.remap(r)),
      ExprKind::Array(es) => ExprKind::Array(es.remap(r)),
      ExprKind::Sizeof(ty) => ExprKind::Sizeof(ty.remap(r)),
      ExprKind::Ref(e) => ExprKind::Ref(e.remap(r)),
      ExprKind::Mm0(e) => ExprKind::Mm0(e.remap(r)),
      &ExprKind::Call {f, ref tys, ref args} =>
        ExprKind::Call {f, tys: tys.remap(r), args: args.remap(r)},
      ExprKind::If {cond, then, els} => ExprKind::If {
        cond: cond.remap(r), then: then.remap(r), els: els.remap(r)},
    }
  }
}

impl HasAlpha for ExprKind {
  #[allow(clippy::many_single_char_names)]
  fn alpha(&self, a: &mut Alpha) -> Self {
    macro_rules! a {($e:expr) => {$e.alpha(a)}}
    match self {
      ExprKind::Unit => ExprKind::Unit,
      ExprKind::Var(v) => ExprKind::Var(*a.0.get(v).unwrap_or(v)),
      &ExprKind::Const(c) => ExprKind::Const(c),
      &ExprKind::Bool(b) => ExprKind::Bool(b),
      ExprKind::Int(n) => ExprKind::Int(n.clone()),
      ExprKind::Unop(op, e) => ExprKind::Unop(*op, a!(e)),
      ExprKind::Binop(op, e1, e2) => ExprKind::Binop(*op, a!(e1), a!(e2)),
      ExprKind::Index(a, i) => ExprKind::Index(a!(a), a!(i)),
      ExprKind::Slice(a, i, l) => ExprKind::Slice(a!(a), a!(i), a!(l)),
      ExprKind::Proj(a, i) => ExprKind::Proj(a!(a), *i),
      ExprKind::UpdateIndex(a, i, v) => ExprKind::UpdateIndex(a!(a), a!(i), a!(v)),
      ExprKind::UpdateSlice(a, i, l, v) => ExprKind::UpdateSlice(a!(a), a!(i), a!(l), a!(v)),
      ExprKind::UpdateProj(a, i, v) => ExprKind::UpdateProj(a!(a), *i, a!(v)),
      ExprKind::List(es) => ExprKind::List(a!(es)),
      ExprKind::Array(es) => ExprKind::Array(a!(es)),
      ExprKind::Sizeof(ty) => ExprKind::Sizeof(a!(ty)),
      ExprKind::Ref(e) => ExprKind::Ref(a!(e)),
      ExprKind::Mm0(e) => ExprKind::Mm0(a!(e)),
      &ExprKind::Call {f, ref tys, ref args} =>
        ExprKind::Call {f, tys: tys.clone(), args: a!(args)},
      ExprKind::If {cond, then, els} => ExprKind::If {
        cond: a!(cond), then: a!(then), els: a!(els)},
    }
  }
}

mk_id! {
  /// A basic block ID, which is used to look up blocks in the [`Cfg`].
  BlockId
}

impl BlockId {
  /// The ID of the entry block.
  pub const ENTRY: Self = Self(0);
}

/// A vector indexed by [`BlockId`]s.
pub type BlockVec<T> = super::IdxVec<BlockId, T>;

/// A collection of contexts, maintaining a tree structure. The underlying data structure is a list
/// of `CtxBuf` structs, each of which is a `CtxId` pointer to another context, plus an additional
/// list of variables and types. The context at index 0 is the root context, and is its own parent.
#[derive(Debug, DeepSizeOf)]
pub struct Contexts(Vec<CtxBuf>);

impl Remap for Contexts {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self { Self(self.0.remap(r)) }
}

impl Index<CtxBufId> for Contexts {
  type Output = CtxBuf;
  fn index(&self, index: CtxBufId) -> &Self::Output { &self.0[index.0 as usize] }
}
impl IndexMut<CtxBufId> for Contexts {
  fn index_mut(&mut self, index: CtxBufId) -> &mut Self::Output { &mut self.0[index.0 as usize] }
}
impl Default for Contexts {
  fn default() -> Self { Self(vec![CtxBuf::default()]) }
}

impl Contexts {
  /// Given a context ID, retrieve a context buffer, ensuring that it can be directly extended by
  /// allocating a new context buffer if necessary.
  pub fn unshare(&mut self, id: &'_ mut CtxId) -> &mut CtxBuf {
    let ctx = &mut self[id.0];
    if u32::try_from(ctx.vars.len()).expect("overflow") == id.1 {
      // Safety: NLL case 3 (polonius validates this borrow pattern)
      #[allow(clippy::useless_transmute)]
      unsafe { std::mem::transmute::<&mut CtxBuf, &mut CtxBuf>(ctx) }
    } else {
      let size = ctx.size;
      let buf_id = CtxBufId(self.0.len().try_into().expect("overflow"));
      self.0.push(CtxBuf {parent: *id, size: size + id.1, vars: vec![]});
      *id = CtxId(buf_id, 1);
      unwrap_unchecked!(self.0.last_mut())
    }
  }

  /// Given a context, extend it with a variable and type to produce a new context.
  pub fn extend(&mut self, mut ctx: CtxId, var: VarId, r: bool, ty: ExprTy) -> CtxId {
    self.unshare(&mut ctx).vars.push((var, r, ty));
    ctx
  }

  /// Returns an iterator over the variables and their values, in reverse order (from most
  /// recently added to least recent). This is more efficient than forward iteration, which must
  /// keep a stack.
  pub fn rev_iter(&self, CtxId(buf, i): CtxId) -> CtxIter<'_> {
    CtxIter {ctxs: self, buf, iter: self[buf].vars[..i as usize].iter()}
  }

  /// Get the last variable pushed on a context, and its type. Panics if used on the root context.
  #[must_use] pub fn head(&self, id: CtxId) -> &(VarId, bool, ExprTy) {
    self.rev_iter(id).next().expect("not the root context")
  }

  /// Clear all computational relevance settings in the contexts.
  pub fn reset_ghost(&mut self) {
    self.0.iter_mut().for_each(|ctx| ctx.vars.iter_mut().for_each(|v| v.1 = false))
  }

  /// Set computational relevance for all variables in the context for which `vars` returns true.
  /// Note that because contexts are shared, a shared variable will be considered relevant if
  /// it is relevant in any of the contexts that share it.
  ///
  /// Returns the relevance settings applied by this method (not the shared relevance settings
  /// applied to the context).
  pub fn set_ghost(&mut self, mut id: CtxId, mut vars: impl FnMut(VarId) -> bool) -> BitVec {
    let mut buf = &mut self[id.0];
    let mut rel = BitVec::from_elem(u32_as_usize(buf.size), false);
    loop {
      for (i, (v, r, _)) in (buf.size..buf.size + id.1).zip(&mut buf.vars[..id.1 as usize]) {
        let new = vars(*v);
        *r = new;
        rel.set(u32_as_usize(i), new);
      }
      if id.0 == CtxBufId::ROOT { return rel }
      id = buf.parent;
      buf = &mut self[id.0];
    }
  }
}

/// The iterator struct returned by [`Contexts::rev_iter`].
#[must_use] #[derive(Clone, Debug)]
pub struct CtxIter<'a> {
  ctxs: &'a Contexts,
  buf: CtxBufId,
  iter: std::slice::Iter<'a, (VarId, bool, ExprTy)>,
}

impl<'a> Iterator for CtxIter<'a> {
  type Item = &'a (VarId, bool, ExprTy);
  fn next(&mut self) -> Option<Self::Item> {
    loop {
      if let Some(v) = self.iter.next_back() {return Some(v)}
      if self.buf == CtxBufId::ROOT {return None}
      *self = self.ctxs.rev_iter(self.ctxs[self.buf].parent);
    }
  }
  fn size_hint(&self) -> (usize, Option<usize>) { let l = self.len(); (l, Some(l)) }
  fn count(self) -> usize { self.len() }
}

impl ExactSizeIterator for CtxIter<'_> {
  fn len(&self) -> usize { u32_as_usize(self.ctxs[self.buf].size) + self.iter.len() }
}

/// The iterator struct returned by [`Contexts::ctx_rev_iter`].
#[must_use] #[derive(Clone)]
pub struct CtxIterWithRel<'a> {
  a: CtxIter<'a>,
  b: bit_vec::Iter<'a>,
}

impl std::fmt::Debug for CtxIterWithRel<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { "CtxIterWithRel".fmt(f) }
}

impl<'a> Iterator for CtxIterWithRel<'a> {
  type Item = (VarId, bool, &'a ExprTy);
  fn next(&mut self) -> Option<Self::Item> {
    let (v, _, ref ety) = *self.a.next()?;
    Some((v, self.b.next_back()?, ety))
  }
  fn size_hint(&self) -> (usize, Option<usize>) { self.b.size_hint() }
  fn count(self) -> usize { self.len() }
}

impl ExactSizeIterator for CtxIterWithRel<'_> {
  fn len(&self) -> usize { self.b.len() }
}

/// A function for visiting every variable in the tree contexts only once.
#[derive(Default, Debug)]
pub struct CtxVisitor(IdxVec<CtxBufId, u32>);

impl CtxVisitor {
  /// Visit all variables in the given `CtxId`, not including any variables
  /// returned by previous calls to `visit`.
  pub fn visit<'a>(&mut self,
    ctxs: &'a Contexts, mut id: CtxId, mut f: impl FnMut(&'a [(VarId, bool, ExprTy)])
  ) {
    loop {
      if self.0[id.0] >= id.1 { break }
      let ctx = &ctxs[id.0];
      f(&ctx.vars[u32_as_usize(self.0[id.0])..u32_as_usize(id.1)]);
      self.0[id.0] = id.1;
      if id.0 == CtxBufId::ROOT { break }
      id = ctx.parent;
    }
  }
}

/// The calculated predecessor information for blocks in the CFG.
pub type Predecessors = BlockVec<SmallVec<[(Edge, BlockId); 4]>>;

/// A CFG, or control flow graph, for a function. This consists of a set of basic blocks,
/// with block ID 0 being the entry block. The `ctxs` is the context data used to supply the
/// logical context at the beginning of each basic block.
#[derive(Default, Debug, DeepSizeOf)]
pub struct Cfg {
  /// The set of logical contexts for the basic blocks.
  pub ctxs: Contexts,
  /// The set of basic blocks, containing the actual code.
  pub blocks: BlockVec<BasicBlock>,
  /// The largest variable in the CFG plus one, used for generating fresh variables.
  pub max_var: VarId,
  /// The mapping from basic blocks to their predecessors, calculated lazily.
  predecessors: Option<Predecessors>,
  /// The dominator tree, calculated lazily.
  dominator_tree: Option<DominatorTree>,
}

impl Remap for Cfg {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Self {
      ctxs: self.ctxs.remap(r),
      blocks: self.blocks.remap(r),
      max_var: self.max_var,
      predecessors: self.predecessors.clone(),
      dominator_tree: self.dominator_tree.clone(),
    }
  }
}

impl Cfg {
  /// Start a new basic block with the given initial context. This block starts unfinished, that
  /// is, with an empty `Terminator`; the terminator must be filled by the time MIR construction is
  /// complete.
  pub fn new_block(&mut self, parent: CtxId) -> BlockId {
    self.blocks.push(BasicBlock::new(parent, None))
  }

  /// Calculate the predecessor information for this CFG, bypassing the cache.
  #[must_use] pub fn predecessors_uncached(&self) -> Predecessors {
    let mut preds = BlockVec::from(vec![SmallVec::new(); self.blocks.len()]);
    for (id, bl) in self.blocks.enum_iter() {
      for (e, succ) in bl.successors() { preds[succ].push((e, id)) }
    }
    preds
  }

  /// Calculate the predecessor information for this CFG, and return a reference to it.
  pub fn compute_predecessors(&mut self) -> &Predecessors {
    if let Some(preds) = &self.predecessors {
      // Safety: NLL case 3 (polonius validates this borrow pattern)
      #[allow(clippy::useless_transmute)]
      return unsafe { std::mem::transmute::<&Predecessors, &Predecessors>(preds) }
    }
    let preds = self.predecessors_uncached();
    self.predecessors.get_or_insert(preds)
  }

  /// Calculate the dominator information for this CFG, and return a reference to it.
  pub fn compute_dominator_tree(&mut self) -> &DominatorTree {
    if let Some(preds) = &self.dominator_tree {
      // Safety: NLL case 3 (polonius validates this borrow pattern)
      #[allow(clippy::useless_transmute)]
      return unsafe { std::mem::transmute::<&DominatorTree, &DominatorTree>(preds) }
    }
    let preds = self.dominator_tree_uncached();
    self.dominator_tree.get_or_insert(preds)
  }

  /// Retrieve the predecessor information for this CFG.
  /// Panics if [`compute_predecessors`](Cfg::compute_predecessors) is not called first.
  #[inline] #[must_use] pub fn predecessors(&self) -> &Predecessors {
    self.predecessors.as_ref().expect("call compute_predecessors first")
  }

  /// Retrieve the dominator tree information for this CFG.
  /// Panics if [`compute_dominator_tree`](Cfg::compute_dominator_tree) is not called first.
  #[inline] #[must_use] pub fn dominator_tree(&self) -> &DominatorTree {
    self.dominator_tree.as_ref().expect("call compute_dominator_tree first")
  }

  /// Iterator over all blocks that have not been deleted.
  pub fn blocks(&self) -> impl Iterator<Item=(BlockId, &BasicBlock)> {
    self.blocks.enum_iter().filter(|(_, bl)| !bl.is_dead())
  }

  /// Iterator over all blocks that have not been deleted.
  pub fn blocks_mut(&mut self) -> impl Iterator<Item=(BlockId, &mut BasicBlock)> {
    self.blocks.enum_iter_mut().filter(|(_, bl)| !bl.is_dead())
  }
}

impl Index<CtxBufId> for Cfg {
  type Output = CtxBuf;
  fn index(&self, index: CtxBufId) -> &CtxBuf { &self.ctxs[index] }
}
impl IndexMut<CtxBufId> for Cfg {
  fn index_mut(&mut self, index: CtxBufId) -> &mut CtxBuf { &mut self.ctxs[index] }
}
impl Index<BlockId> for Cfg {
  type Output = BasicBlock;
  fn index(&self, index: BlockId) -> &BasicBlock { &self.blocks[index] }
}
impl IndexMut<BlockId> for Cfg {
  fn index_mut(&mut self, index: BlockId) -> &mut BasicBlock { &mut self.blocks[index] }
}

mk_id! {
  /// A "context buffer ID", which points to one of the context buffers in the [`Contexts`] struct.
  CtxBufId
}
impl CtxBufId {
  /// The root context buffer is the first one; this is its own parent.
  pub const ROOT: Self = Self(0);
}

/// A context ID, which consists of a context buffer ID (which selects a context buffer from the
/// [`Contexts`]), plus an index into that buffer. The logical context denoted includes all
/// contexts in the parent chain up to the root, plus the selected context buffer up to the
/// specified index (which may be any number `<= buf.len()`).
#[derive(Copy, Clone, Debug, Default, DeepSizeOf)]
pub struct CtxId(CtxBufId, u32);

impl CtxId {
  /// The empty context.
  pub const ROOT: Self = Self(CtxBufId::ROOT, 0);
}

/// A context buffer.
#[derive(Default, Debug, DeepSizeOf)]
pub struct CtxBuf {
  /// The parent context, which this buffer is viewed as extending.
  pub parent: CtxId,
  /// The cached size of the parent context
  pub size: u32,
  /// The additional variables that this buffer adds to the context.
  pub vars: Vec<(VarId, bool, ExprTy)>,
}

impl Remap for CtxBuf {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Self { parent: self.parent, size: self.size, vars: self.vars.remap(r) }
  }
}

/// The different kinds of projection, used in defining places.
#[derive(Copy, Clone, Debug)]
pub enum ListKind {
  /// A projection `a.i` which retrieves the `i`th element of a tuple.
  Struct,
  /// A projection `a[i]` which retrieves the `i`th element of an array.
  Array,
  /// A projection `a.i` which views a conjunction type as its `i`th conjunct.
  And,
  /// A projection `a.0` which views a value `a: (sn {x : T})` type as `a.0: T`.
  Sn
}
crate::deep_size_0!(ListKind);

impl From<hir::ListKind> for ListKind {
  fn from(lk: hir::ListKind) -> Self {
    match lk {
      hir::ListKind::List |
      hir::ListKind::Struct => Self::Struct,
      hir::ListKind::Array => Self::Array,
      hir::ListKind::And => Self::And,
    }
  }
}

/// Records the types of edge in the control flow graph. This is yielded by the successor and
/// predecessor iterators, to describe, for each edge between two blocks, what kind of terminator
/// produced it.
#[derive(Copy, Clone, Debug)]
pub enum Edge {
  /// An edge from an if terminator to the `cond = true` or `cond = false` target blocks.
  If(bool),
  /// An edge from a jump to its target.
  Jump,
  /// An edge from a simple jump to its target.
  Jump1,
  /// An edge from an assert to the following block.
  Assert,
  /// An edge from a function call to the following block.
  Call,
}
crate::deep_size_0!(Edge);

/// An iterator over the successors of a basic block.
#[must_use] #[derive(Debug)]
pub struct Successors<'a>(SuccessorsState<'a>);

#[derive(Debug)]
enum SuccessorsState<'a> {
  New(&'a Terminator),
  IfNeg(BlockId),
  Zero,
}

impl<'a> Successors<'a> {
  /// Constructs a new `Successors`.
  #[inline] fn new(term: &'a Terminator) -> Self {
    Self(SuccessorsState::New(term))
  }
}

impl<'a> Iterator for Successors<'a> {
  type Item = (Edge, BlockId);
  fn next(&mut self) -> Option<Self::Item> {
    match self.0 {
      SuccessorsState::New(t) => match *t {
        Terminator::If(_, [(_, bl1), (_, bl2)]) => {
          self.0 = SuccessorsState::IfNeg(bl2);
          Some((Edge::If(true), bl1))
        }
        Terminator::Jump(bl, _) => {
          self.0 = SuccessorsState::Zero;
          Some((Edge::Jump, bl))
        }
        Terminator::Jump1(bl) => {
          self.0 = SuccessorsState::Zero;
          Some((Edge::Jump1, bl))
        }
        Terminator::Assert(_, _, _, bl) => {
          self.0 = SuccessorsState::Zero;
          Some((Edge::Assert, bl))
        }
        Terminator::Call {tgt, ..} => {
          self.0 = SuccessorsState::Zero;
          Some((Edge::Call, tgt))
        }
        Terminator::Return(_) |
        Terminator::Unreachable(_) |
        Terminator::Dead => {
          self.0 = SuccessorsState::Zero;
          None
        }
      }
      SuccessorsState::IfNeg(bl) => {
        self.0 = SuccessorsState::Zero;
        Some((Edge::If(false), bl))
      }
      SuccessorsState::Zero => None
    }
  }
}

/// A place is a sequence of projections on a local. A projection is an array index or slice,
/// dereference, or a tuple projection.
#[derive(Copy, Clone, Debug)]
pub enum Projection {
  /// A constant projection into a tuple, array, or and. These projections are generated by tuple
  /// patterns.
  Proj(ListKind, u32),
  /// A variable index into an array. `(index _ i h)`, where `h: i < n` and `_` has type
  /// `(array T n)`.
  Index(VarId, VarId),
  /// A variable slice into an array. `(slice _ i l h)`, where `h: i + l <= n` and `_` has type
  /// `(array T n)`.
  Slice(VarId, VarId, VarId),
  /// A dereference operation `(* _)` on a pointer.
  Deref,
}
crate::deep_size_0!(Projection);

impl Remap for Projection {
  type Target = Self;
  #[inline] fn remap(&self, _: &mut Remapper) -> Self { *self }
}

/// A place is a location in memory that can be read and written to.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct Place {
  /// A local variable as the source of the place.
  pub local: VarId,
  /// A list of projections on the variable to extract the relevant subpart.
  pub proj: Vec<Projection>,
}
impl Place {
  /// Construct a place directly from a local.
  #[must_use] pub fn local(local: VarId) -> Self { Self {local, proj: vec![]} }
  /// Push a projection onto a place.
  #[must_use] pub fn proj(mut self, p: Projection) -> Self { self.proj.push(p); self }

  /// (Internal) iteration over the variables used by a place (in computationally relevant
  /// positions).
  pub fn foreach_use(&self, mut f: impl FnMut(VarId)) {
    f(self.local);
    for proj in &self.proj {
      match *proj {
        Projection::Index(v, _) => f(v),
        Projection::Slice(x, l, _) => { f(x); f(l) }
        Projection::Proj(_, _) | Projection::Deref => {}
      }
    }
  }
}

impl From<VarId> for Place {
  fn from(v: VarId) -> Place { Place::local(v) }
}

impl Remap for Place {
  type Target = Self;
  #[inline] fn remap(&self, _: &mut Remapper) -> Self { self.clone() }
}

/// A constant value.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct Constant {
  /// The type and value of the constant.
  pub ety: ExprTy,
  /// The value of the constant.
  pub k: ConstKind,
}

impl Constant {
  /// Returns a unit constant.
  #[must_use] pub fn unit() -> Self {
    Self { ety: (Some(Rc::new(ExprKind::Unit)), Rc::new(TyKind::Unit)), k: ConstKind::Unit }
  }

  /// Returns a true constant.
  #[must_use] pub fn itrue() -> Self {
    Self { ety: (Some(Rc::new(ExprKind::Unit)), Rc::new(TyKind::True)), k: ConstKind::ITrue }
  }

  /// Returns an uninit constant of the specified type.
  #[must_use] pub fn uninit_core(uninit_ty: Ty) -> Self {
    Self { ety: (Some(Rc::new(ExprKind::Unit)), uninit_ty), k: ConstKind::Uninit }
  }

  /// Returns an uninit constant of the specified type.
  #[must_use] pub fn uninit(ty: Ty) -> Self {
    Self::uninit_core(Rc::new(TyKind::Uninit(ty)))
  }

  /// Returns a boolean constant.
  #[must_use] pub fn bool(b: bool) -> Self {
    Self { ety: (Some(Rc::new(ExprKind::Bool(b))), Rc::new(TyKind::Bool)), k: ConstKind::Bool }
  }

  /// Returns an integral constant.
  #[must_use] pub fn int(ty: IntTy, n: BigInt) -> Self {
    Self { ety: (Some(Rc::new(ExprKind::Int(n))), Rc::new(TyKind::Int(ty))), k: ConstKind::Int }
  }

  /// Returns the size of the specified type as a constant expression.
  #[must_use] pub fn sizeof(ty: Ty) -> Self {
    Self {
      ety: (Some(Rc::new(ExprKind::Sizeof(ty))), Rc::new(TyKind::Int(IntTy::NAT))),
      k: ConstKind::Sizeof
    }
  }

  /// Get the type in a sizeof constant.
  #[must_use] pub fn ty_as_sizeof(&self) -> &Ty {
    if_chain! {
      if let Some(e) = &self.ety.0;
      if let ExprKind::Sizeof(ty) = &**e;
      then { ty }
      else { panic!("not a sizeof constant") }
    }
  }

  /// Return a MM0 proof constant expression.
  #[must_use] pub fn mm0_proof(ty: Ty, val: LispVal) -> Self {
    Self { ety: (Some(Rc::new(ExprKind::Unit)), ty), k: ConstKind::Mm0Proof(val) }
  }

  /// Return a proof by contradiction: the referenced block adds the negation of
  #[must_use] pub fn contra(ty: Ty, bl: BlockId, v: VarId) -> Self {
    Self { ety: (Some(Rc::new(ExprKind::Unit)), ty), k: ConstKind::Contra(bl, v) }
  }

  /// Construct a constant `c as iN`, reducing integer constants and delaying anything else.
  #[must_use] pub fn as_(&self, ity: IntTy) -> Self {
    if let (ConstKind::Int, Some(ExprKind::Int(n))) = (&self.k, self.ety.0.as_deref()) {
      if let Some(n) = super::Unop::As(ity).apply_int(n) {
        return Self::int(ity, n.into_owned())
      }
    }
    Self {
      ety: (self.ety.0.clone(), Ty::new(TyKind::Int(ity))),
      k: ConstKind::As(Box::new((self.clone(), ity)))
    }
  }
}

impl Remap for Constant {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Self { ety: self.ety.remap(r), k: self.k.remap(r) }
  }
}

/// The different types of constant.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum ConstKind {
  /// A unit constant `()`.
  Unit,
  /// A true constant `()`.
  ITrue,
  /// A boolean constant.
  Bool,
  /// An integer constant.
  Int,
  /// The constant `uninit`, which has type `(? T)`. Used as an rvalue,
  /// this means the target place can receive any bit pattern.
  Uninit,
  /// A named constant.
  Const(AtomId),
  /// The size of a type, which must be evaluable at compile time.
  Sizeof,
  /// A proof embedded from MM0.
  Mm0Proof(LispVal),
  /// A proof by contradiction: This has type `cond`, where the target block exists in a context
  /// extended by `v: !cond` and ends in a proof of contradiction.
  Contra(BlockId, VarId),
  /// A constant `c as iN`, when we can't immediately work out the expression.
  As(Box<(Constant, IntTy)>),
}

impl Remap for ConstKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      Self::Unit => Self::Unit,
      Self::ITrue => Self::ITrue,
      Self::Bool => Self::Bool,
      Self::Int => Self::Int,
      Self::Uninit => Self::Uninit,
      Self::Const(a) => Self::Const(a.remap(r)),
      Self::Sizeof => Self::Sizeof,
      Self::Mm0Proof(p) => Self::Mm0Proof(p.remap(r)),
      &Self::Contra(bl, v) => Self::Contra(bl, v),
      Self::As(p) => Self::As(p.remap(r)),
    }
  }
}

/// An rvalue is an expression that can be used as the right hand side of an assignment;
/// most side-effect-free expressions fall in this category.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum Operand {
  /// Copies the value at the given place. Requires that the type of the place is a copy type.
  Copy(Place),
  /// Moves the value out of the given place, which must not be used again.
  Move(Place),
  /// Copies the moved version of the data at the given place.
  Ref(Place),
  /// Synthesize a constant value.
  Const(Box<Constant>),
}

impl Operand {
  /// Get the `Place` of this operand, unless it is not a place.
  pub fn place(&self) -> Result<&Place, &Constant> {
    match self {
      Self::Copy(p) | Self::Move(p) | Self::Ref(p) => Ok(p),
      Self::Const(c) => Err(c)
    }
  }

  /// (Internal) iteration over the variables used by an operand (in computationally relevant
  /// positions).
  pub fn foreach_use(&self, f: impl FnMut(VarId)) {
    if let Ok(p) = self.place() { p.foreach_use(f) }
  }
}

impl Remap for Operand {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      Operand::Copy(x) => Operand::Copy(x.remap(r)),
      Operand::Move(x) => Operand::Move(x.remap(r)),
      Operand::Ref(x) => Operand::Ref(x.remap(r)),
      Operand::Const(x) => Operand::Const(x.remap(r)),
    }
  }
}

impl From<Constant> for Operand {
  #[inline] fn from(c: Constant) -> Operand { Operand::Const(Box::new(c)) }
}
impl From<Place> for Operand {
  #[inline] fn from(p: Place) -> Operand { Operand::Move(p) }
}
impl From<VarId> for Operand {
  #[inline] fn from(v: VarId) -> Operand { Place::local(v).into() }
}

impl Operand {
  /// Convert an operand to an rvalue.
  #[inline] #[must_use] pub fn rv(self) -> RValue { RValue::Use(self) }
}

/// A proof that `v @ x: T` can be retyped as `v @ x': U`. That is, this operation can change
/// the pure value `x` but the bit representation `v` is unchanged.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum PunKind {
  /// * `Pun(x, Sn(None))` proves that `x: sn x`
  /// * `Pun(x, Sn(Some(h)))` proves that `x: sn y` where `h: x = y`
  Sn(Option<Operand>),
  /// `Pun(e1, And([e2, e3, .., en]))` proves that `e1` has the intersection type
  /// `T1 /\ T2 /\ .. /\ Tn`.
  And(Vec<Operand>),
  /// `Pun(e, Ptr)` reinterprets a pointer as a `u64`.
  Ptr,
  /// `Pun(v, DropAs(ck))` proves that `v @ x: iN`  given `v @ (x as iN): iN`, where the embedded
  /// cast `ck` proves `x: iN` from `x: iM`. Here `iM` is the provided `IntTy` and `iN` is
  /// implicit.
  DropAs(Box<(IntTy, CastKind)>),
}

impl Remap for PunKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      PunKind::Sn(h) => PunKind::Sn(h.remap(r)),
      PunKind::And(es) => PunKind::And(es.remap(r)),
      PunKind::Ptr => PunKind::Ptr,
      PunKind::DropAs(p) => PunKind::DropAs(p.remap(r)),
    }
  }
}

/// A proof that `v @ x: T` can be retyped as `v' @ x: U`. That is, this operation can change
/// the bit representation `v` but the pure value `x` is unchanged.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum CastKind {
  /// Convert between integral types `ity <= ity2`. The sizes are determined
  /// by the size of the input and output types.
  Int,
  /// Proof that `A` is a subtype of `B`
  Subtype(Operand),
  /// Proof that `[x : A] -* [x : B]` for the particular `x` in the cast
  Wand(Option<Operand>),
  /// Proof that `[x : B]` for the particular `x` in the cast
  Mem(Operand),
}

impl Remap for CastKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      CastKind::Int => CastKind::Int,
      CastKind::Subtype(h) => CastKind::Subtype(h.remap(r)),
      CastKind::Wand(h) => CastKind::Wand(h.remap(r)),
      CastKind::Mem(h) => CastKind::Mem(h.remap(r)),
    }
  }
}

impl Unop {
  /// Given an operation `x -> f(x)`, compute the corresponding operation
  /// `x as ity -> f(x) as ity`, where possible.
  #[must_use] pub fn as_(self, ity: IntTy) -> Option<Self> {
    match self {
      Unop::Neg(_) => Some(Unop::Neg(ity)),
      Unop::BitNot(_) => Some(Unop::BitNot(ity)),
      Unop::Not | Unop::As(_, _) => None,
    }
  }
}

impl Binop {
  /// Given an operation `x, y -> f(x, y)`, compute the corresponding operation
  /// `(x as ity, y as ity) -> f(x, y) as ity`, where possible.
  #[must_use] pub fn as_(self, ity: IntTy) -> Option<Self> {
    match self {
      Binop::Add(_) => Some(Binop::Add(ity)),
      Binop::Mul(_) => Some(Binop::Mul(ity)),
      Binop::Sub(_) => Some(Binop::Sub(ity)),
      Binop::BitAnd(_) => Some(Binop::BitAnd(ity)),
      Binop::BitOr(_) => Some(Binop::BitOr(ity)),
      Binop::BitXor(_) => Some(Binop::BitXor(ity)),
      Binop::Max(_) | Binop::Min(_) | Binop::And | Binop::Or | Binop::Shl(_) | Binop::Shr(_) |
      Binop::Le(_) | Binop::Lt(_) | Binop::Eq(_) | Binop::Ne(_) => None,
    }
  }
}

/// An rvalue is an expression that can be used as the right hand side of an assignment;
/// most side-effect-free expressions fall in this category.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum RValue {
  /// Directly use a place value or constant.
  Use(Operand),
  /// Apply a unary operator.
  Unop(Unop, Operand),
  /// Apply a binary operator.
  Binop(Binop, Operand, Operand),
  /// Apply generic equality (or disequality if `inverted = true`).
  Eq(Ty, bool, Operand, Operand),
  /// Construct an lvalue reference with the specified type, aka "bit-cast".
  Pun(PunKind, Place),
  /// Apply an identity function on values that can change the type.
  Cast(CastKind, Operand, Ty),
  /// Make a struct from the given values.
  List(Box<[Operand]>),
  /// Make an array from the given values.
  Array(Box<[Operand]>),
  /// Move the target place into a ghost variable.
  Ghost(Operand),
  /// Get a pointer to the target place.
  Borrow(Place),
  /// A pure expression lifted from MM0, based on supplied values for the substitution.
  Mm0(Box<[Operand]>),
  /// Take the type of a variable.
  Typeof(Operand),
}

impl RValue {
  /// (Internal) iteration over the variables used by an rvalue (in computationally relevant
  /// positions).
  pub fn foreach_use(&self, f: &mut impl FnMut(VarId)) {
    match self {
      RValue::Use(o) |
      RValue::Unop(_, o) |
      RValue::Cast(_, o, _) => o.foreach_use(f),
      RValue::Binop(_, o1, o2) |
      RValue::Eq(_, _, o1, o2) => { o1.foreach_use(&mut *f); o2.foreach_use(f) }
      RValue::Pun(_, p) |
      RValue::Borrow(p) => p.foreach_use(f),
      RValue::List(args) |
      RValue::Array(args) => for o in &**args { o.foreach_use(&mut *f) }
      RValue::Ghost(_) |
      RValue::Mm0(_) |
      RValue::Typeof(_) => {}
    }
  }
}

impl Remap for RValue {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      RValue::Use(e) => RValue::Use(e.remap(r)),
      RValue::Unop(op, e) => RValue::Unop(*op, e.remap(r)),
      RValue::Binop(op, e1, e2) => RValue::Binop(*op, e1.remap(r), e2.remap(r)),
      RValue::Eq(ty, inv, e1, e2) => RValue::Eq(ty.remap(r), *inv, e1.remap(r), e2.remap(r)),
      RValue::Pun(pk, e) => RValue::Pun(pk.remap(r), e.remap(r)),
      RValue::Cast(ck, ty, e) => RValue::Cast(ck.remap(r), ty.remap(r), e.remap(r)),
      RValue::List(e) => RValue::List(e.remap(r)),
      RValue::Array(e) => RValue::Array(e.remap(r)),
      RValue::Ghost(e) => RValue::Ghost(e.remap(r)),
      RValue::Borrow(e) => RValue::Borrow(e.remap(r)),
      RValue::Mm0(e) => RValue::Mm0(e.remap(r)),
      RValue::Typeof(e) => RValue::Typeof(e.remap(r)),
    }
  }
}

impl From<Operand> for RValue {
  #[inline] fn from(op: Operand) -> RValue { op.rv() }
}
impl From<Constant> for RValue {
  #[inline] fn from(c: Constant) -> RValue { Operand::from(c).rv() }
}
impl From<Place> for RValue {
  #[inline] fn from(p: Place) -> RValue { Operand::from(p).rv() }
}
impl From<VarId> for RValue {
  #[inline] fn from(v: VarId) -> RValue { Place::local(v).into() }
}

/// The different kinds of let statement.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum LetKind {
  /// A declaration of a variable with a value, `let x: T = rv;`. The `bool` is true if this
  /// variable is non-ghost.
  Let(VarId, bool, Option<Expr>),
  /// `Own(x, T, p, &sn x)` is an existential pattern match on `(own T)`, producing a
  /// value `x` and a pointer `p: &sn x`.
  Own([(VarId, bool, Ty); 2]),
}

impl LetKind {
  /// Returns true if the variables declared in this let binding are computationally relevant.
  #[must_use] pub fn relevant(&self) -> bool {
    match *self {
      LetKind::Let(_, r, _) => r,
      LetKind::Own([(_, xr, _), (_, yr, _)]) => xr || yr,
    }
  }
}

impl Remap for LetKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match *self {
      Self::Let(x, g, ref ty) => Self::Let(x, g, ty.remap(r)),
      Self::Own([(x, xg, ref xt), (y, yg, ref yt)]) =>
        Self::Own([(x, xg, xt.remap(r)), (y, yg, yt.remap(r))])
    }
  }
}

/// An individual rename `(from, to: T)` in [`Statement::Assign`].
#[derive(Clone, Debug, DeepSizeOf)]
pub struct Rename {
  /// The variable before the rename.
  pub from: VarId,
  /// The variable after the rename.
  pub to: VarId,
  /// True if variable `to` is relevant (non-ghost).
  pub rel: bool,
  /// The type of the variable after the rename.
  pub ety: ExprTy,
}

impl Remap for Rename {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Rename { from: self.from, to: self.to, rel: self.rel, ety: self.ety.remap(r) }
  }
}

/// A statement is an operation in a basic block that does not end the block. Generally this means
/// that it has simple control flow behavior, in that it always steps to the following statement
/// after performing some action that cannot fail.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum Statement {
  /// A let or tuple destructuring of values from an [`RValue`] of the specified type.
  Let(LetKind, Ty, RValue),
  /// `Assign(lhs, rhs, vars)` is the statement `lhs <- rhs`.
  /// `vars` is a list of tuples `(from, to: T)` which says that the value `from` is
  /// transformed into `to`, and `to: T` is introduced into the context.
  Assign(Place, Operand, Box<[Rename]>),
}

impl Remap for Statement {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      Self::Let(lk, ty, rv) => Self::Let(lk.remap(r), ty.remap(r), rv.remap(r)),
      Self::Assign(lhs, rhs, vars) => Self::Assign(lhs.remap(r), rhs.remap(r), vars.remap(r)),
    }
  }
}

impl Statement {
  /// The number of variables created by this statement.
  #[must_use] pub fn num_defs(&self) -> usize {
    match self {
      Statement::Let(LetKind::Let(..), _, _) => 1,
      Statement::Let(LetKind::Own(..), _, _) => 2,
      Statement::Assign(_, _, vars) => vars.len(),
    }
  }

  /// (Internal) iteration over the variables created by a statement.
  pub fn foreach_def<'a>(&'a self, mut f: impl FnMut(VarId, bool, Option<&'a Expr>, &'a Ty)) {
    match self {
      &Statement::Let(LetKind::Let(v, r, ref e), ref ty, _) => f(v, r, e.as_ref(), ty),
      &Statement::Let(LetKind::Own([(x, xr, ref xt), (y, yr, ref yt)]), _, _) => {
        f(x, xr, None, xt);
        f(y, yr, None, yt);
      }
      Statement::Assign(_, _, vars) => vars.iter().for_each(|Rename {to, rel, ety: (e, ty), ..}| {
        f(*to, *rel, e.as_ref(), ty)
      }),
    }
  }

  /// (Internal) iteration over the variables used by a statement (in computationally relevant
  /// positions).
  pub fn foreach_use(&self, f: &mut impl FnMut(VarId)) {
    match self {
      Statement::Assign(lhs, rhs, vars) => {
        let mut needed = false;
        for r in &**vars {
          if r.rel { needed = true; f(r.from) }
        }
        if needed { lhs.foreach_use(&mut *f); rhs.foreach_use(f) }
      }
      Statement::Let(lk, _, rv) => if lk.relevant() { rv.foreach_use(f) }
    }
  }
}

/// A terminator is the final statement in a basic block. Anything with nontrivial control flow
/// is a terminator, and it determines where to jump afterward.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum Terminator {
  /// A `goto label(x -> arg,*);` statement - unconditionally jump to the basic block `label`.
  /// The `x -> arg` values assign values to variables, where `x` is a variable in the context of
  /// the target and `arg` is an operand evaluated in the current basic block context.
  /// Any variables `x` that do not exist in the target context are ignored, and variables in the
  /// intersection of the two contexts are optional, where if they are not specified then they
  /// are assumed to keep their values. Variables in the target context but not the source must
  /// be specified.
  Jump(BlockId, Vec<(VarId, bool, Operand)>),
  /// Semantically equivalent to `Jump(tgt, [])`, with the additional guarantee that this jump is
  /// the only incoming edge to the target block. This is used to cheaply append basic blocks.
  Jump1(BlockId),
  /// A `return(x -> arg,*);` statement - unconditionally return from the function.
  /// The `x -> arg` values assign values to variables, where `x` is a variable in the function
  /// returns and `arg` is an operand evaluated in the current basic block context.
  Return(Vec<(VarId, bool, Operand)>),
  /// A `unreachable e;` statement takes a proof `e` of false and cancels this basic block.
  /// Later optimization passes will attempt to delete the entire block.
  Unreachable(Operand),
  /// A branch expression `if cond {h. goto l1} else {h'. goto l2}`.
  /// We require that context of `l1` extends the current one with `h: cond`,
  /// and the context of `l2` extends the current one with `h': !cond`.
  If(Operand, [(VarId, BlockId); 2]),
  /// An assert expression `if cond {h. goto l1} else {fail}`.
  /// This is lowered the same as a branch, but there is no actual `fail` basic block to
  /// jump to.
  /// The `bool` is true if the following block is reachable (i.e. this is not `assert false`).
  Assert(Operand, VarId, bool, BlockId),
  /// A `f(tys, es) -> l(xs)` function call, which calls `f` with type arguments `tys` and
  /// values `es`, and jumps to `l`, using `xs` to store the return values.
  Call {
    /// The function to call.
    f: AtomId,
    /// Is this a side-effectful function?
    /// Side effect free functions can be removed by dead code elimination.
    se: bool,
    /// The list of type arguments to the function.
    tys: Box<[Ty]>,
    /// The list of regular arguments to the function.
    args: Box<[(bool, Operand)]>,
    /// True if the block after the call is reachable (i.e. the function does not return `false`).
    reach: bool,
    /// The block after the call. This exists even if the call doesn't return, but in that case
    /// the block is purely virtual.
    tgt: BlockId,
    /// The list of variables returned from the call, which are introduced into the context of the
    /// target block.
    rets: Box<[VarId]>
  },
  /// This block is not reachable from the entry block. Similar to `unreachable`, but
  /// provides no proof of false, and it is a type error to jump to a dead block.
  Dead,
}

impl Remap for Terminator {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      Self::Jump(id, args) => Self::Jump(*id, args.remap(r)),
      &Self::Jump1(id) => Self::Jump1(id),
      Self::Return(args) => Self::Return(args.remap(r)),
      Self::Unreachable(rv) => Self::Unreachable(rv.remap(r)),
      Self::If(cond, args) => Self::If(cond.remap(r), *args),
      Self::Assert(cond, v, reach, bl) => Self::Assert(cond.remap(r), *v, *reach, *bl),
      Self::Call {f, se, tys, args, reach, tgt, rets} => Self::Call {
        f: f.remap(r), se: *se, tys: tys.remap(r), args: args.remap(r),
        reach: *reach, tgt: *tgt, rets: rets.remap(r)
      },
      Self::Dead => Self::Dead,
    }
  }
}

impl Terminator {
  /// (Internal) iteration over the variables used by a terminator (in computationally relevant
  /// positions).
  pub fn foreach_use(&self, f: &mut impl FnMut(VarId)) {
    match self {
      Terminator::Jump(_, args) |
      Terminator::Return(args) => for (_, r, o) in args { if *r { o.foreach_use(&mut *f) } }
      Terminator::Call { args, .. } => for (r, o) in &**args { if *r { o.foreach_use(&mut *f) } }
      Terminator::Unreachable(o) |
      Terminator::If(o, _) |
      Terminator::Assert(o, _, true, _) => o.foreach_use(f),
      Terminator::Assert(_, _, false, _) |
      Terminator::Jump1(_) |
      Terminator::Dead => {}
    }
  }
}

/// A basic block, which consists of an initial context (containing the logical parameters to the
/// block), followed by a list of statements, and ending with a terminator. The terminator is
/// optional only during MIR construction, and represents an "unfinished" block.
#[derive(Debug, DeepSizeOf)]
pub struct BasicBlock {
  /// The initial context on entry to the block.
  pub ctx: CtxId,
  /// The computational relevance of all the variables on entry to the block
  /// (filled by ghost propagation pass).
  pub relevance: Option<BitVec>,
  /// If false, then the current context is able to prove false,
  /// and all control paths end in `unreachable`.
  pub reachable: bool,
  /// The list of statements, which may extend the context.
  pub stmts: Vec<Statement>,
  /// The final statement, which may jump to another basic block or perform another control flow
  /// function.
  pub term: Option<Terminator>,
}

impl Remap for BasicBlock {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Self {
      ctx: self.ctx, relevance: self.relevance.clone(), reachable: self.reachable,
      stmts: self.stmts.remap(r), term: self.term.remap(r)
    }
  }
}

impl BasicBlock {
  fn new(ctx: CtxId, term: Option<Terminator>) -> Self {
    Self { ctx, relevance: None, reachable: true, stmts: vec![], term }
  }

  /// Construct an iterator over the variables in the context, using the relevance values after
  /// ghost analysis, instead of the relevance values stored in the context itself.
  /// Only callable after ghost analysis is done.
  pub fn ctx_rev_iter<'a>(&'a self, ctxs: &'a Contexts) -> CtxIterWithRel<'a> {
    let rel = self.relevance.as_ref().expect("ghost analysis not done yet");
    let a = ctxs.rev_iter(self.ctx);
    debug_assert_eq!(rel.len(), a.len());
    CtxIterWithRel { a, b: rel.iter() }
  }

  /// Finish this basic block by adding the terminator.
  /// It is a bug to terminate a basic block that is already terminated.
  pub fn terminate(&mut self, term: Terminator) {
    assert!(mem::replace(&mut self.term, Some(term)).is_none())
  }

  /// Get the terminator for this block.
  /// It is a bug to call this method if the basic block is not terminated.
  #[must_use] pub fn terminator(&self) -> &Terminator {
    self.term.as_ref().expect("unfinished block")
  }

  /// An iterator over the successors of this basic block.
  #[inline] pub fn successors(&self) -> Successors<'_> { Successors::new(self.terminator()) }

  /// A dead block constant, which can be used as the contents of a dead block.
  pub const DEAD: Self = BasicBlock {
    ctx: CtxId::ROOT,
    relevance: None,
    reachable: false,
    stmts: Vec::new(),
    term: Some(Terminator::Dead)
  };

  /// Returns true if this is a dead block, meaning that the block ID is not usable for jumping to.
  #[must_use] #[inline]
  pub fn is_dead(&self) -> bool { matches!(self.term, Some(Terminator::Dead)) }
}

/// A procedure (or function or intrinsic), a top level item similar to function declarations in C.
#[derive(Debug, DeepSizeOf)]
pub struct Proc {
  /// The type of declaration: `func`, `proc`, or `intrinsic`.
  pub kind: ProcKind,
  /// The name of the procedure.
  pub name: Spanned<AtomId>,
  /// The number of type arguments
  pub tyargs: u32,
  /// The arguments of the procedure.
  pub args: Vec<Arg>,
  /// The return values of the procedure. (Functions and procedures return multiple values in MMC.)
  pub rets: Vec<Arg>,
  /// The body of the procedure.
  pub body: Cfg,
}

impl Remap for Proc {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Self {
      kind: self.kind,
      name: self.name.remap(r),
      tyargs: self.tyargs,
      args: self.args.remap(r),
      rets: self.rets.remap(r),
      body: self.body.remap(r),
    }
  }
}
