//! The mid level IR, a basic block based representation used for most optimizations.

use std::{collections::HashMap, ops::{Index, IndexMut}, rc::Rc};
use std::mem;
use bit_vec::BitVec;
use num::BigInt;
use smallvec::SmallVec;
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;
use crate::{Symbol, mir_opt::storage::Allocations, u32_as_usize};
use super::{IntTy, Size, ProofId, LambdaId, IdxVec, Spanned, ast::ProcKind, ast, global, hir,
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
  #[must_use] fn alpha(&self, a: &mut Alpha) -> Self;
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
    Self { subst: self.subst.alpha(a), expr: self.expr }
  }
}

mk_id! {
  /// A variable ID. We use a different numbering here to avoid confusion with `VarId`s from HIR.
  VarId(Debug("v"))
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
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(Lifetime);

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
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(ArgAttr);

impl ArgAttr {
  /// The [`GHOST`](Self::GHOST) flag modulated by a boolean.
  #[inline] #[must_use] pub fn ghost(b: bool) -> ArgAttr {
    if b { ArgAttr::GHOST } else { ArgAttr::empty() }
  }
}

/// An argument in a struct (dependent tuple).
#[derive(Clone, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Arg {
  /// Extra properties of the binding
  pub attr: ArgAttr,
  /// The variable to bind
  pub var: VarId,
  /// The type of the variable
  pub ty: Ty,
}

impl std::fmt::Debug for Arg {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.attr.contains(ArgAttr::EXISTENTIAL) {
      if self.attr.contains(ArgAttr::SINGLETON) { write!(f, "sn ")? }
      else { write!(f, "ex ")? }
    }
    if self.attr.contains(ArgAttr::GHOST) { write!(f, "ghost ")? }
    write!(f, "{:?}: {:?}", self.var, self.ty)
  }
}

/// The type of embedded MM0 expressions.
pub type Mm0Expr = global::Mm0Expr<Expr>;

/// A type, which classifies regular variables (not type variables, not hypotheses).
pub type Ty = Rc<TyKind>;

/// A type, which classifies regular variables (not type variables, not hypotheses).
#[derive(Hash, PartialEq, Eq)]
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
}

impl std::fmt::Debug for TyKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    match self {
      TyKind::Var(v) => write!(f, "{:?}", v),
      TyKind::Unit => write!(f, "()"),
      TyKind::True => write!(f, "true"),
      TyKind::False => write!(f, "false"),
      TyKind::Bool => write!(f, "bool"),
      TyKind::Int(ity) => write!(f, "{}", ity),
      TyKind::Array(ty, n) => write!(f, "[{:?}; {:?}]", ty, n),
      TyKind::Own(ty) => match &**ty {
        TyKind::Ref(lft, ty) => write!(f, "&'{:?} {:?}", lft, ty),
        _ => write!(f, "own {:?}", ty)
      },
      TyKind::Ref(lft, ty) => write!(f, "ref '{:?} {:?})", &lft, ty),
      TyKind::RefSn(x) => write!(f, "&sn {:?}", x),
      TyKind::Sn(e, ty) => write!(f, "sn({:?}: {:?})", e, ty),
      TyKind::Struct(args) => write!(f, "({:?})", args.iter().format(", ")),
      TyKind::All(a, p, q) => write!(f, "A. {:?}: {:?}, {:?}", a, p, q),
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
        write!(f, "{}", name)?;
        if !tys.is_empty() { write!(f, "<{:?}>", tys.iter().format(", "))? }
        write!(f, "({:?})", es.iter().format(", "))
      }
      TyKind::Heap(x, v, t) => write!(f, "({:?} => {:?}: {:?})", x, v, t),
      TyKind::HasTy(v, t) => write!(f, "[{:?}: {:?}]", v, t),
      TyKind::Input => write!(f, "Input"),
      TyKind::Output => write!(f, "Output"),
      TyKind::Moved(ty) => write!(f, "|{:?}|", ty),
    }
  }
}

impl TyKind {
  /// Get this type as an [`IntTy`].
  #[must_use] pub fn as_int_ty(&self) -> Option<IntTy> {
    if let TyKind::Int(ity) = *self { Some(ity) } else { None }
  }

  /// Does this type have a [`TyKind::Var`]?
  #[must_use] pub fn has_tyvar(&self) -> bool {
    match self {
      TyKind::Unit |
      TyKind::True |
      TyKind::False |
      TyKind::Bool |
      TyKind::Int(_) |
      TyKind::Input |
      TyKind::Output => false,
      TyKind::Var(_) => true,
      TyKind::Own(ty) |
      TyKind::Ref(_, ty) |
      TyKind::Not(ty) |
      TyKind::Ghost(ty) |
      TyKind::Uninit(ty) |
      TyKind::Moved(ty) => ty.has_tyvar(),
      TyKind::Array(ty, n) => ty.has_tyvar() || n.has_tyvar(),
      TyKind::RefSn(p) => p.has_tyvar(),
      TyKind::Sn(e, ty) |
      TyKind::HasTy(e, ty) => e.has_tyvar() || ty.has_tyvar(),
      TyKind::Struct(tys) => tys.iter().any(|arg| arg.ty.has_tyvar()),
      TyKind::All(_, ty1, ty2) |
      TyKind::Imp(ty1, ty2) |
      TyKind::Wand(ty1, ty2) => ty1.has_tyvar() || ty2.has_tyvar(),
      TyKind::And(tys) |
      TyKind::Or(tys) => tys.iter().any(|ty| ty.has_tyvar()),
      TyKind::If(e, ty1, ty2) => e.has_tyvar() || ty1.has_tyvar() || ty2.has_tyvar(),
      TyKind::Pure(e) => e.has_tyvar(),
      TyKind::User(_, tys, es) =>
        tys.iter().any(|ty| ty.has_tyvar()) || es.iter().any(|e| e.has_tyvar()),
      TyKind::Heap(e1, e2, ty) => e1.has_tyvar() || e2.has_tyvar() || ty.has_tyvar(),
    }
  }

  /// Substitute into the type arguments of a type.
  #[must_use] pub fn subst(self: &Ty, tyargs: &[Ty]) -> Ty {
    if !tyargs.is_empty() {
      unimplemented!("type substitution")
    }
    self.clone()
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
#[derive(Debug)]
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

/// A variant is a pure expression, together with a
/// well founded order that decreases on all calls.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Variant(pub Expr, pub VariantType);

/// A place expression.
pub type EPlace = Rc<EPlaceKind>;

/// A place expression, with its type. If this is `None` then it involves creating a new
/// temporary, i.e. it refers to an anonymous place.
pub type EPlaceTy = (Option<EPlace>, Ty);

/// A place expression.
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[derive(Hash, PartialEq, Eq)]
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

impl std::fmt::Debug for EPlaceKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      EPlaceKind::Var(v) => write!(f, "{:?}", v),
      EPlaceKind::Index(arr, _, idx) => write!(f, "{:?}[{:?}]", arr, idx),
      EPlaceKind::Slice(arr, _, [idx, len]) => write!(f, "{:?}[{:?}..+{:?}]", arr, idx, len),
      EPlaceKind::Proj(e, _, j) => write!(f, "{:?}.{}", e, j),
    }
  }
}

impl EPlaceKind {
  /// Does this place expression have a [`TyKind::Var`]?
  #[must_use] pub fn has_tyvar(&self) -> bool {
    match self {
      EPlaceKind::Var(_) => false,
      EPlaceKind::Index(p, ty, e) => p.has_tyvar() || ty.has_tyvar() || e.has_tyvar(),
      EPlaceKind::Slice(p, ty, [e1, e2]) =>
        p.has_tyvar() || ty.has_tyvar() || e1.has_tyvar() || e2.has_tyvar(),
      EPlaceKind::Proj(p, ty, _) => p.has_tyvar() || ty.has_tyvar(),
    }
  }

  /// Convert this place to an expression.
  #[must_use] pub fn to_expr(&self) -> Expr {
    Rc::new(match self {
      EPlaceKind::Var(v) => ExprKind::Var(*v),
      EPlaceKind::Index(p, _, e) => ExprKind::Index(p.to_expr(), e.clone()),
      EPlaceKind::Slice(p, _, [e1, e2]) => ExprKind::Slice(p.to_expr(), e1.clone(), e2.clone()),
      EPlaceKind::Proj(p, _, i) => ExprKind::Proj(p.to_expr(), *i),
    })
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
#[derive(Hash, PartialEq, Eq)]
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
}

impl ExprKind {
  /// Does this expression have a [`TyKind::Var`]?
  #[must_use] pub fn has_tyvar(&self) -> bool {
    match self {
      ExprKind::Unit |
      ExprKind::Var(_) |
      ExprKind::Const(_) |
      ExprKind::Bool(_) |
      ExprKind::Int(_) => false,
      ExprKind::Unop(_, e) |
      ExprKind::Proj(e, _) => e.has_tyvar(),
      ExprKind::Binop(_, e1, e2) |
      ExprKind::Index(e1, e2) |
      ExprKind::UpdateProj(e1, _, e2) => e1.has_tyvar() || e2.has_tyvar(),
      ExprKind::If { cond: e1, then: e2, els: e3 } |
      ExprKind::Slice(e1, e2, e3) |
      ExprKind::UpdateIndex(e1, e2, e3) => e1.has_tyvar() || e2.has_tyvar() || e3.has_tyvar(),
      ExprKind::UpdateSlice(e1, e2, e3, e4) =>
        e1.has_tyvar() || e2.has_tyvar() || e3.has_tyvar() || e4.has_tyvar(),
      ExprKind::List(es) |
      ExprKind::Array(es) |
      ExprKind::Mm0(Mm0Expr { subst: es, ..}) => es.iter().any(|e| e.has_tyvar()),
      ExprKind::Sizeof(ty) => ty.has_tyvar(),
      ExprKind::Ref(p) => p.has_tyvar(),
      ExprKind::Call { tys, args, .. } =>
        tys.iter().all(|e| e.has_tyvar()) || args.iter().any(|e| e.has_tyvar()),
    }
  }
}

impl std::fmt::Debug for ExprKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    match self {
      ExprKind::Unit => write!(f, "()"),
      ExprKind::Var(v) => write!(f, "{:?}", v),
      ExprKind::Const(c) => write!(f, "{}", c),
      ExprKind::Bool(b) => write!(f, "{}", b),
      ExprKind::Int(n) => write!(f, "{}", n),
      ExprKind::Unop(op, e) => write!(f, "{} {:?}", op, e),
      ExprKind::Binop(op, e1, e2) => write!(f, "({:?} {} {:?})", e1, op, e2),
      ExprKind::List(es) |
      ExprKind::Array(es) => write!(f, "{:?}", es),
      ExprKind::Index(a, i) => write!(f, "{:?}[{:?}]", a, i),
      ExprKind::Slice(a, i, n) => write!(f, "{:?}[{:?}..+{:?}]", a, i, n),
      ExprKind::Proj(a, i) => write!(f, "{:?}.{}", a, i),
      ExprKind::UpdateIndex(a, i, val) => write!(f, "({:?}[{:?}] .= {:?})", a, i, val),
      ExprKind::UpdateSlice(a, i, l, val) =>
        write!(f, "({:?}[{:?}..+{:?}] .= {:?})", a, i, l, val),
      ExprKind::UpdateProj(a, n, val) => write!(f, "({:?}.{:?} .= {:?})", a, n, val),
      ExprKind::Ref(e) => write!(f, "&{:?}", e),
      ExprKind::Sizeof(ty) => write!(f, "sizeof({:?})", ty),
      ExprKind::Mm0(e) => write!(f, "{:?}", e),
      ExprKind::Call {f: func, tys, args} => {
        write!(f, "{}", func)?;
        if !tys.is_empty() { write!(f, "<{:?}>", tys.iter().format(", "))? }
        write!(f, "({:?})", args.iter().format(", "))
      }
      ExprKind::If {cond, then, els} =>
        write!(f, "if {:?} {{ {:?} }} else {{ {:?} }}", cond, then, els),
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
  BlockId(Debug("bb"))
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
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Contexts(IdxVec<CtxBufId, CtxBuf>);

impl Index<CtxBufId> for Contexts {
  type Output = CtxBuf;
  fn index(&self, index: CtxBufId) -> &Self::Output { &self.0[index] }
}
impl IndexMut<CtxBufId> for Contexts {
  fn index_mut(&mut self, index: CtxBufId) -> &mut Self::Output { &mut self.0[index] }
}
impl Default for Contexts {
  fn default() -> Self { Self(vec![CtxBuf::default()].into()) }
}

impl Contexts {
  /// The number of allocated context buffers.
  #[allow(clippy::len_without_is_empty)]
  #[must_use] pub fn len(&self) -> usize { self.0.len() }

  /// Given a context ID, retrieve a context buffer, ensuring that it can be directly extended by
  /// allocating a new context buffer if necessary.
  fn unshare(&mut self, id: &'_ mut CtxId) -> &mut CtxBuf {
    let ctx = &mut self[id.0];
    if u32::try_from(ctx.vars.len()).expect("overflow") == id.1 {
      // Safety: NLL case 3 (polonius validates this borrow pattern)
      #[allow(clippy::useless_transmute)]
      unsafe { std::mem::transmute::<&mut CtxBuf, &mut CtxBuf>(ctx) }
    } else {
      let size = ctx.size;
      let buf_id = self.0.push(CtxBuf {parent: *id, size: size + id.1, vars: vec![]});
      *id = CtxId(buf_id, 0);
      unwrap_unchecked!(self.0 .0.last_mut())
    }
  }

  /// Given a context, extend it with a variable and type to produce a new context.
  pub fn extend(&mut self, mut ctx: CtxId, var: VarId, r: bool, ty: ExprTy) -> CtxId {
    self.unshare(&mut ctx).vars.push((var, r, ty));
    ctx.1 += 1;
    ctx
  }

  /// Returns an iterator over the variables and their values, in reverse order (from most
  /// recently added to least recent). This is more efficient than forward iteration, which must
  /// keep a stack.
  pub fn rev_iter(&self, CtxId(buf, i): CtxId) -> CtxRevIter<'_> {
    CtxRevIter {ctxs: self, buf, iter: self[buf].vars[..i as usize].iter()}
  }

  /// Construct an iterator over the variables in the context, using the relevance values after
  /// ghost analysis, instead of the relevance values stored in the context itself.
  /// Only callable after ghost analysis is done.
  pub fn rev_iter_with_rel<'a>(&'a self, id: CtxId, rel: &'a BitVec) -> CtxRevIterWithRel<'a> {
    let a = self.rev_iter(id);
    debug_assert_eq!(rel.len(), a.len());
    CtxRevIterWithRel { a, b: rel.iter() }
  }

  /// Returns an iterator over the variables and their values.
  /// Prefer `rev_iter` when possible, since this has to maintain a stack.
  pub fn iter(&self, mut id: CtxId) -> CtxIter<'_> {
    let mut iters = vec![];
    loop {
      let ctx = &self[id.0];
      iters.push(&ctx.vars[..id.1 as usize]);
      if id.0 == CtxBufId::ROOT {break}
      id = ctx.parent;
    }
    iters.into_iter().rev().flatten()
  }

  /// Get the last variable pushed on a context, and its type. Panics if used on the root context.
  #[must_use] pub fn head(&self, id: CtxId) -> &(VarId, bool, ExprTy) {
    self.rev_iter(id).next().expect("not the root context")
  }

  /// Clear all computational relevance settings in the contexts.
  pub fn reset_ghost(&mut self) {
    self.0 .0.iter_mut().for_each(|ctx| ctx.vars.iter_mut().for_each(|v| v.1 = false))
  }

  /// Set computational relevance for all variables in the context for which `vars` returns true.
  /// Note that because contexts are shared, a shared variable will be considered relevant if
  /// it is relevant in any of the contexts that share it.
  ///
  /// Returns the relevance settings applied by this method (not the shared relevance settings
  /// applied to the context).
  pub fn set_ghost(&mut self, mut id: CtxId, mut vars: impl FnMut(VarId) -> bool) -> BitVec {
    let mut buf = &mut self[id.0];
    let mut rel = BitVec::from_elem(u32_as_usize(buf.size + id.1), false);
    loop {
      for (i, (v, r, _)) in (buf.size..buf.size + id.1).zip(&mut buf.vars[..u32_as_usize(id.1)]) {
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
pub struct CtxRevIter<'a> {
  ctxs: &'a Contexts,
  buf: CtxBufId,
  iter: std::slice::Iter<'a, (VarId, bool, ExprTy)>,
}

impl<'a> Iterator for CtxRevIter<'a> {
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

impl ExactSizeIterator for CtxRevIter<'_> {
  fn len(&self) -> usize { u32_as_usize(self.ctxs[self.buf].size) + self.iter.len() }
}

/// The iterator struct returned by [`Contexts::iter`].
pub type CtxIter<'a> = std::iter::Flatten<std::iter::Rev<
  std::vec::IntoIter<&'a [(VarId, bool, ExprTy)]>>>;

/// The iterator struct returned by [`BasicBlock::ctx_rev_iter`].
#[must_use] #[derive(Clone)]
pub struct CtxRevIterWithRel<'a> {
  a: CtxRevIter<'a>,
  b: bit_vec::Iter<'a>,
}

impl std::fmt::Debug for CtxRevIterWithRel<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { "CtxRevIterWithRel".fmt(f) }
}

impl<'a> Iterator for CtxRevIterWithRel<'a> {
  type Item = (VarId, bool, &'a ExprTy);
  fn next(&mut self) -> Option<Self::Item> {
    let (v, _, ref ety) = *self.a.next()?;
    Some((v, self.b.next_back()?, ety))
  }
  fn size_hint(&self) -> (usize, Option<usize>) { self.b.size_hint() }
  fn count(self) -> usize { self.len() }
}

impl ExactSizeIterator for CtxRevIterWithRel<'_> {
  fn len(&self) -> usize { self.b.len() }
}

/// The iterator struct returned by [`BasicBlock::ctx_rev_iter`].
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
    Some((v, self.b.next()?, ety))
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
#[derive(Clone, Default)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Cfg {
  /// The set of logical contexts for the basic blocks.
  pub ctxs: Contexts,
  /// The set of basic blocks, containing the actual code.
  pub blocks: BlockVec<BasicBlock>,
  /// The block tree, which encodes the reducible structure of the CFG.
  pub tree: BlockTree,
  /// The largest variable in the CFG plus one, used for generating fresh variables.
  pub max_var: VarId,
  /// The mapping from basic blocks to their predecessors, calculated lazily.
  predecessors: Option<Predecessors>,
  /// The dominator tree, calculated lazily.
  dominator_tree: Option<DominatorTree>,
}

impl std::fmt::Debug for Cfg {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    // writeln!(f, "ctxs: {:?}", self.ctxs)?;
    for (i, bl) in self.blocks() { bl.debug_fmt(Some(i), Some(&self.ctxs), f)? }
    Ok(())
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
  CtxBufId(Debug("cb"))
}
impl CtxBufId {
  /// The root context buffer is the first one; this is its own parent.
  pub const ROOT: Self = Self(0);
}

/// A context ID, which consists of a context buffer ID (which selects a context buffer from the
/// [`Contexts`]), plus an index into that buffer. The logical context denoted includes all
/// contexts in the parent chain up to the root, plus the selected context buffer up to the
/// specified index (which may be any number `<= buf.len()`).
#[derive(Copy, Clone, Default, Hash, PartialEq, Eq)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct CtxId(pub CtxBufId, pub u32);

impl CtxId {
  /// The empty context.
  pub const ROOT: Self = Self(CtxBufId::ROOT, 0);
}

impl std::fmt::Debug for CtxId {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{:?}+{}", self.0, self.1)
  }
}

/// A context buffer.
#[derive(Clone, Default, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct CtxBuf {
  /// The parent context, which this buffer is viewed as extending.
  pub parent: CtxId,
  /// The cached size of the parent context
  pub size: u32,
  /// The additional variables that this buffer adds to the context.
  pub vars: Vec<(VarId, bool, ExprTy)>,
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
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(ListKind);

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
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(Edge);

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
        Terminator::Jump(bl, _, _) => {
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
        Terminator::Exit(_) |
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
#[derive(Copy, Clone)]
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
  /// A dereference operation `(* _)` on a pointer. (This must be the first projection in the list,
  /// if present.)
  Deref,
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(Projection);

impl std::fmt::Debug for Projection {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Proj(_, i) => write!(f, ".{}", i),
      Self::Index(i, _) => write!(f, "[{}]", i),
      Self::Slice(i, l, _) => write!(f, "[{}..+{}]", i, l),
      Self::Deref => write!(f, ".*"),
    }
  }
}

/// A place is a location in memory that can be read and written to.
#[derive(Clone)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Place {
  /// A local variable as the source of the place.
  pub local: VarId,
  /// A list of projections on the variable to extract the relevant subpart.
  /// The type of each element of the list is the type *before* projecting that element.
  pub proj: Vec<(Ty, Projection)>,
}

impl std::fmt::Debug for Place {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{:?}", self.local)?;
    for (_, p) in &self.proj { write!(f, "{:?}", p)? }
    Ok(())
  }
}

impl Place {
  /// Construct a place directly from a local.
  #[must_use] pub fn local(local: VarId) -> Self { Self {local, proj: vec![]} }
  /// Push a projection onto a place.
  #[must_use] pub fn proj(mut self, p: (Ty, Projection)) -> Self { self.proj.push(p); self }
}

impl From<VarId> for Place {
  fn from(v: VarId) -> Place { Place::local(v) }
}

/// A constant value.
#[derive(Clone)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
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
  #[must_use] pub fn sizeof(sz: Size, ty: Ty) -> Self {
    Self {
      ety: (Some(Rc::new(ExprKind::Sizeof(ty))), Rc::new(TyKind::Int(IntTy::UInt(sz)))),
      k: ConstKind::Sizeof
    }
  }

  /// Get the type and size of a sizeof constant.
  #[must_use] pub fn ty_as_sizeof(&self) -> (Size, &Ty) {
    if_chain! {
      if let (Some(e), &TyKind::Int(IntTy::UInt(sz))) = (&self.ety.0, &*self.ety.1);
      if let ExprKind::Sizeof(ty) = &**e;
      then { (sz, ty) }
      else { panic!("not a sizeof constant") }
    }
  }

  /// Return a MM0 proof constant expression.
  #[must_use] pub fn mm0_proof(ty: Ty, val: ProofId) -> Self {
    Self { ety: (Some(Rc::new(ExprKind::Unit)), ty), k: ConstKind::Mm0Proof(val) }
  }

  /// Return a proof by contradiction: the referenced block adds the negation of
  #[must_use] pub fn contra(ty: Ty, bl: BlockId, v: VarId) -> Self {
    Self { ety: (Some(Rc::new(ExprKind::Unit)), ty), k: ConstKind::Contra(bl, v) }
  }

  /// Construct a constant `c as iN`, reducing integer constants and delaying anything else.
  #[must_use] pub fn as_(&self, ity: IntTy) -> Self {
    match self.k {
      ConstKind::Int => if_chain! {
        if let Some(ExprKind::Int(n)) = self.ety.0.as_deref();
        if let Some(n) = super::Unop::As(ity).apply_int(n);
        then { return Self::int(ity, n.into_owned()) }
      },
      ConstKind::Sizeof => if_chain! {
        let (sz, ty) = self.ty_as_sizeof();
        if let IntTy::UInt(sz2) = ity;
        then { return Self::sizeof(sz.min(sz2), ty.clone()) }
      },
      _ => {}
    }
    Self {
      ety: (self.ety.0.clone(), Ty::new(TyKind::Int(ity))),
      k: ConstKind::As(Box::new((self.clone(), ity)))
    }
  }
}

/// The different types of constant.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
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
  Const(Symbol),
  /// The size of a type, which must be evaluable at compile time.
  Sizeof,
  /// A proof embedded from MM0.
  Mm0Proof(ProofId),
  /// A proof by contradiction: This has type `cond`, where the target block exists in a context
  /// extended by `v: !cond` and ends in a proof of contradiction.
  Contra(BlockId, VarId),
  /// A constant `c as iN`, when we can't immediately work out the expression.
  As(Box<(Constant, IntTy)>),
}

impl std::fmt::Debug for Constant {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match &self.k {
      ConstKind::Unit => write!(f, "()"),
      ConstKind::ITrue => write!(f, "<>"),
      ConstKind::Bool |
      ConstKind::Int => self.ety.0.as_ref().expect("illformed").fmt(f),
      ConstKind::Uninit => write!(f, "uninit"),
      ConstKind::Const(s) => write!(f, "({}: {:?})", s, self.ety.1),
      ConstKind::Sizeof => write!(f, "sizeof {:?}", self.ety.1),
      ConstKind::Mm0Proof(p) => p.fmt(f),
      ConstKind::Contra(_, _) => write!(f, "(contra: {:?})", self.ety.1),
      ConstKind::As(c) => write!(f, "({:?} as {:?})", c.0, c.1),
    }
  }
}

/// An rvalue is an expression that can be used as the right hand side of an assignment;
/// most side-effect-free expressions fall in this category.
#[derive(Clone)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
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

impl std::fmt::Debug for Operand {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Copy(p) => p.fmt(f),
      Self::Move(p) => write!(f, "move {:?}", p),
      Self::Ref(p) => write!(f, "ref {:?}", p),
      Self::Const(c) => c.fmt(f),
    }
  }
}

impl Operand {
  /// Get the `Place` of this operand, unless it is not a place.
  pub fn place(&self) -> Result<&Place, &Constant> {
    match self {
      Self::Copy(p) | Self::Move(p) | Self::Ref(p) => Ok(p),
      Self::Const(c) => Err(c)
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
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
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

/// A proof that `v @ x: T` can be retyped as `v' @ x: U`. That is, this operation can change
/// the bit representation `v` but the pure value `x` is unchanged.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
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
#[derive(Clone)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
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
  Mm0(LambdaId, Box<[Operand]>),
  /// Take the type of a variable.
  Typeof(Operand),
}

impl std::fmt::Debug for RValue {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Use(o) => o.fmt(f),
      Self::Unop(Unop::As(_, ity), o) => write!(f, "{:?} as {:?}", o, ity),
      Self::Unop(op, o) => write!(f, "{:?} {:?}", op, o),
      Self::Binop(op, o1, o2) => write!(f, "{:?} {:?} {:?}", o1, op, o2),
      Self::Eq(_, false, o1, o2) => write!(f, "{:?} == {:?}", o1, o2),
      Self::Eq(_, true, o1, o2) => write!(f, "{:?} != {:?}", o1, o2),
      Self::Pun(_, p) => write!(f, "pun {:?}", p),
      Self::Cast(_, o, ty) => write!(f, "cast ({:?}: {:?})", o, ty),
      Self::List(os) |
      Self::Array(os) => write!(f, "{:?}", os),
      Self::Ghost(o) => write!(f, "ghost {:?}", o),
      Self::Borrow(p) => write!(f, "&{:?}", p),
      Self::Mm0(l, os) => write!(f, "pure {:?}{:?}", l, os),
      Self::Typeof(e) => write!(f, "typeof {:?}", e),
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
#[derive(Clone)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum LetKind {
  /// A declaration of a variable with a value, `let x: T = rv;`. The `bool` is true if this
  /// variable is non-ghost.
  Let(VarId, bool, Option<Expr>),
  /// `Own(x, T, p, &sn x)` is an existential pattern match on `(own T)`, producing a
  /// value `x` and a pointer `p: &sn x`.
  Own([(VarId, bool, Ty); 2]),
}

impl std::fmt::Debug for LetKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match *self {
      Self::Let(v, r, ref e) => {
        write!(f, "{}{:?}", if r {""} else {"ghost "}, v)?;
        if let Some(e) = e { write!(f, " => {:?}", e)? }
        Ok(())
      },
      Self::Own([(v1, r1, _), (v2, r2, _)]) =>
        write!(f, "({}{:?}, {}{:?})",
          if r1 {""} else {"ghost "}, v1, if r2 {""} else {"ghost "}, v2),
    }
  }
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

/// An individual rename `(from, to: T)` in [`Statement::Assign`].
#[derive(Clone)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
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

impl std::fmt::Debug for Rename {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{:?} -> {}{:?}", self.from, if self.rel {""} else {"ghost "}, self.to)
  }
}

/// A statement is an operation in a basic block that does not end the block. Generally this means
/// that it has simple control flow behavior, in that it always steps to the following statement
/// after performing some action that cannot fail.
#[derive(Clone)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum Statement {
  /// A let or tuple destructuring of values from an [`RValue`] of the specified type.
  Let(LetKind, Ty, RValue),
  /// `Assign(lhs, T, rhs, vars)` is the statement `lhs: T <- rhs`.
  /// `vars` is a list of tuples `(from, to: T)` which says that the value `from` is
  /// transformed into `to`, and `to: T` is introduced into the context.
  Assign(Place, Ty, Operand, Box<[Rename]>),
  /// Declare that we may backward-jump to any of the blocks in this list.
  /// This is used to forward declare blocks like the start block in a while or label.
  /// The block's context must extend the context at this point in the basic block
  /// (which is an argument to the statement declaration).
  /// This is a ghost operation which does nothing to the state.
  LabelGroup(SmallVec<[BlockId; 2]>, CtxId),
  /// Exit the scope of a previously declared label group.
  PopLabelGroup,
  /// Declare that we may forward-jump to this block. This is used to forward declare
  /// blocks like the block after an if statement or while.
  /// The block's context must extend the context at this point in the basic block
  /// (the argument to this statement is the initial context, and the block's context
  /// is the derived context).
  /// This is a ghost operation which does nothing to the state.
  DominatedBlock(BlockId, CtxId),
}

impl std::fmt::Debug for Statement {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    match self {
      Self::Let(lk, ty, rv) => write!(f, "let {:?}: {:?} := {:?}", lk, ty, rv),
      Self::Assign(lhs, ty, rhs, renames) =>
        write!(f, "{:?}: {:?} <- {:?}, with {:?}", lhs, ty, rhs, renames),
      Self::LabelGroup(bls, _) => write!(f, "label_group({:?})", bls.iter().format(", ")),
      Self::PopLabelGroup => write!(f, "pop_label_group"),
      Self::DominatedBlock(bl, _) => write!(f, "dominated_block({:?})", bl),
    }
  }
}

impl Statement {
  /// True if this statement is computationally relevant.
  #[must_use] pub fn relevant(&self) -> bool {
    match self {
      Self::Let(lk, _, _) => lk.relevant(),
      Self::Assign(_, _, _, vars) => vars.iter().any(|v| v.rel),
      Self::LabelGroup(..) | Self::PopLabelGroup | Self::DominatedBlock(..) => false,
    }
  }

  /// The number of variables created by this statement.
  #[must_use] pub fn num_defs(&self) -> usize {
    match self {
      Self::Let(LetKind::Let(..), _, _) => 1,
      Self::Let(LetKind::Own(..), _, _) => 2,
      Self::Assign(_, _, _, vars) => vars.len(),
      Self::LabelGroup(..) | Self::PopLabelGroup | Self::DominatedBlock(..) => 0,
    }
  }

  /// (Internal) iteration over the variables created by a statement.
  pub fn foreach_def<'a>(&'a self, mut f: impl FnMut(VarId, bool, Option<&'a Expr>, &'a Ty)) {
    match self {
      &Self::Let(LetKind::Let(v, r, ref e), ref ty, _) => f(v, r, e.as_ref(), ty),
      &Self::Let(LetKind::Own([(x, xr, ref xt), (y, yr, ref yt)]), _, _) => {
        f(x, xr, None, xt);
        f(y, yr, None, yt);
      }
      Self::Assign(_, _, _, vars) =>
        vars.iter().for_each(|Rename {to, rel, ety: (e, ty), ..}| {
          f(*to, *rel, e.as_ref(), ty)
        }),
      Self::LabelGroup(..) | Self::PopLabelGroup | Self::DominatedBlock(..) => {}
    }
  }

  /// (Internal) iteration over the variables used by a statement (in computationally relevant
  /// positions).
  pub fn foreach_use(&self, f: &mut impl FnMut(VarId)) {
    UseVisitor(f).visit_stmt(self)
  }
}

/// A terminator is the final statement in a basic block. Anything with nontrivial control flow
/// is a terminator, and it determines where to jump afterward.
#[derive(Clone)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum Terminator {
  /// A `goto label(x -> arg,*);` statement - unconditionally jump to the basic block `label`.
  /// The `x -> arg` values assign values to variables, where `x` is a variable in the context of
  /// the target and `arg` is an operand evaluated in the current basic block context.
  /// Any variables `x` that do not exist in the target context are ignored, and variables in the
  /// intersection of the two contexts are optional, where if they are not specified then they
  /// are assumed to keep their values. Variables in the target context but not the source must
  /// be specified.
  ///
  /// This is the only terminator that admits back-edges, and the final argument is the variant,
  /// a ghost value to prove that this jump decreases the variant of the target.
  Jump(BlockId, Vec<(VarId, bool, Operand)>, Option<Operand>),
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
    f: Symbol,
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
    rets: Box<[(bool, VarId)]>
  },
  /// Successfully exit the program.
  /// The operand should be a proof of the postcondition of the program.
  Exit(Operand),
  /// This block is not reachable from the entry block. Similar to `unreachable`, but
  /// provides no proof of false, and it is a type error to jump to a dead block.
  Dead,
}

impl std::fmt::Debug for Terminator {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    struct DebugArg<'a>(&'a (VarId, bool, Operand));
    impl std::fmt::Debug for DebugArg<'_> {
      fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (v, b, ref o) = *self.0;
        write!(f, "{}{:?} := {:?}", if b {""} else {"ghost "}, v, o)
      }
    }
    use itertools::Itertools;
    match self {
      Self::Jump(bl, args, variant) => {
        write!(f, "jump {:?}({:?})", bl, args.iter().map(DebugArg).format(", "))?;
        if let Some(var) = variant { write!(f, " variant {:?}", var)? }
        Ok(())
      },
      Self::Jump1(bl) => write!(f, "jump {:?}", bl),
      Self::Return(args) => write!(f, "return {:?}", args.iter().map(DebugArg).format(", ")),
      Self::Unreachable(o) => write!(f, "unreachable {:?}", o),
      Self::If(cond, [(v1, bl1), (v2, bl2)]) => write!(f,
        "if {:?} then {:?}. {:?} else {:?}. {:?}", cond, v1, bl1, v2, bl2),
      Self::Assert(cond, v, true, bl) => write!(f, "assert {:?} -> {:?}. {:?}", cond, v, bl),
      Self::Assert(cond, _, false, _) => write!(f, "assert {:?} -> !", cond),
      Self::Call { f: func, tys, args, reach, tgt, rets, .. } => {
        write!(f, "call {}", func)?;
        if !tys.is_empty() { write!(f, "<{:?}>", tys.iter().format(", "))? }
        write!(f, "(")?;
        let mut first = true;
        for &(r, ref o) in &**args {
          if first { first = false } else { write!(f, ", ")? }
          write!(f, "{}{:?}", if r {""} else {"ghost "}, o)?
        }
        write!(f, ") -> ")?;
        if *reach {
          for &(r, v) in &**rets { write!(f, "{}{:?}.", if r {""} else {"ghost "}, v)? }
          write!(f, " {:?}", tgt)
        } else {
          write!(f, "!")
        }
      }
      Self::Exit(o) => write!(f, "exit {:?}", o),
      Self::Dead => write!(f, "dead")
    }
  }
}

impl Terminator {
  /// (Internal) iteration over the variables used by a terminator (in computationally relevant
  /// positions).
  pub fn foreach_use(&self, f: impl FnMut(VarId)) {
    UseVisitor(f).visit_terminator(self)
  }
}

pub(crate) trait Visitor {
  fn visit_var(&mut self, _: VarId) {}

  fn visit_place(&mut self, p: &Place) {
    self.visit_var(p.local);
    for proj in &p.proj {
      match proj.1 {
        Projection::Index(v, _) => self.visit_var(v),
        Projection::Slice(x, l, _) => { self.visit_var(x); self.visit_var(l) }
        Projection::Proj(_, _) | Projection::Deref => {}
      }
    }
  }

  fn visit_constant(&mut self, _: &Constant) {}

  fn visit_operand(&mut self, o: &Operand) {
    match o.place() {
      Ok(p) => self.visit_place(p),
      Err(c) => self.visit_constant(c),
    }
  }

  fn visit_rvalue(&mut self, rv: &RValue) {
    match rv {
      RValue::Use(o) |
      RValue::Unop(_, o) |
      RValue::Cast(_, o, _) => self.visit_operand(o),
      RValue::Binop(_, o1, o2) |
      RValue::Eq(_, _, o1, o2) => { self.visit_operand(o1); self.visit_operand(o2) }
      RValue::Pun(_, p) |
      RValue::Borrow(p) => self.visit_place(p),
      RValue::List(args) |
      RValue::Array(args) => for o in &**args { self.visit_operand(o) }
      RValue::Ghost(_) |
      RValue::Mm0(..) |
      RValue::Typeof(_) => {}
    }
  }

  fn visit_stmt(&mut self, s: &Statement) {
    match s {
      Statement::Assign(lhs, _, rhs, vars) => {
        let mut needed = false;
        for r in &**vars {
          if r.rel { needed = true; self.visit_var(r.from) }
        }
        if needed { self.visit_place(lhs); self.visit_operand(rhs) }
      }
      Statement::Let(lk, _, rv) => if lk.relevant() { self.visit_rvalue(rv) }
      Statement::LabelGroup(..) | Statement::PopLabelGroup | Statement::DominatedBlock(..) => {}
    }
  }

  fn visit_terminator(&mut self, term: &Terminator) {
    match term {
      Terminator::Jump(_, args, _) |
      Terminator::Return(args) => for (_, r, o) in args { if *r { self.visit_operand(o) } }
      Terminator::Call { args, .. } => for (r, o) in &**args { if *r { self.visit_operand(o) } }
      Terminator::Unreachable(o) |
      Terminator::Exit(o) |
      Terminator::If(o, _) |
      Terminator::Assert(o, _, true, _) => self.visit_operand(o),
      Terminator::Assert(_, _, false, _) |
      Terminator::Jump1(_) |
      Terminator::Dead => {}
    }
  }

  fn visit_basic_block(&mut self, bl: &BasicBlock) {
    if !bl.is_dead() {
      for s in &bl.stmts {
        self.visit_stmt(s)
      }
      if let Some(t) = &bl.term {
        self.visit_terminator(t)
      }
    }
  }
}

/// A visitor that calls the function `F` on every computationally relevant use of a variable.
struct UseVisitor<F>(F);

impl<F: FnMut(VarId)> Visitor for UseVisitor<F> {
  fn visit_var(&mut self, v: VarId) { (self.0)(v) }
}

/// A basic block, which consists of an initial context (containing the logical parameters to the
/// block), followed by a list of statements, and ending with a terminator. The terminator is
/// optional only during MIR construction, and represents an "unfinished" block.
#[derive(Clone)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
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

impl std::fmt::Debug for BasicBlock {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.debug_fmt(None, None, f)
  }
}

impl BasicBlock {
  fn new(ctx: CtxId, term: Option<Terminator>) -> Self {
    Self { ctx, relevance: None, reachable: true, stmts: vec![], term }
  }

  /// Construct an iterator over the variables in the context, using the relevance values after
  /// ghost analysis, instead of the relevance values stored in the context itself.
  /// Only callable after ghost analysis is done.
  pub fn ctx_rev_iter<'a>(&'a self, ctxs: &'a Contexts) -> CtxRevIterWithRel<'a> {
    let rel = self.relevance.as_ref().expect("ghost analysis not done yet");
    ctxs.rev_iter_with_rel(self.ctx, rel)
  }

  /// Construct an iterator over the variables in the context, using the relevance values after
  /// ghost analysis, instead of the relevance values stored in the context itself.
  /// Only callable after ghost analysis is done.
  pub fn ctx_iter<'a>(&'a self, ctxs: &'a Contexts) -> CtxIterWithRel<'a> {
    let rel = self.relevance.as_ref().expect("ghost analysis not done yet");
    let a = ctxs.iter(self.ctx);
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

  fn debug_fmt(&self,
    name: Option<BlockId>, ctxs: Option<&Contexts>,
    f: &mut std::fmt::Formatter<'_>
  ) -> std::fmt::Result {
    if !self.reachable { write!(f, "ghost ")? }
    if let Some(n) = name { write!(f, "{:?}", n)? } else { write!(f, "bb?")? }
    if let Some(ctxs) = ctxs {
      write!(f, "(")?;
      let long_layout = ctxs.rev_iter(self.ctx).len() > 3;
      if long_layout { writeln!(f)? }
      let mut first = true;
      let mut write = |v, r, e: &Option<_>, ty| {
        if long_layout { write!(f, "    ")? }
        else if !std::mem::take(&mut first) { write!(f, ", ")? }
        write!(f, "{}{:?}", if r {""} else {"ghost "}, v)?;
        if let Some(e) = e { write!(f, " => {:?}", e)? }
        write!(f, ": {:?}", ty)?;
        if long_layout { writeln!(f, ",")? }
        Ok(())
      };
      if self.relevance.is_some() {
        for (v, r, (e, ty)) in self.ctx_iter(ctxs) { write(v, r, e, ty)? }
      } else {
        for &(v, r, (ref e, ref ty)) in ctxs.iter(self.ctx) { write(v, r, e, ty)? }
      }
      write!(f, ")")?
    } else {
      write!(f, "({:?})", self.ctx)?
    }
    writeln!(f, ":")?;
    for s in &self.stmts { writeln!(f, "    {:?};", s)? }
    match &self.term {
      None => writeln!(f, "    ..."),
      Some(t) => writeln!(f, "    {:?};", t),
    }
  }
}

/// The block tree is a spanning tree of (parts of) the CFG with the following properties:
///
/// * The entry is in the block tree
/// * If B is in the CFG and is the target of a [`Terminator::Jump`], then it is in the block tree
///
/// Here "`B` is in the block tree" means that `One(B)` appears somewhere in the tree.
/// (In `LabelGroup(ls, t)`, every block in `ls` also appears in `t`).
///
/// The context C of a block in the tree is defined as:
/// * The outermost context is empty
/// * If `LabelGroup(ls, t)` is in context `C`, then `Many(t)` has context `C' = C ++ ls`
/// * If `Many(ls)` is in context `C`, then `ls[i]` is in context `C ++ ls[i+1..]`
/// * If `One(B)` is in context `C`, then `B` is closed in `C`, where:
///
/// A block `B` in the CFG is closed in a set `S` of blocks if:
/// * If it terminates in `Jump(s)` then `s` is in `S`
/// * If it terminates in a `Jump1`, `Assert` or `Call` going to `B'` then `B'` is closed in `S`
/// * Otherwise, it is closed in `S`
///
/// In other words, the block tree enumerates all the jump targets, in such a way that every
/// block jumps forward in the `Many` order, except for back-edges that are represented as
/// `LabelGroup` nodes in the tree.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum BlockTree {
  /// A label group, which makes the list of `BlockId`s available as jump targets in
  /// the remainder of the list.
  LabelGroup(Box<(SmallVec<[BlockId; 2]>, Vec<BlockTree>)>),
  /// A topological order on blocks, such that all jumps only go to blocks later in
  /// the list (or to blocks in the context up the tree).
  Many(Vec<BlockTree>),
  /// An individual block.
  One(BlockId),
}

impl Default for BlockTree {
  fn default() -> Self { Self::One(BlockId::ENTRY) }
}

/// A procedure (or function or intrinsic), a top level item similar to function declarations in C.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Proc {
  /// The type of declaration: `func`, `proc`, or `intrinsic`.
  pub kind: ProcKind,
  /// The name of the procedure.
  pub name: Spanned<Symbol>,
  /// The number of type arguments
  pub tyargs: u32,
  /// The arguments of the procedure.
  pub args: Vec<Arg>,
  /// The return values of the procedure. (Functions and procedures return multiple values in MMC.)
  pub rets: Vec<Arg>,
  /// The body of the procedure.
  pub body: Cfg,
  /// The result of the allocation pass, created once optimization is done.
  pub(crate) allocs: Option<Rc<Allocations>>,
}
