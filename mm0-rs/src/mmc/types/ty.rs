//! Types used in the rest of the compiler.

use std::{fmt::Display, ops::BitOrAssign};
use num::BigInt;
use crate::elab::{environment::AtomId, lisp::print::{EnvDisplay, FormatEnv}};
use super::{Binop, Mm0ExprNode, Size, Unop, VarId, ast::TyVarId};

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
    /// Does this type/expr have an `Error` subexpression?
    const HAS_ERROR     = 1 << 4;
    /// Does this type/expr have a metavariable?
    const HAS_MVAR =
      Self::HAS_TY_MVAR.bits | Self::HAS_PROP_MVAR.bits |
      Self::HAS_EXPR_MVAR.bits | Self::HAS_LFT_MVAR.bits;
  }
}
crate::deep_size_0!(Flags);

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
#[derive(Debug, DeepSizeOf)]
pub struct WithMeta<T> {
  /// The flags.
  pub flags: Flags,
  /// The kind data.
  pub k: T
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
impl<T: EnvDisplay> EnvDisplay for WithMeta<T> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.k.fmt(fe, f)
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

macro_rules! mk_id {($($id:ident),*) => {$(
  /// A newtype wrapper around IDs to avoid mixing ID types.
  #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
  pub struct $id(pub u32);
  crate::deep_size_0!($id);

  impl<'a> super::super::union_find::UnifyKey for $id {
    fn index(&self) -> u32 { self.0 }
    fn from_index(u: u32) -> Self { $id(u) }
  }
)*}}
mk_id!(TyMVarId, PropMVarId, ExprMVarId, LftMVarId);

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
crate::deep_size_0!(Lifetime);

impl std::fmt::Display for Lifetime {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Lifetime::Extern => "extern".fmt(f),
      Lifetime::Place(v) => v.fmt(f),
      Lifetime::Infer(_) => "_".fmt(f),
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
#[derive(Copy, Clone, Debug, DeepSizeOf, PartialEq, Eq, Hash)]
pub enum Coercion<'a> {
  /// An error coercion maps `X -> Y` for any `X, Y`. To use this variant,
  /// an error must have been previously reported regarding this type error.
  Error,
  /// A fake variant so that `Coercion` depends on `'a`.
  /// Will be deleted when the real thing arrives.
  Phantom(&'a ())
}

impl BitOrAssign<Coercion<'_>> for Flags {
  fn bitor_assign(&mut self, coe: Coercion<'_>) {
    match coe {
      Coercion::Error => *self |= Flags::HAS_ERROR,
      Coercion::Phantom(_) => unreachable!()
    }
  }
}

/// A strongly typed tuple pattern.
pub type TuplePattern<'a> = &'a TuplePatternS<'a>;
/// A strongly typed tuple pattern.
pub type TuplePatternS<'a> = WithMeta<TuplePatternKind<'a>>;

/// A strongly typed tuple pattern.
#[derive(Debug, DeepSizeOf, PartialEq, Eq, Hash)]
pub enum TuplePatternKind<'a> {
  /// A variable binding.
  Name(VarId, Ty<'a>),
  /// An inline coercion.
  Coercion(TuplePattern<'a>, &'a [Coercion<'a>], Ty<'a>),
  /// A tuple destructuring pattern.
  Tuple(&'a [TuplePattern<'a>], Ty<'a>),
}

impl<'a> TuplePatternKind<'a> {
  /// The type of values that will be matched by the pattern.
  pub fn ty(&self) -> Ty<'a> {
    match *self {
      TuplePatternKind::Name(_, ty) |
      TuplePatternKind::Coercion(_, _, ty) |
      TuplePatternKind::Tuple(_, ty) => ty
    }
  }
}

impl AddFlags for TuplePatternKind<'_> {
  fn add(&self, f: &mut Flags) {
    match *self {
      TuplePatternKind::Name(_, ty) => *f |= ty,
      TuplePatternKind::Coercion(pat, cs, ty) => *f |= (pat, cs, ty),
      TuplePatternKind::Tuple(pats, ty) => *f |= (pats, ty),
    }
  }
}

impl EnvDisplay for TuplePatternKind<'_> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    match *self {
      TuplePatternKind::Name(v, _) => write!(f, "v{}", v),
      TuplePatternKind::Coercion(pat, _, _) => pat.fmt(fe, f),
      TuplePatternKind::Tuple(pats, _) =>
        write!(f, "({})", pats.iter().map(|&pat| fe.to(pat)).format(" ")),
    }
  }
}

/// An argument declaration for a function.
pub type Arg<'a> = &'a ArgS<'a>;
/// An argument declaration for a function.
pub type ArgS<'a> = WithMeta<ArgKind<'a>>;

/// An argument declaration for a function.
#[derive(Debug, DeepSizeOf, PartialEq, Eq, Hash)]
pub enum ArgKind<'a> {
  /// A standard argument of the form `{x : T}`, a "lambda binder"
  Lam(TuplePattern<'a>),
  /// A substitution argument of the form `{{x : T} := val}`. (These are not supplied in
  /// invocations, they act as let binders in the remainder of the arguments.)
  Let(TuplePattern<'a>, Expr<'a>),
}

impl AddFlags for ArgKind<'_> {
  fn add(&self, f: &mut Flags) {
    match *self {
      ArgKind::Lam(pat) => *f |= pat,
      ArgKind::Let(pat, e) => *f |= (pat, e),
    }
  }
}

impl EnvDisplay for ArgKind<'_> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match *self {
      ArgKind::Lam(pat) => write!(f, "{}: {}", fe.to(pat), fe.to(pat.k.ty())),
      ArgKind::Let(pat, e) => write!(f, "{}: {} := {}", fe.to(pat), fe.to(pat.k.ty()), fe.to(e)),
    }
  }
}

/// A pattern, the left side of a switch statement.
pub type Pattern<'a> = &'a PatternS<'a>;
/// A pattern, the left side of a switch statement.
pub type PatternS<'a> = WithMeta<PatternKind<'a>>;

/// A pattern, the left side of a switch statement.
#[derive(Debug, DeepSizeOf, PartialEq, Eq, Hash)]
pub enum PatternKind<'a> {
  /// A wildcard binding.
  Ignore,
  /// A variable binding.
  Var(VarId),
  /// A constant value.
  Const(AtomId),
  /// A numeric literal.
  Number(&'a BigInt),
  /// A pattern guard: Matches the inner pattern, and then if the expression returns
  /// true, this is also considered to match.
  With(Pattern<'a>, Expr<'a>),
  /// A disjunction of patterns.
  Or(&'a [Pattern<'a>]),
}

impl AddFlags for PatternKind<'_> {
  fn add(&self, f: &mut Flags) {
    match *self {
      PatternKind::Ignore |
      PatternKind::Var(_) |
      PatternKind::Const(_) |
      PatternKind::Number(_) => {}
      PatternKind::With(_, e) => *f |= e,
      PatternKind::Or(pats) => *f |= pats,
    }
  }
}

impl EnvDisplay for PatternKind<'_> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    match *self {
      PatternKind::Ignore => "_".fmt(f),
      PatternKind::Var(v) => write!(f, "v{}", v),
      PatternKind::Const(c) => c.fmt(fe, f),
      PatternKind::Number(n) => n.fmt(f),
      PatternKind::With(pat, e) => write!(f, "{{{} with {}}}", fe.to(pat), fe.to(e)),
      PatternKind::Or(pats) =>
        write!(f, "{{{}}}", pats.iter().map(|&pat| fe.to(pat)).format(" or ")),
    }
  }
}

/// An embedded MM0 expression inside MMC. All free variables have been replaced by indexes,
/// with `subst` holding the internal names of these variables.
#[derive(Copy, Clone, Debug, DeepSizeOf)]
pub struct Mm0Expr<'a> {
  /// The mapping from indexes in the `expr` to internal names.
  /// (The user-facing names have been erased.)
  pub subst: &'a [Expr<'a>],
  /// The root node of the expression.
  pub expr: &'a Mm0ExprNode,
}

impl std::hash::Hash for Mm0Expr<'_> {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    self.subst.hash(state);
    (self.expr as *const Mm0ExprNode).hash(state);
  }
}

impl PartialEq for Mm0Expr<'_> {
  fn eq(&self, other: &Self) -> bool {
    self.subst == other.subst && std::ptr::eq(self.expr, other.expr)
  }
}
impl Eq for Mm0Expr<'_> {}

impl EnvDisplay for Mm0Expr<'_> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self.expr {
      Mm0ExprNode::Const(e) => e.fmt(fe, f),
      &Mm0ExprNode::Var(i) => self.subst[i as usize].fmt(fe, f),
      Mm0ExprNode::Expr(t, es) => {
        write!(f, "({}", fe.to(t))?;
        for expr in es {
          write!(f, " {}", fe.to(&Mm0Expr {subst: self.subst, expr}))?
        }
        write!(f, ")")
      }
    }
  }
}

/// A type, which classifies regular variables (not type variables, not hypotheses).
pub type Ty<'a> = &'a TyS<'a>;
/// A type, which classifies regular variables (not type variables, not hypotheses).
pub type TyS<'a> = WithMeta<TyKind<'a>>;

/// A type, which classifies regular variables (not type variables, not hypotheses).
#[derive(Debug, DeepSizeOf, PartialEq, Eq, Hash)]
pub enum TyKind<'a> {
  /// `()` is the type with one element; `sizeof () = 0`.
  Unit,
  /// `bool` is the type of booleans, that is, bytes which are 0 or 1; `sizeof bool = 1`.
  Bool,
  /// A type variable.
  Var(TyVarId),
  /// `i(8*N)` is the type of N byte signed integers `sizeof i(8*N) = N`.
  Int(Size),
  /// `u(8*N)` is the type of N byte unsigned integers; `sizeof u(8*N) = N`.
  UInt(Size),
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
  /// `(& T)` is a type of borrowed pointers. This type is elaborated to
  /// `(& a T)` where `a` is a lifetime; this is handled a bit differently than rust
  /// (see [`Lifetime`]).
  Shr(Lifetime, Ty<'a>),
  /// `&sn x` is the type of pointers to the place `x` (a variable or indexing expression).
  RefSn(Expr<'a>),
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
  /// `(or A B C)` is an undiscriminated anonymous union of types `A, B, C`.
  /// `sizeof (or A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (or A B C)` iff
  /// `x :> A \/ x :> B \/ x :> C`.
  If(Expr<'a>, Ty<'a>, Ty<'a>),
  /// A switch (pattern match) statement, given the initial expression and a list of match arms.
  Match(Expr<'a>, Ty<'a>, &'a [(Pattern<'a>, Ty<'a>)]),
  /// `(ghost A)` is a computationally irrelevant version of `A`, which means
  /// that the logical storage of `(ghost A)` is the same as `A` but the physical storage
  /// is the same as `()`. `sizeof (ghost A) = 0`.
  Ghost(Ty<'a>),
  /// `(? T)` is the type of possibly-uninitialized `T`s. The typing predicate
  /// for this type is vacuous, but it has the same size as `T`, so overwriting with
  /// a `T` is possible.
  Uninit(Ty<'a>),
  /// A propositional type, used for hypotheses.
  Prop(Prop<'a>),
  /// A user-defined type-former.
  User(AtomId, &'a [Ty<'a>], &'a [Expr<'a>]),
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

impl AddFlags for TyKind<'_> {
  fn add(&self, f: &mut Flags) {
    match *self {
      TyKind::Unit |
      TyKind::Bool |
      TyKind::Var(_) |
      TyKind::Int(_) |
      TyKind::UInt(_) |
      TyKind::Input |
      TyKind::Output => {}
      TyKind::Array(ty, e) => *f |= (ty, e),
      TyKind::Own(ty) => *f |= ty,
      TyKind::Ref(lft, ty) => *f |= (lft, ty),
      TyKind::Shr(lft, ty) => *f |= (lft, ty),
      TyKind::RefSn(e) => *f |= e,
      TyKind::List(tys) => *f |= tys,
      TyKind::Sn(e, ty) => *f |= (e, ty),
      TyKind::Struct(args) => *f |= args,
      TyKind::And(tys) => *f |= tys,
      TyKind::Or(tys) => *f |= tys,
      TyKind::If(e, tru, fal) => *f |= (e, tru, fal),
      TyKind::Match(e, ty, brs) => *f |= (e, ty, brs),
      TyKind::Ghost(ty) => *f |= ty,
      TyKind::Uninit(ty) => *f |= ty,
      TyKind::Prop(p) => *f |= p,
      TyKind::User(_, tys, es) => *f |= (tys, es),
      TyKind::Moved(ty) => *f |= ty,
      TyKind::Infer(_) => *f |= Flags::HAS_TY_MVAR,
      TyKind::Error => *f |= Flags::HAS_ERROR,
    }
  }
}

impl EnvDisplay for TyKind<'_> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    match *self {
      TyKind::Var(v) => v.fmt(f),
      TyKind::Unit => "()".fmt(f),
      TyKind::Bool => "bool".fmt(f),
      TyKind::Int(Size::S8) => "i8".fmt(f),
      TyKind::Int(Size::S16) => "i16".fmt(f),
      TyKind::Int(Size::S32) => "i32".fmt(f),
      TyKind::Int(Size::S64) => "i64".fmt(f),
      TyKind::Int(Size::Inf) => "int".fmt(f),
      TyKind::UInt(Size::S8) => "u8".fmt(f),
      TyKind::UInt(Size::S16) => "u16".fmt(f),
      TyKind::UInt(Size::S32) => "u32".fmt(f),
      TyKind::UInt(Size::S64) => "u64".fmt(f),
      TyKind::UInt(Size::Inf) => "nat".fmt(f),
      TyKind::Array(ty, n) => write!(f, "(array {} {})", fe.to(ty), fe.to(n)),
      TyKind::Own(ty) => write!(f, "(own {})", fe.to(ty)),
      TyKind::Ref(lft, ty) => write!(f, "(ref {} {})", lft, fe.to(ty)),
      TyKind::Shr(lft, ty) => write!(f, "(& {} {})", lft, fe.to(ty)),
      TyKind::RefSn(x) => write!(f, "(&sn {})", fe.to(x)),
      TyKind::List(tys) => write!(f, "(list {})", tys.iter().map(|&ty| fe.to(ty)).format(" ")),
      TyKind::Sn(e, ty) => write!(f, "(sn {{{}: {}}})", fe.to(e), fe.to(ty)),
      TyKind::Struct(args) => {
        "(struct".fmt(f)?;
        for &arg in args { write!(f, " {{{}}}", fe.to(arg))? }
        ")".fmt(f)
      }
      TyKind::And(tys) => write!(f, "(and {})", tys.iter().map(|&ty| fe.to(ty)).format(" ")),
      TyKind::Or(tys) => write!(f, "(or {})", tys.iter().map(|&ty| fe.to(ty)).format(" ")),
      TyKind::If(cond, then, els) => write!(f, "(if {} {} {})", fe.to(cond), fe.to(then), fe.to(els)),
      TyKind::Match(c, ty, brs) => {
        write!(f, "(match {{{}: {}}}", fe.to(c), fe.to(ty))?;
        for &(pat, e) in brs { write!(f, " {{{} => {}}}", fe.to(pat), fe.to(e))? }
        ")".fmt(f)
      }
      TyKind::Ghost(ty) => write!(f, "(ghost {})", fe.to(ty)),
      TyKind::Uninit(ty) => write!(f, "(? {})", fe.to(ty)),
      TyKind::Prop(p) => write!(f, "$ {} $", fe.to(p)),
      TyKind::User(name, tys, es) => {
        write!(f, "({}", fe.to(&name))?;
        for &ty in tys { " ".fmt(f)?; ty.fmt(fe, f)? }
        for &e in es { " ".fmt(f)?; e.fmt(fe, f)? }
        ")".fmt(f)
      }
      TyKind::Input => "Input".fmt(f),
      TyKind::Output => "Output".fmt(f),
      TyKind::Moved(ty) => write!(f, "|{}|", fe.to(ty)),
      TyKind::Infer(v) => write!(f, "?T{}", v.0),
      TyKind::Error => "??".fmt(f),
    }
  }
}

/// A separating proposition, which classifies hypotheses / proof terms.
pub type Prop<'a> = &'a PropS<'a>;
/// A separating proposition, which classifies hypotheses / proof terms.
pub type PropS<'a> = WithMeta<PropKind<'a>>;

/// A separating proposition, which classifies hypotheses / proof terms.
#[derive(Debug, DeepSizeOf, PartialEq, Eq, Hash)]
pub enum PropKind<'a> {
  /// A true proposition.
  True,
  /// A false proposition.
  False,
  /// A universally quantified proposition.
  All(TuplePattern<'a>, Prop<'a>),
  /// An existentially quantified proposition.
  Ex(TuplePattern<'a>, Prop<'a>),
  /// Implication (plain, non-separating).
  Imp(Prop<'a>, Prop<'a>),
  /// Negation.
  Not(Prop<'a>),
  /// Conjunction (non-separating).
  And(&'a [Prop<'a>]),
  /// Disjunction.
  Or(&'a [Prop<'a>]),
  /// The empty heap.
  Emp,
  /// Separating conjunction.
  Sep(&'a [Prop<'a>]),
  /// Separating implication.
  Wand(Prop<'a>, Prop<'a>),
  /// An (executable) boolean expression, interpreted as a pure proposition
  Pure(Expr<'a>),
  /// Equality (possibly non-decidable).
  Eq(Expr<'a>, Expr<'a>),
  /// A heap assertion `l |-> (v: T)`.
  Heap(Expr<'a>, Expr<'a>, Ty<'a>),
  /// An explicit typing assertion `[v : T]`.
  HasTy(Expr<'a>, Ty<'a>),
  /// The move operator `|T|` on types.
  Moved(Prop<'a>),
  /// An embedded MM0 proposition of sort `wff`.
  Mm0(Mm0Expr<'a>),
  /// An inference variable.
  Infer(PropMVarId),
  /// A type error that has been reported.
  Error,
}

impl AddFlags for PropKind<'_> {
  fn add(&self, f: &mut Flags) {
    match *self {
      PropKind::True |
      PropKind::False |
      PropKind::Emp => {}
      PropKind::All(pat, p) => *f |= (pat, p),
      PropKind::Ex(pat, p) => *f |= (pat, p),
      PropKind::Imp(p, q) => *f |= (p, q),
      PropKind::Not(p) => *f |= p,
      PropKind::And(ps) => *f |= ps,
      PropKind::Or(ps) => *f |= ps,
      PropKind::Sep(ps) => *f |= ps,
      PropKind::Wand(p, q) => *f |= (p, q),
      PropKind::Pure(e) => *f |= e,
      PropKind::Eq(e1, e2) => *f |= (e1, e2),
      PropKind::Heap(e, v, ty) => *f |= (e, v, ty),
      PropKind::HasTy(v, ty) => *f |= (v, ty),
      PropKind::Moved(p) => *f |= p,
      PropKind::Mm0(ref e) => *f |= e.subst,
      PropKind::Infer(_) => *f |= Flags::HAS_PROP_MVAR,
      PropKind::Error => *f |= Flags::HAS_ERROR,
    }
  }
}

impl EnvDisplay for PropKind<'_> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    match *self {
      PropKind::True => "true".fmt(f),
      PropKind::False => "false".fmt(f),
      PropKind::All(a, pr) => write!(f, "A. {} {}", fe.to(a), fe.to(pr)),
      PropKind::Ex(a, pr) => write!(f, "E. {} {}", fe.to(a), fe.to(pr)),
      PropKind::Imp(p, q) => write!(f, "({} -> {})", fe.to(p), fe.to(q)),
      PropKind::Not(pr) => write!(f, "~{}", fe.to(pr)),
      PropKind::And(pr) if pr.is_empty() => "true".fmt(f),
      PropKind::And(pr) => write!(f, "({})", pr.iter().map(|&p| fe.to(p)).format(" /\\ ")),
      PropKind::Or(pr) if pr.is_empty() => "false".fmt(f),
      PropKind::Or(pr) => write!(f, "({})", pr.iter().map(|&p| fe.to(p)).format(" \\/ ")),
      PropKind::Emp => "emp".fmt(f),
      PropKind::Sep(pr) if pr.is_empty() => "emp".fmt(f),
      PropKind::Sep(pr) => write!(f, "({})", pr.iter().map(|&p| fe.to(p)).format(" * ")),
      PropKind::Wand(p, q) => write!(f, "({} -* {})", fe.to(p), fe.to(q)),
      PropKind::Pure(e) => e.fmt(fe, f),
      PropKind::Eq(e1, e2) => write!(f, "{} = {}", fe.to(e1), fe.to(e2)),
      PropKind::Heap(x, v, t) => write!(f, "{} => {}: {}", fe.to(x), fe.to(v), fe.to(t)),
      PropKind::HasTy(v, t) => write!(f, "[{}: {}]", fe.to(v), fe.to(t)),
      PropKind::Moved(p) => write!(f, "|{}|", fe.to(p)),
      PropKind::Mm0(e) => e.fmt(fe, f),
      PropKind::Infer(v) => write!(f, "?P{}", v.0),
      PropKind::Error => "??".fmt(f),
    }
  }
}

/// A pure expression. (Regular expressions are not manipulated like types,
/// i.e. copied and substituted around, so they are in the [`hir`](super::hir) module.)
pub type Expr<'a> = &'a ExprS<'a>;
/// A pure expression.
pub type ExprS<'a> = WithMeta<ExprKind<'a>>;

/// A pure expression.
#[derive(Debug, DeepSizeOf, PartialEq, Eq, Hash)]
pub enum ExprKind<'a> {
  /// A `()` literal.
  Unit,
  /// A variable reference.
  Var(VarId),
  /// A user constant.
  Const(AtomId),
  /// A global variable.
  Global(AtomId),
  /// A number literal.
  Bool(bool),
  /// A number literal.
  Int(&'a BigInt),
  /// A unary operation.
  Unop(Unop, Expr<'a>),
  /// A binary operation.
  Binop(Binop, Expr<'a>, Expr<'a>),
  /// An index operation `(index a i): T` where `a: (array T n)`
  /// and `i: nat`.
  Index(Expr<'a>, Expr<'a>),
  /// If `x: (array T n)`, then `(slice x a b): (array T b)`.
  Slice(Expr<'a>, Expr<'a>, Expr<'a>),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(Expr<'a>, u32),
  /// `(list e1 ... en)` returns a tuple of the arguments.
  List(&'a [Expr<'a>]),
  /// `(pure $e$)` embeds an MM0 expression `$e$` as the target type,
  /// one of the numeric types
  Mm0(Mm0Expr<'a>),
  /// A function call
  Call {
    /// The function to call.
    f: AtomId,
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
  /// A switch (pattern match) statement, given the initial expression and a list of match arms.
  Match(Expr<'a>, &'a [(Pattern<'a>, Expr<'a>)]),
  /// An inference variable.
  Infer(ExprMVarId),
  /// A type error that has been reported.
  Error,
}

impl AddFlags for ExprKind<'_> {
  fn add(&self, f: &mut Flags) {
    match *self {
      ExprKind::Unit |
      ExprKind::Var(_) |
      ExprKind::Const(_) |
      ExprKind::Global(_) |
      ExprKind::Bool(_) |
      ExprKind::Int(_) => {}
      ExprKind::Unop(_, e) => *f |= e,
      ExprKind::Binop(_, e1, e2) => *f |= (e1, e2),
      ExprKind::Index(a, i) => *f |= (a, i),
      ExprKind::Slice(a, i, n) => *f |= (a, i, n),
      ExprKind::Proj(e, _) => *f |= e,
      ExprKind::List(es) => *f |= es,
      ExprKind::Mm0(ref e) => *f |= e.subst,
      ExprKind::Call {tys, args, ..} => *f |= (tys, args),
      ExprKind::If {cond, then, els} => *f |= (cond, then, els),
      ExprKind::Match(e, brs) => *f |= (e, brs),
      ExprKind::Infer(_) => *f |= Flags::HAS_EXPR_MVAR,
      ExprKind::Error => *f |= Flags::HAS_ERROR,
    }
  }
}

impl EnvDisplay for ExprKind<'_> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    match *self {
      ExprKind::Unit => "()".fmt(f),
      ExprKind::Var(v) => v.fmt(f),
      ExprKind::Const(c) => c.fmt(fe, f),
      ExprKind::Global(v) => v.fmt(fe, f),
      ExprKind::Bool(b) => b.fmt(f),
      ExprKind::Int(n) => n.fmt(f),
      ExprKind::Unop(op, e) => write!(f, "({} {})", op, fe.to(e)),
      ExprKind::Binop(op, e1, e2) => write!(f, "{{{} {} {}}}", fe.to(e1), op, fe.to(e2)),
      ExprKind::List(es) => write!(f, "(list {})", es.iter().map(|&e| fe.to(e)).format(" ")),
      ExprKind::Index(a, i) => write!(f, "(index {} {})", fe.to(a), fe.to(i)),
      ExprKind::Slice(a, i, n) => write!(f, "(slice {} {} {})", fe.to(a), fe.to(i), fe.to(n)),
      ExprKind::Proj(a, i) => write!(f, "({} . {})", fe.to(a), i),
      ExprKind::Mm0(ref e) => e.fmt(fe, f),
      ExprKind::Call {f: x, tys, args} => {
        write!(f, "({}", fe.to(&x))?;
        for &ty in tys { write!(f, " {}", fe.to(ty))? }
        for &arg in args { write!(f, " {}", fe.to(arg))? }
        ")".fmt(f)
      }
      ExprKind::If {cond, then, els} => write!(f, "(if {} {} {})", fe.to(cond), fe.to(then), fe.to(els)),
      ExprKind::Match(c, brs) => {
        write!(f, "(match {}", fe.to(c))?;
        for &(pat, e) in brs { write!(f, " {{{} => {}}}", fe.to(pat), fe.to(e))? }
        ")".fmt(f)
      }
      ExprKind::Infer(v) => write!(f, "?v{}", v.0),
      ExprKind::Error => "??".fmt(f),
    }
  }
}
