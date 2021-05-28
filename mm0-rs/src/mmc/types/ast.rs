//! The AST, the result after parsing and name resolution.
//!
//! This is produced by the [`build_ast`](super::super::build_ast) pass,
//! and consumed by the [`ast_lower`](super::super::ast_lower) pass.
//! At this point all the renaming shenanigans in the surface syntax are gone
//! and all variables are declared only once, so we can start to apply SSA-style
//! analysis to the result. We still haven't typechecked anything, so it's
//! possible that variables are applied to the wrong arguments and so on.
//!
//! One complication where type checking affects name resolution has to do with
//! determining when variables are renamed after a mutation. Consider:
//! ```text
//! (begin
//!   {x := 1}
//!   (assert {x = 1})
//!   {{y : (&sn x)} := (& x)}
//!   {(* y) <- 2}
//!   (assert {x = 2}))
//! ```
//! It is important for us to resolve the `x` in the last line to a fresh variable
//! `x'`  distinct from the `x` on the first line, because we know that `x = 1`.
//! In the surface syntax this is explained as name shadowing - we have a new `x`
//! and references resolve to that instead, but once we have done name resolution
//! we would like these two to actually resolve to different variables. However,
//! the line responsible for the modification of `x`, `{(* y) <- 2}`, doesn't
//! mention `x` at all - it is only when we know the type of `y` that we can
//! determine that `(* y)` resolves to `x` as an lvalue.
//!
//! We could delay name resolution until type checking, but this makes things a
//! lot more complicated, and possibly also harder to reason about at the user
//! level. The current compromise is that one has to explicitly declare any
//! variable renames using `with` if they aren't syntactically obvious, so in
//! this case you would have to write `{{(* y) <- 2} with {x -> x'}}` to say that
//! `x` changes (or `{{(* y) <- 2} with x}` if the name shadowing is acceptable).

use num::BigInt;
use crate::{AtomId, Remap, Remapper, LispVal, FileSpan};
use super::{Binop, FieldName, Mm0Expr, Size, Spanned, Unop, VarId, entity::Intrinsic};

/// A "lifetime" in MMC is a variable or place from which references can be derived.
/// For example, if we `let y = &x[1]` then `y` has the type `(& x T)`. As long as
/// heap variables referring to lifetime `x` exist, `x` cannot be modified or dropped.
/// There is a special lifetime `extern` that represents inputs to the current function.
#[derive(Clone, Copy, Debug)]
pub enum Lifetime {
  /// The `extern` lifetime is the inferred lifetime for function arguments such as
  /// `fn f(x: &T)`.
  Extern,
  /// A variable lifetime `x` is the annotation on references derived from `x`
  /// (or derived from other references derived from `x`).
  Place(VarId),
  /// A lifetime that has not been inferred yet.
  Infer,
}
crate::deep_size_0!(Lifetime);

impl std::fmt::Display for Lifetime {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Lifetime::Extern => "extern".fmt(f),
      Lifetime::Place(v) => v.fmt(f),
      Lifetime::Infer => "_".fmt(f),
    }
  }
}

/// A tuple pattern, which destructures the results of assignments from functions with
/// mutiple return values, as well as explicit tuple values and structs.
pub type TuplePattern = Spanned<TuplePatternKind>;

/// A tuple pattern, which destructures the results of assignments from functions with
/// mutiple return values, as well as explicit tuple values and structs.
#[derive(Debug, DeepSizeOf)]
pub enum TuplePatternKind {
  /// A variable binding, or `_` for an ignored binding. The `bool` is true if the variable
  /// is ghost.
  Name(bool, AtomId, VarId),
  /// A type ascription. The type is unparsed.
  Typed(Box<TuplePattern>, Box<Type>),
  /// A tuple, with the given arguments. Names are given to the intermediates,
  /// which will agree with the `Name` at the leaves.
  Tuple(Box<[(VarId, TuplePattern)]>),
}

impl Remap for TuplePatternKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      &TuplePatternKind::Name(b, n, v) => TuplePatternKind::Name(b, n.remap(r), v),
      TuplePatternKind::Typed(pat, ty) => TuplePatternKind::Typed(pat.remap(r), ty.remap(r)),
      TuplePatternKind::Tuple(pats) => TuplePatternKind::Tuple(pats.remap(r)),
    }
  }
}

impl TuplePatternKind {
  /// Extracts the single name of this tuple pattern, or `None`
  /// if this does any tuple destructuring.
  #[must_use] pub fn as_single_name(&self) -> Option<(bool, VarId)> {
    match self {
      &Self::Name(g, _, v) => Some((g, v)),
      Self::Typed(pat, _) => pat.k.as_single_name(),
      Self::Tuple(_) => None
    }
  }
}

/// An argument declaration for a function.
pub type Arg = Spanned<(ArgAttr, ArgKind)>;

/// An argument declaration for a function.
#[derive(Debug, DeepSizeOf)]
pub enum ArgKind {
  /// A standard argument of the form `{x : T}`, a "lambda binder"
  Lam(TuplePatternKind),
  /// A substitution argument of the form `{{x : T} := val}`. (These are not supplied in
  /// invocations, they act as let binders in the remainder of the arguments.)
  Let(TuplePattern, Box<Expr>),
}

impl Remap for ArgKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      ArgKind::Lam(pat) => ArgKind::Lam(pat.remap(r)),
      ArgKind::Let(pat, val) => ArgKind::Let(pat.remap(r), val.remap(r)),
    }
  }
}

impl ArgKind {
  /// Extracts the binding part of this argument.
  #[must_use] pub fn var(&self) -> &TuplePatternKind {
    match self {
      Self::Lam(pat) | Self::Let(Spanned {k: pat, ..}, _) => pat,
    }
  }
}

/// A type expression.
pub type Type = Spanned<TypeKind>;

/// A type variable index.
pub type TyVarId = u32;

/// A type, which classifies regular variables (not type variables, not hypotheses).
#[derive(Debug, DeepSizeOf)]
pub enum TypeKind {
  /// `()` is the type with one element; `sizeof () = 0`.
  /// This is also the proposition `emp`.
  Unit,
  /// `true` is the true proposition; `sizeof true = 0`. Unlike `Unit`,
  /// this does not assert the emptiness of the data, it holds of any value.
  True,
  /// `false` is the false proposition; `sizeof false = 0`.
  False,
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
  Array(Box<Type>, Box<Expr>),
  /// `own T` is a type of owned pointers. The typehood predicate is
  /// `x :> own T` iff `E. v (x |-> v) * v :> T`.
  Own(Box<Type>),
  /// `(ref T)` is a type of borrowed values. This type is elaborated to
  /// `(ref a T)` where `a` is a lifetime; this is handled a bit differently than rust
  /// (see [`Lifetime`]).
  Ref(Option<Box<Spanned<Lifetime>>>, Box<Type>),
  /// `&sn x` is the type of pointers to the place `x` (a variable or indexing expression).
  RefSn(Box<Expr>),
  /// `(A, B, C)` is a tuple type with elements `A, B, C`;
  /// `sizeof (list A B C) = sizeof A + sizeof B + sizeof C`.
  List(Box<[Type]>),
  /// `(sn {a : T})` the type of values of type `T` that are equal to `a`.
  /// This is useful for asserting that a computationally relevant value can be
  /// expressed in terms of computationally irrelevant parts.
  Sn(Box<Expr>),
  /// `{x : A, y : B, z : C}` is the dependent version of `list`;
  /// it is a tuple type with elements `A, B, C`, but the types `A, B, C` can
  /// themselves refer to `x, y, z`.
  /// `sizeof {x : A, _ : B x} = sizeof A + max_x (sizeof (B x))`.
  ///
  /// The top level declaration `(struct foo {x : A} {y : B})` desugars to
  /// `(typedef foo {x : A, y : B})`.
  Struct(Box<[Arg]>),
  /// A universally quantified proposition.
  All(Box<[TuplePattern]>, Box<Type>),
  /// Implication (plain, non-separating).
  Imp(Box<Type>, Box<Type>),
  /// Separating implication.
  Wand(Box<Type>, Box<Type>),
  /// Negation.
  Not(Box<Type>),
  /// `(and A B C)` is an intersection type of `A, B, C`;
  /// `sizeof (and A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (and A B C)` iff
  /// `x :> A /\ x :> B /\ x :> C`. (Note that this is regular conjunction,
  /// not separating conjunction.)
  And(Box<[Type]>),
  /// `(or A B C)` is an undiscriminated anonymous union of types `A, B, C`.
  /// `sizeof (or A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (or A B C)` iff
  /// `x :> A \/ x :> B \/ x :> C`.
  Or(Box<[Type]>),
  /// `(or A B C)` is an undiscriminated anonymous union of types `A, B, C`.
  /// `sizeof (or A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (or A B C)` iff
  /// `x :> A \/ x :> B \/ x :> C`.
  If(Box<Expr>, Box<Type>, Box<Type>),
  /// `(ghost A)` is a computationally irrelevant version of `A`, which means
  /// that the logical storage of `(ghost A)` is the same as `A` but the physical storage
  /// is the same as `()`. `sizeof (ghost A) = 0`.
  Ghost(Box<Type>),
  /// `(? T)` is the type of possibly-uninitialized `T`s. The typing predicate
  /// for this type is vacuous, but it has the same size as `T`, so overwriting with
  /// a `T` is possible.
  Uninit(Box<Type>),
  /// A boolean expression, interpreted as a pure proposition
  Pure(Box<Expr>),
  /// A user-defined type-former.
  User(AtomId, Box<[Type]>, Box<[Expr]>),
  /// A heap assertion `l |-> (v: T)`.
  Heap(Box<Expr>, Box<Expr>),
  /// An explicit typing assertion `[v : T]`.
  HasTy(Box<Expr>, Box<Type>),
  /// The input token.
  Input,
  /// The output token.
  Output,
  /// A moved-away type.
  Moved(Box<Type>),
  /// A `_` type.
  Infer,
  /// A type error that has been reported.
  Error,
}

impl Remap for TypeKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      TypeKind::Unit => TypeKind::Unit,
      TypeKind::True => TypeKind::True,
      TypeKind::False => TypeKind::False,
      TypeKind::Bool => TypeKind::Bool,
      &TypeKind::Var(i) => TypeKind::Var(i),
      &TypeKind::Int(i) => TypeKind::Int(i),
      &TypeKind::UInt(i) => TypeKind::UInt(i),
      TypeKind::Array(ty, n) => TypeKind::Array(ty.remap(r), n.remap(r)),
      TypeKind::Own(ty) => TypeKind::Own(ty.remap(r)),
      TypeKind::Ref(lft, ty) => TypeKind::Ref(lft.clone(), ty.remap(r)),
      TypeKind::RefSn(ty) => TypeKind::RefSn(ty.remap(r)),
      TypeKind::List(tys) => TypeKind::List(tys.remap(r)),
      TypeKind::Sn(e) => TypeKind::Sn(e.remap(r)),
      TypeKind::Struct(tys) => TypeKind::Struct(tys.remap(r)),
      TypeKind::All(p, q) => TypeKind::All(p.remap(r), q.remap(r)),
      TypeKind::Imp(p, q) => TypeKind::Imp(p.remap(r), q.remap(r)),
      TypeKind::Wand(p, q) => TypeKind::Wand(p.remap(r), q.remap(r)),
      TypeKind::Not(p) => TypeKind::Not(p.remap(r)),
      TypeKind::And(tys) => TypeKind::And(tys.remap(r)),
      TypeKind::Or(tys) => TypeKind::Or(tys.remap(r)),
      TypeKind::If(c, t, e) => TypeKind::If(c.remap(r), t.remap(r), e.remap(r)),
      TypeKind::Ghost(ty) => TypeKind::Ghost(ty.remap(r)),
      TypeKind::Uninit(ty) => TypeKind::Uninit(ty.remap(r)),
      TypeKind::Pure(p) => TypeKind::Pure(p.remap(r)),
      TypeKind::User(f, tys, es) => TypeKind::User(f.remap(r), tys.remap(r), es.remap(r)),
      TypeKind::Heap(p, q) => TypeKind::Heap(p.remap(r), q.remap(r)),
      TypeKind::HasTy(p, q) => TypeKind::HasTy(p.remap(r), q.remap(r)),
      TypeKind::Input => TypeKind::Input,
      TypeKind::Output => TypeKind::Output,
      TypeKind::Moved(tys) => TypeKind::Moved(tys.remap(r)),
      TypeKind::Infer => TypeKind::Infer,
      TypeKind::Error => TypeKind::Error,
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
  UpLe(Expr)
}

impl Remap for VariantType {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      VariantType::Down => VariantType::Down,
      VariantType::UpLt(e) => VariantType::UpLt(e.remap(r)),
      VariantType::UpLe(e) => VariantType::UpLe(e.remap(r)),
    }
  }
}

/// A variant is a pure expression, together with a
/// well founded order that decreases on all calls.
pub type Variant = Spanned<(Expr, VariantType)>;

/// A label in a label group declaration. Individual labels in the group
/// are referred to by their index in the list.
#[derive(Debug, DeepSizeOf)]
pub struct Label {
  /// The arguments of the label
  pub args: Box<[Arg]>,
  /// The variant, for recursive calls
  pub variant: Option<Box<Variant>>,
  /// The code that is executed when you jump to the label
  pub body: Spanned<Block>,
}

impl Remap for Label {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Self {
      args: self.args.remap(r),
      variant: self.variant.remap(r),
      body: self.body.remap(r)
    }
  }
}

/// A block is a list of statements, with an optional terminating expression.
#[derive(Debug, DeepSizeOf)]
pub struct Block {
  /// The list of statements in the block.
  pub stmts: Vec<Stmt>,
  /// The optional last statement, or `()` if not specified.
  pub expr: Option<Box<Expr>>,
}

impl Remap for Block {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Self {
      stmts: self.stmts.remap(r),
      expr: self.expr.remap(r),
    }
  }
}

/// A statement in a block.
pub type Stmt = Spanned<StmtKind>;

/// A statement in a block.
#[derive(Debug, DeepSizeOf)]
pub enum StmtKind {
  /// A let binding.
  Let {
    /// A tuple pattern, containing variable bindings.
    lhs: TuplePattern,
    /// The expression to evaluate.
    rhs: Expr,
  },
  /// An expression to be evaluated for its side effects, with the result being discarded.
  Expr(ExprKind),
  /// A label, which looks exactly like a local function but has no independent stack frame.
  /// They are called like regular functions but can only appear in tail position.
  Label(VarId, Box<[Label]>),
}

impl Remap for StmtKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      StmtKind::Let {lhs, rhs} => StmtKind::Let {lhs: lhs.remap(r), rhs: rhs.remap(r)},
      StmtKind::Expr(e) => StmtKind::Expr(e.remap(r)),
      StmtKind::Label(v, ls) => StmtKind::Label(*v, ls.remap(r)),
    }
  }
}

/// This enum is used to distinguish between proper if statements and short-circuiting
/// boolean operators that have been desugared to if statements.
#[derive(Copy, Clone, Debug)]
pub enum IfKind {
  /// This is an `(if cond e1 e2)` statement.
  If,
  /// This is a `(if e1 e2 false)` statement, as the desugaring of `e1 && e2`.
  And,
  /// This is a `(if e1 true e2)` statement, as the desugaring of `e1 || e2`.
  Or,
}
crate::deep_size_0!(IfKind);

/// An expression.
pub type Expr = Spanned<ExprKind>;

/// An expression. A block is a list of expressions.
#[derive(Debug, DeepSizeOf)]
pub enum ExprKind {
  /// A `()` literal.
  Unit,
  /// A variable reference.
  Var(VarId),
  /// A user constant.
  Const(AtomId),
  /// A boolean literal.
  Bool(bool),
  /// A number literal.
  Int(BigInt),
  /// A unary operation.
  Unop(Unop, Box<Expr>),
  /// A binary operation.
  Binop(Binop, Box<Expr>, Box<Expr>),
  /// `(sn x)` constructs the unique member of the type `(sn x)`.
  /// `(sn y h)` is also a member of `(sn x)` if `h` proves `y = x`.
  Sn(Box<Expr>, Option<Box<Expr>>),
  /// An index operation `(index a i h): T` where `a: (array T n)`,
  /// `i: nat`, and `h: i < n`.
  Index(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
  /// If `x: (array T n)`, then `(slice x a b h): (array T b)` if
  /// `h` is a proof that `a + b <= n`.
  Slice(Box<(Expr, Expr, Expr)>, Option<Box<Expr>>),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(Box<Expr>, Spanned<FieldName>),
  /// A deref operation `*x: T` where `x: &T`.
  Deref(Box<Expr>),
  /// `(list e1 ... en)` returns a tuple of the arguments.
  List(Vec<Expr>),
  /// A ghost expression.
  Ghost(Box<Expr>),
  /// Evaluates the expression as a pure expression, so it will not take
  /// ownership of the result.
  Ref(Box<Expr>),
  /// `(& x)` constructs a reference to `x`.
  Borrow(Box<Expr>),
  /// `(pure $e$)` embeds an MM0 expression `$e$` as the target type,
  /// one of the numeric types
  Mm0(Mm0Expr<Expr>),
  /// A type ascription.
  Typed(Box<Expr>, Box<Type>),
  /// A truncation / bit cast operation.
  As(Box<Expr>, Box<Type>),
  /// Combine an expression with a proof that it has the right type.
  Cast(Box<Expr>, Option<Box<Expr>>),
  /// Reinterpret an expression given a proof that it has the right type.
  Pun(Box<Expr>, Option<Box<Expr>>),
  /// An expression denoting an uninitialized value.
  Uninit,
  /// Return the size of a type.
  Sizeof(Box<Type>),
  /// Take the type of a variable.
  Typeof(Box<Expr>),
  /// `(assert p)` evaluates `p: bool` and returns a proof of `p`.
  Assert(Box<Expr>),
  /// An assignment / mutation.
  Assign {
    /// A place (lvalue) to write to.
    lhs: Box<Expr>,
    /// The expression to evaluate.
    rhs: Box<Expr>,
    /// An array of `new -> old` mappings as `(new, old)` pairs; the `new` variable is a variable
    /// id already in scope, while `old` is a new binding representing the previous
    /// value of the variable before the assignment.
    /// (This ordering is chosen so that the variable ID retains its "newest" value
    /// through any number of writes to it, while non-updatable `old` variables are created
    /// by the various assignments.)
    oldmap: Box<[(VarId, VarId)]>,
  },
  /// A function call.
  Call {
    /// The function to call.
    f: Spanned<AtomId>,
    /// The type arguments.
    tys: Vec<Type>,
    /// The function arguments.
    args: Vec<Expr>,
    /// The variant, if needed.
    variant: Option<Box<Expr>>,
  },
  /// An entailment proof, which takes a proof of `P1 * ... * Pn => Q` and expressions proving
  /// `P1, ..., Pn` and is a hypothesis of type `Q`.
  Entail(LispVal, Box<[Expr]>),
  /// A block scope.
  Block(Block),
  /// An if-then-else expression (at either block or statement level). The initial atom names
  /// a hypothesis that the expression is true in one branch and false in the other.
  If {
    /// Distinguishes if statements from short-circuiting boolean operators.
    ik: IfKind,
    /// The hypothesis name.
    hyp: Option<VarId>,
    /// The if condition.
    cond: Box<Expr>,
    /// The then case.
    then: Box<Expr>,
    /// The else case.
    els: Box<Expr>
  },
  /// A while loop.
  While {
    /// The name of this loop, which can be used as a target for jumps.
    label: VarId,
    /// The variables that are mutated in the loop.
    muts: Box<[VarId]>,
    /// A hypothesis that the condition is true in the loop and false after it.
    hyp: Option<VarId>,
    /// The loop condition.
    cond: Box<Expr>,
    /// The variant, which must decrease on every round around the loop.
    var: Option<Box<Variant>>,
    /// The body of the loop.
    body: Box<Block>,
    /// True if there is an early `break` inside the loop. If this is true, then the loop does
    /// not introduce a `hyp: !cond` assumption after the loop.
    has_break: bool,
  },
  /// `(unreachable h)` takes a proof of false and undoes the current code path.
  Unreachable(Box<Expr>),
  /// `(lab e1 ... en)` jumps to label `lab` with `e1 ... en` as arguments.
  /// Here the `VarId` is the target label group, and the `u16` is the index
  /// in the label group.
  Jump(VarId, u16, Vec<Expr>, Option<Box<Expr>>),
  /// `(break lab e)` jumps out of the scope containing label `lab`,
  /// returning `e` as the result of the block. Unlike [`Jump`](Self::Jump),
  /// this does not contain a label index because breaking from any label
  /// in the group has the same effect.
  Break(VarId, Box<Expr>),
  /// `(return e1 ... en)` returns `e1, ..., en` from the current function.
  Return(Vec<Expr>),
  /// An inference hole `_`, which will give a compile error if it cannot be inferred
  /// but queries the compiler to provide a type context. The `bool` is true if this variable
  /// was created by the user through an explicit `_`, while compiler-generated inference
  /// variables have it set to false.
  Infer(bool),
  /// A cloned expr, for copied subterms.
  Rc(std::rc::Rc<Expr>),
  /// An upstream error.
  Error
}

impl Remap for ExprKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      ExprKind::Unit => ExprKind::Unit,
      &ExprKind::Var(v) => ExprKind::Var(v),
      &ExprKind::Const(a) => ExprKind::Const(a.remap(r)),
      &ExprKind::Bool(b) => ExprKind::Bool(b),
      ExprKind::Int(n) => ExprKind::Int(n.clone()),
      ExprKind::Unop(op, e) => ExprKind::Unop(*op, e.remap(r)),
      ExprKind::Binop(op, e1, e2) => ExprKind::Binop(*op, e1.remap(r), e2.remap(r)),
      ExprKind::Sn(e, h) => ExprKind::Sn(e.remap(r), h.remap(r)),
      ExprKind::Index(a, i, h) => ExprKind::Index(a.remap(r), i.remap(r), h.remap(r)),
      ExprKind::Slice(e, h) => ExprKind::Slice(e.remap(r), h.remap(r)),
      ExprKind::Proj(e, i) => ExprKind::Proj(e.remap(r), i.clone()),
      ExprKind::Deref(e) => ExprKind::Deref(e.remap(r)),
      ExprKind::List(e) => ExprKind::List(e.remap(r)),
      ExprKind::Ghost(e) => ExprKind::Ghost(e.remap(r)),
      ExprKind::Ref(e) => ExprKind::Ref(e.remap(r)),
      ExprKind::Borrow(e) => ExprKind::Borrow(e.remap(r)),
      ExprKind::Mm0(e) => ExprKind::Mm0(e.remap(r)),
      ExprKind::Typed(e, ty) => ExprKind::Typed(e.remap(r), ty.remap(r)),
      ExprKind::As(e, ty) => ExprKind::As(e.remap(r), ty.remap(r)),
      ExprKind::Cast(e, h) => ExprKind::Cast(e.remap(r), h.remap(r)),
      ExprKind::Pun(e, h) => ExprKind::Pun(e.remap(r), h.remap(r)),
      ExprKind::Uninit => ExprKind::Uninit,
      ExprKind::Sizeof(ty) => ExprKind::Sizeof(ty.remap(r)),
      ExprKind::Typeof(e) => ExprKind::Typeof(e.remap(r)),
      ExprKind::Assert(e) => ExprKind::Assert(e.remap(r)),
      ExprKind::Assign {lhs, rhs, oldmap} => ExprKind::Assign {
        lhs: lhs.remap(r), rhs: rhs.remap(r), oldmap: oldmap.clone() },
      ExprKind::Call {f, tys, args, variant} => ExprKind::Call {
        f: f.remap(r), tys: tys.remap(r), args: args.remap(r), variant: variant.remap(r) },
      ExprKind::Entail(p, q) => ExprKind::Entail(p.remap(r), q.remap(r)),
      ExprKind::Block(e) => ExprKind::Block(e.remap(r)),
      ExprKind::If {ik, hyp, cond, then, els} => ExprKind::If {
        ik: *ik, hyp: *hyp, cond: cond.remap(r), then: then.remap(r), els: els.remap(r) },
      ExprKind::While {label, muts, hyp, cond, var, body, has_break} => ExprKind::While {
        label: *label, muts: muts.remap(r), hyp: *hyp, has_break: *has_break,
        cond: cond.remap(r), var: var.remap(r), body: body.remap(r) },
      ExprKind::Unreachable(e) => ExprKind::Unreachable(e.remap(r)),
      ExprKind::Jump(l, i, e, var) => ExprKind::Jump(*l, *i, e.remap(r), var.remap(r)),
      ExprKind::Break(v, e) => ExprKind::Break(*v, e.remap(r)),
      ExprKind::Return(e) => ExprKind::Return(e.remap(r)),
      ExprKind::Rc(e) => ExprKind::Rc(e.remap(r)),
      &ExprKind::Infer(b) => ExprKind::Infer(b),
      ExprKind::Error => ExprKind::Error,
    }
  }
}

impl ExprKind {
  /// Construct a binary operation application, but desugar `e1 && e2` and `e1 || e2`
  /// to if statements to ensure short-circuiting evaluation.
  #[must_use] pub fn binop(span: &FileSpan, op: Binop, e1: Expr, e2: Expr) -> Self {
    match op {
      Binop::And => Self::If {
        ik: IfKind::And, hyp: None,
        cond: Box::new(e1),
        then: Box::new(e2),
        els: Box::new(Spanned {span: span.clone(), k: ExprKind::Bool(false)})
      },
      Binop::Or => Self::If {
        ik: IfKind::Or, hyp: None,
        cond: Box::new(e1),
        then: Box::new(Spanned {span: span.clone(), k: ExprKind::Bool(true)}),
        els: Box::new(e2),
      },
      _ => Self::Binop(op, Box::new(e1), Box::new(e2))
    }
  }
}

/// A field of a struct.
#[derive(Debug, DeepSizeOf)]
pub struct Field {
  /// The name of the field.
  pub name: AtomId,
  /// True if the field is computationally irrelevant.
  pub ghost: bool,
  /// The type of the field.
  pub ty: Type,
}

/// A procedure kind, which defines the different kinds of function-like declarations.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ProcKind {
  /// A (pure) function, which generates a logic level function as well as code. (Body required.)
  Func,
  /// A procedure, which is opaque except for its type. (Body provided.)
  Proc,
  /// The main procedure. (Body provided.)
  Main,
  /// An intrinsic declaration, which is only here to put the function declaration in user code.
  /// The compiler will ensure this matches an existing intrinsic, and intrinsics cannot be
  /// called until they are declared using an `intrinsic` declaration.
  Intrinsic(Intrinsic),
}
crate::deep_size_0!(ProcKind);

/// A return value, after resolving `mut` / `out` annotations.
#[derive(Debug, DeepSizeOf)]
pub enum Ret {
  /// This is a regular argument, with the given argument pattern.
  Reg(TuplePattern),
  /// This is an `out` argument: `Out(g, i, n, v, ty)` means that this argument was marked as
  /// `out` corresponding to argument `i` in the inputs; `n` or `v` is the name of the binder,
  /// and `ty` is the type, if provided.
  Out(bool, u32, AtomId, VarId, Option<Box<Type>>),
}

bitflags! {
  /// Attributes on function arguments.
  pub struct ArgAttr: u8 {
    /// A `(mut x)` argument, which is modified in the body and passed out
    /// via an `(out x x')` in the returns.
    const MUT = 1 << 0;
    /// An `(implicit x)` argument, which indicates that the variable will be
    /// inferred in applications.
    const IMPLICIT = 1 << 1;
    /// A `(global x)` argument, which indicates that the variable is not passed directly
    /// but is instead sourced from a global variable of the same name.
    const GLOBAL = 1 << 2;
    /// An argument is nondependent if the remainder of the type does not depend on this variable.
    const NONDEP = 1 << 3;
    /// An argument is ghost if the computer does not need to construct an actual bit pattern
    /// for this argument.
    const GHOST = 1 << 4;
  }
}
crate::deep_size_0!(ArgAttr);

impl Remap for ArgAttr {
  type Target = Self;
  fn remap(&self, _: &mut Remapper) -> Self { *self }
}

/// A top level program item. (A program AST is a list of program items.)
pub type Item = Spanned<ItemKind>;

/// A top level program item. (A program AST is a list of program items.)
#[derive(Debug, DeepSizeOf)]
pub enum ItemKind {
  /// A procedure (or function or intrinsic), a top level item similar to function declarations in C.
  Proc {
    /// The type of declaration: `func`, `proc`, or `intrinsic`.
    kind: ProcKind,
    /// The name of the procedure.
    name: Spanned<AtomId>,
    /// The number of type arguments
    tyargs: u32,
    /// The arguments of the procedure.
    args: Box<[Arg]>,
    /// The return values of the procedure. (Functions and procedures return multiple values in MMC.)
    rets: Vec<Ret>,
    /// The variant, used for recursive functions.
    variant: Option<Box<Variant>>,
    /// The body of the procedure.
    body: Block
  },
  /// A global variable declaration.
  Global {
    /// The variable(s) being declared
    lhs: TuplePattern,
    /// The value of the declaration
    rhs: Expr,
  },
  /// A constant declaration.
  Const {
    /// The constant(s) being declared
    lhs: TuplePattern,
    /// The value of the declaration
    rhs: Expr,
  },
  /// A type definition.
  Typedef {
    /// The name of the newly declared type
    name: Spanned<AtomId>,
    /// The number of type arguments
    tyargs: u32,
    /// The arguments of the type declaration, for a parametric type
    args: Box<[Arg]>,
    /// The value of the declaration (another type)
    val: Type,
  },
}
