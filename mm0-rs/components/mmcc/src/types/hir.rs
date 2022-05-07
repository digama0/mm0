//! The high level IR, used during type inference.

use std::fmt::Debug;

use num::BigInt;
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;
use crate::{FileSpan, Symbol, types::indent};
use super::{Mm0Expr, VarId, IntTy, ProofId, ty};
pub use super::ast::ProcKind;

/// A "generation ID", which tracks the program points where mutation
/// can occur. The actual set of logical variables is some subset of
/// all `(VarId, GenId)` pairs; one of the roles of the type inference pass
/// is to determine which variables change across each generation
/// and which do not.
#[derive(Copy, Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct GenId(pub u32);
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(GenId);

impl GenId {
  /// This is a special generation ID that tracks the latest version
  /// of all variables. Most regular variables act as if they have this
  /// generation ID.
  pub const LATEST: Self = Self(0);
  /// The initial generation, before any mutations.
  pub const ROOT: Self = Self(1);
}

/// A spanned expression.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Spanned<'a, T> {
  /// The span of the expression
  pub span: &'a FileSpan,
  /// The data (the `k` stands for `kind` because it's often a `*Kind` enum
  /// but it can be anything).
  pub k: T,
}

impl<'a, T> Spanned<'a, T> {
  /// Transform a `Spanned<'a, T>` into `Spanned<'a, U>` given `f: T -> U`.
  pub fn map_into<U>(self, f: impl FnOnce(T) -> U) -> Spanned<'a, U> {
    Spanned { span: self.span, k: f(self.k) }
  }
  /// Transform a `&Spanned<'a, T>` into `Spanned<'a, U>` given `f: &T -> U`.
  pub fn map<'b, U>(&'b self, f: impl FnOnce(&'b T) -> U) -> Spanned<'a, U> {
    Spanned { span: self.span, k: f(&self.k) }
  }
  /// Transform a `Spanned<'a, T>` into `Spanned<U>` given `f: T -> U`.
  pub fn map_clone<U>(self, f: impl FnOnce(T) -> U) -> super::Spanned<U> {
    super::Spanned { span: self.span.clone(), k: f(self.k) }
  }
  /// Transform a `Spanned<'a, T>` into `Spanned<T>`.
  pub fn cloned(self) -> super::Spanned<T> { self.map_clone(|v| v) }
}

impl<T> super::Spanned<T> {
  /// Transform a `&'a Spanned<T>` into `hir::Spanned<'a, U>` given `f: &'a T -> U`.
  pub fn map_hir<U>(&self, f: impl FnOnce(&T) -> U) -> Spanned<'_, U> {
    Spanned { span: &self.span, k: f(&self.k) }
  }
  /// Transform a `&'a Spanned<T>` into `hir::Spanned<'a, T>`.
  pub fn as_ref(&self) -> Spanned<'_, T> where T: Clone { self.map_hir(T::clone) }
}

/// The type of variant, or well founded order that recursions decrease.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum VariantType<'a> {
  /// This variant is a nonnegative natural number which decreases to 0.
  Down,
  /// This variant is a natural number or integer which increases while
  /// remaining less than this constant.
  UpLt(ty::Expr<'a>),
  /// This variant is a natural number or integer which increases while
  /// remaining less than or equal to this constant.
  UpLe(ty::Expr<'a>),
}

/// A variant is a pure expression, together with a
/// well founded order that decreases on all calls.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Variant<'a>(pub ty::Expr<'a>, pub VariantType<'a>);

/// An argument declaration for a function.
pub type Arg<'a> = (ty::ArgAttr, ArgKind<'a>);

/// An argument declaration for a function.
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum ArgKind<'a> {
  /// A standard argument of the form `{x : T}`, a "lambda binder"
  Lam(Spanned<'a, ty::TuplePattern<'a>>),
  /// A substitution argument of the form `{{x : T} := val}`. (These are not supplied in
  /// invocations, they act as let binders in the remainder of the arguments.)
  Let(Spanned<'a, ty::TuplePattern<'a>>, ty::Expr<'a>, Option<Box<Expr<'a>>>),
}

impl<'a> ArgKind<'a> {
  /// Get the variable part of this argument.
  #[must_use] pub fn var(&self) -> Spanned<'a, ty::TuplePattern<'a>> {
    match *self { Self::Lam(pat) | Self::Let(pat, ..) => pat }
  }

  fn debug_with_attr(&self,
    attr: ty::ArgAttr,
    f: &mut std::fmt::Formatter<'_>
  ) -> std::fmt::Result {
    if attr.contains(ty::ArgAttr::IMPLICIT) { write!(f, "implicit ")? }
    if attr.contains(ty::ArgAttr::GHOST) { write!(f, "ghost ")? }
    if attr.contains(ty::ArgAttr::MUT) { write!(f, "mut ")? }
    if attr.contains(ty::ArgAttr::GLOBAL) { write!(f, "global ")? }
    write!(f, "{:?}", self)
  }
}

impl Debug for ArgKind<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Lam(pat) => pat.fmt(f),
      Self::Let(pat, _, Some(e)) => write!(f, "{:?} := {:?}", pat, e),
      Self::Let(pat, e, _) => write!(f, "{:?} := {:?}", pat, e),
    }
  }
}

impl<'a> From<&ArgKind<'a>> for ty::ArgKind<'a> {
  fn from(arg: &ArgKind<'a>) -> Self {
    match *arg {
      ArgKind::Lam(pat) => Self::Lam(pat.k),
      ArgKind::Let(pat, e, _) => Self::Let(pat.k, e),
    }
  }
}

/// A label in a label group declaration. Individual labels in the group
/// are referred to by their index in the list.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Label<'a> {
  /// The arguments of the label
  pub args: Box<[Arg<'a>]>,
  /// The variant, for recursive calls
  pub variant: Option<Variant<'a>>,
  /// The code that is executed when you jump to the label
  pub body: Spanned<'a, Block<'a>>,
}

/// A block is a list of statements, with an optional terminating expression.
#[derive(Default)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Block<'a> {
  /// The list of statements in the block.
  pub stmts: Vec<Stmt<'a>>,
  /// The optional last statement, or `()` if not specified.
  pub expr: Option<Box<Expr<'a>>>,
  /// The generation after the block,
  pub gen: GenId,
  /// The variables modified by the block.
  pub muts: Vec<VarId>,
}

impl Debug for Block<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.debug_indent(0, f)
  }
}

impl Block<'_> {
  fn debug_indent(&self, i: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if !self.muts.is_empty() {
      indent(i, f)?; write!(f, "#![mut")?;
      for &v in &self.muts { write!(f, " {}", v)? }
      writeln!(f, "]")?
    }
    for stmt in &self.stmts { indent(i, f)?; stmt.k.debug_indent(i, f)? }
    if let Some(expr) = &self.expr {
      indent(i, f)?; expr.k.0.debug_indent(i, f)?
    }
    Ok(())
  }
}

/// A statement in a block.
pub type Stmt<'a> = Spanned<'a, StmtKind<'a>>;

/// A statement in a block.
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum StmtKind<'a> {
  /// A let binding.
  Let {
    /// A tuple pattern, containing variable bindings.
    lhs: Spanned<'a, ty::TuplePattern<'a>>,
    /// The expression to evaluate.
    rhs: Expr<'a>,
  },
  /// An expression to be evaluated for its side effects, with the result being discarded.
  Expr((ExprKind<'a>, ty::ExprTy<'a>)),
  /// A label, which looks exactly like a local function but has no independent stack frame.
  /// They are called like regular functions but can only appear in tail position.
  /// If the `bool` is false then the label group is dead (never jumped to).
  Label(VarId, bool, Box<[Label<'a>]>),
}

impl Debug for StmtKind<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.debug_indent(0, f)
  }
}

impl StmtKind<'_> {
  fn debug_indent(&self, i: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      StmtKind::Let { lhs, rhs } => {
        write!(f, "let {:?} = ", lhs)?;
        rhs.k.0.debug_indent(i, f)?;
        writeln!(f, ";")
      }
      StmtKind::Expr(e) => {
        e.0.debug_indent(i, f)?;
        writeln!(f, ";")
      }
      StmtKind::Label(a, r, labs) => {
        for (i, lab) in labs.iter().enumerate() {
          writeln!(f, "{}label {:?}.{}(", if *r {""} else {"ghost "}, a, i)?;
          for &(attr, ref arg) in &*lab.args {
            indent(i+1, f)?; arg.debug_with_attr(attr, f)?; writeln!(f, ",")?;
            if let Some(var) = &lab.variant { indent(i+1, f)?; writeln!(f, "{:?},", var)?; }
          }
          indent(i, f)?; writeln!(f, ") = {{")?;
          lab.body.k.debug_indent(i+1, f)?;
          indent(i, f)?; writeln!(f, "}};")?;
        }
        Ok(())
      }
    }
  }
}

/// The different kinds of projection, used in defining places.
#[derive(Copy, Clone, Debug)]
pub enum ListKind {
  /// A projection `a.i` which retrieves the `i`th element of a tuple.
  List,
  /// A projection `a.i` which retrieves the `i`th element of a dependent tuple.
  Struct,
  /// A projection `a[i]` which retrieves the `i`th element of an array.
  Array,
  /// A projection `a.i` which views a conjunction type as its `i`th conjunct.
  And,
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(ListKind);

/// A while loop expression. An additional field `has_break` is stored in the return type
/// of the expression: If `cond` is a pure expression and there are no early `break`s inside the
/// loop, then the return type is `!cond`; otherwise `()`.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct While<'a> {
  /// The name of this loop, which can be used as a target for jumps.
  pub label: VarId,
  /// A hypothesis that the condition is true in the loop.
  pub hyp: Option<Spanned<'a, VarId>>,
  /// The loop condition.
  pub cond: Box<Expr<'a>>,
  /// The variant, which must decrease on every round around the loop.
  pub variant: Option<Variant<'a>>,
  /// The body of the loop.
  pub body: Box<Block<'a>>,
  /// The generation after the loop.
  pub gen: GenId,
  /// The variables that were modified by the loop.
  pub muts: Box<[VarId]>,
  /// If this is `Some(b)` then `cond` reduces to `Bool(b)` and so the loop
  /// trivializes or is an infinite loop.
  pub trivial: Option<bool>,
}

/// Categorizes the way the returns of a call expression are packed.
#[derive(Debug, Copy, Clone)]
pub enum ReturnKind {
  /// This function has at least one false return value, and so it does not return.
  Unreachable,
  /// This function has no return values.
  Unit,
  /// This function has one return value, and is not packed.
  One,
  /// This function has more than one return value, and is packed into a struct.
  Struct(u16),
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(ReturnKind);

/// A call expression.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Call<'a> {
  /// The function to call.
  pub f: Spanned<'a, Symbol>,
  /// True if this function contains side effects.
  pub side_effect: bool,
  /// The type arguments.
  pub tys: &'a [ty::Ty<'a>],
  /// The function arguments.
  pub args: Vec<Expr<'a>>,
  /// The variant, if needed.
  pub variant: Option<Box<Expr<'a>>>,
  /// The generation after the function call (the same as the current generation if this function
  /// does not mutate any variables)
  pub gen: GenId,
  /// Categorizes the way the returns are packed.
  pub rk: ReturnKind,
}

/// A place expression.
pub type Place<'a> = Spanned<'a, (PlaceKind<'a>, ty::Ty<'a>)>;

impl<'a> Place<'a> {
  /// Get the (stored) type of the expression.
  #[inline] #[must_use] pub fn ty(&self) -> ty::Ty<'a> { self.k.1 }
}

/// A place expression.
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[allow(clippy::type_complexity)]
pub enum PlaceKind<'a> {
  /// A variable reference.
  Var(VarId),
  /// An deref operation `*x: T` where `x: &T`. The provided type is `&T`.
  Deref(Box<(ty::Ty<'a>, Expr<'a>)>),
  /// An index operation `(index _ i h): T` where `_: (array T n)`,
  /// `i: nat`, and `h: i < n`. The provided type is `(array T n)`.
  /// If `h` is the `Err` variant, then it is an expr evaluating to `n`.
  Index(Box<(ty::Ty<'a>, Place<'a>, Expr<'a>, Result<Expr<'a>, Expr<'a>>)>),
  /// If `x: (array T n)`, then `(slice x a b h): (array T b)` if
  /// `h` is a proof that `a + b <= n`. The provided type is `(array T n)`.
  /// If `h` is the `Err` variant, then it is an expr evaluating to `n`.
  Slice(Box<(ty::Ty<'a>, Place<'a>, [Expr<'a>; 2], Result<Expr<'a>, Expr<'a>>)>),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  /// The provided type is `(T0, ..., T(n-1))` or `{f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(ListKind, Box<(ty::Ty<'a>, Place<'a>)>, u32),
  /// An upstream error.
  Error
}

impl Debug for PlaceKind<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.debug_indent(0, f)
  }
}

impl PlaceKind<'_> {
  fn debug_indent(&self, i: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      PlaceKind::Var(v) => write!(f, "{:?}", v),
      PlaceKind::Deref(e) => { write!(f, "*")?; e.1.k.0.debug_indent(i, f) }
      PlaceKind::Index(args) => {
        let (_, arr, idx, h) = &**args;
        arr.k.0.debug_indent(i, f)?;
        write!(f, "[")?;
        idx.k.0.debug_indent(i, f)?;
        if let Ok(h) = h {
          write!(f, ", ")?;
          h.k.0.debug_indent(i, f)?;
        }
        write!(f, "]")
      }
      PlaceKind::Slice(args) => {
        let (_, arr, [idx, len], h) = &**args;
        arr.k.0.debug_indent(i, f)?;
        write!(f, "[")?;
        idx.k.0.debug_indent(i, f)?;
        write!(f, "..+")?;
        len.k.0.debug_indent(i, f)?;
        if let Ok(h) = h {
          write!(f, ", ")?;
          h.k.0.debug_indent(i, f)?;
        }
        write!(f, "]")
      }
      PlaceKind::Proj(lk, e, j) => {
        e.1.k.0.debug_indent(i, f)?;
        if let ListKind::Array = lk { write!(f, "[{}]", j) } else { write!(f, ".{}", j) }
      }
      PlaceKind::Error => write!(f, "??"),
    }
  }
}

/// (Elaborated) unary operations.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Unop {
  /// Computes `-e as iN` from `e as iN`, or `-e` from `e` for `int`.
  Neg(IntTy),
  /// Logical (boolean) NOT
  Not,
  /// Computes `~e as iN` from `e as iN`, or `~e` from `e` for `int`.
  BitNot(IntTy),
  /// Truncation: Computes `e as i[to]` from `e as i[from]` (or `e`).
  /// (Requires `!(from <= to)` and `to.size() != Inf`.)
  As(/* from */ IntTy, /* to */ IntTy),
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(Unop);

impl std::fmt::Debug for Unop {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Unop::Neg(ity) => write!(f, "-[{}]", ity),
      Unop::Not => write!(f, "not"),
      Unop::BitNot(ity) => write!(f, "bnot[{}]", ity),
      Unop::As(from, to) => write!(f, "as[{} -> {}]", from, to),
    }
  }
}

/// (Elaborated) binary operations.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Binop {
  /// Integer addition
  Add(IntTy),
  /// Integer multiplication
  Mul(IntTy),
  /// Integer subtraction
  Sub(IntTy),
  /// Maximum
  Max(IntTy),
  /// Minimum
  Min(IntTy),
  /// Logical (boolean) AND
  And,
  /// Logical (boolean) OR
  Or,
  /// Bitwise AND, for signed or unsigned integers of any size
  BitAnd(IntTy),
  /// Bitwise OR, for signed or unsigned integers of any size
  BitOr(IntTy),
  /// Bitwise XOR, for signed or unsigned integers of any size
  BitXor(IntTy),
  /// Shift left
  Shl(IntTy),
  /// Shift right (arithmetic)
  Shr(IntTy),
  /// Less than, for signed or unsigned integers of any size
  Lt(IntTy),
  /// Less than or equal, for signed or unsigned integers of any size
  Le(IntTy),
  /// Equal, for signed or unsigned integers of any size
  Eq(IntTy),
  /// Not equal, for signed or unsigned integers of any size
  Ne(IntTy),
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(Binop);

impl std::fmt::Debug for Binop {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Binop::Add(ity) => write!(f, "+[{}]", ity),
      Binop::Mul(ity) => write!(f, "*[{}]", ity),
      Binop::Sub(ity) => write!(f, "-[{}]", ity),
      Binop::Max(ity) => write!(f, "max[{}]", ity),
      Binop::Min(ity) => write!(f, "min[{}]", ity),
      Binop::And => write!(f, "and"),
      Binop::Or => write!(f, "or"),
      Binop::BitAnd(ity) => write!(f, "band[{}]", ity),
      Binop::BitOr(ity) => write!(f, "bor[{}]", ity),
      Binop::BitXor(ity) => write!(f, "bxor[{}]", ity),
      Binop::Shl(ity) => write!(f, "shl[{}]", ity),
      Binop::Shr(ity) => write!(f, "shr[{}]", ity),
      Binop::Lt(ity) => write!(f, "<[{}]", ity),
      Binop::Le(ity) => write!(f, "<=[{}]", ity),
      Binop::Eq(ity) => write!(f, "=[{}]", ity),
      Binop::Ne(ity) => write!(f, "!=[{}]", ity),
    }
  }
}

impl super::Binop {
  /// Convert [`types::Binop`](super::Binop) into [`hir::Binop`](Binop), which requires an
  /// integral type, which represents the type of inputs and outputs for integer ops,
  /// the type of the left input for `Shl`/`Shr`, and the type of the inputs for comparisons.
  /// It is ignored for `And`/`Or`.
  #[must_use] pub fn as_hir(self, ity: IntTy) -> Binop {
    use super::Binop::*;
    match self {
      Add => Binop::Add(ity),
      Mul => Binop::Mul(ity),
      Sub => Binop::Sub(ity),
      Max => Binop::Max(ity),
      Min => Binop::Min(ity),
      And => Binop::And,
      Or => Binop::Or,
      BitAnd => Binop::BitAnd(ity),
      BitOr => Binop::BitOr(ity),
      BitXor => Binop::BitXor(ity),
      Shl => Binop::Shl(ity),
      Shr => Binop::Shr(ity),
      Lt => Binop::Lt(ity),
      Le => Binop::Le(ity),
      Eq => Binop::Eq(ity),
      Ne => Binop::Ne(ity),
    }
  }
}

/// An expression.
pub type Expr<'a> = Spanned<'a, (ExprKind<'a>, ty::ExprTy<'a>)>;

impl<'a> Expr<'a> {
  /// Get the (stored) type of the expression.
  #[inline] #[must_use] pub fn ty(&self) -> ty::Ty<'a> { self.k.1 .1 }
}

/// An expression. A block is a list of expressions.
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[allow(clippy::type_complexity)]
pub enum ExprKind<'a> {
  /// A `()` literal.
  Unit,
  /// A proof of true.
  ITrue,
  /// A variable reference.
  Var(VarId, GenId),
  /// A user constant.
  Const(Symbol),
  /// A boolean literal.
  Bool(bool),
  /// A number literal.
  Int(&'a BigInt),
  /// A unary operation.
  Unop(Unop, Box<Expr<'a>>),
  /// A binary operation.
  Binop(Binop, Box<Expr<'a>>, Box<Expr<'a>>),
  /// Equality, or disequality if `inverted = true`.
  Eq(ty::Ty<'a>, bool, Box<Expr<'a>>, Box<Expr<'a>>),
  /// `(sn x)` constructs the unique member of the type `(sn x)`.
  /// `(sn y h)` is also a member of `(sn x)` if `h` proves `y = x`.
  Sn(Box<Expr<'a>>, Option<Box<Expr<'a>>>),
  /// An index operation `(index a i h): T` where `a: (array T n)`,
  /// `i: nat`, and `h: i < n`.
  /// If `h` is the `Err` variant, then it is an expr evaluating to `n`.
  Index(Box<(ty::Ty<'a>, [Expr<'a>; 2], Result<Expr<'a>, Expr<'a>>)>),
  /// If `x: (array T n)`, then `(slice x a b h): (array T b)` if
  /// `h` is a proof that `a + b <= n`.
  /// If `h` is the `Err` variant, then it is an expr evaluating to `n`.
  Slice(Box<(ty::Ty<'a>, [Expr<'a>; 3], Result<Expr<'a>, Expr<'a>>)>),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(ListKind, Box<(ty::Ty<'a>, Expr<'a>)>, u32),
  /// An lvalue-to-rvalue conversion `x: T` where `x: ref T`.
  Rval(Box<Expr<'a>>),
  /// An deref operation `*x: T` where `x: &sn y` and `y: T`. The provided type is `&sn y`.
  Deref(Box<(ty::Ty<'a>, Expr<'a>)>),
  /// `(list e1 ... en)` returns a tuple of the arguments (of type
  /// `List`, `Struct`, `Array` or `And`). In the `And` case,
  /// all arguments must be copy or all cover the same heap location,
  /// and expressions have to be pure and have the same value.
  List(ListKind, Vec<Expr<'a>>),
  /// A ghost expression.
  Ghost(Box<Expr<'a>>),
  /// Evaluates the expression as a pure expression, so it will not take
  /// ownership of the result.
  Ref(Box<Place<'a>>),
  /// Capture a place being used as a function argument.
  ArgRef(Box<Place<'a>>),
  /// `(& x)` constructs a reference to `x`.
  Borrow(Box<Place<'a>>),
  /// `(pure $e$)` embeds an MM0 expression `$e$` as the target type,
  /// one of the numeric types
  Mm0(Mm0Expr<Expr<'a>>),
  /// Combine an expression with a proof that it has the right type.
  /// The given type is the type of `e` (which should be defeq to the actual type of `e`)
  Cast(Box<Expr<'a>>, ty::Ty<'a>, CastKind<'a>),
  /// An expression denoting an uninitialized value of the given type.
  Uninit,
  /// Return the size of a type.
  Sizeof(ty::Ty<'a>),
  /// Take the type of a variable, producing a proof of type `T`.
  Typeof(Box<Expr<'a>>),
  /// `(assert p)` evaluates `p: bool` and returns a proof of `T` (coerced from `p`).
  Assert(Box<Expr<'a>>),
  /// An assignment / mutation.
  Assign {
    /// A place (lvalue) to write to.
    lhs: Box<Place<'a>>,
    /// The expression to evaluate.
    rhs: Box<Expr<'a>>,
    /// An array of `new: ty -> old` mappings as `(new, old, ty)` tuples; the `new` variable
    /// is a variable id already in scope, while `old` is a new binding representing the previous
    /// value of the variable before the assignment.
    /// (This ordering is chosen so that the variable ID retains its "newest" value
    /// through any number of writes to it, while non-updatable `old` variables are created
    /// by the various assignments.)
    /// The type `ty` is the type of `new` after the mutation.
    map: Box<[(Spanned<'a, VarId>, Spanned<'a, VarId>, ty::ExprTy<'a>)]>,
    /// The generation after the mutation.
    gen: GenId,
  },
  /// A function call (or something that looks like one at parse time).
  Call(Call<'a>),
  /// A proof of a closed pure proposition.
  Mm0Proof(ProofId),
  /// A block scope.
  Block(Block<'a>),
  /// An if-then-else expression (at either block or statement level). The initial atom names
  /// a hypothesis that the expression is true in one branch and false in the other.
  If {
    /// The hypothesis name.
    hyp: Option<[Spanned<'a, VarId>; 2]>,
    /// The if condition.
    cond: Box<Expr<'a>>,
    /// The then/else cases.
    cases: Box<[Expr<'a>; 2]>,
    /// The generation at the join point,
    gen: GenId,
    /// The variables that were modified by the if statement.
    muts: Vec<VarId>,
  },
  /// A while loop. If `cond` is a pure expression and there are no early `break`s inside the loop,
  /// then the return type is `!cond`; otherwise `()`.
  While(Box<While<'a>>),
  /// `(unreachable h)` takes a proof of false and undoes the current code path.
  Unreachable(Box<Expr<'a>>),
  /// `(lab e1 ... en)` jumps to label `lab` with `e1 ... en` as arguments.
  /// Here the `VarId` is the target label group, and the `u16` is the index
  /// in the label group.
  Jump(VarId, u16, Vec<Expr<'a>>, Option<Box<Expr<'a>>>),
  /// `(break lab e)` jumps out of the scope containing label `lab`,
  /// returning `e` as the result of the block. Unlike [`Jump`](Self::Jump),
  /// this does not contain a label index because breaking from any label
  /// in the group has the same effect.
  Break(VarId, Box<Expr<'a>>),
  /// `(return e1 ... en)` returns `e1, ..., en` from the current function.
  Return(Vec<Expr<'a>>),
  /// Same as `return`, but accepts a single argument of the sigma type and unpacks it
  /// into the returns.
  UnpackReturn(Box<(ty::Ty<'a>, Expr<'a>)>),
  /// An inference hole `_`, which will give a compile error if it cannot be inferred
  /// but queries the compiler to provide a type context. The `bool` is true if this variable
  /// was created by the user through an explicit `_`, while compiler-generated inference
  /// variables have it set to false.
  Infer(bool),
  /// An upstream error.
  Error
}

impl Debug for ExprKind<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.debug_indent(0, f)
  }
}

impl ExprKind<'_> {
  fn debug_indent(&self, i: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      ExprKind::Unit => write!(f, "()"),
      ExprKind::ITrue => write!(f, "itrue"),
      ExprKind::Var(v, _) => write!(f, "{:?}", v),
      ExprKind::Const(c) => write!(f, "{}", c),
      ExprKind::Bool(b) => write!(f, "{}", b),
      ExprKind::Int(n) => write!(f, "{}", n),
      ExprKind::Unop(op, e) => { write!(f, "{:?} ", op)?; e.k.0.debug_indent(i, f) }
      ExprKind::Binop(op, e1, e2) => {
        e1.k.0.debug_indent(i, f)?;
        write!(f, " {:?} ", op)?;
        e2.k.0.debug_indent(i, f)
      }
      ExprKind::Eq(_, false, e1, e2) => {
        e1.k.0.debug_indent(i, f)?;
        write!(f, " == ")?;
        e2.k.0.debug_indent(i, f)
      }
      ExprKind::Eq(_, true, e1, e2) => {
        e1.k.0.debug_indent(i, f)?;
        write!(f, " != ")?;
        e2.k.0.debug_indent(i, f)
      }
      ExprKind::Sn(e, h) => {
        write!(f, "sn(")?;
        e.k.0.debug_indent(i, f)?;
        write!(f, ", ")?;
        match h {
          None => write!(f, "-)"),
          Some(h) => {
            h.k.0.debug_indent(i, f)?;
            write!(f, ")")
          }
        }
      }
      ExprKind::Index(args) => {
        let (_, [arr, idx], h) = &**args;
        arr.k.0.debug_indent(i, f)?;
        write!(f, "[")?;
        idx.k.0.debug_indent(i, f)?;
        if let Ok(h) = h {
          write!(f, ", ")?;
          h.k.0.debug_indent(i, f)?;
        }
        write!(f, "]")
      }
      ExprKind::Slice(args) => {
        let (_, [arr, idx, len], h) = &**args;
        arr.k.0.debug_indent(i, f)?;
        write!(f, "[")?;
        idx.k.0.debug_indent(i, f)?;
        write!(f, "..+")?;
        len.k.0.debug_indent(i, f)?;
        if let Ok(h) = h {
          write!(f, ", ")?;
          h.k.0.debug_indent(i, f)?;
        }
        write!(f, "]")
      }
      ExprKind::Proj(lk, e, j) => {
        e.1.k.0.debug_indent(i, f)?;
        if let ListKind::Array = lk { write!(f, "[{}]", j) } else { write!(f, ".{}", j) }
      }
      ExprKind::Rval(e) => e.k.0.debug_indent(i, f),
      ExprKind::Deref(e) => { write!(f, "*")?; e.1.k.0.debug_indent(i, f) }
      ExprKind::List(_, es) => {
        writeln!(f, "[")?;
        for e in es {
          indent(i+1, f)?; e.k.0.debug_indent(i+1, f)?; writeln!(f, ",")?;
        }
        indent(i, f)?; write!(f, "]")
      }
      ExprKind::Ghost(e) => {
        write!(f, "ghost(")?; e.k.0.debug_indent(i, f)?; write!(f, ")")
      }
      ExprKind::Ref(e) => { write!(f, "ref ")?; e.k.0.debug_indent(i, f) }
      ExprKind::ArgRef(e) => e.k.0.debug_indent(i, f),
      ExprKind::Borrow(e) => { write!(f, "&")?; e.k.0.debug_indent(i, f) }
      ExprKind::Mm0(e) => {
        write!(f, "{:?}", e.expr)?;
        if !e.subst.is_empty() {
          writeln!(f, "[")?;
          for e in &e.subst {
            indent(i+1, f)?; e.k.0.debug_indent(i+1, f)?; writeln!(f, ",")?;
          }
          indent(i, f)?; write!(f, "]")?;
        }
        Ok(())
      }
      ExprKind::Cast(e, ty, _) => {
        write!(f, "cast(")?;
        e.k.0.debug_indent(i, f)?;
        write!(f, ": {:?})", ty)
      }
      ExprKind::Uninit => write!(f, "uninit"),
      ExprKind::Sizeof(ty) => {
        write!(f, "sizeof({:?})", ty)
      }
      ExprKind::Typeof(e) => {
        write!(f, "typeof(")?;
        e.k.0.debug_indent(i, f)?;
        write!(f, ")")
      }
      ExprKind::Assert(e) => {
        write!(f, "assert(")?;
        e.k.0.debug_indent(i, f)?;
        write!(f, ")")
      }
      ExprKind::Assign { lhs, rhs, map, .. } => {
        lhs.k.0.debug_indent(i, f)?;
        write!(f, " <- ")?;
        rhs.k.0.debug_indent(i, f)?;
        write!(f, " with [")?;
        for (new, old, _) in &**map { write!(f, "{} <- {}, ", new.k, old.k)? }
        write!(f, "]")
      }
      ExprKind::Call(c) => {
        use itertools::Itertools;
        write!(f, "{}", c.f.k)?;
        if !c.tys.is_empty() { write!(f, "<{:?}>", c.tys.iter().format(", "))? }
        writeln!(f, "(")?;
        for e in &c.args {
          indent(i+1, f)?; e.k.0.debug_indent(i+1, f)?; writeln!(f, ",")?;
        }
        if let Some(var) = &c.variant { indent(i+1, f)?; writeln!(f, "{:?},", var)?; }
        indent(i, f)?; write!(f, ")")
      }
      ExprKind::Mm0Proof(p) => write!(f, "{:?}", p),
      ExprKind::Block(bl) => {
        writeln!(f, "{{")?;
        bl.debug_indent(i+1, f)?;
        indent(i, f)?; write!(f, "}}")
      }
      ExprKind::If { hyp, cond, cases, muts, .. } => {
        if !muts.is_empty() {
          write!(f, "#[muts")?;
          for &v in muts { write!(f, " {}", v)? }
          writeln!(f, "]")?; indent(i, f)?;
        }
        write!(f, "if ")?;
        if let Some([h, _]) = hyp { write!(f, "{}: ", h.k)? }
        cond.k.0.debug_indent(i+1, f)?;
        writeln!(f, " {{")?;
        cases[0].k.0.debug_indent(i+1, f)?;
        indent(i, f)?; writeln!(f, "}} else ")?;
        if let Some([_, h]) = hyp { write!(f, "{}: ", h.k)? }
        writeln!(f, "{{")?;
        cases[1].k.0.debug_indent(i+1, f)?;
        indent(i, f)?; write!(f, "}}")
      }
      ExprKind::While(w) => {
        if !w.muts.is_empty() {
          write!(f, "#[muts")?;
          for &v in &*w.muts { write!(f, " {}", v)? }
          writeln!(f, "]")?; indent(i, f)?;
        }
        write!(f, "{:?}: while ", w.label)?;
        if let Some(h) = w.hyp { write!(f, "{}: ", h.k)? }
        w.cond.k.0.debug_indent(i+1, f)?;
        if let Some(var) = &w.variant {
          writeln!(f)?;
          indent(i+1, f)?; writeln!(f, "{:?}", var)?;
          indent(i, f)?; writeln!(f, "{{")?;
        } else {
          writeln!(f, " {{")?;
        }
        w.body.debug_indent(i+1, f)?; writeln!(f)?;
        indent(i, f)?; write!(f, "}}")
      }
      ExprKind::Unreachable(e) => {
        write!(f, "unreachable ")?;
        e.k.0.debug_indent(i, f)
      }
      ExprKind::Jump(lab, j, es, var) => {
        writeln!(f, "jump {:?}.{}(", lab, j)?;
        for e in es {
          indent(i+1, f)?; e.k.0.debug_indent(i+1, f)?; writeln!(f, ",")?;
        }
        if let Some(var) = var { indent(i+1, f)?; writeln!(f, "{:?},", var)?; }
        indent(i, f)?; write!(f, ")")
      }
      ExprKind::Break(lab, e) => {
        write!(f, "break {} ", lab)?;
        e.k.0.debug_indent(i, f)
      }
      ExprKind::Return(es) => {
        writeln!(f, "return(")?;
        for e in es {
          indent(i+1, f)?; e.k.0.debug_indent(i+1, f)?; writeln!(f, ",")?;
        }
        indent(i, f)?; write!(f, ")")
      }
      ExprKind::UnpackReturn(e) => {
        write!(f, "return ")?;
        e.1.k.0.debug_indent(i, f)
      },
      ExprKind::Infer(true) => write!(f, "?_"),
      ExprKind::Infer(false) => write!(f, "_"),
      ExprKind::Error => write!(f, "??"),
    }
  }
}

/// A `cast` kind, which determines what the type of `h` in `(cast x h)` is.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum CastKind<'a> {
  /// Casting integral types `u32 -> i64` and so on
  Int,
  /// Casting a pointer type to `u64`
  Ptr,
  /// Casting a `&sn x` to `&T` assuming `x: T`
  Shr,
  /// Proof that `A` is a subtype of `B`
  Subtype(Box<Expr<'a>>),
  /// Proof that `[x : A] -* [x : B]` for the particular `x` in the cast
  Wand(Option<Box<Expr<'a>>>),
  /// Proof that `[x : B]` for the particular `x` in the cast
  Mem(Box<Expr<'a>>),
}

impl<'a> CastKind<'a> {
  /// Constructor for [`CastKind::Mem`].
  #[inline] #[must_use] pub fn mem(o: Option<Box<Expr<'a>>>) -> Self {
    if let Some(e) = o { Self::Mem(e) } else { Self::Wand(None) }
  }

  /// Constructor for [`CastKind::Subtype`].
  #[inline] #[must_use] pub fn subtype(o: Option<Box<Expr<'a>>>) -> Self {
    if let Some(e) = o { Self::Subtype(e) } else { Self::Wand(None) }
  }
}

/// A top level program item. (A program AST is a list of program items.)
pub type Item<'a> = Spanned<'a, ItemKind<'a>>;

/// A top level program item. (A program AST is a list of program items.)
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum ItemKind<'a> {
  /// A procedure (or function or intrinsic), a top level item similar to function declarations in C.
  Proc {
    /// The type of declaration: `func`, `proc`, or `intrinsic`.
    kind: ProcKind,
    /// The name of the procedure.
    name: Spanned<'a, Symbol>,
    /// The number of type arguments
    tyargs: u32,
    /// The arguments of the procedure.
    args: Box<[Arg<'a>]>,
    /// The generation for the return values.
    gen: GenId,
    /// The out parameter origin variables. `outs.len() <= rets.len()` and the first
    /// `outs.len()` arguments in `rets` correspond to the out arguments.
    outs: Box<[u32]>,
    /// The out parameters and return values of the procedure.
    /// (Functions and procedures return multiple values in MMC.)
    rets: Box<[Arg<'a>]>,
    /// The variant, used for recursive functions.
    variant: Option<Variant<'a>>,
    /// The body of the procedure.
    body: Block<'a>
  },
  /// A global variable declaration.
  Global {
    /// The variable(s) being declared
    lhs: Spanned<'a, ty::TuplePattern<'a>>,
    /// The value of the declaration
    rhs: Expr<'a>,
  },
}

impl Debug for ItemKind<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    match self {
      &Self::Proc { kind, ref name, tyargs, ref args, ref rets, ref variant, ref body, .. } => {
        write!(f, "{}", match kind {
          ProcKind::Func => "func",
          ProcKind::Proc => "proc",
          ProcKind::Main => "#[main] proc",
        })?;
        write!(f, " {}", name.k)?;
        if tyargs != 0 {
          write!(f, "<{}>", (0..tyargs).map(|n| format!("T{}", n)).format(", "))?
        }
        write!(f, "(")?;
        if !args.is_empty() {
          writeln!(f)?;
          for &(attr, ref arg) in &**args {
            write!(f, "  ")?;
            arg.debug_with_attr(attr, f)?;
            writeln!(f, ",")?;
          }
        }
        if let Some(var) = variant { writeln!(f, "  {:?},", var)? }
        if !rets.is_empty() {
          writeln!(f, ") -> (")?;
          for &(attr, ref arg) in &**rets {
            write!(f, "  ")?;
            arg.debug_with_attr(attr, f)?;
            writeln!(f, ",")?;
          }
        }
        writeln!(f, ") = {{")?;
        body.debug_indent(1, f)?;
        writeln!(f, "\n}}")
      }
      Self::Global { lhs, rhs } => {
        write!(f, "global {:?} = ", lhs)?;
        rhs.k.0.debug_indent(1, f)
      }
    }
  }
}
