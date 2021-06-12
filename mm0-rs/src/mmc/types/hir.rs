//! The high level IR, used during type inference.

use num::BigInt;
use crate::{AtomId, LispVal, FileSpan};
use super::{Mm0Expr, VarId, IntTy, ty};
pub use super::ast::ProcKind;

/// A "generation ID", which tracks the program points where mutation
/// can occur. The actual set of logical variables is some subset of
/// all `(VarId, GenId)` pairs; one of the roles of the type inference pass
/// is to determine which variables change across each generation
/// and which do not.
#[derive(Copy, Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct GenId(pub u32);
crate::deep_size_0!(GenId);

impl GenId {
  /// This is a special generation ID that tracks the latest version
  /// of all variables. Most regular variables act as if they have this
  /// generation ID.
  pub const LATEST: Self = Self(0);
  /// The initial generation, before any mutations.
  pub const ROOT: Self = Self(1);
}

/// A spanned expression.
#[derive(Clone, Debug, DeepSizeOf)]
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
}

impl<T> super::Spanned<T> {
  /// Transform a `&'a Spanned<T>` into `hir::Spanned<'a, U>` given `f: &'a T -> U`.
  pub fn map_hir<U>(&self, f: impl FnOnce(&T) -> U) -> Spanned<'_, U> {
    Spanned { span: &self.span, k: f(&self.k) }
  }
}

/// A context is a singly linked list of logical variable declarations.
/// The collection of all contexts forms a tree.
#[derive(Copy, Clone, Debug)]
pub struct Context<'a>(pub Option<&'a ContextNext<'a>>);

/// A nonempty context extends a context by a single variable declaration.
#[derive(Copy, Clone, Debug)]
pub struct ContextNext<'a> {
  /// The total number of variables in this context.
  pub len: u32,
  /// The variable name.
  pub var: VarId,
  /// The variable's generation ID.
  pub gen: GenId,
  /// The variable's value.
  pub val: ty::Expr<'a>,
  /// The variable's type.
  pub ty: ty::Ty<'a>,
  /// The parent context, which this context extends.
  pub parent: Context<'a>,
}

impl<'a> PartialEq for Context<'a> {
  fn eq(&self, other: &Self) -> bool { self.0 == other.0 }
}
impl<'a> Eq for Context<'a> {}

impl<'a> PartialEq for ContextNext<'a> {
  fn eq(&self, other: &Self) -> bool { std::ptr::eq(self, other) }
}
impl<'a> Eq for ContextNext<'a> {}

impl<'a> From<&'a ContextNext<'a>> for Context<'a> {
  fn from(ctx: &'a ContextNext<'a>) -> Self { Self(Some(ctx)) }
}

impl<'a> Context<'a> {
  /// The root context, with no variables.
  pub const ROOT: Self = Context(None);

  /// The length of a context (the number of variables).
  #[must_use] pub fn len(self) -> u32 {
    if let Some(c) = &self.0 {c.len} else {0}
  }

  /// Is this context root?
  #[must_use] pub fn is_empty(self) -> bool { self.0.is_none() }

  /// The parent context, or `ROOT` if the context is already root.
  #[must_use] pub fn parent(self) -> Self {
    if let Some(c) = &self.0 {c.parent} else {Self::ROOT}
  }

  /// The greatest lower bound of two contexts, i.e. the largest
  /// context of which both `self` and `other` are descended.
  #[must_use] pub fn glb(mut self, mut other: Self) -> Self {
    if self.len() == other.len() {
      return self
    }
    while other.len() > self.len() {
      other = other.parent();
    }
    while self.len() > other.len() {
      self = self.parent();
    }
    while self != other {
      self = self.parent();
      other = other.parent();
    }
    self
  }

  /// Retrieve a variable from the context by ID, returning the `ContextNext`
  /// containing that variable's data.
  #[must_use] pub fn find(mut self, v: VarId) -> Option<&'a ContextNext<'a>> {
    loop {
      if let Some(c) = self.0 {
        if c.var == v { return self.0 }
        self = c.parent
      } else { return None }
    }
  }
}

impl<'a> IntoIterator for Context<'a> {
  type Item = &'a ContextNext<'a>;
  type IntoIter = ContextIter<'a>;
  fn into_iter(self) -> ContextIter<'a> { ContextIter(self.0) }
}

/// An iterator over the context, from the most recently introduced variable
/// to the beginning.
#[derive(Debug)]
pub struct ContextIter<'a>(Option<&'a ContextNext<'a>>);

impl<'a> Iterator for ContextIter<'a> {
  type Item = &'a ContextNext<'a>;
  fn next(&mut self) -> Option<&'a ContextNext<'a>> {
    let c = self.0?;
    self.0 = c.parent.0;
    Some(c)
  }
}

impl<'a> ContextNext<'a> {
  /// Create a new `ContextNext`, automatically filling the `len` field.
  #[must_use] pub fn new(
    parent: Context<'a>, v: VarId,
    gen: GenId, val: ty::Expr<'a>, ty: ty::Ty<'a>
  ) -> Self {
    Self {len: parent.len() + 1, var: v, gen, val, ty, parent}
  }
}

/// The type of variant, or well founded order that recursions decrease.
#[derive(Clone, Copy, Debug, DeepSizeOf)]
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
#[derive(Clone, Copy, Debug, DeepSizeOf)]
pub struct Variant<'a>(pub ty::Expr<'a>, pub VariantType<'a>);

/// An argument declaration for a function.
pub type Arg<'a> = (ty::ArgAttr, ArgKind<'a>);

/// An argument declaration for a function.
#[derive(Debug, DeepSizeOf)]
pub enum ArgKind<'a> {
  /// A standard argument of the form `{x : T}`, a "lambda binder"
  Lam(ty::TuplePattern<'a>),
  /// A substitution argument of the form `{{x : T} := val}`. (These are not supplied in
  /// invocations, they act as let binders in the remainder of the arguments.)
  Let(ty::TuplePattern<'a>, ty::Expr<'a>, Option<Box<Expr<'a>>>),
}

impl<'a> From<&ArgKind<'a>> for ty::ArgKind<'a> {
  fn from(arg: &ArgKind<'a>) -> Self {
    match *arg {
      ArgKind::Lam(pat) => Self::Lam(pat),
      ArgKind::Let(pat, e, _) => Self::Let(pat, e),
    }
  }
}

/// A label in a label group declaration. Individual labels in the group
/// are referred to by their index in the list.
#[derive(Debug, DeepSizeOf)]
pub struct Label<'a> {
  /// The arguments of the label
  pub args: Box<[Arg<'a>]>,
  /// The variant, for recursive calls
  pub variant: Option<Variant<'a>>,
  /// The code that is executed when you jump to the label
  pub body: Block<'a>,
}

/// A block is a list of statements, with an optional terminating expression.
#[derive(Default, Debug, DeepSizeOf)]
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

/// A statement in a block.
pub type Stmt<'a> = Spanned<'a, StmtKind<'a>>;

/// A statement in a block.
#[derive(Debug, DeepSizeOf)]
pub enum StmtKind<'a> {
  /// A let binding.
  Let {
    /// A tuple pattern, containing variable bindings.
    lhs: ty::TuplePattern<'a>,
    /// The expression to evaluate.
    rhs: Expr<'a>,
  },
  /// An expression to be evaluated for its side effects, with the result being discarded.
  Expr((ExprKind<'a>, ty::ExprTy<'a>)),
  /// A label, which looks exactly like a local function but has no independent stack frame.
  /// They are called like regular functions but can only appear in tail position.
  Label(VarId, Box<[Label<'a>]>),
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
crate::deep_size_0!(ListKind);

/// A while loop expression. An additional field `has_break` is stored in the return type
/// of the expression: If `cond` is a pure expression and there are no early `break`s inside the
/// loop, then the return type is `!cond`; otherwise `()`.
#[derive(Debug, DeepSizeOf)]
pub struct While<'a> {
  /// The name of this loop, which can be used as a target for jumps.
  pub label: VarId,
  /// A hypothesis that the condition is true in the loop.
  pub hyp: Option<VarId>,
  /// The loop condition.
  pub cond: Box<Expr<'a>>,
  /// The variant, which must decrease on every round around the loop.
  pub var: Option<Variant<'a>>,
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
crate::deep_size_0!(ReturnKind);

/// A call expression.
#[derive(Debug, DeepSizeOf)]
pub struct Call<'a> {
  /// The function to call.
  pub f: Spanned<'a, AtomId>,
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
#[derive(Debug, DeepSizeOf)]
pub enum PlaceKind<'a> {
  /// A variable reference.
  Var(VarId),
  /// An deref operation `*x: T` where `x: &T`.
  Deref(Box<Expr<'a>>),
  /// An index operation `(index _ i h): T` where `_: (array T n)`,
  /// `i: nat`, and `h: i < n`.
  /// If `h` is the `Err` variant, then it is an expr evaluating to `n`.
  Index(Box<(Place<'a>, Expr<'a>, Result<Expr<'a>, Expr<'a>>)>),
  /// If `x: (array T n)`, then `(slice x a b h): (array T b)` if
  /// `h` is a proof that `a + b <= n`.
  /// If `h` is the `Err` variant, then it is an expr evaluating to `n`.
  Slice(Box<(Place<'a>, [Expr<'a>; 2], Result<Expr<'a>, Expr<'a>>)>),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(ListKind, Box<Place<'a>>, u32),
  /// An upstream error.
  Error
}

/// (Elaborated) unary operations.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Unop {
  /// Computes `-e as iN` from `e as iN`, or `-e` from `e` for `int`.
  Neg(IntTy),
  /// Logical (boolean) NOT
  Not,
  /// Computes `~e as iN` from `e as iN`, or `~e` from `e` for `int`.
  BitNot(IntTy),
  /// Truncation: Computes `e as i[to]` from `e as i[from]` (or `e`).
  /// (Requires `!(from <= to)` and `to.size() != Inf`.)
  As(IntTy, IntTy),
}
crate::deep_size_0!(Unop);

/// (Elaborated) binary operations.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
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
crate::deep_size_0!(Binop);

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
#[derive(Debug, DeepSizeOf)]
#[allow(clippy::type_complexity)]
pub enum ExprKind<'a> {
  /// A `()` literal.
  Unit,
  /// A proof of true.
  ITrue,
  /// A variable reference.
  Var(VarId, GenId),
  /// A user constant.
  Const(AtomId),
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
  Index(Box<([Expr<'a>; 2], Result<Expr<'a>, Expr<'a>>)>),
  /// If `x: (array T n)`, then `(slice x a b h): (array T b)` if
  /// `h` is a proof that `a + b <= n`.
  /// If `h` is the `Err` variant, then it is an expr evaluating to `n`.
  Slice(Box<([Expr<'a>; 3], Result<Expr<'a>, Expr<'a>>)>),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(ListKind, Box<Expr<'a>>, u32),
  /// An lvalue-to-rvalue conversion `x: T` where `x: ref T`.
  Rval(Box<Expr<'a>>),
  /// An deref operation `*x: T` where `x: &T`.
  Deref(Box<Expr<'a>>),
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
    map: Box<[(VarId, VarId, ty::ExprTy<'a>)]>,
    /// The generation after the mutation.
    gen: GenId,
  },
  /// A function call (or something that looks like one at parse time).
  Call(Call<'a>),
  /// A proof of a closed pure proposition.
  Mm0Proof(&'a LispVal),
  /// A block scope.
  Block(Block<'a>),
  /// An if-then-else expression (at either block or statement level). The initial atom names
  /// a hypothesis that the expression is true in one branch and false in the other.
  If {
    /// The hypothesis name.
    hyp: Option<[VarId; 2]>,
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
  UnpackReturn(Box<Expr<'a>>),
  /// An inference hole `_`, which will give a compile error if it cannot be inferred
  /// but queries the compiler to provide a type context. The `bool` is true if this variable
  /// was created by the user through an explicit `_`, while compiler-generated inference
  /// variables have it set to false.
  Infer(bool),
  /// An upstream error.
  Error
}

/// A `cast` kind, which determines what the type of `h` in `(cast x h)` is.
#[derive(Debug, DeepSizeOf)]
pub enum CastKind<'a> {
  /// Casting integral types `u32 -> i64` and so on
  Int,
  /// Casting a pointer type to `u64`
  Ptr,
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
#[derive(Debug, DeepSizeOf)]
pub enum ItemKind<'a> {
  /// A procedure (or function or intrinsic), a top level item similar to function declarations in C.
  Proc {
    /// The type of declaration: `func`, `proc`, or `intrinsic`.
    kind: ProcKind,
    /// The name of the procedure.
    name: Spanned<'a, AtomId>,
    /// The number of type arguments
    tyargs: u32,
    /// The arguments of the procedure.
    args: Box<[Arg<'a>]>,
    /// The generation for the return values.
    gen: GenId,
    /// The return values of the procedure. (Functions and procedures return multiple values in MMC.)
    rets: Box<[Arg<'a>]>,
    /// The variant, used for recursive functions.
    variant: Option<Variant<'a>>,
    /// The body of the procedure.
    body: Block<'a>
  },
  /// A global variable declaration.
  Global {
    /// The variable(s) being declared
    lhs: ty::TuplePattern<'a>,
    /// The value of the declaration
    rhs: Expr<'a>,
  },
}
