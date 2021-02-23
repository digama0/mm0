//! The high level IR, used during type inference.

use num::BigInt;
use crate::{elab::{environment::AtomId, lisp::LispVal}, util::FileSpan};
use super::{Binop, Mm0Expr, Unop, VarId, ast::ProcKind, ty};

/// A "generation ID", which tracks the program points where mutation
/// can occur. The actual set of logical variables is some subset of
/// all `(VarId, GenId)` pairs; one of the roles of the type inference pass
/// is to determine which variables change across each generation
/// and which do not.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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

  /// Construct an `Expr, Ty` pair from a variable record.
  #[must_use] pub fn expr_ty(&self) -> ty::ExprTy<'a> { (Some(self.val), self.ty) }
}

/// The type of variant, or well founded order that recursions decrease.
#[derive(Debug, DeepSizeOf)]
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
#[derive(Debug, DeepSizeOf)]
pub struct Variant<'a>(pub ty::Expr<'a>, pub VariantType<'a>);

/// A label in a label group declaration. Individual labels in the group
/// are referred to by their index in the list.
#[derive(Debug, DeepSizeOf)]
pub struct Label<'a> {
  /// The arguments of the label
  pub args: &'a [ty::Arg<'a>],
  /// The variant, for recursive calls
  pub variant: Option<Box<Variant<'a>>>,
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
  Expr(ExprKind<'a>),
  /// A label, which looks exactly like a local function but has no independent stack frame.
  /// They are called like regular functions but can only appear in tail position.
  Label(VarId, Box<[Label<'a>]>),
}

/// An expression.
pub type Expr<'a> = Spanned<'a, ExprKind<'a>>;

/// An expression. A block is a list of expressions.
#[derive(Debug, DeepSizeOf)]
#[allow(clippy::type_complexity)]
pub enum ExprKind<'a> {
  /// A `()` literal.
  Unit,
  /// A variable reference.
  Var(VarId, GenId),
  /// A user constant.
  Const(AtomId),
  /// A global variable.
  Global(AtomId),
  /// A boolean literal.
  Bool(bool),
  /// A number literal.
  Int(&'a BigInt),
  /// A unary operation.
  Unop(Unop, Box<Expr<'a>>),
  /// A binary operation.
  Binop(Binop, Box<Expr<'a>>, Box<Expr<'a>>),
  /// `(sn x)` constructs the unique member of the type `(sn x)`.
  /// `(sn y h)` is also a member of `(sn x)` if `h` proves `y = x`.
  Sn(Box<Expr<'a>>, Option<Box<Expr<'a>>>),
  /// An index operation `(index a i h): T` where `a: (array T n)`,
  /// `i: nat`, and `h: i < n`.
  Index(Box<Expr<'a>>, Box<Expr<'a>>, Option<Box<Expr<'a>>>),
  /// If `x: (array T n)`, then `(slice x a b h): (array T b)` if
  /// `h` is a proof that `a + b <= n`.
  Slice(Box<(Expr<'a>, Expr<'a>, Expr<'a>)>, Option<Box<Expr<'a>>>),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(Box<Expr<'a>>, u32),
  /// An lvalue-to-rvalue conversion `x: T` where `x: ref T`.
  Rval(Box<Expr<'a>>),
  /// An deref operation `*x: T` where `x: &T`.
  Deref(Box<Expr<'a>>),
  /// `(list e1 ... en)` returns a tuple of the arguments (of type
  /// `List`, `Struct`, `Array` or `And`). In the `And` case,
  /// all arguments must be copy or all cover the same heap location,
  /// and expressions have to be pure and have the same value.
  List(Vec<Expr<'a>>, ty::Ty<'a>),
  /// A ghost expression.
  Ghost(Box<Expr<'a>>),
  /// Evaluates the expression as a pure expression, so it will not take
  /// ownership of the result.
  Place(Box<Expr<'a>>),
  /// `(& x)` constructs a reference to `x`.
  Ref(Box<Expr<'a>>),
  /// `(pure $e$)` embeds an MM0 expression `$e$` as the target type,
  /// one of the numeric types
  Mm0(Mm0Expr<Expr<'a>>, ty::Ty<'a>),
  /// A truncation / bit cast operation.
  As(Box<Expr<'a>>, ty::Ty<'a>, ty::Ty<'a>, ty::AsKind),
  /// Combine an expression with a proof that it has the right type.
  Cast(Box<Expr<'a>>, ty::Ty<'a>, ty::Ty<'a>, CastKind<'a>),
  /// Reinterpret an expression given a proof that it has the right type.
  Pun(Box<Expr<'a>>, Option<Box<Expr<'a>>>),
  /// An expression denoting an uninitialized value of the given type.
  Uninit(ty::Ty<'a>),
  /// Return the size of a type.
  Sizeof(ty::Ty<'a>),
  /// Take the type of a variable, producing a proof of type `T`.
  Typeof(Box<Expr<'a>>, ty::Ty<'a>),
  /// `(assert p)` evaluates `p: bool` and returns a proof of `T` (coerced from `p`).
  Assert(Box<Expr<'a>>, ty::Ty<'a>),
  /// An assignment / mutation.
  Assign {
    /// A place (lvalue) to write to.
    lhs: Box<Expr<'a>>,
    /// The expression to evaluate.
    rhs: Box<Expr<'a>>,
    /// An array of `new -> old` mappings as `(new, old)` pairs; the `new` variable is a variable
    /// id already in scope, while `old` is a new binding representing the previous
    /// value of the variable before the assignment.
    /// (This ordering is chosen so that the variable ID retains its "newest" value
    /// through any number of writes to it, while non-updatable `old` variables are created
    /// by the various assignments.)
    oldmap: Box<[(VarId, VarId)]>,
    /// The generation after the mutation.
    gen: GenId,
  },
  /// A function call (or something that looks like one at parse time).
  Call {
    /// The function to call.
    f: Spanned<'a, AtomId>,
    /// The type arguments.
    tys: Vec<ty::Ty<'a>>,
    /// The function arguments.
    args: Vec<Expr<'a>>,
    /// The variant, if needed.
    variant: Option<Box<Expr<'a>>>,
  },
  /// An entailment proof, which takes a proof of `P1 * ... * Pn => Q` and expressions proving
  /// `P1, ..., Pn` and is a hypothesis of type `Q`.
  Proof(Proof<'a>),
  /// A block scope.
  Block(Block<'a>),
  /// An if-then-else expression (at either block or statement level). The initial atom names
  /// a hypothesis that the expression is true in one branch and false in the other.
  If {
    /// The hypothesis name.
    hyp: Option<VarId>,
    /// The if condition.
    cond: Box<Expr<'a>>,
    /// The then/else cases.
    cases: Box<[(Expr<'a>, Box<[(VarId, GenId)]>); 2]>,
    /// The generation at the join point.
    gen: GenId,
  },
  /// A while loop.
  While {
    /// The name of this loop, which can be used as a target for jumps.
    label: VarId,
    /// A hypothesis that the condition is true in the loop and false after it.
    hyp: Option<VarId>,
    /// The loop condition.
    cond: Box<Expr<'a>>,
    /// The variant, which must decrease on every round around the loop.
    var: Option<Box<Variant<'a>>>,
    /// The body of the loop.
    body: Box<Block<'a>>,
  },
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

/// A proof expression, which proves some hypothesis.
#[derive(Debug, DeepSizeOf)]
pub enum Proof<'a> {
  /// A proof of [`PropKind::True`]
  ITrue,
  /// A proof of [`PropKind::Emp`]
  IEmp,
  /// And introduction
  IAnd(Box<[Expr<'a>]>),
  /// Sep introduction
  ISep(Box<[Expr<'a>]>),
  /// A proof of `P`.
  Mm0(&'a LispVal, ty::Ty<'a>),
}

/// A `cast` kind, which determines what the type of `h` in `(cast x h)` is.
#[derive(Debug, DeepSizeOf)]
pub enum CastKind<'a> {
  /// Proof that `A` is a subtype of `B`
  Subtype(Option<Box<Expr<'a>>>),
  /// Proof that `[x : A] -* [x : B]` for the particular `x` in the cast
  Wand(ty::Expr<'a>, Option<Box<Expr<'a>>>),
  /// Proof that `[x : B]` for the particular `x` in the cast
  Mem(ty::Expr<'a>, Option<Box<Expr<'a>>>),
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
    args: &'a [ty::Arg<'a>],
    /// The return values of the procedure. (Functions and procedures return multiple values in MMC.)
    rets: &'a [ty::Arg<'a>],
    /// The variant, used for recursive functions.
    variant: Option<Box<Variant<'a>>>,
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
  /// A constant declaration.
  Const {
    /// The constant(s) being declared
    lhs: ty::TuplePattern<'a>,
    /// The value of the declaration
    rhs: ty::Expr<'a>,
  },
  /// A type definition.
  Typedef {
    /// The name of the newly declared type
    name: Spanned<'a, AtomId>,
    /// The number of type arguments
    tyargs: u32,
    /// The arguments of the type declaration, for a parametric type
    args: &'a [ty::Arg<'a>],
    /// The value of the declaration (another type)
    val: ty::Ty<'a>,
  },
}
