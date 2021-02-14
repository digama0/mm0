//! The high level IR, used during type inference.

use crate::util::FileSpan;

use super::{ty,  VarId};

/// A "generation ID", which tracks the program points where mutation
/// can occur. The actual set of logical variables is some subset of
/// all `(VarId, GenId)` pairs; one of the roles of the type inference pass
/// is to determine which variables change across each generation
/// and which do not.
#[derive(Copy, Clone, Debug)]
pub struct GenId(pub u32);

impl GenId {
  /// This is a special generation ID that tracks the latest version
  /// of all variables. Most regular variables act as if they have this
  /// generation ID.
  pub const LATEST: Self = Self(0);
  /// The initial generation, before any mutations.
  pub const ROOT: Self = Self(1);
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
  pub fn len(self) -> u32 {
    if let Some(c) = &self.0 {c.len} else {0}
  }

  /// The parent context, or `ROOT` if the context is already root.
  pub fn parent(self) -> Self {
    if let Some(c) = &self.0 {c.parent} else {Self::ROOT}
  }

  /// The greatest lower bound of two contexts, i.e. the largest
  /// context of which both `self` and `other` are descended.
  pub fn glb(mut self, mut other: Self) -> Self {
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
}

impl<'a> ContextNext<'a> {
  /// Create a new `ContextNext`, automatically filling the `len` field.
  pub fn new(parent: Context<'a>, var: VarId, gen: GenId, ty: ty::Ty<'a>) -> Self {
    Self {len: parent.len() + 1, var, gen, ty, parent}
  }
}

/// A partially elaborated tuple pattern.
#[derive(Debug)]
pub struct TuplePattern<'a> {
  /// The span of the pattern.
  pub span: &'a FileSpan,
  /// The pattern kind, see [`TuplePatternKind`].
  pub k: TuplePatternKind<'a>,
}

/// A partially elaborated tuple pattern.
#[derive(Debug)]
pub enum TuplePatternKind<'a> {
  /// A simple pattern, containing the actual binding in the [`ContextNext`].
  Name(bool, &'a ContextNext<'a>),
  /// A coercion. This is not available in the surface syntax, but if we have a binder
  /// like `let ((a, b), c) = ...` and we need to insert a coercion in the inner pattern,
  /// we desugar it to `let (x, c) = ...; let (a, b) = coe(x);`, except that at this
  /// point we don't want to make any structural syntax changes yet so we store the intent
  /// to insert the `coe` function while keeping it as a nested pattern-match,
  /// so the syntax is more like `let ((a, b) => coe, c) = ...` where `=> coe` means to apply
  /// the `coe` function to the value matched at that level.
  Coercion(Box<TuplePattern<'a>>, &'a [ty::Coercion<'a>], ty::Ty<'a>),
  /// A tuple pattern match. This has been typechecked, and the `Ty` determines what kind
  /// of pattern match it is.
  Tuple(&'a [TuplePattern<'a>], ty::Ty<'a>),
  /// An unelaborated tuple pattern match. The subpatterns are elaborated with metavariable types,
  /// but we don't yet know how to connect this list of types to the target type - for example
  /// the target type could be a metavariable, and propagating our default guess of a nondependent
  /// tuple could cause a type error if it turns out to be a dependent tuple.
  UnelaboratedTuple(&'a [TuplePattern<'a>], ty::Ty<'a>),
}

impl<'a> TuplePattern<'a> {
  /// The type of the values matched by this tuple pattern.
  pub fn ty(&self) -> ty::Ty<'a> {
    match self.k {
      TuplePatternKind::Name(_, &ContextNext {ty, ..}) |
      TuplePatternKind::Coercion(_, _, ty) |
      TuplePatternKind::Tuple(_, ty) |
      TuplePatternKind::UnelaboratedTuple(_, ty) => ty
    }
  }
}

/// An argument in a `struct` or function parameters.
#[derive(Debug)]
pub enum Arg<'a> {
  /// The usual lambda binder: `x: T`.
  Lam(TuplePattern<'a>),
  /// A definition binder: `x: T := e`.
  Let(TuplePattern<'a>, ty::Expr<'a>),
}

impl<'a> Arg<'a> {
  /// The variable part of the argument.
  pub fn var(&self) -> &TuplePattern<'a> {
    match self { Arg::Lam(pat) | Arg::Let(pat, _) => pat }
  }
}
