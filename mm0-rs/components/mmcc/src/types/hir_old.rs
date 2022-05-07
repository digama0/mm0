//! Types used in the rest of the compiler.
use std::sync::Arc;
use std::rc::Rc;
use num::BigInt;
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;
use crate::FileSpan;
use crate::elab::{environment::Symbol,
  lisp::{LispVal, Uncons, print::{EnvDisplay, FormatEnv}}};
use super::{Binop, Mm0Expr, Size, Unop, VarId, ast};

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
  Unknown,
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(Lifetime);

impl std::fmt::Display for Lifetime {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Lifetime::Extern => "extern".fmt(f),
      Lifetime::Place(v) => v.fmt(f),
      Lifetime::Unknown => "_".fmt(f),
    }
  }
}

// /// An argument to a function.
// #[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
// pub struct Arg {
//   /// The name of the argument, if not `_`.
//   pub name: Option<(Symbol, FileSpan)>,
//   /// True if the argument is a ghost variable (computationally irrelevant).
//   pub ghost: bool,
//   /// The (unparsed) type of the argument.
//   pub ty: LispVal,
// }

// impl PartialEq<Arg> for Arg {
//   fn eq(&self, other: &Arg) -> bool {
//     let b = match (&self.name, &other.name) {
//       (None, None) => true,
//       (&Some((a, _)), &Some((b, _))) => a == b,
//       _ => false
//     };
//     b && self.ghost == other.ghost && self.ty == other.ty
//   }
// }
// impl Eq for Arg {}

/// The type of variant, or well founded order that recursions decrease.
#[derive(PartialEq, Eq, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum VariantType {
  /// This variant is a nonnegative natural number which decreases to 0.
  Down,
  /// This variant is a natural number or integer which increases while
  /// remaining less than this constant.
  UpLt(LispVal),
  /// This variant is a natural number or integer which increases while
  /// remaining less than or equal to this constant.
  UpLe(LispVal)
}

/// A variant is a pure expression, together with a
/// well founded order that decreases on all calls.
pub type Variant = (LispVal, VariantType);

/// A strongly typed tuple pattern.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum TuplePattern {
  /// A variable binding. The `bool` is true if the variable is ghost.
  Name(bool, VarId, Option<FileSpan>, Box<Type>),
  /// A unit pattern match.
  Unit,
  /// A singleton pattern match `(x h) := sn e`, where `x: T` and `h: x = e`.
  Single(Box<(TuplePattern, TuplePattern)>),
}

impl TuplePattern {
  /// Get an expr representation of the tuple constructed by this pattern.
  /// (Note that this can't be done on user-level names, since the pattern match
  /// may contain `_` patterns that would not be valid in the expression.
  /// We always name these variables with internal names, and these are used in the tuple.)
  #[must_use] pub fn to_expr(&self) -> PureExpr {
    match self {
      &Self::Name(_, a, _, _) => PureExpr::Var(a),
      Self::Unit => PureExpr::Unit,
      Self::Single(p) => p.0.to_expr(),
    }
  }

  /// True if all the bindings in this pattern are ghost.
  #[must_use] pub fn ghost(&self) -> bool {
    match self {
      &TuplePattern::Name(g, _, _, _) => g,
      TuplePattern::Unit => true,
      TuplePattern::Single(p) => p.0.ghost(),
    }
  }
}

/// A pattern, the left side of a switch statement.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum Pattern {
  /// A variable binding, unless this is the name of a constant in which case
  /// it is a constant value.
  VarOrConst(Symbol),
  /// A numeric literal.
  Number(BigInt),
  /// A hypothesis pattern, which binds the first argument to a proof that the
  /// scrutinee satisfies the pattern argument.
  Hyped(Symbol, Box<Pattern>),
  /// A pattern guard: Matches the inner pattern, and then if the expression returns
  /// true, this is also considered to match.
  With(Box<(Pattern, LispVal)>),
  /// A disjunction of patterns.
  Or(Box<[Pattern]>),
}

/// An expression or statement. A block is a list of expressions.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum PExpr {
  /// A variable move expression. Unlike `Pure(Var(v))`, this will take the value in `v`,
  /// leaving it moved out.
  Var(VarId),
  /// An integer or natural number.
  Int(BigInt),
  /// The unit value `()`.
  Unit,
  /// A boolean literal.
  Bool(bool),
  /// A unary operation.
  Unop(Unop, Box<PExpr>),
  /// A binary operation.
  Binop(Binop, Box<PExpr>, Box<PExpr>),
  /// A tuple constructor.
  Tuple(Box<[PExpr]>, Box<Type>),
  /// An index operation `(index a i h): T` where `a: (array T n)`,
  /// `i: nat`, and `h: i < n`.
  Index(Box<PExpr>, Rc<PExpr>, Box<PExpr>),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(Box<PExpr>, u32),
  /// An deref operation `(* x): T` where `x: (& T)`.
  Deref(Box<PExpr>),
  /// A ghost expression.
  Ghost(Box<PExpr>),
  /// A truncation / bit cast operation.
  As(Box<(PExpr, Type)>),
  /// A `(pure expression.
  Pure(Box<(Mm0Expr<PExpr>, Type)>),
  /// A let binding.
  Let {
    /// A tuple pattern, containing variable bindings.
    lhs: TuplePattern,
    /// The expression to evaluate, or [`None`] for uninitialized.
    rhs: Box<PExpr>,
  },
  /// A function call or intrinsic.
  Call {
    /// The function to call.
    f: Symbol,
    /// The span of the head of the function.
    fsp: Option<FileSpan>,
    /// The function arguments.
    args: Box<[PExpr]>,
    /// The variant, if needed.
    variant: Option<Box<PExpr>>,
  },
  // /// An entailment proof, which takes a proof of `P1 * ... * Pn => Q` and expressions proving
  // /// `P1, ..., Pn` and is a hypothesis of type `Q`.
  // Entail(LispVal, Box<[PExpr]>),
  /// A block scope.
  Block(Box<[PExpr]>),
  /// A label, which looks exactly like a local function but has no independent stack frame.
  /// They are called like regular functions but can only appear in tail position.
  Label {
    /// The name of the label
    name: Symbol,
    /// The arguments of the label
    args: Box<[TuplePattern]>,
    /// The variant, for recursive calls
    variant: Option<Variant>,
    /// The code that is executed when you jump to the label
    body: Box<[PExpr]>,
  },
  // /// An if-then-else expression (at either block or statement level). The initial atom names
  // /// a hypothesis that the expression is true in one branch and false in the other.
  // If(Box<(Option<Symbol>, PExpr, PExpr, PExpr)>),
  // /// A switch (pattern match) statement, given the initial expression and a list of match arms.
  // Switch(Box<PExpr>, Box<[(Pattern, PExpr)]>),
  /// A while loop.
  While {
    /// A hypothesis that the condition is true in the loop and false after it.
    hyp: Option<Symbol>,
    /// The loop condition.
    cond: Box<PExpr>,
    /// The variant, which must decrease on every round around the loop.
    var: Option<Variant>,
    /// The body of the loop.
    body: Box<[PExpr]>,
  },
  /// `(assert p)` evaluates `p: bool` and returns a proof of `p`.
  Assert(Rc<PExpr>),
  // /// A hole `_`, which is a compile error but queries the compiler to provide a type context.
  // Hole(FileSpan),
}

/// An expression or statement. A block is a list of expressions.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum Expr {
  /// A pure expression.
  Pure(PureExpr),
  /// A variable move expression. Unlike `Pure(Var(v))`, this will take the value in `v`,
  /// leaving it moved out.
  Var(VarId),
  /// A unary operation.
  Unop(Unop, Box<Expr>),
  /// A binary operation.
  Binop(Binop, Box<Expr>, Box<Expr>),
  /// A tuple constructor.
  Tuple(Box<[Expr]>, Box<Type>),
  /// An index operation `(index a i h): T` where `a: (array T n)`,
  /// `i: nat`, and `h: i < n`.
  Index(Box<Expr>, Rc<PureExpr>, Box<Expr>),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(Box<Expr>, u32),
  /// An deref operation `(* x): T` where `x: (& T)`.
  Deref(Box<Expr>),
  /// A ghost expression.
  Ghost(Box<Expr>),
  /// A truncation / bit cast operation.
  As(Box<(Expr, Type)>),
  /// A let binding.
  Let {
    /// A tuple pattern, containing variable bindings.
    lhs: TuplePattern,
    /// The expression to evaluate, or [`None`] for uninitialized.
    rhs: Box<Expr>,
  },
  /// A function call or intrinsic.
  Call {
    /// The function to call.
    f: Symbol,
    /// The span of the head of the function.
    fsp: Option<FileSpan>,
    /// The function arguments.
    args: Box<[Expr]>,
    /// The variant, if needed.
    variant: Option<Box<Expr>>,
  },
  // /// An entailment proof, which takes a proof of `P1 * ... * Pn => Q` and expressions proving
  // /// `P1, ..., Pn` and is a hypothesis of type `Q`.
  // Entail(LispVal, Box<[Expr]>),
  /// A block scope.
  Block(Box<[Expr]>),
  /// A label, which looks exactly like a local function but has no independent stack frame.
  /// They are called like regular functions but can only appear in tail position.
  Label {
    /// The name of the label
    name: Symbol,
    /// The arguments of the label
    args: Box<[TuplePattern]>,
    /// The variant, for recursive calls
    variant: Option<Variant>,
    /// The code that is executed when you jump to the label
    body: Box<[Expr]>,
  },
  // /// An if-then-else expression (at either block or statement level). The initial atom names
  // /// a hypothesis that the expression is true in one branch and false in the other.
  // If(Box<(Option<Symbol>, Expr, Expr, Expr)>),
  // /// A switch (pattern match) statement, given the initial expression and a list of match arms.
  // Switch(Box<Expr>, Box<[(Pattern, Expr)]>),
  /// A while loop.
  While {
    /// A hypothesis that the condition is true in the loop and false after it.
    hyp: Option<Symbol>,
    /// The loop condition.
    cond: Box<Expr>,
    /// The variant, which must decrease on every round around the loop.
    var: Option<Variant>,
    /// The body of the loop.
    body: Box<[Expr]>,
  },
  /// `(assert p)` evaluates `p: bool` and returns a proof of `p`.
  Assert(Rc<PureExpr>),
  // /// A hole `_`, which is a compile error but queries the compiler to provide a type context.
  // Hole(FileSpan),
}

/// A procedure kind, which defines the different kinds of function-like declarations.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ProcKind {
  /// A (pure) function, which generates a logic level function as well as code. (Body required.)
  Func,
  /// A procedure, which is opaque except for its type. (Body provided.)
  Proc,
  /// A precedure declaration, used for forward declarations. (Body not provided.)
  ProcDecl,
  /// An intrinsic declaration, which is only here to put the function declaration in user code.
  /// The compiler will ensure this matches an existing intrinsic, and intrinsics cannot be
  /// called until they are declared using an `intrinsic` declaration.
  Intrinsic,
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(ProcKind);

/// A procedure (or function or intrinsic), a top level item similar to function declarations in C.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Proc {
  /// The type of declaration: `func`, `proc`, `proc` with no body, or `intrinsic`.
  pub kind: ProcKind,
  /// The name of the procedure.
  pub name: Symbol,
  /// The span of the procedure name.
  pub span: Option<FileSpan>,
  /// The arguments of the procedure.
  pub args: (Vec<bool>, Vec<ast::TuplePattern>),
  /// The return values of the procedure. (Functions and procedures return multiple values in MMC.)
  pub rets: (Vec<Option<Symbol>>, Vec<ast::TuplePattern>),
  /// The variant, used for recursive functions.
  pub variant: Option<Variant>,
}

// impl Proc {
//   /// Checks if this proc equals `other`, ignoring the `kind` field.
//   /// (This is how we validate a proc against a proc decl.)
//   #[must_use] pub fn eq_decl(&self, other: &Proc) -> bool {
//     self.name == other.name &&
//     self.args == other.args &&
//     self.rets == other.rets &&
//     self.variant == other.variant
//   }
// }

/// A field of a struct.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Field {
  /// The name of the field.
  pub name: Symbol,
  /// True if the field is computationally irrelevant.
  pub ghost: bool,
  /// The type of the field (unparsed).
  pub ty: LispVal,
}

/// A top level program item. (A program AST is a list of program items.)
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum Ast {
  /// A procedure, behind an Arc so it can be cheaply copied.
  Proc(Arc<Proc>, Uncons),
  /// A global variable declaration.
  Global {
    /// The span of the `{x := ...}` in `(global {x := ...})`
    full: Option<FileSpan>,
    /// The variable(s) being declared
    lhs: ast::TuplePattern,
    /// The value of the declaration
    rhs: LispVal,
  },
  /// A constant declaration.
  Const {
    /// The span of the `{x := ...}` in `(const {x := ...})`
    full: Option<FileSpan>,
    /// The constant(s) being declared
    lhs: ast::TuplePattern,
    /// The value of the declaration
    rhs: LispVal,
  },
  /// A type definition.
  Typedef {
    /// The name of the newly declared type
    name: Symbol,
    /// The span of the name
    span: Option<FileSpan>,
    /// The arguments of the type declaration, for a parametric type
    args: Box<[ast::TuplePattern]>,
    /// The value of the declaration (another type)
    val: LispVal,
  },
  /// A structure definition.
  Struct {
    /// The name of the structure
    name: Symbol,
    /// The span of the name
    span: Option<FileSpan>,
    /// The parameters of the type
    args: Box<[ast::TuplePattern]>,
    /// The fields of the structure
    fields: Box<[ast::TuplePattern]>,
  },
}

impl Ast {
  /// Make a new `AST::Proc`.
  #[must_use] pub fn proc((p, body): (Proc, Uncons)) -> Ast { Ast::Proc(Arc::new(p), body) }
}

/// A "place", or lvalue, is a position in the context that can be read or written.
/// Expressions can evaluate to places, for example if `x: &sn y` then `*x` evaluates
/// to the place `y`.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum Place {
  /// A variable.
  Var(VarId),
  /// A projection into a tuple `a.i: T` where `a: (T0, ..., Tn)`.
  Proj(Box<Place>, u32),
  /// An index expression `a[i]: T` where `a: [T; n]` and `i: nat`.
  Index(Box<Place>, Rc<PureExpr>),
}

impl Place {
  /// Substitute an expression for a variable in a place.
  pub fn subst(&mut self, v: VarId, e: &Rc<PureExpr>) {
    match self {
      Self::Var(_) => {} // Substitution does not operate on lvalues
      Self::Proj(x, _) => x.subst(v, e),
      Self::Index(x, i) => {x.subst(v, e); PureExpr::subst_rc(i, v, e)}
    }
  }
}

impl EnvDisplay for Place {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use std::fmt::Display;
    match self {
      Place::Var(v) => v.fmt(f),
      Place::Index(a, i) => write!(f, "(index {} {})", fe.to(a), fe.to(i)),
      Place::Proj(a, i) => write!(f, "({} . {})", fe.to(a), i),
    }
  }
}

/// Pure expressions in an abstract domain. The interpretation depends on the type,
/// but most expressions operate on the type of (signed unbounded) integers.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum PureExpr {
  /// A variable.
  Var(VarId),
  /// An integer or natural number.
  Int(BigInt),
  /// The unit value `()`.
  Unit,
  /// A boolean literal.
  Bool(bool),
  /// A unary operation.
  Unop(Unop, Rc<PureExpr>),
  /// A binary operation.
  Binop(Binop, Rc<PureExpr>, Rc<PureExpr>),
  /// A tuple constructor.
  Tuple(Box<[PureExpr]>, Box<Type>),
  /// An index operation `a[i]: T` where `a: [T; n]` and `i: nat`.
  Index(Box<PureExpr>, Rc<PureExpr>),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(Box<PureExpr>, u32),
  /// A deref operation `*x: T` where `x: &sn e`.
  Deref(Box<PureExpr>),
  /// A ghost expression.
  Ghost(Rc<PureExpr>),
  /// A truncation / bit cast operation.
  As(Box<(PureExpr, Type)>),
  /// A truncation / bit cast operation.
  Pure(Box<(Mm0Expr<PureExpr>, Type)>),
  /// A deferred substitution into an expression.
  Subst(Rc<PureExpr>, VarId, Rc<PureExpr>),
}

impl PureExpr {
  /// Substitute an expression for a variable in a pure expression.
  pub fn subst_rc(self: &mut Rc<Self>, v: VarId, e: &Rc<PureExpr>) {
    *self = Rc::new(PureExpr::Subst(self.clone(), v, e.clone()))
  }
}

impl EnvDisplay for PureExpr {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use {std::fmt::Display, itertools::Itertools};
    match self {
      PureExpr::Var(v) => v.fmt(f),
      PureExpr::Int(n) => n.fmt(f),
      PureExpr::Unit => "()".fmt(f),
      PureExpr::Bool(b) => b.fmt(f),
      PureExpr::Unop(op, e) => write!(f, "({} {})", op, fe.to(e)),
      PureExpr::Binop(op, e1, e2) => write!(f, "{{{} {} {}}}", fe.to(e1), op, fe.to(e2)),
      PureExpr::Tuple(es, ty) => write!(f, "{{(list {}) : {}}}",
        es.iter().map(|e| fe.to(e)).format(" "), fe.to(ty)),
      PureExpr::Index(a, i) => write!(f, "(index {} {})", fe.to(a), fe.to(i)),
      PureExpr::Proj(a, i) => write!(f, "({} . {})", fe.to(a), i),
      PureExpr::Deref(e) => write!(f, "(* {})", fe.to(e)),
      PureExpr::Ghost(e) => write!(f, "(ghost {})", fe.to(e)),
      PureExpr::As(e) => write!(f, "{{{} as {}}}", fe.to(&e.0), fe.to(&e.1)),
      PureExpr::Pure(e) => write!(f, "{{(pure {}) : {}}}", fe.to(&e.0), fe.to(&e.1)),
      PureExpr::Subst(x, v, e) => write!(f, "({})[{} -> {}]", fe.to(x), v, fe.to(e)),
    }
  }
}

/// A type, which classifies regular variables (not type variables, not hypotheses).
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum Type {
  /// `()` is the type with one element; `sizeof () = 0`.
  Unit,
  /// `bool` is the type of booleans, that is, bytes which are 0 or 1; `sizeof bool = 1`.
  Bool,
  /// A type variable.
  Var(VarId),
  /// `i(8*N)` is the type of N byte signed integers `sizeof i(8*N) = N`.
  Int(Size),
  /// `u(8*N)` is the type of N byte unsigned integers; `sizeof u(8*N) = N`.
  UInt(Size),
  /// The type `[T; n]` is an array of `n` elements of type `T`;
  /// `sizeof [T; n] = sizeof T * n`.
  Array(Box<Type>, Rc<PureExpr>),
  /// `own T` is a type of owned pointers. The typehood predicate is
  /// `x :> own T` iff `E. v: T, x |-> v`.
  Own(Box<Type>),
  /// `& a T` is a type of shared pointers. The typehood predicate is
  /// `x :> &'a T` iff `E. v: ref a T, x = &v`.
  Shr(Lifetime, Box<Type>),
  /// `(ref T)` is a type of borrowed values. This type is elaborated to
  /// `(ref a T)` where `a` is a lifetime; this is handled a bit differently than rust
  /// (see [`Lifetime`]).
  Ref(Lifetime, Box<Type>),
  /// `&sn x` is the type of pointers to the place `x` (a variable or indexing expression).
  RefSn(Box<Place>),
  /// `(A, B, C)` is a tuple type with elements `A, B, C`;
  /// `sizeof (list A B C) = sizeof A + sizeof B + sizeof C`.
  List(Box<[Type]>),
  /// `(sn {a : T})` the type of values of type `T` that are equal to `a`.
  /// This is useful for asserting that a computationally relevant value can be
  /// expressed in terms of computationally irrelevant parts.
  Single(Rc<PureExpr>, Box<Type>),
  /// `{x : A, y : B, z : C}` is the dependent version of `list`;
  /// it is a tuple type with elements `A, B, C`, but the types `A, B, C` can
  /// themselves refer to `x, y, z`.
  /// `sizeof {x : A, _ : B x} = sizeof A + max_x (sizeof (B x))`.
  ///
  /// The top level declaration `(struct foo {x : A} {y : B})` desugars to
  /// `(typedef foo {x : A, y : B})`.
  Struct(Box<[(VarId, Type)]>),
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
  /// `(ghost A)` is a computationally irrelevant version of `A`, which means
  /// that the logical storage of `(ghost A)` is the same as `A` but the physical storage
  /// is the same as `()`. `sizeof (ghost A) = 0`.
  Ghost(Box<Type>),
  /// A propositional type, used for hypotheses.
  Prop(Box<Prop>),
  /// A user-defined type-former.
  User(Symbol, Box<[Type]>, Box<[Rc<PureExpr>]>),
  /// The input token.
  Input,
  /// The output token.
  Output,
  /// A moved-away type.
  Moved(Box<Type>),
  /// A substitution into a type.
  Subst(Box<Type>, VarId, Rc<PureExpr>),
}

impl Type {
  /// Create a ghost node if the boolean is true.
  #[must_use] pub fn ghost_if(ghost: bool, this: Type) -> Type {
    if ghost { Type::Ghost(Box::new(this)) } else { this }
  }

  /// Substitute an expression for a variable in a type.
  pub fn subst(&mut self, v: VarId, e: &Rc<PureExpr>) {
    #[allow(clippy::enum_glob_use)] use Type::*;
    match self {
      Var(_) | Unit | Bool | Int(_) | UInt(_) | Input | Output => {}
      Array(ty, n) => { ty.subst(v, e); PureExpr::subst_rc(n, v, e) }
      Own(ty) | Ghost(ty) | Moved(ty) | Ref(_, ty) | Shr(_, ty) => ty.subst(v, e),
      RefSn(x) => x.subst(v, e),
      List(tys) | And(tys) | Or(tys) => for ty in &mut **tys { ty.subst(v, e) },
      Single(a, ty) => { PureExpr::subst_rc(a, v, e); ty.subst(v, e) }
      Struct(tys) => for ty in &mut **tys { ty.1.subst(v, e) },
      User(_, tys, es) => {
        for ty in &mut **tys { ty.subst(v, e) }
        for ei in &mut **es { PureExpr::subst_rc(ei, v, e) }
      }
      Prop(pr) => pr.subst(v, e),
      Subst(_,_,_) => *self = Type::Subst(Box::new(std::mem::replace(self, Type::Unit)), v, e.clone()),
    }
  }
}

impl EnvDisplay for Type {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use {std::fmt::Display, itertools::Itertools};
    match self {
      Type::Var(v) => v.fmt(f),
      Type::Unit => "()".fmt(f),
      Type::Bool => "bool".fmt(f),
      Type::Int(Size::S8) => "i8".fmt(f),
      Type::Int(Size::S16) => "i16".fmt(f),
      Type::Int(Size::S32) => "i32".fmt(f),
      Type::Int(Size::S64) => "i64".fmt(f),
      Type::Int(Size::Inf) => "int".fmt(f),
      Type::UInt(Size::S8) => "u8".fmt(f),
      Type::UInt(Size::S16) => "u16".fmt(f),
      Type::UInt(Size::S32) => "u32".fmt(f),
      Type::UInt(Size::S64) => "u64".fmt(f),
      Type::UInt(Size::Inf) => "nat".fmt(f),
      Type::Array(ty, n) => write!(f, "(array {} {})", fe.to(ty), fe.to(n)),
      Type::Own(ty) => write!(f, "(own {})", fe.to(ty)),
      Type::Ref(lft, ty) => write!(f, "(ref {} {})", lft, fe.to(ty)),
      Type::Shr(lft, ty) => write!(f, "(& {} {})", lft, fe.to(ty)),
      Type::RefSn(x) => write!(f, "(&sn {})", fe.to(x)),
      Type::List(tys) => write!(f, "(list {})", tys.iter().map(|ty| fe.to(ty)).format(" ")),
      Type::Single(e, ty) => write!(f, "(sn {{{}: {}}})", fe.to(e), fe.to(ty)),
      Type::Struct(tys) => {
        write!(f, "(struct")?;
        for (a, ty) in &**tys { write!(f, " {{{}: {}}}", a, fe.to(ty))? }
        ")".fmt(f)
      }
      Type::And(tys) => write!(f, "(and {})", tys.iter().map(|ty| fe.to(ty)).format(" ")),
      Type::Or(tys) => write!(f, "(or {})", tys.iter().map(|ty| fe.to(ty)).format(" ")),
      Type::Ghost(ty) => write!(f, "(ghost {})", fe.to(ty)),
      Type::Prop(p) => write!(f, "$ {} $", fe.to(p)),
      Type::User(name, tys, es) => {
        write!(f, "({}", fe.to(name))?;
        for ty in &**tys { " ".fmt(f)?; ty.fmt(fe, f)? }
        for e in &**es { " ".fmt(f)?; e.fmt(fe, f)? }
        ")".fmt(f)
      }
      Type::Input => "Input".fmt(f),
      Type::Output => "Output".fmt(f),
      Type::Moved(ty) => write!(f, "|{}|", fe.to(ty)),
      Type::Subst(ty, v, e) => write!(f, "({})[{} -> {}]", fe.to(ty), v, fe.to(e)),
    }
  }
}

/// A separating proposition, which classifies hypotheses / proof terms.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum Prop {
  // /// An unresolved metavariable.
  // MVar(usize),
  /// A true proposition.
  True,
  /// A false proposition.
  False,
  /// A universally quantified proposition.
  All(VarId, Box<(Type, Prop)>),
  /// An existentially quantified proposition.
  Ex(VarId, Box<(Type, Prop)>),
  /// Implication (plain, non-separating).
  Imp(Box<(Prop, Prop)>),
  /// Negation.
  Not(Box<Prop>),
  /// Conjunction (non-separating).
  And(Box<[Prop]>),
  /// Disjunction.
  Or(Box<[Prop]>),
  /// The empty heap.
  Emp,
  /// Separating conjunction.
  Sep(Box<[Prop]>),
  /// Separating implication.
  Wand(Box<(Prop, Prop)>),
  /// An (executable) boolean expression, interpreted as a pure proposition
  Pure(Rc<PureExpr>),
  /// Equality (possibly non-decidable).
  Eq(Rc<PureExpr>, Rc<PureExpr>),
  /// A heap assertion `l |-> (v: T)`.
  Heap(Rc<PureExpr>, Rc<PureExpr>, Box<Type>),
  /// An explicit typing assertion `[v : T]`.
  HasTy(Rc<PureExpr>, Box<Type>),
  /// The move operator `|T|` on types.
  Moved(Box<Prop>),
  /// An embedded MM0 proposition of sort `wff`.
  Mm0(Mm0Expr<PureExpr>),
  /// A substitution into a proposition.
  Subst(Box<Prop>, VarId, Rc<PureExpr>),
}

impl Prop {
  /// Substitute an expression for a variable in a proposition.
  pub fn subst(&mut self, v: VarId, e: &Rc<PureExpr>) {
    #[allow(clippy::enum_glob_use)] use Prop::*;
    match self {
      True | False | Emp => {}
      Imp(p) | Wand(p) => {p.0.subst(v, e); p.1.subst(v, e)}
      Not(p) | Moved(p) => p.subst(v, e),
      And(prs) | Or(prs) | Sep(prs) => for pr in &mut **prs { pr.subst(v, e) },
      Pure(a) => PureExpr::subst_rc(a, v, e),
      Eq(a, b) => {PureExpr::subst_rc(a, v, e); PureExpr::subst_rc(b, v, e)}
      Heap(a, b, ty) => {PureExpr::subst_rc(a, v, e); PureExpr::subst_rc(b, v, e); ty.subst(v, e)}
      _ => *self = Prop::Subst(Box::new(std::mem::replace(self, Prop::Emp)), v, e.clone()),
    }
  }
}

impl EnvDisplay for Prop {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use {std::fmt::Display, itertools::Itertools};
    match self {
      // &Prop::MVar(n) => LispKind::MVar(n, InferTarget::Unknown).fmt(fe, f),
      Prop::True => "true".fmt(f),
      Prop::False => "false".fmt(f),
      Prop::All(a, pr) => write!(f, "A. {}: {}, {}", a, fe.to(&pr.0), fe.to(&pr.1)),
      Prop::Ex(a, pr) => write!(f, "E. {}: {}, {}", a, fe.to(&pr.0), fe.to(&pr.1)),
      Prop::Imp(pr) => write!(f, "({} -> {})", fe.to(&pr.0), fe.to(&pr.1)),
      Prop::Not(pr) => write!(f, "~{}", fe.to(pr)),
      Prop::And(pr) if pr.is_empty() => "true".fmt(f),
      Prop::And(pr) => write!(f, "({})", pr.iter().map(|p| fe.to(p)).format(" /\\ ")),
      Prop::Or(pr) if pr.is_empty() => "false".fmt(f),
      Prop::Or(pr) => write!(f, "({})", pr.iter().map(|p| fe.to(p)).format(" \\/ ")),
      Prop::Emp => "emp".fmt(f),
      Prop::Sep(pr) if pr.is_empty() => "emp".fmt(f),
      Prop::Sep(pr) => write!(f, "({})", pr.iter().map(|p| fe.to(p)).format(" * ")),
      Prop::Wand(pr) => write!(f, "({} -* {})", fe.to(&pr.0), fe.to(&pr.1)),
      Prop::Pure(e) => e.fmt(fe, f),
      Prop::Eq(e1, e2) => write!(f, "{} = {}", fe.to(e1), fe.to(e2)),
      Prop::Heap(x, v, t) => write!(f, "{} => {}: {}", fe.to(x), fe.to(v), fe.to(t)),
      Prop::HasTy(v, t) => write!(f, "[{}: {}]", fe.to(v), fe.to(t)),
      Prop::Moved(p) => write!(f, "|{}|", fe.to(p)),
      Prop::Mm0(e) => e.fmt(fe, f),
      Prop::Subst(x, v, e) => write!(f, "({})[{} -> {}]", fe.to(x), v, fe.to(e)),
    }
  }
}

