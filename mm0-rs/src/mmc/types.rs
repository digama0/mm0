//! Types used in the rest of the compiler.
use std::sync::Arc;
use std::{rc::Rc, collections::HashMap};
use num::BigInt;
use crate::util::FileSpan;
use crate::elab::{environment::{AtomID, Environment},
  lisp::{LispKind, InferTarget, LispVal, Uncons, print::{EnvDisplay, FormatEnv}}};

// /// An argument to a function.
// #[derive(Debug, DeepSizeOf)]
// pub struct Arg {
//   /// The name of the argument, if not `_`.
//   pub name: Option<(AtomID, FileSpan)>,
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
#[derive(PartialEq, Eq, Debug, DeepSizeOf)]
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

/// An invariant is a local variable in a loop, that is passed as an argument
/// on recursive calls.
#[derive(Debug, DeepSizeOf)]
pub struct Invariant {
  /// The variable name.
  pub name: AtomID,
  /// True if the variable is ghost (computationally irrelevant).
  pub ghost: bool,
  /// The type of the variable, or none for inferred.
  pub ty: Option<LispVal>,
  /// The initial value of the variable.
  pub val: Option<LispVal>,
}

/// A tuple pattern, which destructures the results of assignments from functions with
/// mutiple return values, as well as explicit tuple values and structs.
#[derive(Debug, DeepSizeOf)]
pub enum TuplePattern {
  /// A variable binding, or `_` for an ignored binding. The `bool` is true if the variable
  /// is ghost.
  Name(bool, AtomID, Option<FileSpan>),
  /// A type ascription.
  Typed(Box<(TuplePattern, Type)>),
  /// A tuple, with the given arguments.
  Tuple(Box<[TuplePattern]>, Option<FileSpan>),
}
/// A strongly typed tuple pattern.
#[derive(Debug, DeepSizeOf)]
pub enum TypedTuplePattern {
  /// A variable binding. The `bool` is true if the variable is ghost.
  Name(bool, AtomID, Option<FileSpan>, Box<Type>),
  /// A unit pattern match.
  Unit,
  /// A singleton pattern match `(x h) := sn e`, where `x: T` and `h: x = e`.
  Single(Box<(TypedTuplePattern, TypedTuplePattern)>),
}

impl TypedTuplePattern {
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
}

/// A pattern, the left side of a switch statement.
#[derive(Debug, DeepSizeOf)]
pub enum Pattern {
  /// A variable binding, unless this is the name of a constant in which case
  /// it is a constant value.
  VarOrConst(AtomID),
  /// A numeric literal.
  Number(BigInt),
  /// A hypothesis pattern, which binds the first argument to a proof that the
  /// scrutinee satisfies the pattern argument.
  Hyped(AtomID, Box<Pattern>),
  /// A pattern guard: Matches the inner pattern, and then if the expression returns
  /// true, this is also considered to match.
  With(Box<(Pattern, LispVal)>),
  /// A disjunction of patterns.
  Or(Box<[Pattern]>),
}

/// An expression or statement. A block is a list of expressions.
#[derive(Debug, DeepSizeOf)]
pub enum Expr {
  /// A pure expression.
  Pure(PureExpr),
  /// A variable move expression. Unlike `Pure(Var(v))`, this will take the value in `v`,
  /// leaving it moved out.
  Var(AtomID),
  /// A unary operation.
  Unop(Unop, Box<Expr>),
  /// A binary operation.
  Binop(Binop, Box<Expr>, Box<Expr>),
  /// A tuple constructor.
  Tuple(Box<[Expr]>),
  /// An index operation `(index a i h): T` where `a: (array T n)`,
  /// `i: nat`, and `h: i < n`.
  Index(Box<Expr>, Box<Expr>, Box<ProofExpr>),
  /// An deref operation `(* x): T` where `x: (own T)`.
  DerefOwn(Box<Expr>),
  /// An deref operation `(* x): T` where `x: (& T)`.
  Deref(Box<Expr>),
  /// An deref operation `(* x): T` where `x: (&mut T)`.
  DerefMut(Box<Expr>),
  /// A ghost expression.
  Ghost(Box<Expr>),
  /// A let binding.
  Let {
    /// A tuple pattern, containing variable bindings.
    lhs: TypedTuplePattern,
    /// The expression to evaluate, or [`None`] for uninitialized.
    rhs: Option<Box<Expr>>,
  },
  // /// A function call (or something that looks like one at parse time).
  // Call {
  //   /// The function to call.
  //   f: AtomID,
  //   /// The function arguments.
  //   args: Box<[Expr]>,
  //   /// The variant, if needed.
  //   variant: Option<Variant>,
  // },
  // /// An entailment proof, which takes a proof of `P1 * ... * Pn => Q` and expressions proving
  // /// `P1, ..., Pn` and is a hypothesis of type `Q`.
  // Entail(LispVal, Box<[Expr]>),
  /// A block scope.
  Block(Box<[Expr]>),
  /// A label, which looks exactly like a local function but has no independent stack frame.
  /// They are called like regular functions but can only appear in tail position.
  Label {
    /// The name of the label
    name: AtomID,
    /// The arguments of the label
    args: Box<[TuplePattern]>,
    /// The variant, for recursive calls
    variant: Option<Variant>,
    /// The code that is executed when you jump to the label
    body: Box<[Expr]>,
  },
  // /// An if-then-else expression (at either block or statement level). The initial atom names
  // /// a hypothesis that the expression is true in one branch and false in the other.
  // If(Box<(Option<AtomID>, Expr, Expr, Expr)>),
  // /// A switch (pattern match) statement, given the initial expression and a list of match arms.
  // Switch(Box<Expr>, Box<[(Pattern, Expr)]>),
  /// A while loop.
  While {
    /// A hypothesis that the condition is true in the loop and false after it.
    hyp: Option<AtomID>,
    /// The loop condition.
    cond: Box<Expr>,
    /// The variant, which must decrease on every round around the loop.
    var: Option<Variant>,
    /// The invariants, which must be supplied on every round around the loop.
    invar: Box<[Invariant]>,
    /// The body of the loop.
    body: Box<[Expr]>,
  },
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
crate::deep_size_0!(ProcKind);

/// A procedure (or function or intrinsic), a top level item similar to function declarations in C.
#[derive(Debug, DeepSizeOf)]
pub struct Proc {
  /// The type of declaration: `func`, `proc`, `proc` with no body, or `intrinsic`.
  pub kind: ProcKind,
  /// The name of the procedure.
  pub name: AtomID,
  /// The span of the procedure name.
  pub span: Option<FileSpan>,
  /// The arguments of the procedure.
  pub args: Box<[super::parser::TuplePattern]>,
  /// The return values of the procedure. (Functions and procedures return multiple values in MMC.)
  pub rets: Box<[super::parser::TuplePattern]>,
  /// The variant, used for recursive functions.
  pub variant: Option<Variant>,
  /// The body of the procedure.
  pub muts: Box<[(AtomID, Option<FileSpan>)]>,
}

impl Proc {
  /// Checks if this proc equals `other`, ignoring the `body` and `kind` fields.
  /// (This is how we validate a proc against a proc decl.)
  #[must_use] pub fn eq_decl(&self, other: &Proc) -> bool {
    self.name == other.name &&
    self.args == other.args &&
    self.rets == other.rets &&
    self.variant == other.variant &&
    self.muts == other.muts
  }
}

/// A field of a struct.
#[derive(Debug, DeepSizeOf)]
pub struct Field {
  /// The name of the field.
  pub name: AtomID,
  /// True if the field is computationally irrelevant.
  pub ghost: bool,
  /// The type of the field (unparsed).
  pub ty: LispVal,
}

/// A top level program item. (A program AST is a list of program items.)
#[derive(Debug, DeepSizeOf)]
pub enum AST {
  /// A procedure, behind an Arc so it can be cheaply copied.
  Proc(Arc<Proc>, Uncons),
  /// A global variable declaration.
  Global {
    /// The variable(s) being declared
    lhs: super::parser::TuplePattern,
    /// The value of the declaration
    rhs: Option<LispVal>,
  },
  /// A constant declaration.
  Const {
    /// The constant(s) being declared
    lhs: super::parser::TuplePattern,
    /// The value of the declaration
    rhs: LispVal,
  },
  /// A type definition.
  Typedef {
    /// The name of the newly declared type
    name: AtomID,
    /// The span of the name
    span: Option<FileSpan>,
    /// The arguments of the type declaration, for a parametric type
    args: Box<[super::parser::TuplePattern]>,
    /// The value of the declaration (another type)
    val: LispVal,
  },
  /// A structure definition.
  Struct {
    /// The name of the structure
    name: AtomID,
    /// The span of the name
    span: Option<FileSpan>,
    /// The parameters of the type
    args: Box<[super::parser::TuplePattern]>,
    /// The fields of the structure
    fields: Box<[super::parser::TuplePattern]>,
  },
}

impl AST {
  /// Make a new `AST::Proc`.
  #[must_use] pub fn proc((p, body): (Proc, Uncons)) -> AST { AST::Proc(Arc::new(p), body) }
}

macro_rules! make_keywords {
  {$($(#[$attr:meta])* $x:ident: $e:expr,)*} => {
    make_keywords! {@IMPL $($(#[$attr])* $x concat!("The keyword `", $e, "`.\n"), $e,)*}
  };
  {@IMPL $($(#[$attr:meta])* $x:ident $doc0:expr, $e:expr,)*} => {
    /// The type of MMC keywords, which are atoms with a special role in the MMC parser.
    #[derive(Debug, PartialEq, Eq, Copy, Clone)]
    pub enum Keyword { $(#[doc=$doc0] $(#[$attr])* $x),* }
    crate::deep_size_0!(Keyword);

    impl Environment {
      /// Make the initial MMC keyword map in the given environment.
      #[allow(clippy::string_lit_as_bytes)]
      pub fn make_keywords(&mut self) -> HashMap<AtomID, Keyword> {
        let mut atoms = HashMap::new();
        $(atoms.insert(self.get_atom($e.as_bytes()), Keyword::$x);)*
        atoms
      }
    }
  }
}

make_keywords! {
  Add: "+",
  Arrow: "=>",
  Begin: "begin",
  Colon: ":",
  ColonEq: ":=",
  Const: "const",
  Else: "else",
  Entail: "entail",
  Func: "func",
  Finish: "finish",
  Ghost: "ghost",
  Global: "global",
  Intrinsic: "intrinsic",
  Invariant: "invariant",
  If: "if",
  Le: "<=",
  Lt: "<",
  Mut: "mut",
  Or: "or",
  Proc: "proc",
  Star: "*",
  Struct: "struct",
  Switch: "switch",
  Typedef: "typedef",
  Variant: "variant",
  While: "while",
  With: "with",
}

/// Possible sizes for integer operations and types.
#[derive(Copy, Clone, Debug)]
pub enum Size {
  /// 8 bits, or 1 byte. Used for `u8` and `i8`.
  S8,
  /// 16 bits, or 2 bytes. Used for `u16` and `i16`.
  S16,
  /// 32 bits, or 4 bytes. Used for `u32` and `i32`.
  S32,
  /// 64 bits, or 8 bytes. Used for `u64` and `i64`.
  S64,
  /// Unbounded size. Used for `nat` and `int`. (These types are only legal for
  /// ghost variables, but they are also used to indicate "correct to an unbounded model"
  /// for operations like [`Unop::BitNot`] when it makes sense. We do not actually support
  /// bignum compilation.)
  Inf,
}
crate::deep_size_0!(Size);

/// (Elaborated) unary operations.
#[derive(Copy, Clone, Debug)]
pub enum Unop {
  /// Logical (boolean) NOT
  Not,
  /// Bitwise NOT. For fixed size this is the operation `2^n - x - 1`, and
  /// for infinite size this is `-x - 1`. Note that signed NOT
  BitNot(Size),
}
crate::deep_size_0!(Unop);

impl Unop {
  /// Return a string representation of the [`Unop`].
  #[must_use] pub fn to_str(self) -> &'static str {
    match self {
      Unop::Not => "not",
      Unop::BitNot(_) => "bnot",
    }
  }
}

impl std::fmt::Display for Unop {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.to_str().fmt(f)
  }
}

/// (Elaborated) binary operations.
#[derive(Copy, Clone, Debug)]
pub enum Binop {
  /// Integer addition
  Add,
  /// Integer multiplication
  Mul,
  /// Integer subtraction
  Sub,
  /// Logical (boolean) AND
  And,
  /// Logical (boolean) OR
  Or,
  /// Bitwise AND, for signed or unsigned integers of any size
  BitAnd,
  /// Bitwise OR, for signed or unsigned integers of any size
  BitOr,
  /// Bitwise XOR, for signed or unsigned integers of any size
  BitXor,
  /// Less than, for signed or unsigned integers of any size
  Lt,
  /// Less than or equal, for signed or unsigned integers of any size
  Le,
  /// Equal, for signed or unsigned integers of any size
  Eq,
  /// Not equal, for signed or unsigned integers of any size
  Ne,
}
crate::deep_size_0!(Binop);

impl Binop {
  /// Return a string representation of the [`Binop`].
  #[must_use] pub fn to_str(self) -> &'static str {
    match self {
      Binop::Add => "+",
      Binop::Mul => "*",
      Binop::Sub => "-",
      Binop::And => "and",
      Binop::Or => "or",
      Binop::BitAnd => "band",
      Binop::BitOr => "bor",
      Binop::BitXor => "bxor",
      Binop::Lt => "<",
      Binop::Le => "<=",
      Binop::Eq => "=",
      Binop::Ne => "!=",
    }
  }
}

impl std::fmt::Display for Binop {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.to_str().fmt(f)
  }
}

/// A proof expression, or "hypothesis".
#[derive(Debug, DeepSizeOf)]
pub enum ProofExpr {
  /// An assertion expression `(assert p): p`.
  Assert(Box<PureExpr>),
}

/// Pure expressions in an abstract domain. The interpretation depends on the type,
/// but most expressions operate on the type of (signed unbounded) integers.
#[derive(Debug, DeepSizeOf)]
pub enum PureExpr {
  /// A variable.
  Var(AtomID),
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
  Tuple(Box<[PureExpr]>),
  /// An index operation `(index a i h): T` where `a: (array T n)`,
  /// `i: nat`, and `h: i < n`.
  Index(Box<PureExpr>, Rc<PureExpr>, Box<ProofExpr>),
  /// An deref operation `(* x): T` where `x: (own T)`.
  DerefOwn(Box<PureExpr>),
  /// An deref operation `(* x): T` where `x: (& T)`.
  Deref(Box<PureExpr>),
  /// An deref operation `(* x): T` where `x: (&mut T)`.
  DerefMut(Box<PureExpr>),
  /// A ghost expression.
  Ghost(Rc<PureExpr>),
}

impl EnvDisplay for PureExpr {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use {std::fmt::Display, itertools::Itertools};
    match self {
      &PureExpr::Var(v) => v.fmt(fe, f),
      PureExpr::Int(n) => n.fmt(f),
      PureExpr::Unit => "()".fmt(f),
      PureExpr::Bool(b) => b.fmt(f),
      PureExpr::Unop(op, e) => write!(f, "({} {})", op, fe.to(e)),
      PureExpr::Binop(op, e1, e2) => write!(f, "{{{} {} {}}}", fe.to(e1), op, fe.to(e2)),
      PureExpr::Tuple(es) => write!(f, "(list {})", es.iter().map(|e| fe.to(e)).format(" ")),
      PureExpr::Index(a, i, _) => write!(f, "(index {} {})", fe.to(a), fe.to(i)),
      PureExpr::DerefOwn(e) |
      PureExpr::Deref(e) |
      PureExpr::DerefMut(e) => write!(f, "(* {})", fe.to(e)),
      PureExpr::Ghost(e) => write!(f, "(ghost {})", fe.to(e)),
    }
  }
}


/// A type, which classifies regular variables (not type variables, not hypotheses).
#[derive(Clone, Debug, DeepSizeOf)]
pub enum Type {
  /// A type variable.
  Var(AtomID),
  /// `()` is the type with one element; `sizeof () = 0`.
  Unit,
  /// `bool` is the type of booleans, that is, bytes which are 0 or 1; `sizeof bool = 1`.
  Bool,
  /// `i(8*N)` is the type of N byte signed integers `sizeof i(8*N) = N`.
  Int(Size),
  /// `u(8*N)` is the type of N byte unsigned integers; `sizeof u(8*N) = N`.
  UInt(Size),
  /// The type `(array T n)` is an array of `n` elements of type `T`;
  /// `sizeof (array T n) = sizeof T * n`.
  Array(Box<Type>, Rc<PureExpr>),
  /// `(own T)` is a type of owned pointers. The typehood predicate is
  /// `x :> own T` iff `E. v (x |-> v) * v :> T`.
  Own(Box<Type>),
  /// `(& T)` is a type of borrowed pointers. This type is treated specially;
  /// the `x |-> v` assumption is stored separately from regular types, and
  /// `(* x)` is treated as sugar for `v`.
  Ref(Box<Type>),
  /// `(&mut T)` is a type of mutable pointers. This is also treated specially;
  /// it is sugar for `(mut {x : (own T)})`, which is to say `x` has
  /// type `own T` in the function but must also be passed back out of the
  /// function.
  RefMut(Box<Type>),
  /// `(list A B C)` is a tuple type with elements `A, B, C`;
  /// `sizeof (list A B C) = sizeof A + sizeof B + sizeof C`.
  List(Box<[Type]>),
  /// `(sn {a : T})` the type of values of type `T` that are equal to `a`.
  /// This is useful for asserting that a computationally relevant value can be
  /// expressed in terms of computationally irrelevant parts.
  Single(Rc<PureExpr>, Box<Type>),
  /// `(struct {x : A} {y : B} {z : C})` is the dependent version of `list`;
  /// it is a tuple type with elements `A, B, C`, but the types `A, B, C` can
  /// themselves refer to `x, y, z`.
  /// `sizeof (struct {x : A} {_ : B x}) = sizeof A + max_x (sizeof (B x))`.
  ///
  /// The top level declaration `(struct foo {x : A} {y : B})` desugars to
  /// `(typedef foo (struct {x : A} {y : B}))`.
  Struct(Box<[(AtomID, Type)]>),
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
  User(AtomID, Box<[Type]>, Rc<[PureExpr]>),
  /// The input token.
  Input,
  /// The output token.
  Output,
  /// A moved-away type.
  Moved(Box<Type>),
}

impl Type {
  /// Create a ghost node if the boolean is true.
  #[must_use] pub fn ghost_if(ghost: bool, this: Type) -> Type {
    if ghost { Type::Ghost(Box::new(this)) } else { this }
  }
}

impl EnvDisplay for Type {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use {std::fmt::Display, itertools::Itertools};
    match self {
      Type::Var(v) => v.fmt(fe, f),
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
      Type::Ref(ty) => write!(f, "(& {})", fe.to(ty)),
      Type::RefMut(ty) => write!(f, "(&mut {})", fe.to(ty)),
      Type::List(tys) => write!(f, "(list {})", tys.iter().map(|ty| fe.to(ty)).format(" ")),
      Type::Single(e, ty) => write!(f, "(sn {{{}: {}}})", fe.to(e), fe.to(ty)),
      Type::Struct(tys) => {
        write!(f, "(struct")?;
        for (a, ty) in &**tys { write!(f, " {{{}: {}}}", fe.to(a), fe.to(ty))? }
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
    }
  }
}

/// A separating proposition, which classifies hypotheses / proof terms.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum Prop {
  /// An unresolved metavariable.
  MVar(usize),
  /// A true proposition.
  True,
  /// A false proposition.
  False,
  /// A universally quantified proposition.
  All(AtomID, Box<(Type, Prop)>),
  /// An existentially quantified proposition.
  Ex(AtomID, Box<(Type, Prop)>),
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
  MM0(LispVal),
}

impl EnvDisplay for Prop {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use {std::fmt::Display, itertools::Itertools};
    match self {
      &Prop::MVar(n) => LispKind::MVar(n, InferTarget::Unknown).fmt(fe, f),
      Prop::True => "true".fmt(f),
      Prop::False => "false".fmt(f),
      Prop::All(a, pr) => write!(f, "A. {}: {}, {}", fe.to(a), fe.to(&pr.0), fe.to(&pr.1)),
      Prop::Ex(a, pr) => write!(f, "E. {}: {}, {}", fe.to(a), fe.to(&pr.0), fe.to(&pr.1)),
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
      Prop::MM0(e) => e.fmt(fe, f),
    }
  }
}

