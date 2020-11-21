//! Types used in the rest of the compiler.
use std::sync::Arc;
use std::{rc::Rc, collections::HashMap};
use num::BigInt;
use crate::util::FileSpan;
use crate::elab::{environment::{AtomID, Environment},
  lisp::{LispVal, Uncons}};

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

/// A block is a local scope. Like functions, this requires explicit importing
/// of variables from external scope if they will be mutated after the block.
#[derive(Debug, DeepSizeOf)]
pub struct Block {
  /// The list of variables that will be updated by the block. Variables
  /// in external scope that are not in this list are treated as read only.
  pub muts: Box<[(AtomID, Option<FileSpan>)]>,
  /// The statements of the block.
  pub stmts: Uncons
}

/// A tuple pattern, which destructures the results of assignments from functions with
/// mutiple return values, as well as explicit tuple values and structs.
#[derive(Debug, DeepSizeOf)]
pub enum TuplePattern {
  /// A variable binding, or `_` for an ignored binding. The `bool` is true if the variable
  /// is ghost.
  Name(bool, AtomID, Option<FileSpan>),
  /// A type ascription. The type is unparsed.
  Typed(Box<TuplePattern>, LispVal),
  /// A tuple, with the given arguments.
  Tuple(Box<[TuplePattern]>),
}

impl TuplePattern {
  /// The `_` tuple pattern. This is marked as ghost because it can't be referred to so
  /// it is always safe to make irrelevant.
  pub const UNDER: TuplePattern = TuplePattern::Name(true, AtomID::UNDER, None);

  /// The name of a variable binding (or `_` for a tuple pattern)
  #[must_use] pub fn name(&self) -> AtomID {
    match self {
      &TuplePattern::Name(_, a, _) => a,
      TuplePattern::Typed(p, _) => p.name(),
      _ => AtomID::UNDER
    }
  }

  /// The span of a variable binding (or `None` for a tuple pattern).
  #[must_use] pub fn fspan(&self) -> Option<&FileSpan> {
    match self {
      TuplePattern::Name(_, _, fsp) => fsp.as_ref(),
      TuplePattern::Typed(p, _) => p.fspan(),
      _ => None
    }
  }

  /// True if all the bindings in this pattern are ghost.
  #[must_use] pub fn ghost(&self) -> bool {
    match self {
      &TuplePattern::Name(g, _, _) => g,
      TuplePattern::Typed(p, _) => p.ghost(),
      TuplePattern::Tuple(ps) => ps.iter().all(TuplePattern::ghost),
    }
  }

  /// The type of this binding, or `_` if there is no explicit type.
  #[must_use] pub fn ty(&self) -> LispVal {
    match self {
      TuplePattern::Typed(_, ty) => ty.clone(),
      _ => LispVal::atom(AtomID::UNDER)
    }
  }
}

impl PartialEq<TuplePattern> for TuplePattern {
  fn eq(&self, other: &TuplePattern) -> bool {
    match (self, other) {
      (TuplePattern::Name(g1, a1, _), TuplePattern::Name(g2, a2, _)) => g1 == g2 && a1 == a2,
      (TuplePattern::Typed(p1, ty1), TuplePattern::Typed(p2, ty2)) => p1 == p2 && ty1 == ty2,
      (TuplePattern::Tuple(ps1), TuplePattern::Tuple(ps2)) => ps1 == ps2,
      _ => false
    }
  }
}
impl Eq for TuplePattern {}

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
  /// A `()` literal.
  Nil,
  /// A variable reference.
  Var(AtomID),
  /// A number literal.
  Number(BigInt),
  /// A let binding.
  Let {
    /// True if the `rhs` expression should not be evaluated,
    /// and all variables in the declaration should be considered ghost.
    ghost: bool,
    /// A tuple pattern, containing variable bindings.
    lhs: TuplePattern,
    /// The expression to evaluate, or `None` for uninitialized.
    rhs: Option<Box<Expr>>,
  },
  /// A function call (or something that looks like one at parse time).
  Call {
    /// The function to call.
    f: AtomID,
    /// The function arguments.
    args: Box<[Expr]>,
    /// The variant, if needed.
    variant: Option<Variant>,
  },
  /// An entailment proof, which takes a proof of `P1 * ... * Pn => Q` and expressions proving
  /// `P1, ..., Pn` and is a hypothesis of type `Q`.
  Entail(LispVal, Box<[Expr]>),
  /// A block scope.
  Block(Block),
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
    body: Block,
  },
  /// An if-then-else expression (at either block or statement level). The initial atom names
  /// a hypothesis that the expression is true in one branch and false in the other.
  If(Box<(Option<AtomID>, Expr, Expr, Expr)>),
  /// A switch (pattern match) statement, given the initial expression and a list of match arms.
  Switch(Box<Expr>, Box<[(Pattern, Expr)]>),
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
    body: Block,
  },
  /// A hole `_`, which is a compile error but queries the compiler to provide a type context.
  Hole(FileSpan),
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
  pub args: Box<[TuplePattern]>,
  /// The return values of the procedure. (Functions and procedures return multiple values in MMC.)
  pub rets: Box<[TuplePattern]>,
  /// The variant, used for recursive functions.
  pub variant: Option<Variant>,
  /// The body of the procedure.
  pub body: Block,
}

impl Proc {
  /// Checks if this proc equals `other`, ignoring the `body` and `kind` fields.
  /// (This is how we validate a proc against a proc decl.)
  #[must_use] pub fn eq_decl(&self, other: &Proc) -> bool {
    self.name == other.name &&
    self.args == other.args &&
    self.rets == other.rets &&
    self.variant == other.variant &&
    self.body.muts == other.body.muts
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
  Proc(Arc<Proc>),
  /// A global variable declaration.
  Global {
    /// The variable(s) being declared
    lhs: TuplePattern,
    /// The value of the declaration
    rhs: Option<LispVal>,
  },
  /// A constant declaration.
  Const {
    /// The constant(s) being declared
    lhs: TuplePattern,
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
    args: Box<[TuplePattern]>,
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
    args: Box<[TuplePattern]>,
    /// The fields of the structure
    fields: Box<[TuplePattern]>,
  },
}

impl AST {
  /// Make a new `AST::Proc`.
  #[must_use] pub fn proc(p: Proc) -> AST { AST::Proc(Arc::new(p)) }
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
  /// for operations like `Unop::BitNot` when it makes sense. We do not actually support
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

/// (Elaborated) binary operations.
#[derive(Copy, Clone, Debug)]
pub enum Binop {
  /// Integer addition
  Add,
  /// Integer multiplication
  Mul,
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

/// A type, which classifies regular variables (not type variables, not hypotheses).
#[derive(Debug, DeepSizeOf)]
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
  /// `(struct {x : A} {y : B} {z : C})` is the dependent version of `list`;
  /// it is a tuple type with elements `A, B, C`, but the types `A, B, C` can
  /// themselves refer to `x, y, z`.
  /// `sizeof (struct {x : A} {_ : B x}) = sizeof A + max_x (sizeof (B x))`.
  ///
  /// The top level declaration `(struct foo {x : A} {y : B})` desugars to
  /// `(typedef foo (struct {x : A} {y : B}))`.
  Struct(Box<[Type]>),
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
  /// `(ghost A)` is a compoutationally irrelevant version of `A`, which means
  /// that the logical storage of `(ghost A)` is the same as `A` but the physical storage
  /// is the same as `()`. `sizeof (ghost A) = 0`.
  Ghost(Box<Type>),
  /// A propositional type, used for hypotheses.
  Prop(Box<Prop>),
  /// A user-defined type-former.
  _User(AtomID, Box<[Type]>, Box<[PureExpr]>),
}

impl Type {
  /// Create a ghost node if the boolean is true.
  #[must_use] pub fn ghost_if(ghost: bool, this: Type) -> Type {
    if ghost { Type::Ghost(Box::new(this)) } else { this }
  }
}

/// A separating proposition, which classifies hypotheses / proof terms.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum Prop {
  /// An unresolved metavariable.
  MVar(usize),
  /// An (executable) boolean expression, interpreted as a pure proposition
  Pure(Rc<PureExpr>),
}
