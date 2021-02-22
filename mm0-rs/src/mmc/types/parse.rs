//! The types output by the parser.
//!
//! This is a sort of "pre-AST" type, because the [parser](super::super::parser) does
//! parsing on demand, meaning that these types are shallow, or nonrecursive: the
//! unparsed [`LispVal`] data is deconstructed to a top level expression / pattern which
//! contains more `LispVal` data in the immediate subterms, requiring more calls to the
//! parser to parse these and so on. The driver for the parser is
//! [`BuildAst`](super::super::build_ast::BuildAst), which constructs a proper AST using the
//! types in the [`types::ast`](super::ast) module.

use num::BigInt;
use crate::elab::environment::AtomId;
use crate::elab::lisp::{LispVal, Uncons, print::{EnvDisplay, FormatEnv}};
use crate::util::FileSpan;
use super::{Spanned, Size, FieldName};

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
  Place(AtomId),
  /// A lifetime that has not been inferred yet.
  Infer,
}
crate::deep_size_0!(Lifetime);

impl EnvDisplay for Lifetime {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use std::fmt::Display;
    match self {
      Lifetime::Extern => "extern".fmt(f),
      Lifetime::Place(v) => v.fmt(fe, f),
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
  Name(bool, AtomId),
  /// A type ascription. The type is unparsed.
  Typed(Box<TuplePattern>, LispVal),
  /// A tuple, with the given arguments.
  Tuple(Vec<TuplePattern>),
}

impl TuplePatternKind {
  /// The `_` tuple pattern. This is marked as ghost because it can't be referred to so
  /// it is always safe to make irrelevant.
  pub const UNDER: Self = Self::Name(true, AtomId::UNDER);

  /// Extracts the single name of this tuple pattern, or `None`
  /// if this does any tuple destructuring.
  #[must_use] pub fn as_single_name(&self) -> Option<AtomId> {
    match self {
      &Self::Name(_, v) => Some(v),
      Self::Typed(pat, _) => pat.k.as_single_name(),
      Self::Tuple(_) => None
    }
  }
}

impl TuplePattern {
  /// Map a function over the names in the pattern.
  pub fn on_names<E>(&self, f: &mut impl FnMut(&FileSpan, AtomId) -> Result<(), E>) -> Result<(), E> {
    match self.k {
      TuplePatternKind::Name(_, v) => f(&self.span, v)?,
      TuplePatternKind::Typed(ref pat, _) => pat.on_names(f)?,
      TuplePatternKind::Tuple(ref pats) => for pat in pats { pat.on_names(f)? }
    }
    Ok(())
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
  Let(TuplePattern, LispVal),
}

impl ArgKind {
  /// Extracts the binding part of this argument.
  #[must_use] pub fn var(&self) -> &TuplePatternKind {
    match self {
      Self::Lam(pat) | Self::Let(Spanned {k: pat, ..}, _) => pat,
    }
  }
}

/// A pattern, the left side of a match statement.
pub type Pattern = Spanned<PatternKind>;

/// A pattern, the left side of a match statement.
#[derive(Debug)]
pub enum PatternKind {
  /// A variable binding.
  Var(AtomId),
  /// A user-defined constant.
  Const(AtomId),
  /// A numeric literal.
  Number(BigInt),
  /// A hypothesis pattern, which binds the first argument to a proof that the
  /// scrutinee satisfies the pattern argument.
  Hyped(AtomId, LispVal),
  /// A pattern guard: Matches the inner pattern, and then if the expression returns
  /// true, this is also considered to match.
  With(LispVal, LispVal),
  /// A disjunction of patterns.
  Or(Uncons),
}

/// A rename is a `{old -> old'}` or `{new' <- new}` clause appearing in a `with`
/// associated to a let binding or assignment, as in `{{x <- 2} with {x -> x_old}}`.
#[derive(Clone, Debug, Default, DeepSizeOf)]
pub struct Renames {
  /// `{from -> to}` means that the variable `from` should be renamed to `to`
  /// (after evaluation of the main expression).
  /// The elements of this list are `(from, to)` pairs.
  pub old: Vec<(AtomId, AtomId)>,
  /// `{to <- from}` means that the new value of the variable `from` should be called `to`,
  /// so that the old value of variable `from` is available by that name.
  /// The elements of this list are `(from, to)` pairs.
  pub new: Vec<(AtomId, AtomId)>,
}

/// A type expression.
pub type Type = Spanned<TypeKind>;

/// A type, which classifies regular variables (not type variables, not hypotheses).
#[derive(Debug, DeepSizeOf)]
pub enum TypeKind {
  /// `()` is the type with one element; `sizeof () = 0`.
  Unit,
  /// A true proposition.
  True,
  /// A false proposition.
  False,
  /// `bool` is the type of booleans, that is, bytes which are 0 or 1; `sizeof bool = 1`.
  Bool,
  /// A type variable.
  Var(AtomId),
  /// `i(8*N)` is the type of N byte signed integers `sizeof i(8*N) = N`.
  Int(Size),
  /// `u(8*N)` is the type of N byte unsigned integers; `sizeof u(8*N) = N`.
  UInt(Size),
  /// The type `[T; n]` is an array of `n` elements of type `T`;
  /// `sizeof [T; n] = sizeof T * n`.
  Array(LispVal, LispVal),
  /// `own T` is a type of owned pointers. The typehood predicate is
  /// `x :> own T` iff `E. v (x |-> v) * v :> T`.
  Own(LispVal),
  /// `(ref T)` is a type of borrowed values. This type is elaborated to
  /// `(ref a T)` where `a` is a lifetime; this is handled a bit differently than rust
  /// (see [`Lifetime`]).
  Ref(Option<Box<Spanned<Lifetime>>>, LispVal),
  /// `(& T)` is a type of borrowed pointers. This type is elaborated to
  /// `(& a T)` where `a` is a lifetime; this is handled a bit differently than rust
  /// (see [`Lifetime`]).
  Shr(Option<Box<Spanned<Lifetime>>>, LispVal),
  /// `&sn x` is the type of pointers to the place `x` (a variable or indexing expression).
  RefSn(LispVal),
  /// `(A, B, C)` is a tuple type with elements `A, B, C`;
  /// `sizeof (list A B C) = sizeof A + sizeof B + sizeof C`.
  List(Vec<LispVal>),
  /// `(sn {a : T})` the type of values of type `T` that are equal to `a`.
  /// This is useful for asserting that a computationally relevant value can be
  /// expressed in terms of computationally irrelevant parts.
  Sn(LispVal),
  /// `{x : A, y : B, z : C}` is the dependent version of `list`;
  /// it is a tuple type with elements `A, B, C`, but the types `A, B, C` can
  /// themselves refer to `x, y, z`.
  /// `sizeof {x : A, _ : B x} = sizeof A + max_x (sizeof (B x))`.
  ///
  /// The top level declaration `(struct foo {x : A} {y : B})` desugars to
  /// `(typedef foo {x : A, y : B})`.
  Struct(Vec<Arg>),
  /// A universally quantified proposition.
  All(Vec<TuplePattern>, LispVal),
  /// An existentially quantified proposition.
  Ex(Vec<TuplePattern>, LispVal),
  /// Implication (plain, non-separating).
  Imp(LispVal, LispVal),
  /// Separating implication.
  Wand(LispVal, LispVal),
  /// Negation.
  Not(LispVal),
  /// `(and A B C)` is an intersection type of `A, B, C`;
  /// `sizeof (and A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (and A B C)` iff
  /// `x :> A /\ x :> B /\ x :> C`. (Note that this is regular conjunction,
  /// not separating conjunction.)
  And(Vec<LispVal>),
  /// `(or A B C)` is an undiscriminated anonymous union of types `A, B, C`.
  /// `sizeof (or A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (or A B C)` iff
  /// `x :> A \/ x :> B \/ x :> C`.
  Or(Vec<LispVal>),
  /// `(ghost A)` is a computationally irrelevant version of `A`, which means
  /// that the logical storage of `(ghost A)` is the same as `A` but the physical storage
  /// is the same as `()`. `sizeof (ghost A) = 0`.
  Ghost(LispVal),
  /// `(? T)` is the type of possibly-uninitialized `T`s. The typing predicate
  /// for this type is vacuous, but it has the same size as `T`, so overwriting with
  /// a `T` is possible.
  Uninit(LispVal),
  /// `(if c A B)` is a conditional type: if `c` is true then this is `A`, otherwise `B`.
  If([LispVal; 3]),
  /// A switch (pattern match) statement, given the initial expression and a list of match arms.
  Match(LispVal, Vec<(LispVal, LispVal)>),
  /// A boolean expression, interpreted as a pure proposition
  Pure(Box<ExprKind>),
  /// A user-defined type-former.
  User(AtomId, Box<[LispVal]>, Box<[LispVal]>),
  /// A heap assertion `l |-> (v: T)`.
  Heap(LispVal, LispVal),
  /// An explicit typing assertion `[v : T]`.
  HasTy(LispVal, LispVal),
  /// The input token.
  Input,
  /// The output token.
  Output,
  /// A moved-away type.
  Moved(LispVal),
  /// A typechecking error that we have reported already.
  Error
}

/// The type of variant, or well founded order that recursions decrease.
#[derive(Debug, DeepSizeOf)]
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
pub type Variant = Spanned<(LispVal, VariantType)>;

/// A call expression, which requires a second round of parsing depending
/// on the context of declared entities - it might still be a primitive
/// operation like `(return e)` but it looks basically like a function call.
#[derive(Debug, DeepSizeOf)]
pub struct CallExpr {
  /// The function to call.
  pub f: Spanned<AtomId>,
  /// The function arguments.
  pub args: Vec<LispVal>,
  /// The variant, if needed.
  pub variant: Option<LispVal>,
}

/// A parsed label expression `((begin (lab x y)) body)`.
#[derive(Debug, DeepSizeOf)]
pub struct Label {
  /// The name of the label
  pub name: AtomId,
  /// The arguments of the label
  pub args: Vec<Arg>,
  /// The variant, for recursive calls
  pub variant: Option<Box<Variant>>,
  /// The code that is executed when you jump to the label
  pub body: Uncons,
}

/// An expression or statement.
pub type Expr = Spanned<ExprKind>;

/// An expression or statement. A block is a list of expressions.
#[derive(Debug, DeepSizeOf)]
pub enum ExprKind {
  /// A `()` literal.
  Unit,
  /// A variable reference.
  Var(AtomId),
  /// A boolean literal.
  Bool(bool),
  /// A number literal.
  Int(BigInt),
  /// A let binding.
  Let {
    /// A tuple pattern, containing variable bindings.
    lhs: Box<TuplePattern>,
    /// The expression to evaluate.
    rhs: LispVal,
    /// The list of simultaneous variable renames.
    with: Renames
  },
  /// An assignment / mutation.
  Assign {
    /// A place (lvalue) to write to.
    lhs: LispVal,
    /// The expression to evaluate.
    rhs: LispVal,
    /// The list of simultaneous variable renames.
    with: Renames
  },
  /// A field access `e.field`.
  Proj(LispVal, Spanned<FieldName>),
  /// A function call (or something that looks like one at parse time).
  Call(CallExpr),
  /// An entailment proof, which takes a proof of `P1 * ... * Pn => Q` and expressions proving
  /// `P1, ..., Pn` and is a hypothesis of type `Q`.
  Entail(LispVal, Vec<LispVal>),
  /// A block scope.
  Block(Uncons),
  /// A label, which looks exactly like a local function but has no independent stack frame.
  /// They are called like regular functions but can only appear in tail position.
  Label(Label),
  /// An if-then-else expression (at either block or statement level). The initial atom names
  /// a hypothesis that the expression is true in one branch and false in the other.
  If {
    /// The list of `(h,C,T)` triples in `if {h1 : C1} T1 if {h2 : C2} T2 else E`.
    branches: Vec<(Option<AtomId>, LispVal, LispVal)>,
    /// The else case, the `E` in `if {h1 : C1} T1 if {h2 : C2} T2 else E`.
    els: Option<LispVal>
  },
  /// A switch (pattern match) statement, given the initial expression and a list of match arms.
  Match(LispVal, Vec<(LispVal, LispVal)>),
  /// A while loop.
  While {
    /// The set of variables that are mutated in the while loop.
    muts: Vec<Spanned<AtomId>>,
    /// A hypothesis that the condition is true in the loop and false after it.
    hyp: Option<Spanned<AtomId>>,
    /// The loop condition.
    cond: LispVal,
    /// The variant, which must decrease on every round around the loop.
    var: Option<Box<Variant>>,
    /// The body of the loop.
    body: Uncons,
  },
  /// A hole `_`, which is a compile error but queries the compiler to provide a type context.
  Hole,
}

/// The simplest kind of call, which takes zero or more expression arguments.
#[derive(Copy, Clone, Debug)]
pub enum NAryCall {
  /// `{x + y}` returns the integer sum of the arguments
  Add,
  /// `{x * y}` returns the integer product of the arguments
  Mul,
  /// `(and x1 ... xn)` returns the boolean `AND` of the arguments.
  And,
  /// `(or x1 ... xn)` returns the boolean `OR` of the arguments.
  Or,
  /// `(not x1 ... xn)` returns the boolean `NOR` of the arguments,
  /// usually used in the unary case as `NOT`
  Not,
  /// `(band e1 ... en)` returns the bitwise `AND` of the arguments.
  BitAnd,
  /// `(bor e1 ... en)` returns the bitwise `OR` of the arguments.
  BitOr,
  /// `(bxor e1 ... en)` returns the bitwise `XOR` of the arguments.
  BitXor,
  /// `(bnot e1 ... en)` returns the bitwise `NOR` of the arguments,
  /// usually used in the unary case as `NOT`
  BitNot,
  /// `(assert p)` evaluates `p` and if it is false, crashes the program with an error.
  /// It returns a proof that `p` is true (because if `p` is false then the
  /// rest of the function is not evaluated).
  Assert,
  /// `(list e1 ... en)` returns a tuple of the arguments.
  List,
  /// `{x <= y}` returns true if `x` is less than or equal to `y`
  Le,
  /// `{x < y}` returns true if `x` is less than `y`
  Lt,
  /// `{x == y}` returns true if `x` is equal to `y`
  Eq,
  /// `{x != y}` returns true if `x` is not equal to `y`
  Ne,
  /// `(ghost x)` returns the same thing as `x` but in the type `(ghost A)`.
  /// `(ghost x y z)` is shorthand for `(ghost (list x y z))`.
  GhostList,
  /// `(return e1 ... en)` returns `e1, ..., en` from the current function.
  Return,
}

/// A parsed call-like expression.
#[derive(Debug)]
pub enum CallKind {
  /// A user-defined constant.
  Const(AtomId),
  /// A user-defined global variable.
  Global(AtomId),
  /// An application of an [`NAryCall`] to zero or more arguments.
  NAry(NAryCall, Vec<LispVal>),
  /// `(- x)` is the negation of x.
  Neg(LispVal),
  /// `{x - y - z}` returns the subtraction of `y,z,...` from `x`.
  Sub(LispVal, std::vec::IntoIter<LispVal>),
  /// `{a shl b}` computes the value `a * 2 ^ b`, a left shift of `a` by `b`.
  Shl(LispVal, LispVal),
  /// `{a shr b}` computes the value `a // 2 ^ b`, a right shift of `a` by `b`.
  /// This is an arithmetic shift on signed integers and a logical shift on unsigned integers.
  Shr(LispVal, LispVal),
  /// A `(pure)` expression, which embeds MM0 syntax to produce an expression
  /// of numeric or boolean type.
  Mm0(Box<[(AtomId, LispVal)]>, LispVal),
  /// `{e : T}` is `e`, with the type `T`. This is used only to direct
  /// type inference, it has no effect otherwise.
  Typed(LispVal, LispVal),
  /// `{x as T}` performs truncation and non-value preserving casts a la `reinterpret_cast`.
  As(LispVal, LispVal),
  /// `(cast x h)` returns `x` at type `T` if `h` proves `x` has type `T`.
  Cast(LispVal, Option<LispVal>),
  /// `(pun x h)` reinterprets the bits of `x` at type `T` if `h` proves this is valid.
  Pun(LispVal, Option<LispVal>),
  /// `(sn x)` is an element of type `(sn x)`. `(sn y h)` is also a member of `(sn x)` if `h: y = x`.
  Sn(LispVal, Option<LispVal>),
  /// `{uninit : (? T)}` is an effectful expression producing an undefined value
  /// in any `(? T)` type.
  Uninit,
  /// If `x` has type `T`, then `(typeof! x)` is a proof that `x :> T`.
  /// This consumes `x`'s type.
  TypeofBang(LispVal),
  /// If `x` has type `T` where `T` is a copy type, then `(typeof x)` is a
  /// proof that `x :> T`. This version of `typeof!` only works on copy types
  /// so that it doesn't consume `x`.
  Typeof(LispVal),
  /// `(sizeof T)` is the size of `T` in bytes.
  Sizeof(LispVal),
  /// `(ref x)` constructs `x` as an lvalue.
  Place(LispVal),
  /// `(& x)` constructs a reference to `x`.
  Ref(LispVal),
  /// The function `(index a i h)` is the equivalent of `C`'s `a[i]`;
  /// it has type `(own T)` if `a` has type `(own (array T i))` and type `(& T)`
  /// if `a` has type `(& (array T i))`. The hypothesis `h` is a proof that
  /// `i` is in the bounds of the array.
  Index(LispVal, LispVal, Option<LispVal>),
  /// If `x: (array T n)`, then `(slice x a b h): (array T b)` if
  /// `h` is a proof that `a + b <= n`. Computationally this corresponds to
  /// simply `&x + a * sizeof T`, in the manner of C pointer arithmetic.
  Slice(LispVal, LispVal, LispVal, Option<LispVal>),
  /// `(unreachable h)` takes a proof of false and undoes the current code path.
  Unreachable(Option<LispVal>),
  /// `(lab e1 ... en)` jumps to label `lab` with `e1 ... en` as arguments.
  Jump(Option<AtomId>, std::vec::IntoIter<LispVal>, Option<LispVal>),
  /// * `(break e)` jumps out of the nearest enclosing loop, returning `e` to the enclosing scope.
  /// * `(break lab e)` jumps out of the scope containing label `lab`,
  ///   returning `e` as the result of the block.
  Break(Option<AtomId>, std::vec::IntoIter<LispVal>),
  /// `(f e1 ... en)` calls a user-defined or intrinsic function called `f` with
  /// `e1 ... en` as arguments.
  Call(CallExpr, u32),
  /// An upstream error.
  Error,
}

/// A field of a struct.
#[derive(Debug, DeepSizeOf)]
pub struct Field {
  /// The name of the field.
  pub name: AtomId,
  /// True if the field is computationally irrelevant.
  pub ghost: bool,
  /// The type of the field (unparsed).
  pub ty: LispVal,
}

pub use super::ast::ProcKind;

/// The annotations that can appear on function arguments.
#[derive(Clone, Copy, Debug, Default)]
pub struct ArgAttr {
  /// `(mut {x : T})` in function arguments means that `x` will be mutated
  /// as a side effect of the call. It should be paired with `out` in the function
  /// returns to indicate the resulting name; otherwise it will be prepended to
  /// the function returns as an `out` with the same name.
  pub mut_: bool,
  /// `(global {x : T})` in function arguments means that `x` is the name of a global
  /// variable that will be used in the function.
  pub global: bool,
  /// `(implicit {x : T})` in function arguments means that applications will
  /// use `_` for this argument instead of supplying a value.
  pub implicit: bool,
  /// `(out x {x' : T})` in function returns means that the variable `x`
  /// (which must be a `(mut x)` in the function arguments) is being mutated to
  /// `x'`; this acts as a binder declaring variable `x'`, and both `x` and `x'`
  /// can be used in subsequent types.
  pub out: Option<AtomId>,
}
crate::deep_size_0!(ArgAttr);

/// A procedure (or function or intrinsic), a top level item similar to function declarations in C.
#[derive(Debug, DeepSizeOf)]
pub struct Proc {
  /// The type of declaration: `func`, `proc`, or `intrinsic`.
  pub kind: ProcKind,
  /// The name of the procedure.
  pub name: Spanned<AtomId>,
  /// The type arguments of the procedure.
  pub tyargs: Vec<Spanned<AtomId>>,
  /// The arguments of the procedure.
  pub args: Vec<Arg>,
  /// The return values of the procedure. (Functions and procedures return multiple values in MMC.)
  pub rets: Vec<Arg>,
  /// The variant, used for recursive functions.
  pub variant: Option<Box<Variant>>,
  /// The body of the procedure.
  pub body: Uncons
}

/// A top level program item. (A program AST is a list of program items.)
pub type Item = Spanned<ItemKind>;

/// A top level program item. (A program AST is a list of program items.)
#[derive(Debug, DeepSizeOf)]
pub enum ItemKind {
  /// A procedure, behind an Arc so it can be cheaply copied.
  Proc(Proc),
  /// A global variable declaration.
  Global(Box<TuplePattern>, LispVal),
  /// A constant declaration.
  Const(Box<TuplePattern>, LispVal),
  /// A type definition.
  Typedef {
    /// The name of the newly declared type
    name: Spanned<AtomId>,
    /// The type arguments of the type declaration, for a parametric type
    tyargs: Vec<Spanned<AtomId>>,
    /// The arguments of the type declaration, for a parametric type
    args: Vec<Arg>,
    /// The value of the declaration (another type)
    val: LispVal,
  },
  /// A structure definition.
  Struct {
    /// The name of the structure
    name: Spanned<AtomId>,
    /// The type arguments of the type
    tyargs: Vec<Spanned<AtomId>>,
    /// The parameters of the type
    args: Vec<Arg>,
    /// The fields of the structure
    fields: Vec<Arg>,
  },
}
