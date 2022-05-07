//! The AST, the result after parsing and name resolution.
//!
//! This is produced by the [`build_ast`](super::super::build_ast) pass,
//! and consumed by the [`infer`](super::super::infer) pass.
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
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;
use crate::{FileSpan, Symbol, types::indent};
use super::{Binop, FieldName, ProofId, Mm0Expr, Size, Spanned, Unop, VarId};

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
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(Lifetime);

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
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum TuplePatternKind {
  /// A variable binding, or `_` for an ignored binding. The `bool` is true if the variable
  /// is ghost.
  Name(bool, Symbol, VarId),
  /// A type ascription. The type is unparsed.
  Typed(Box<TuplePattern>, Box<Type>),
  /// A tuple, with the given arguments. Names are given to the intermediates,
  /// which will agree with the `Name` at the leaves.
  Tuple(Box<[(VarId, TuplePattern)]>),
}

impl TuplePatternKind {
  /// Extracts the single name of this tuple pattern, or `None`
  /// if this does any tuple destructuring.
  #[must_use] pub fn as_single_name(&self) -> Option<(bool, Symbol, VarId)> {
    match self {
      &Self::Name(g, name, v) => Some((g, name, v)),
      Self::Typed(pat, _) => pat.k.as_single_name(),
      Self::Tuple(_) => None
    }
  }
}

/// An argument declaration for a function.
pub type Arg = Spanned<(ArgAttr, ArgKind)>;

/// An argument declaration for a function.
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum ArgKind {
  /// A standard argument of the form `{x : T}`, a "lambda binder"
  Lam(TuplePatternKind),
  /// A substitution argument of the form `{{x : T} := val}`. (These are not supplied in
  /// invocations, they act as let binders in the remainder of the arguments.)
  Let(TuplePattern, Box<Expr>),
}

impl std::fmt::Debug for ArgKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Lam(pat) => pat.fmt(f),
      Self::Let(pat, e) => write!(f, "{:?} := {:?}", pat, e),
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

  fn debug_with_attr(&self,
    attr: ArgAttr,
    f: &mut std::fmt::Formatter<'_>
  ) -> std::fmt::Result {
    if attr.contains(ArgAttr::IMPLICIT) { write!(f, "implicit ")? }
    if attr.contains(ArgAttr::GHOST) { write!(f, "ghost ")? }
    if attr.contains(ArgAttr::MUT) { write!(f, "mut ")? }
    if attr.contains(ArgAttr::GLOBAL) { write!(f, "global ")? }
    write!(f, "{:?}", self)
  }
}

/// A type expression.
pub type Type = Spanned<TypeKind>;

/// A type variable index.
pub type TyVarId = u32;

/// A type, which classifies regular variables (not type variables, not hypotheses).
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
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
  User(Symbol, Box<[Type]>, Box<[Expr]>),
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

impl TypeKind {
  /// Construct a shared reference `&'lft ty`, which is sugar for `&sn (ref 'lft ty)`.
  #[must_use]
  pub fn shr(span: FileSpan, lft: Option<Box<Spanned<Lifetime>>>, ty: Box<Type>) -> Self {
    Self::Own(Box::new(Spanned {span, k: Self::Ref(lft, ty)}))
  }

  /// Construct an existential type `exists (x1:T) .. (xn:Tn), ty`, which is sugar for
  /// `struct (x1: T1) .. (xn: Tn) (_: ty)`, where the last argument is anonymous.
  /// `v` is a fresh variable associated to this anonymous argument.
  #[must_use]
  pub fn ex(span: FileSpan, args: Vec<TuplePattern>, v: VarId, ty: Box<Type>) -> Self {
    let mut pats = Vec::with_capacity(args.len() + 1);
    let f = |pat| (ArgAttr::empty(), ArgKind::Lam(pat));
    pats.extend(args.into_iter().map(|pat| pat.map_into(f)));
    let k = TuplePatternKind::Name(true, Symbol::UNDER, v);
    let k = f(TuplePatternKind::Typed(Box::new(Spanned {span: span.clone(), k}), ty));
    pats.push(Spanned {span, k});
    TypeKind::Struct(pats.into_boxed_slice())
  }
}

/// The type of variant, or well founded order that recursions decrease.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
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

/// A variant is a pure expression, together with a
/// well founded order that decreases on all calls.
pub type Variant = Spanned<(Expr, VariantType)>;

/// A label in a label group declaration. Individual labels in the group
/// are referred to by their index in the list.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Label {
  /// The arguments of the label
  pub args: Box<[Arg]>,
  /// The variant, for recursive calls
  pub variant: Option<Box<Variant>>,
  /// The code that is executed when you jump to the label
  pub body: Spanned<Block>,
}

/// A block is a list of statements, with an optional terminating expression.
#[derive(Default)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Block {
  /// The list of statements in the block.
  pub stmts: Vec<Stmt>,
  /// The optional last statement, or `()` if not specified.
  pub expr: Option<Box<Expr>>,
}

impl std::fmt::Debug for Block {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.debug_indent(0, f)
  }
}

impl Block {
  fn debug_indent(&self, i: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for stmt in &self.stmts { indent(i, f)?; stmt.k.debug_indent(i, f)? }
    if let Some(expr) = &self.expr {
      indent(i, f)?; expr.k.debug_indent(i, f)?
    }
    Ok(())
  }
}

/// A statement in a block.
pub type Stmt = Spanned<StmtKind>;

/// A statement in a block.
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
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

impl std::fmt::Debug for StmtKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.debug_indent(0, f)
  }
}

impl StmtKind {
  fn debug_indent(&self, i: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      StmtKind::Let { lhs, rhs } => {
        write!(f, "let {:?} = ", lhs)?;
        rhs.k.debug_indent(i, f)?;
        writeln!(f, ";")
      }
      StmtKind::Expr(e) => {
        e.debug_indent(i, f)?;
        writeln!(f, ";")
      }
      StmtKind::Label(a, labs) => {
        for (i, lab) in labs.iter().enumerate() {
          writeln!(f, "label {:?}.{}(", a, i)?;
          for &Spanned { k: (attr, ref arg), .. } in &*lab.args {
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
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(IfKind);

/// A label, which is a combination of a label group (which is identified by a `VarId`)
/// and an index into that group. This is used in the handling of `let rec` jumps, which
/// introduce a family of labels that can be jumped to within its scope.
/// Labels for loops just use groups of size 1, so the sub-index is always 0.
#[derive(Copy, Clone, Debug)]
pub struct LabelId(pub VarId, pub u16);
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(LabelId);

/// An expression.
pub type Expr = Spanned<ExprKind>;

/// An expression. A block is a list of expressions.
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum ExprKind {
  /// A `()` literal.
  Unit,
  /// A variable reference.
  Var(VarId),
  /// A user constant.
  Const(Symbol),
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
    oldmap: Box<[(Spanned<VarId>, Spanned<VarId>)]>,
  },
  /// A function call.
  Call {
    /// The function to call.
    f: Spanned<Symbol>,
    /// The type arguments.
    tys: Vec<Type>,
    /// The function arguments.
    args: Vec<Expr>,
    /// The variant, if needed.
    variant: Option<Box<Expr>>,
  },
  /// An entailment proof, which takes a proof of `P1 * ... * Pn => Q` and expressions proving
  /// `P1, ..., Pn` and is a hypothesis of type `Q`.
  Entail(Spanned<ProofId>, Box<[Expr]>),
  /// A block scope.
  Block(Block),
  /// An if-then-else expression (at either block or statement level). The initial atom names
  /// a hypothesis that the expression is true in one branch and false in the other.
  If {
    /// Distinguishes if statements from short-circuiting boolean operators.
    ik: IfKind,
    /// The hypothesis name.
    hyp: Option<[Spanned<VarId>; 2]>,
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
    hyp: Option<Spanned<VarId>>,
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
  Jump(LabelId, Vec<Expr>, Option<Box<Expr>>),
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

impl std::fmt::Debug for ExprKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.debug_indent(0, f)
  }
}

impl ExprKind {
  fn debug_indent(&self, i: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      ExprKind::Unit => write!(f, "()"),
      ExprKind::Var(v) => write!(f, "{:?}", v),
      ExprKind::Const(c) => write!(f, "{}", c),
      ExprKind::Bool(b) => write!(f, "{}", b),
      ExprKind::Int(n) => write!(f, "{}", n),
      ExprKind::Unop(op, e) => { write!(f, "{:?} ", op)?; e.k.debug_indent(i, f) }
      ExprKind::Binop(op, e1, e2) => {
        e1.k.debug_indent(i, f)?;
        write!(f, " {} ", op)?;
        e2.k.debug_indent(i, f)
      }
      ExprKind::Sn(e, h) => {
        write!(f, "sn(")?;
        e.k.debug_indent(i, f)?;
        write!(f, ", ")?;
        match h {
          None => write!(f, "-)"),
          Some(h) => {
            h.k.debug_indent(i, f)?;
            write!(f, ")")
          }
        }
      }
      ExprKind::Index(arr, idx, h) => {
        arr.k.debug_indent(i, f)?;
        write!(f, "[")?;
        idx.k.debug_indent(i, f)?;
        if let Some(h) = h {
          write!(f, ", ")?;
          h.k.debug_indent(i, f)?;
        }
        write!(f, "]")
      }
      ExprKind::Slice(args, h) => {
        let (arr, idx, len) = &**args;
        arr.k.debug_indent(i, f)?;
        write!(f, "[")?;
        idx.k.debug_indent(i, f)?;
        write!(f, "..+")?;
        len.k.debug_indent(i, f)?;
        if let Some(h) = h {
          write!(f, ", ")?;
          h.k.debug_indent(i, f)?;
        }
        write!(f, "]")
      }
      ExprKind::Proj(e, j) => {
        e.k.debug_indent(i, f)?;
        write!(f, ".{}", j.k)
      }
      ExprKind::Deref(e) => { write!(f, "*")?; e.k.debug_indent(i, f) }
      ExprKind::List(es) => {
        writeln!(f, "[")?;
        for e in es {
          indent(i+1, f)?; e.k.debug_indent(i+1, f)?; writeln!(f, ",")?;
        }
        indent(i, f)?; write!(f, "]")
      }
      ExprKind::Ghost(e) => {
        write!(f, "ghost(")?; e.k.debug_indent(i, f)?; write!(f, ")")
      }
      ExprKind::Ref(e) => { write!(f, "ref ")?; e.k.debug_indent(i, f) }
      ExprKind::Borrow(e) => { write!(f, "&")?; e.k.debug_indent(i, f) }
      ExprKind::Mm0(e) => {
        write!(f, "{:?}", e.expr)?;
        if !e.subst.is_empty() {
          writeln!(f, "[")?;
          for e in &e.subst {
            indent(i+1, f)?; e.k.debug_indent(i+1, f)?; writeln!(f, ",")?;
          }
          indent(i, f)?; write!(f, "]")?;
        }
        Ok(())
      }
      ExprKind::Typed(e, ty) => write!(f, "({:?}: {:?})", e, ty),
      ExprKind::As(e, ty) => write!(f, "({:?} as {:?})", e, ty),
      ExprKind::Cast(e, h) => {
        write!(f, "cast(")?;
        e.k.debug_indent(i, f)?;
        if let Some(h) = h { write!(f, ", {:?}", h)? }
        write!(f, ")")
      }
      ExprKind::Pun(e, h) => {
        write!(f, "pun(")?;
        e.k.debug_indent(i, f)?;
        if let Some(h) = h { write!(f, ", {:?}", h)? }
        write!(f, ")")
      }

      ExprKind::Uninit => write!(f, "uninit"),
      ExprKind::Sizeof(ty) => {
        write!(f, "sizeof({:?})", ty)
      }
      ExprKind::Typeof(e) => {
        write!(f, "typeof(")?;
        e.k.debug_indent(i, f)?;
        write!(f, ")")
      }
      ExprKind::Assert(e) => {
        write!(f, "assert(")?;
        e.k.debug_indent(i, f)?;
        write!(f, ")")
      }
      ExprKind::Assign { lhs, rhs, oldmap } => {
        lhs.k.debug_indent(i, f)?;
        write!(f, " <- ")?;
        rhs.k.debug_indent(i, f)?;
        if !oldmap.is_empty() {
          write!(f, " with [")?;
          for (new, old) in &**oldmap { write!(f, "{} <- {}, ", new.k, old.k)? }
          write!(f, "]")?
        }
        Ok(())
      }
      ExprKind::Call { f: func, tys, args, variant } => {
        use itertools::Itertools;
        write!(f, "{}", func.k)?;
        if !tys.is_empty() { write!(f, "<{:?}>", tys.iter().format(", "))? }
        writeln!(f, "(")?;
        for e in args {
          indent(i+1, f)?; e.k.debug_indent(i+1, f)?; writeln!(f, ",")?;
        }
        if let Some(var) = variant { indent(i+1, f)?; writeln!(f, "{:?},", var)?; }
        indent(i, f)?; write!(f, ")")
      }
      ExprKind::Entail(p, es) => {
        write!(f, "{:?}", p.k)?;
        if !es.is_empty() {
          writeln!(f, "(")?;
          for e in &**es {
            indent(i+1, f)?; e.k.debug_indent(i+1, f)?; writeln!(f, ",")?;
          }
          indent(i, f)?; write!(f, ")")?;
        }
        Ok(())
      }
      ExprKind::Block(bl) => {
        writeln!(f, "{{")?;
        bl.debug_indent(i+1, f)?;
        indent(i, f)?; write!(f, "}}")
      }
      ExprKind::If { ik: _, hyp, cond, then, els } => {
        write!(f, "if ")?;
        if let Some([h, _]) = hyp { write!(f, "{}: ", h.k)? }
        cond.k.debug_indent(i+1, f)?;
        writeln!(f, " {{")?;
        then.k.debug_indent(i+1, f)?;
        indent(i, f)?; writeln!(f, "}} else ")?;
        if let Some([_, h]) = hyp { write!(f, "{}: ", h.k)? }
        writeln!(f, "{{")?;
        els.k.debug_indent(i+1, f)?;
        indent(i, f)?; write!(f, "}}")
      }
      ExprKind::While { label, muts, hyp, cond, var, body, .. } => {
        if !muts.is_empty() {
          write!(f, "#[muts")?;
          for &v in &**muts { write!(f, " {}", v)? }
          writeln!(f, "]")?; indent(i, f)?;
        }
        write!(f, "{}: while ", label)?;
        if let Some(h) = hyp { write!(f, "{}: ", h.k)? }
        cond.k.debug_indent(i+1, f)?;
        if let Some(var) = var {
          writeln!(f)?;
          indent(i+1, f)?; writeln!(f, "{:?}", var)?;
          indent(i, f)?; writeln!(f, "{{")?;
        } else {
          writeln!(f, " {{")?;
        }
        body.debug_indent(i+1, f)?;
        indent(i, f)?; write!(f, "}}")
      }
      ExprKind::Unreachable(e) => {
        write!(f, "unreachable ")?;
        e.k.debug_indent(i, f)
      }
      ExprKind::Jump(LabelId(lab, j), es, var) => {
        write!(f, "jump {}.{}(", lab, j)?;
        for e in es {
          indent(i+1, f)?; e.k.debug_indent(i+1, f)?; writeln!(f, ",")?;
        }
        if let Some(var) = var { indent(i+1, f)?; writeln!(f, "{:?},", var)?; }
        indent(i, f)?; write!(f, ")")
      }
      ExprKind::Break(lab, e) => {
        write!(f, "break {} ", lab)?;
        e.k.debug_indent(i, f)
      }
      ExprKind::Return(es) => {
        writeln!(f, "return(")?;
        for e in es {
          indent(i+1, f)?; e.k.debug_indent(i+1, f)?; writeln!(f, ",")?;
        }
        indent(i, f)?; write!(f, ")")
      }
      ExprKind::Infer(true) => write!(f, "?_"),
      ExprKind::Infer(false) => write!(f, "_"),
      ExprKind::Rc(e) => e.k.debug_indent(i, f),
      ExprKind::Error => write!(f, "??"),
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

impl Expr {
  /// Construct an expression list constructor, with the special cases:
  /// * An empty list becomes a unit literal `()`
  /// * A singleton list `(e)` is treated as `e`
  #[must_use] pub fn list(span: &FileSpan, args: Vec<Expr>) -> Expr {
    match args.len() {
      0 => Spanned {span: span.clone(), k: ExprKind::Unit},
      // Safety: it's not empty
      1 => unsafe { args.into_iter().next().unwrap_unchecked() },
      _ => Spanned {span: span.clone(), k: ExprKind::List(args)},
    }
  }

  /// Construct a `!e` boolean negation expression.
  #[must_use] pub fn not(self, span: &FileSpan) -> Self {
    Spanned {span: span.clone(), k: ExprKind::Unop(Unop::Not, Box::new(self))}
  }

  /// Construct a `~e` bitwise negation expression.
  #[must_use] pub fn bit_not(self, span: &FileSpan) -> Self {
    Spanned {span: span.clone(), k: ExprKind::Unop(Unop::Not, Box::new(self))}
  }
}

/// A field of a struct.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Field {
  /// The name of the field.
  pub name: Symbol,
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
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(ProcKind);

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
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(ArgAttr);

/// An out parameter in a function's returns.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct OutArg {
  /// The index of the argument in the inputs
  pub input: u32,
  /// The name of the binder
  pub name: Spanned<Symbol>,
  /// The variable in the binder
  pub var: VarId,
  /// The type, if provided
  pub ty: Option<Box<Type>>,
}
/// A top level program item. (A program AST is a list of program items.)
pub type Item = Spanned<ItemKind>;

/// A top level program item. (A program AST is a list of program items.)
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum ItemKind {
  /// A procedure (or function or intrinsic), a top level item similar to function declarations in C.
  Proc {
    /// An intrinsic declaration, which is only here to put the function declaration in user code.
    /// The compiler will ensure this matches an existing intrinsic, and intrinsics cannot be
    /// called until they are declared using an `intrinsic` declaration.
    intrinsic: Option<super::entity::IntrinsicProc>,
    /// The type of declaration: `func`, `proc`, or `intrinsic`.
    kind: ProcKind,
    /// The name of the procedure.
    name: Spanned<Symbol>,
    /// The number of type arguments
    tyargs: u32,
    /// The arguments of the procedure.
    args: Box<[Arg]>,
    /// The out parameters of the procedure.
    outs: Box<[OutArg]>,
    /// The return values of the procedure. (Functions and procedures return multiple values in MMC.)
    rets: Box<[TuplePattern]>,
    /// The variant, used for recursive functions.
    variant: Option<Box<Variant>>,
    /// The body of the procedure.
    body: Block
  },
  /// A global variable declaration.
  Global(
    /// An intrinsic global declaration.
    /// The compiler will ensure this matches an existing intrinsic, and intrinsics cannot be
    /// used until they are declared using an `intrinsic` declaration.
    Option<super::entity::IntrinsicGlobal>,
    /// The variable(s) being declared
    TuplePattern,
    /// The value of the declaration
    Expr,
  ),
  /// A constant declaration.
  Const(
    /// An intrinsic constant declaration.
    /// The compiler will ensure this matches an existing intrinsic, and intrinsics cannot be
    /// used until they are declared using an `intrinsic` declaration.
    Option<super::entity::IntrinsicConst>,
    /// The constant(s) being declared
    TuplePattern,
    /// The value of the declaration
    Expr,
  ),
  /// A type definition.
  Typedef {
    /// An intrinsic typedef.
    /// The compiler will ensure this matches an existing intrinsic, and intrinsics cannot be
    /// used until they are declared using an `intrinsic` declaration.
    intrinsic: Option<super::entity::IntrinsicType>,
    /// The name of the newly declared type
    name: Spanned<Symbol>,
    /// The number of type arguments
    tyargs: u32,
    /// The arguments of the type declaration, for a parametric type
    args: Box<[Arg]>,
    /// The value of the declaration (another type)
    val: Type,
  },
}
