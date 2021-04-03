//! The mid level IR, a basic block based representation used for most optimizations.
#![allow(unused)]

use std::{ops::{Index, IndexMut}, rc::Rc};
use std::convert::TryInto;
use std::mem;
use num::BigInt;
use crate::{AtomId, FileSpan, LispVal, Remap, Remapper};
use super::{Binop, Unop, VarId, Spanned, IntTy, ast::ProcKind, ty, ast, global};
pub use {ast::TyVarId, ty::Lifetime};

bitflags! {
  /// Attributes on arguments in a `(struct)` dependent tuple type.
  pub struct ArgAttr: u8 {
    /// An argument is nondependent if the remainder of the type does not depend on this variable.
    const NONDEP = 1;
    /// An existential argument represents `exists x. p(x)` instead of `sigma x. p(x)`; the
    /// difference is that a witness to `exists x. p(x)` is `a` such that `a: p(x)` for some `x`,
    /// while a witness to `sigma x. p(x)` is a tuple `(x, a)` such that `a: p(x)`. Thus we cannot
    /// project out existential arguments (nor can we get the type of arguments depending on an
    /// existential argument).
    const EXISTENTIAL = 2;
    /// An singleton argument is a special case where an existential argument can support
    /// projections, because it has a singleton type (for example `()`, `sn x`, or a proposition).
    const SINGLETON = 4;
    /// A ghost argument is one that has no bit-representation; a representative of
    /// `sigma x: ghost T. p(x)` is just a representative of `p(x)`, while a representative of
    /// `sigma x: T. p(x)` is the concatenation of a representative of `T` and a representative of
    /// `p(x)`. (In other words, this is like `EXISTENTIAL` but at the computation level instead of
    /// the logical level.)
    const GHOST = 8;
  }
}
crate::deep_size_0!(ArgAttr);

impl Remap for ArgAttr {
  type Target = Self;
  fn remap(&self, _: &mut Remapper) -> Self { *self }
}

/// An argument in a struct (dependent tuple).
#[derive(Debug, DeepSizeOf)]
pub struct Arg {
  /// Extra properties of the binding
  attr: ArgAttr,
  /// The variable to bind
  var: VarId,
  /// The type of the variable
  ty: Ty,
}

impl Remap for Arg {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Self {
      attr: self.attr,
      var: self.var,
      ty: self.ty.remap(r),
    }
  }
}

/// The type of embedded MM0 expressions.
pub type Mm0Expr = global::Mm0Expr<Expr>;

/// A type, which classifies regular variables (not type variables, not hypotheses).
pub type Ty = Rc<TyKind>;

/// A type, which classifies regular variables (not type variables, not hypotheses).
#[derive(Debug, DeepSizeOf)]
pub enum TyKind {
  /// `()` is the type with one element; `sizeof () = 0`.
  Unit,
  /// A true proposition.
  True,
  /// A false proposition.
  False,
  /// `bool` is the type of booleans, that is, bytes which are 0 or 1; `sizeof bool = 1`.
  Bool,
  /// A type variable.
  Var(TyVarId),
  /// The integral types:
  /// * `i(8*N)` is the type of N byte signed integers `sizeof i(8*N) = N`.
  /// * `u(8*N)` is the type of N byte unsigned integers; `sizeof u(8*N) = N`.
  Int(IntTy),
  /// The type `[T; n]` is an array of `n` elements of type `T`;
  /// `sizeof [T; n] = sizeof T * n`.
  Array(Ty, Expr),
  /// `own T` is a type of owned pointers. The typehood predicate is
  /// `x :> own T` iff `E. v (x |-> v) * v :> T`.
  Own(Ty),
  /// `(ref T)` is a type of borrowed values. This type is elaborated to
  /// `(ref a T)` where `a` is a lifetime; this is handled a bit differently than rust
  /// (see [`Lifetime`]).
  Ref(Lifetime, Ty),
  /// `&sn x` is the type of pointers to the place `x` (a variable or indexing expression).
  RefSn(Expr),
  /// `(A, B, C)` is a tuple type with elements `A, B, C`;
  /// `sizeof (list A B C) = sizeof A + sizeof B + sizeof C`.
  List(Box<[Ty]>),
  /// `(sn {a : T})` the type of values of type `T` that are equal to `a`.
  /// This is useful for asserting that a computationally relevant value can be
  /// expressed in terms of computationally irrelevant parts.
  Sn(Expr, Ty),
  /// `{x : A, y : B, z : C}` is the dependent version of `list`;
  /// it is a tuple type with elements `A, B, C`, but the types `A, B, C` can
  /// themselves refer to `x, y, z`.
  /// `sizeof {x : A, _ : B x} = sizeof A + max_x (sizeof (B x))`.
  ///
  /// The top level declaration `(struct foo {x : A} {y : B})` desugars to
  /// `(typedef foo {x : A, y : B})`.
  Struct(Box<[Arg]>),
  /// A universally quantified proposition.
  All(VarId, Ty, Ty),
  /// Implication (plain, non-separating).
  Imp(Ty, Ty),
  /// Separating implication.
  Wand(Ty, Ty),
  /// Negation.
  Not(Ty),
  /// `(and A B C)` is an intersection type of `A, B, C`;
  /// `sizeof (and A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (and A B C)` iff
  /// `x :> A /\ x :> B /\ x :> C`. (Note that this is regular conjunction,
  /// not separating conjunction.)
  And(Box<[Ty]>),
  /// `(or A B C)` is an undiscriminated anonymous union of types `A, B, C`.
  /// `sizeof (or A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (or A B C)` iff
  /// `x :> A \/ x :> B \/ x :> C`.
  Or(Box<[Ty]>),
  /// `(or A B C)` is an undiscriminated anonymous union of types `A, B, C`.
  /// `sizeof (or A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (or A B C)` iff
  /// `x :> A \/ x :> B \/ x :> C`.
  If(Expr, Ty, Ty),
  /// `(ghost A)` is a computationally irrelevant version of `A`, which means
  /// that the logical storage of `(ghost A)` is the same as `A` but the physical storage
  /// is the same as `()`. `sizeof (ghost A) = 0`.
  Ghost(Ty),
  /// `(? T)` is the type of possibly-uninitialized `T`s. The typing predicate
  /// for this type is vacuous, but it has the same size as `T`, so overwriting with
  /// a `T` is possible.
  Uninit(Ty),
  /// A boolean expression, interpreted as a pure proposition
  Pure(Expr),
  /// A user-defined type-former.
  User(AtomId, Box<[Ty]>, Box<[Expr]>),
  /// A heap assertion `l |-> (v: |T|)`.
  Heap(Expr, Expr, Ty),
  /// An explicit typing assertion `[v : T]`.
  HasTy(Expr, Ty),
  /// The input token.
  Input,
  /// The output token.
  Output,
  /// A moved-away type.
  Moved(Ty),
  /// A type error that has been reported.
  Error,
}

impl Remap for TyKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      TyKind::Unit => TyKind::Unit,
      TyKind::True => TyKind::True,
      TyKind::False => TyKind::False,
      TyKind::Bool => TyKind::Bool,
      &TyKind::Var(v) => TyKind::Var(v),
      &TyKind::Int(ity) => TyKind::Int(ity),
      TyKind::Array(ty, n) => TyKind::Array(ty.remap(r), n.remap(r)),
      TyKind::Own(ty) => TyKind::Own(ty.remap(r)),
      TyKind::Ref(lft, ty) => TyKind::Ref(*lft, ty.remap(r)),
      TyKind::RefSn(e) => TyKind::RefSn(e.remap(r)),
      TyKind::List(tys) => TyKind::List(tys.remap(r)),
      TyKind::Sn(a, ty) => TyKind::Sn(a.remap(r), ty.remap(r)),
      TyKind::Struct(args) => TyKind::Struct(args.remap(r)),
      TyKind::All(v, pat, ty) => TyKind::All(*v, pat.remap(r), ty.remap(r)),
      TyKind::Imp(p, q) => TyKind::Imp(p.remap(r), q.remap(r)),
      TyKind::Wand(p, q) => TyKind::Wand(p.remap(r), q.remap(r)),
      TyKind::Not(p) => TyKind::Not(p.remap(r)),
      TyKind::And(ps) => TyKind::And(ps.remap(r)),
      TyKind::Or(ps) => TyKind::Or(ps.remap(r)),
      TyKind::If(c, t, e) => TyKind::If(c.remap(r), t.remap(r), e.remap(r)),
      TyKind::Ghost(ty) => TyKind::Ghost(ty.remap(r)),
      TyKind::Uninit(ty) => TyKind::Uninit(ty.remap(r)),
      TyKind::Pure(e) => TyKind::Pure(e.remap(r)),
      TyKind::User(f, tys, es) => TyKind::User(*f, tys.remap(r), es.remap(r)),
      TyKind::Heap(e, v, ty) =>
        TyKind::Heap(e.remap(r), v.remap(r), ty.remap(r)),
      TyKind::HasTy(e, ty) => TyKind::HasTy(e.remap(r), ty.remap(r)),
      TyKind::Input => TyKind::Input,
      TyKind::Output => TyKind::Output,
      TyKind::Moved(ty) => TyKind::Moved(ty.remap(r)),
      TyKind::Error => TyKind::Error,
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
  UpLe(Expr),
}

/// A variant is a pure expression, together with a
/// well founded order that decreases on all calls.
#[derive(Debug, DeepSizeOf)]
pub struct Variant(pub Expr, pub VariantType);

/// A pure expression. (Regular expressions are not manipulated like types,
/// i.e. copied and substituted around, so they are in the [`hir`](super::hir) module.)
pub type Expr = Rc<ExprKind>;

/// A pure expression. (Regular expressions are not manipulated like types,
/// i.e. copied and substituted around, so they are in the [`hir`](super::hir) module.)
pub type ExprTy = (Ty, Option<Expr>);

/// A pure expression.
#[derive(Debug, DeepSizeOf)]
pub enum ExprKind {
  /// A `()` literal.
  Unit,
  /// A variable reference.
  Var(VarId),
  /// A user constant.
  Const(AtomId),
  /// A number literal.
  Bool(bool),
  /// A number literal.
  Int(BigInt),
  /// A unary operation.
  Unop(Unop, Expr),
  /// A binary operation.
  Binop(Binop, Expr, Expr),
  /// An index operation `a[i]: T` where `a: (array T n)`
  /// and `i: nat`.
  Index(Expr, Expr),
  /// If `x: (array T n)`, then `x[a..a+b]: (array T b)`.
  Slice(Expr, Expr, Expr),
  /// A projection operation `x.i: T` where
  /// `x: (T0, ..., T(n-1))` or `x: {f0: T0, ..., f(n-1): T(n-1)}`.
  Proj(Expr, u32),
  /// `(update-index a i e)` is the result of `a` after `a[i] = e`.
  UpdateIndex(Expr, Expr, Expr),
  /// `(update-slice x a b e)` is the result of assigning `x[a..a+b] = e`.
  UpdateSlice(Expr, Expr, Expr, Expr),
  /// `(update-proj x i)` is the result of assigning `x.i = e`.
  UpdateProj(Expr, u32, Expr),
  /// `(e1, ..., en)` returns a tuple of the arguments.
  List(Box<[Expr]>),
  /// `[e1, ..., en]`, an array literal.
  Array(Box<[Expr]>),
  /// Return the size of a type.
  Sizeof(Ty),
  /// A pointer to a place.
  Ref(Expr),
  /// `(pure $e$)` embeds an MM0 expression `$e$` as the target type,
  /// one of the numeric types
  Mm0(Mm0Expr),
  /// A function call
  Call {
    /// The function to call.
    f: AtomId,
    /// The type arguments.
    tys: Box<[Ty]>,
    /// The function arguments.
    args: Box<[Expr]>,
  },
  /// An if-then-else expression (at either block or statement level). The initial atom names
  /// a hypothesis that the expression is true in one branch and false in the other.
  If {
    /// The if condition.
    cond: Expr,
    /// The then case.
    then: Expr,
    /// The else case.
    els: Expr
  },
  /// A type error that has been reported.
  Error,
}

impl Remap for ExprKind {
  type Target = Self;
  #[allow(clippy::many_single_char_names)]
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      ExprKind::Unit => ExprKind::Unit,
      &ExprKind::Var(v) => ExprKind::Var(v),
      &ExprKind::Const(c) => ExprKind::Const(c),
      &ExprKind::Bool(b) => ExprKind::Bool(b),
      ExprKind::Int(n) => ExprKind::Int(n.clone()),
      ExprKind::Unop(op, e) => ExprKind::Unop(*op, e.remap(r)),
      ExprKind::Binop(op, e1, e2) => ExprKind::Binop(*op, e1.remap(r), e2.remap(r)),
      ExprKind::Index(a, i) => ExprKind::Index(a.remap(r), i.remap(r)),
      ExprKind::Slice(a, i, l) => ExprKind::Slice(a.remap(r), i.remap(r), l.remap(r)),
      ExprKind::Proj(a, i) => ExprKind::Proj(a.remap(r), *i),
      ExprKind::UpdateIndex(a, i, v) => ExprKind::UpdateIndex(a.remap(r), i.remap(r), v.remap(r)),
      ExprKind::UpdateSlice(a, i, l, v) =>
        ExprKind::UpdateSlice(a.remap(r), i.remap(r), l.remap(r), v.remap(r)),
      ExprKind::UpdateProj(a, i, v) => ExprKind::UpdateProj(a.remap(r), *i, v.remap(r)),
      ExprKind::List(es) => ExprKind::List(es.remap(r)),
      ExprKind::Array(es) => ExprKind::Array(es.remap(r)),
      ExprKind::Sizeof(ty) => ExprKind::Sizeof(ty.remap(r)),
      ExprKind::Ref(e) => ExprKind::Ref(e.remap(r)),
      ExprKind::Mm0(e) => ExprKind::Mm0(e.remap(r)),
      &ExprKind::Call {f, ref tys, ref args} =>
        ExprKind::Call {f, tys: tys.remap(r), args: args.remap(r)},
      ExprKind::If {cond, then, els} => ExprKind::If {
        cond: cond.remap(r), then: then.remap(r), els: els.remap(r)},
      ExprKind::Error => ExprKind::Error,
    }
  }
}

/// A basic block ID, which is used to look up blocks in the [`Cfg`].
#[derive(Copy, Clone, Default, Debug)]
pub struct BlockId(u32);
crate::deep_size_0!(BlockId);

impl Remap for BlockId {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self { *self }
}

/// A collection of contexts, maintaining a tree structure. The underlying data structure is a list
/// of `CtxBuf` structs, each of which is a `CtxId` pointer to another context, plus an additional
/// list of variables and types. The context at index 0 is the root context, and is its own parent.
#[derive(Debug, DeepSizeOf)]
pub struct Contexts(Vec<CtxBuf>);

impl Remap for Contexts {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self { Self(self.0.remap(r)) }
}

impl Index<CtxBufId> for Contexts {
  type Output = CtxBuf;
  fn index(&self, index: CtxBufId) -> &Self::Output { &self.0[index.0 as usize] }
}
impl IndexMut<CtxBufId> for Contexts {
  fn index_mut(&mut self, index: CtxBufId) -> &mut Self::Output { &mut self.0[index.0 as usize] }
}
impl Default for Contexts {
  fn default() -> Self { Self(vec![CtxBuf::default()]) }
}

impl Contexts {
  /// Given a context ID, retrieve a context buffer, ensuring that it can be directly extended by
  /// allocating a new context buffer if necessary.
  #[allow(clippy::useless_transmute)]
  pub fn unshare(&mut self, id: &'_ mut CtxId) -> &mut CtxBuf {
    let mut ctx = &mut self[id.0];
    if ctx.vars.len() as u32 == id.1 {
      /// Safety: NLL case 3 (polonius validates this borrow pattern)
      unsafe { std::mem::transmute::<&mut CtxBuf, &mut CtxBuf>(ctx) }
    } else {
      let buf_id = CtxBufId(self.0.len() as u32);
      self.0.push(CtxBuf {parent: *id, vars: vec![]});
      *id = CtxId(buf_id, 1);
      unwrap_unchecked!(self.0.last_mut())
    }
  }

  /// Given a context, extend it with a variable and type to produce a new context.
  pub fn extend(&mut self, mut ctx: CtxId, var: VarId, ty: ExprTy) -> CtxId {
    self.unshare(&mut ctx).vars.push((var, ty));
    ctx
  }
}

/// A CFG, or control flow graph, for a function. This consists of a set of basic blocks,
/// with block ID 0 being the entry block. The `ctxs` is the context data used to supply the
/// logical context at the beginning of each basic block.
#[derive(Default, Debug, DeepSizeOf)]
pub struct Cfg {
  /// The set of logical contexts for the basic blocks.
  pub ctxs: Contexts,
  /// The set of basic blocks, containing the actual code.
  pub blocks: Vec<BasicBlock>,
}

impl Remap for Cfg {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Self { ctxs: self.ctxs.remap(r), blocks: self.blocks.remap(r) }
  }
}

impl Cfg {
  /// Start a new basic block with the given initial context. This block starts unfinished, that
  /// is, with an empty `Terminator`; the terminator must be filled by the time MIR construction is
  /// complete.
  pub fn new_block(&mut self, parent: CtxId) -> BlockId {
    let id = BlockId(self.blocks.len().try_into().expect("block overflow"));
    self.blocks.push(BasicBlock::new(parent, None));
    id
  }
}

/// A "context buffer ID", which points to one of the context buffers in the [`Contexts`] struct.
#[derive(Copy, Clone, Debug, Default, DeepSizeOf)]
pub struct CtxBufId(u32);

impl CtxBufId {
  /// The root context buffer is the first one; this is its own parent.
  pub const ROOT: Self = Self(0);
}

/// A context ID, which consists of a context buffer ID (which selects a context buffer from the
/// [`Contexts`]), plus an index into that buffer. The logical context denoted includes all
/// contexts in the parent chain up to the root, plus the selected context buffer up to the
/// specified index (which may be any number `<= buf.len()`).
#[derive(Copy, Clone, Debug, Default, DeepSizeOf)]
pub struct CtxId(CtxBufId, u32);

impl CtxId {
  /// The empty context.
  pub const ROOT: Self = Self(CtxBufId::ROOT, 0);
}

/// A context buffer.
#[derive(Default, Debug, DeepSizeOf)]
pub struct CtxBuf {
  /// The parent context, which this buffer is viewed as extending.
  pub parent: CtxId,
  /// The additional variables that this buffer adds to the context.
  pub vars: Vec<(VarId, ExprTy)>,
}

impl Remap for CtxBuf {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Self { parent: self.parent, vars: self.vars.remap(r) }
  }
}

/// A place is a location in memory that can be read and written to.
#[derive(Copy, Clone, Debug, DeepSizeOf)]
pub enum Place {
}

impl Remap for Place {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match *self {
    }
  }
}

/// An rvalue is an expression that can be used as the right hand side of an assignment;
/// most side-effect-free expressions fall in this category.
#[derive(Copy, Clone, Debug, DeepSizeOf)]
pub enum RValue {
}

impl Remap for RValue {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match *self {
    }
  }
}

/// A statement is an operation in a basic block that does not end the block. Generally this means
/// that it has simple control flow behavior, in that it always steps to the following statement
/// after performing some action that cannot fail.
#[derive(Copy, Clone, Debug, DeepSizeOf)]
pub struct Statement(pub StatementKind);

impl Remap for Statement {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self { Self(self.0.remap(r)) }
}

/// The different kinds of statement.
#[derive(Copy, Clone, Debug, DeepSizeOf)]
pub enum StatementKind {
  /// An assignment of an rvalue to a place, `p = rv;`
  Assign(Place, RValue),
}

impl Remap for StatementKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      Self::Assign(p, v) => Self::Assign(p.remap(r), v.remap(r))
    }
  }
}

/// A terminator is the final statement in a basic block. Anything with nontrivial control flow
/// is a terminator, and it determines where to jump afterward.
#[derive(Copy, Clone, Debug, DeepSizeOf)]
pub struct Terminator(pub TerminatorKind);

impl Remap for Terminator {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self { Self(self.0.remap(r)) }
}

/// The different kinds of terminator statement.
#[derive(Clone, Copy, Debug, DeepSizeOf)]
pub enum TerminatorKind {
  /// A `goto label;` statement - unconditionally jump to the basic block `label`.
  Goto(BlockId),
}

impl Remap for TerminatorKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match *self {
      Self::Goto(id) => Self::Goto(id),
    }
  }
}

/// A basic block, which consists of an initial context (containing the logical parameters to the
/// block), followed by a list of statements, and ending with a terminator. The terminator is
/// optional only during MIR construction, and represents an "unfinished" block.
#[derive(Debug, DeepSizeOf)]
pub struct BasicBlock {
  /// The initial context on entry to the block.
  pub ctx: CtxId,
  /// The list of statements, which may extend the context.
  pub stmts: Vec<Statement>,
  /// The final statement, which may jump to another basic block or perform another control flow
  /// function.
  pub term: Option<Terminator>,
}

impl Remap for BasicBlock {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Self { ctx: self.ctx, stmts: self.stmts.remap(r), term: self.term.remap(r) }
  }
}

impl BasicBlock {
  fn new(ctx: CtxId, term: Option<Terminator>) -> Self {
    Self { ctx, stmts: vec![], term }
  }
}

/// A procedure (or function or intrinsic), a top level item similar to function declarations in C.
#[derive(Debug, DeepSizeOf)]
pub struct Proc {
  /// The type of declaration: `func`, `proc`, or `intrinsic`.
  kind: ProcKind,
  /// The name of the procedure.
  name: Spanned<AtomId>,
  /// The number of type arguments
  tyargs: u32,
  /// The arguments of the procedure.
  args: Vec<Arg>,
  /// The return values of the procedure. (Functions and procedures return multiple values in MMC.)
  rets: Vec<Arg>,
  /// The body of the procedure.
  body: Cfg,
}

impl Remap for Proc {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Self {
      kind: self.kind,
      name: self.name.remap(r),
      tyargs: self.tyargs,
      args: self.args.remap(r),
      rets: self.rets.remap(r),
      body: self.body.remap(r),
    }
  }
}
