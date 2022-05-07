//! Type inference and elaboration
#![allow(clippy::needless_collect)]

use std::borrow::{Borrow, Cow};
use std::{cell::RefCell, fmt::Debug, hash::{Hash, Hasher}, mem, ops::Index};
use bumpalo::Bump;
use std::collections::{HashMap, HashSet, hash_map::Entry};
use itertools::Itertools;
use num::Signed;
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;
use types::IntTy;
use crate::types::hir::CastKind;
use crate::{Config, FileSpan, ItemContext, Symbol, alphanumber, u32_as_usize};
use super::types;
use types::{Binop, BinopType, FieldName, Idx, IdxVec, LambdaId, ProofId,
  Size, Spanned, Unop, VarId, ast, global, hir};
use ast::{ProcKind, ArgAttr};
use global::{ToGlobal, ToGlobalCtx};
use hir::{GenId, ListKind, ReturnKind};
use types::entity::{Entity, ConstTc, GlobalTc, ProcTy, ProcTc, TypeTc, TypeTy};
use super::union_find::{UnifyCtx, UnificationTable};
#[allow(clippy::wildcard_imports)] use super::types::ty::*;

/// The possible errors that can occur during type inference and type checking.
#[derive(Debug)]
pub enum TypeError<'a> {
  /// Failed to pattern match type T with the given pattern of type U
  PatternMatch(Ty<'a>, Ty<'a>),
  /// Failed to relate type T to type U according to the relation
  Relate(Ty<'a>, Ty<'a>, Relation),
  /// Expected a pure expression (for the operation at this span)
  ExpectedPure(&'a FileSpan),
  /// Expected a struct expression
  ExpectedStruct(Ty<'a>),
  /// Expected a pointer expression
  ExpectedPtr,
  /// Expected a place expression
  ExpectedPlace,
  /// Expected a type ascription
  ExpectedType,
  /// Could not infer type
  UninferredType,
  /// Could not infer expression
  UninferredExpr,
  /// Struct does not have this field
  FieldMissing(Ty<'a>, FieldName),
  /// Expected `x` args, found `y`
  NumArgs(usize, usize),
  /// `as` conversion from `T` to `U` not supported
  UnsupportedAs(Ty<'a>, Ty<'a>),
  /// Cannot assign to this lvalue
  UnsupportedAssign,
  /// Missing `with` clause for assignment
  MissingAssignWith(VarId),
  /// Provided expressions x and y do not unify in an and-intro expression
  IAndUnify(Expr<'a>, Expr<'a>),
  /// An explicit hole expression, which queries for the full type context.
  /// (This form assumes we don't have an expected expression, else we would just fill it in.)
  Hole(Box<DynContext<'a>>, Option<Ty<'a>>),
  /// Don't know how to evaluate this expression
  UnsupportedSynthesis(Box<DynContext<'a>>, Expr<'a>, Ty<'a>),
  /// Can't match on a place
  UnsupportedPlaceMatch,
  /// Can't use return in this position
  InvalidReturn,
  /// While loop mutates a value without marking it as `mut` in the loop header
  MissingMuts(Vec<VarId>),
  /// A `(variant h)` clause was provided to a function or label that does not declare a variant
  UnexpectedVariant,
  /// More than one `main` function defined
  DoubleMain,
}

impl<'a, C: DisplayCtx<'a>> CtxDisplay<C> for TypeError<'a> {
  fn fmt(&self, ctx: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    macro_rules! p {($e:expr) => {CtxPrint(ctx, $e)}}
    match *self {
      TypeError::PatternMatch(t1, t2) => write!(f,
        "Failed to pattern match type\n  {}\n \
        with the given pattern of type\n  {}",
        p!(t1), p!(t2)),
      TypeError::Relate(t1, t2, Relation::Equal) => write!(f,
        "Type mismatch: type\n  {}\nis not equal to type\n  {}", p!(t1), p!(t2)),
      TypeError::Relate(t1, t2, Relation::Subtype) => write!(f,
        "Type mismatch: type\n  {}\nis not a subtype of\n  {}", p!(t1), p!(t2)),
      TypeError::Relate(t1, t2, Relation::SubtypeEqSize) => write!(f,
        "Type mismatch: type\n  {}\nis not a binary compatible subtype of\n  {}", p!(t1), p!(t2)),
      TypeError::Relate(t1, t2, Relation::Coerce) => write!(f,
        "Type mismatch: type\n  {}\nis not coercible to\n  {}", p!(t1), p!(t2)),
      TypeError::ExpectedPure(_) => write!(f, "Expected a pure expression"),
      TypeError::ExpectedStruct(t) => write!(f, "Expected a struct expression, got\n  {}", p!(t)),
      TypeError::ExpectedPtr => write!(f, "Expected a pointer expression"),
      TypeError::ExpectedPlace => write!(f, "Expected a place expression"),
      TypeError::ExpectedType => write!(f, "Can't infer type, try inserting a type ascription"),
      TypeError::UninferredType => write!(f, "Can't infer type"),
      TypeError::UninferredExpr => write!(f, "Can't infer expression"),
      TypeError::FieldMissing(t, name) => write!(f, "Struct\n  {}\ndoes not have field '{}'",
        p!(t), name),
      TypeError::NumArgs(want, got) => write!(f, "expected {} arguments, got {}", want, got),
      TypeError::UnsupportedAs(t1, t2) => write!(f,
        "{} as {} conversion not supported", p!(t1), p!(t2)),
      TypeError::UnsupportedAssign => write!(f, "Cannot assign to this lvalue"),
      TypeError::MissingAssignWith(v) => write!(f,
        "Missing 'with' clause for assignment. Try inserting {{... with {}}}", p!(&v)),
      TypeError::IAndUnify(e1, e2) => write!(f,
        "And introduction expression mismatch:\n  {}\n!=\n  {}\n\
        Note: and-intro requires all expressions evaluate to the same value", p!(e1), p!(e2)),
      TypeError::Hole(ref dc, None) => write!(f, "{}|- ?", p!(&**dc)),
      TypeError::Hole(ref dc, Some(t)) => write!(f, "{}|- {}", p!(&**dc), p!(t)),
      TypeError::UnsupportedSynthesis(ref dc, e, t) => write!(f, "{}|- {}\n:= {}\n\
        Note: the target expression is known but we don't know how to evaluate it",
        p!(&**dc), p!(t), p!(e)),
      TypeError::UnsupportedPlaceMatch => write!(f, "Can't match on a place"),
      TypeError::InvalidReturn => write!(f, "Can't use return in this position"),
      TypeError::MissingMuts(ref muts) => write!(f, "\
        While loop mutates a value without marking it as 'mut' in the loop header. \
        Try adding:\n  (mut {})", muts.iter().unique().map(|v| p!(v)).format(" ")),
      TypeError::UnexpectedVariant => write!(f, "A (variant h) clause was provided \
        to a function or label that does not declare a variant"),
      TypeError::DoubleMain => write!(f, "The `main` function has been defined more than once"),
    }
  }
}

/// A context is a singly linked list of logical variable declarations.
/// The collection of all contexts forms a tree.
#[derive(Copy, Clone, Debug)]
struct Context<'a>(Option<&'a ContextNext<'a>>);

/// A nonempty context extends a context by a single variable declaration.
#[derive(Copy, Clone, Debug)]
struct ContextNext<'a> {
  /// The total number of variables in this context.
  len: u32,
  /// The variable name.
  var: VarId,
  /// The variable's generation ID.
  gen: GenId,
  /// The variable's value.
  val: Expr<'a>,
  /// The variable's type.
  ty: Ty<'a>,
  /// The parent context, which this context extends.
  parent: Context<'a>,
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
  const ROOT: Self = Context(None);

  /// The length of a context (the number of variables).
  #[must_use] fn len(self) -> u32 {
    if let Some(c) = &self.0 {c.len} else {0}
  }

  /// The parent context, or `ROOT` if the context is already root.
  #[must_use] fn parent(self) -> Self {
    if let Some(c) = &self.0 {c.parent} else {Self::ROOT}
  }

  /// The greatest lower bound of two contexts, i.e. the largest
  /// context of which both `self` and `other` are descended.
  #[must_use] fn glb(mut self, mut other: Self) -> Self {
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
  #[must_use] fn find(mut self, v: VarId) -> Option<&'a ContextNext<'a>> {
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
#[must_use] #[derive(Debug)]
struct ContextIter<'a>(Option<&'a ContextNext<'a>>);

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
  #[must_use] fn new(
    parent: Context<'a>, v: VarId,
    gen: GenId, val: Expr<'a>, ty: Ty<'a>
  ) -> Self {
    Self {len: parent.len() + 1, var: v, gen, val, ty, parent}
  }
}

#[derive(Copy, Clone, Debug)]
struct Interned<T>(T);

impl<T: PartialEq> PartialEq for Interned<&WithMeta<T>> {
  fn eq(&self, other: &Self) -> bool { self.0.k == other.0.k }
}
impl<T: Eq> Eq for Interned<&WithMeta<T>> {}
impl<T: Hash> Hash for Interned<&WithMeta<T>> {
  fn hash<H: Hasher>(&self, s: &mut H) { self.0.k.hash(s) }
}
impl<T> Borrow<T> for Interned<&WithMeta<T>> {
  fn borrow(&self) -> &T { &self.0.k }
}

type InternedSet<T> = hashbrown::HashMap<Interned<T>, ()>;

trait Internable<'a>: Sized + Eq + Hash + AddFlags {
  fn get<'b>(_: &'b Interner<'a>) -> &'b InternedSet<&'a WithMeta<Self>>;
  fn get_mut<'b>(_: &'b mut Interner<'a>) -> &'b mut InternedSet<&'a WithMeta<Self>>;
}

macro_rules! mk_interner {($($field:ident: $ty:ident,)*) => {
  #[derive(Debug, Default)]
  struct Interner<'a> {
    $($field: InternedSet<&'a WithMeta<$ty<'a>>>,)*
  }

  $(impl<'a> Internable<'a> for $ty<'a> {
    fn get<'b>(i: &'b Interner<'a>) -> &'b InternedSet<&'a WithMeta<Self>> { &i.$field }
    fn get_mut<'b>(i: &'b mut Interner<'a>) -> &'b mut InternedSet<&'a WithMeta<Self>> { &mut i.$field }
  })*
}}

mk_interner! {
  tups: TuplePatternS,
  args: ArgS,
  tys: TyKind,
  exprs: ExprKind,
  places: PlaceKind,
}

impl<'a> Interner<'a> {
  fn intern<T: Internable<'a>>(&mut self, alloc: &'a Bump, t: T) -> &'a WithMeta<T> {
    use hashbrown::hash_map::RawEntryMut;
    match T::get_mut(self).raw_entry_mut().from_key(&t) {
      RawEntryMut::Occupied(e) => e.key().0,
      RawEntryMut::Vacant(e) =>
        e.insert(Interned(alloc.alloc(WithMeta::new(t))), ()).0 .0,
    }
  }
}

macro_rules! intern {($ctx:expr, $t:expr) => {{let t = $t; $ctx.intern(t)}}}

#[derive(Debug)]
pub(crate) struct MVarData<'a> {
  span: &'a FileSpan,
}

#[derive(Copy, Clone, Debug)]
enum MVarValue<'a, T> {
  Assigned(T),
  Unassigned(Context<'a>),
}

impl<'a, T: PartialEq + Copy> UnifyCtx<MVarValue<'a, T>> for () {
  type Error = (T, T);

  fn unify_values(&mut self,
    &value1: &MVarValue<'a, T>, &value2: &MVarValue<'a, T>
  ) -> Result<MVarValue<'a, T>, Self::Error> {
    match (value1, value2) {
      (MVarValue::Assigned(ty1), MVarValue::Assigned(ty2)) =>
        if ty1 == ty2 { Ok(value1) } else { Err((ty1, ty2)) },
      (MVarValue::Assigned(_), MVarValue::Unassigned(_)) => Ok(value1),
      (MVarValue::Unassigned(_), MVarValue::Assigned(_)) => Ok(value2),
      (MVarValue::Unassigned(u1), MVarValue::Unassigned(u2)) =>
        Ok(MVarValue::Unassigned(u1.glb(u2)))
    }
  }
}

#[derive(Debug)]
pub(crate) struct Assignments<'a, K, V> {
  mvars: IdxVec<K, MVarData<'a>>,
  table: UnificationTable<K, MVarValue<'a, V>>,
}
impl<K, V> Default for Assignments<'_, K, V> {
  fn default() -> Self { Self { mvars: Default::default(), table: Default::default() } }
}

impl<'a, K: Idx, V> Assignments<'a, K, V> {
  fn new_mvar(&mut self, span: &'a FileSpan, ctx: Context<'a>) -> K {
    let n = K::from_usize(self.mvars.len());
    self.mvars.push(MVarData {span});
    self.table.new_key(MVarValue::Unassigned(ctx));
    n
  }

  fn root(&mut self, k: K) -> K { self.table.find(k) }

  fn equate(&mut self, k1: K, k2: K) where V: PartialEq + Copy {
    self.table.unify_var_var(&mut (), k1, k2)
      .ok().expect("assigning to assigned variable");
  }

  fn assign(&mut self, k: K, v: V) where V: PartialEq + Copy {
    self.table.unify_var_value(&mut (), k, &MVarValue::Assigned(v))
      .ok().expect("assigning to assigned variable");
  }

  pub(crate) fn lookup(&mut self, k: K) -> Option<V> where V: Copy {
    match self.table.probe_value(k) {
      MVarValue::Assigned(v) => Some(*v),
      MVarValue::Unassigned(_) => None,
    }
  }
}

impl<'a, K: Idx, V> Index<K> for Assignments<'a, K, V> {
  type Output = MVarData<'a>;
  fn index(&self, k: K) -> &Self::Output { &self.mvars[k] }
}

impl Unop {
  // #[must_use] fn arg_ty<'a>(self, ctx: &mut InferCtx<'a, '_>) -> Ty<'a> {
  //   match self {
  //     Unop::Not => ctx.common.t_bool,
  //     Unop::Neg |
  //     Unop::BitNot(Size::Inf) |
  //     Unop::As(_) => ctx.common.int(),
  //     Unop::BitNot(sz) => ctx.common.t_uint(sz),
  //   }
  // }
  #[must_use] fn ret_ty<'a>(self, ctx: &mut InferCtx<'a, '_>) -> Ty<'a> {
    match self {
      Unop::Not => ctx.common.t_bool,
      Unop::Neg | Unop::BitNot(Size::Inf) => ctx.common.int(),
      Unop::BitNot(sz) => ctx.common.t_uint(sz),
      Unop::As(ity) => ctx.common.int_ty(ity),
    }
  }
}

/// A partially elaborated tuple pattern.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
struct UnelabTupPat<'a> {
  /// The span of the pattern.
  span: &'a FileSpan,
  /// A context ending in the variable introduced in this pattern.
  ctx: &'a ContextNext<'a>,
  /// The pattern kind, see [`UnelabTupPatKind`].
  k: UnelabTupPatKind<'a>,
}

/// A partially elaborated tuple pattern.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
enum UnelabTupPatKind<'a> {
  /// A simple pattern, containing the actual binding in the [`ContextNext`].
  Name(bool, Symbol),
  /// An unelaborated tuple pattern match. The subpatterns are elaborated with metavariable types,
  /// but we don't yet know how to connect this list of types to the target type - for example
  /// the target type could be a metavariable, and propagating our default guess of a nondependent
  /// tuple could cause a type error if it turns out to be a dependent tuple.
  Tuple(Vec<UnelabTupPat<'a>>),
  /// A failed tuple pattern match.
  Error(Box<UnelabTupPat<'a>>),
}

impl<'a> UnelabTupPat<'a> {
  /// Calls function `f` on all variables in the pattern, in right-to-left order.
  fn on_vars_rev(&self, f: &mut impl FnMut(VarId)) {
    match &self.k {
      &UnelabTupPatKind::Name(..) => {}
      UnelabTupPatKind::Tuple(pats) => for pat in pats.iter().rev() { pat.on_vars_rev(f) }
      UnelabTupPatKind::Error(pat) => pat.on_vars_rev(f),
    }
    f(self.ctx.var)
  }
}

/// An argument in a `struct` or function parameters.
type UnelabArg<'a> = (ArgAttr, UnelabArgKind<'a>);
/// An argument in a `struct` or function parameters.
#[derive(Debug)]
enum UnelabArgKind<'a> {
  /// The usual lambda binder: `x: T`.
  Lam(UnelabTupPat<'a>),
  /// A definition binder: `x: T := e`.
  Let(UnelabTupPat<'a>, Expr<'a>, Option<Box<hir::Expr<'a>>>),
}

impl<'a> UnelabArgKind<'a> {
  /// The variable part of the argument.
  #[must_use] fn var(&self) -> &UnelabTupPat<'a> {
    match self { UnelabArgKind::Lam(pat) | UnelabArgKind::Let(pat, ..) => pat }
  }
}

/// The data for an individual label in a label group. We keep this data structure around while
/// evaluating later statements in the block, and finalize it into a [`hir::Stmt::Label`] when
/// exiting the block.
#[derive(Debug)]
struct UnelabLabelData<'a> {
  /// The context just inside the label (including the label arguments)
  ctx: Context<'a>,
  /// The body of the label
  body: &'a Spanned<ast::Block>,
  /// The final list of arguments
  args: Box<[hir::Arg<'a>]>
}

/// A statement in a block.
#[derive(Debug)]
enum UnelabStmt<'a> {
  /// A let binding.
  Let {
    /// A tuple pattern, containing variable bindings.
    lhs: UnelabTupPat<'a>,
    /// The expression to evaluate.
    rhs: hir::Expr<'a>,
  },
  /// An expression to be evaluated for its side effects, with the result being discarded.
  Expr((hir::ExprKind<'a>, ExprTy<'a>)),
  /// A label, which looks exactly like a local function but has no independent stack frame.
  /// They are called like regular functions but can only appear in tail position.
  Label(VarId, Box<[UnelabLabelData<'a>]>),
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct WhnfTy<'a> {
  uninit: bool,
  ghost: bool,
  moved: bool,
  ty: Ty<'a>,
}

impl Debug for WhnfTy<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.moved { write!(f, "|")? }
    if self.ghost { write!(f, "ghost(")? }
    if self.uninit { write!(f, "Uninit(")? }
    write!(f, "{:?}", self.ty)?;
    if self.uninit { write!(f, ")")? }
    if self.ghost { write!(f, ")")? }
    if self.moved { write!(f, "|")? }
    Ok(())
  }
}
impl<'a> WhnfTy<'a> {
  fn to_ty(mut self, ctx: &mut InferCtx<'a, '_>) -> Ty<'a> {
    if self.moved { self.ty = intern!(ctx, TyKind::Moved(self.ty)) }
    if self.ghost { self.ty = intern!(ctx, TyKind::Ghost(self.ty)) }
    if self.uninit { self.ty = intern!(ctx, TyKind::Uninit(self.ty)) }
    self.ty
  }
  fn is_ty(self) -> bool { !self.uninit && !self.moved && !self.ghost }
  fn moved(mut self, m: bool) -> Self { self.moved |= m; self }
  // fn ghost(mut self) -> Self { self.ghost = true; self }
  // fn uninit(mut self) -> Self { self.uninit = true; self }
  fn map(mut self, ty: Ty<'a>) -> Self { self.ty = ty; self }
}

impl<'a> From<Ty<'a>> for WhnfTy<'a> {
  fn from(ty: Ty<'a>) -> Self {
    let mut ret = Self {ghost: false, uninit: false, moved: false, ty};
    loop {
      match ret.ty.k {
        TyKind::Ghost(ty2) => {ret.ty = ty2; ret.ghost = true}
        TyKind::Uninit(ty2) => {ret.ty = ty2; ret.uninit = true}
        TyKind::Moved(ty2) => {ret.ty = ty2; ret.moved = true}
        _ => return ret
      }
    }
  }
}

#[derive(Clone, Default, Debug)]
struct Subst<'a> {
  tsubst: Option<Vec<Ty<'a>>>,
  fvars: im::HashSet<VarId>,
  subst: im::HashMap<VarId, Result<Expr<'a>, &'a FileSpan>>,
}

impl<'a> Subst<'a> {
  fn push_raw(&mut self, v: VarId, e: Result<Expr<'a>, &'a FileSpan>) {
    assert!(self.subst.insert(v, e).is_none())
  }

  fn add_fvars(&mut self, e: Result<Expr<'a>, &'a FileSpan>) {
    if let Ok(e) = e { e.on_vars(|v| { self.fvars.insert(v); }) }
  }

  fn add_fvars_place(&mut self, e: Place<'a>) { e.on_vars(|v| { self.fvars.insert(v); }) }

  fn push_tuple_pattern_raw(&mut self, ctx: &mut InferCtx<'a, '_>, sp: &'a FileSpan,
    pat: TuplePattern<'a>, e: Result<Expr<'a>, &'a FileSpan>
  ) {
    match pat.k.k {
      TuplePatternKind::Name(_) => {},
      TuplePatternKind::Error(pat) => self.push_tuple_pattern_raw(ctx, sp, pat, e),
      TuplePatternKind::Tuple(pats, mk) => {
        for (i, &pat) in pats.iter().enumerate() {
          let e = e.map(|e| mk.proj(ctx, sp, e, pats.len(), i.try_into().expect("overflow")));
          self.push_tuple_pattern_raw(ctx, sp, pat, e)
        }
      }
    }
    self.push_raw(pat.k.var, e)
  }

  fn push_tuple_pattern(&mut self, ctx: &mut InferCtx<'a, '_>, sp: &'a FileSpan,
    pat: TuplePattern<'a>, e: Result<Expr<'a>, &'a FileSpan>
  ) {
    self.add_fvars(e);
    self.push_tuple_pattern_raw(ctx, sp, pat, e);
  }

  fn subst_var(&mut self, ctx: &mut InferCtx<'a, '_>, sp: &'a FileSpan, v: VarId) -> Option<Expr<'a>> {
    if let im::hashmap::Entry::Occupied(mut e) = self.subst.entry(v) {
      let res = e.get_mut();
      Some(match *res {
        Ok(val) => val,
        Err(span) => {
          ctx.errors.push(hir::Spanned {span, k: TypeError::ExpectedPure(sp)});
          *res = Ok(ctx.common.e_error);
          ctx.common.e_error
        }
      })
    } else { None }
  }

  fn subst_place(&mut self, ctx: &mut InferCtx<'a, '_>, sp: &'a FileSpan, e: Place<'a>) -> Place<'a> {
    macro_rules! subst {($op:expr, $p:expr, $ty:expr $(, $es:expr)*) => {{
      let p2 = self.subst_place(ctx, sp, $p);
      let ty2 = self.subst_ty(ctx, sp, $ty);
      let e2 = ($(self.subst_expr(ctx, sp, $es)),*);
      if $p == p2 && $ty == ty2 && ($($es),*) == e2 { return e }
      intern!(ctx, $op(p2, ty2, e2))
    }}}
    match e.k {
      PlaceKind::Var(v) => match self.subst_var(ctx, sp, v) {
        Some(&WithMeta {k: ExprKind::Ref(pl), ..}) => pl,
        _ => intern!(ctx, PlaceKind::Error),
      },
      PlaceKind::Index(a, ty, i) => subst!(PlaceKind::Index, a, ty, i),
      PlaceKind::Slice(a, ty, [i, l]) =>
        subst!(|a, ty, (i, l)| PlaceKind::Slice(a, ty, [i, l]), a, ty, i, l),
      PlaceKind::Proj(e, ty, i) => subst!(|e, ty, ()| PlaceKind::Proj(e, ty, i), e, ty),
      PlaceKind::Error => e,
    }
  }

  fn subst_expr(&mut self, ctx: &mut InferCtx<'a, '_>, sp: &'a FileSpan, e: Expr<'a>) -> Expr<'a> {
    macro_rules! subst {($op:expr, $($es:expr),*) => {{
      let e2 = ($(self.subst_expr(ctx, sp, $es)),*);
      if ($($es),*) == e2 { return e }
      intern!(ctx, $op(e2))
    }}}
    match e.k {
      ExprKind::Var(v) => self.subst_var(ctx, sp, v).unwrap_or(e),
      ExprKind::Unit |
      ExprKind::Const(_) |
      ExprKind::Bool(_) |
      ExprKind::Int(_) |
      ExprKind::Error => e,
      ExprKind::Unop(op, e) =>
        subst!(|e| ExprKind::Unop(op, e), e),
      ExprKind::Binop(op, e1, e2) =>
        subst!(|(e1, e2)| ExprKind::Binop(op, e1, e2), e1, e2),
      ExprKind::Index(e1, e2) =>
        subst!(|(e1, e2)| ExprKind::Index(e1, e2), e1, e2),
      ExprKind::Slice([e1, e2, e3]) =>
        subst!(|(e1, e2, e3)| ExprKind::Slice([e1, e2, e3]), e1, e2, e3),
      ExprKind::Proj(e, i) =>
        subst!(|e| ExprKind::Proj(e, i), e),
      ExprKind::UpdateIndex([e1, e2, e3]) =>
        subst!(|(e1, e2, e3)| ExprKind::UpdateIndex([e1, e2, e3]), e1, e2, e3),
      ExprKind::UpdateSlice([e1, e2, e3, e4]) =>
        subst!(|(e1, e2, e3, e4)| ExprKind::UpdateSlice([e1, e2, e3, e4]), e1, e2, e3, e4),
      ExprKind::UpdateProj(e1, i, e2) =>
        subst!(|(e1, e2)| ExprKind::UpdateProj(e1, i, e2), e1, e2),
      ExprKind::List(es) => {
        let es2 = es.iter().map(|e| self.subst_expr(ctx, sp, e)).collect::<Vec<_>>();
        if es == es2 { return e }
        intern!(ctx, ExprKind::List(ctx.alloc.alloc_slice_fill_iter(es2.into_iter())))
      }
      ExprKind::Array(es) => {
        let es2 = es.iter().map(|e| self.subst_expr(ctx, sp, e)).collect::<Vec<_>>();
        if es == es2 { return e }
        intern!(ctx, ExprKind::Array(ctx.alloc.alloc_slice_fill_iter(es2.into_iter())))
      }
      ExprKind::Ref(p) => {
        let p2 = self.subst_place(ctx, sp, p);
        if p == p2 { return e }
        intern!(ctx, ExprKind::Ref(p2))
      }
      ExprKind::Sizeof(ty) => {
        let ty2 = self.subst_ty(ctx, sp, ty);
        if ty == ty2 { return e }
        intern!(ctx, ExprKind::Sizeof(ty2))
      }
      ExprKind::Mm0(Mm0Expr {subst, expr}) => {
        let subst2 = subst.iter().map(|e| self.subst_expr(ctx, sp, e)).collect::<Vec<_>>();
        if subst == subst2 { return e }
        let subst = ctx.alloc.alloc_slice_fill_iter(subst2.into_iter());
        intern!(ctx, ExprKind::Mm0(Mm0Expr {subst, expr}))
      }
      ExprKind::Call {f, tys, args} => {
        let tys2 = tys.iter().map(|e| self.subst_ty(ctx, sp, e)).collect::<Vec<_>>();
        let args2 = args.iter().map(|e| self.subst_expr(ctx, sp, e)).collect::<Vec<_>>();
        if tys == tys2 && args == args2 { return e }
        let tys = ctx.alloc.alloc_slice_fill_iter(tys2.into_iter());
        let args = ctx.alloc.alloc_slice_fill_iter(args2.into_iter());
        intern!(ctx, ExprKind::Call {f, tys, args})
      }
      ExprKind::If {cond, then, els} =>
        subst!(|(cond, then, els)| ExprKind::If {cond, then, els}, cond, then, els),
      ExprKind::Infer(v) => {
        if let Some(ty) = ctx.mvars.expr.lookup(v) { return self.subst_expr(ctx, sp, ty) }
        let span = ctx.mvars.expr[v].span;
        ctx.errors.push(hir::Spanned {span, k: TypeError::ExpectedType});
        ctx.mvars.expr.assign(v, ctx.common.e_error);
        ctx.common.e_error
      }
    }
  }

  fn subst_lft(&mut self,
    ctx: &mut InferCtx<'a, '_>, span: &'a FileSpan, lft: Lifetime
  ) -> Option<Lifetime> {
    Some(match lft {
      Lifetime::Extern => lft,
      Lifetime::Place(v) => if let Some(mut origin) = self.subst_var(ctx, span, v) {
        loop {
          match origin.k {
            ExprKind::Var(v) => break Lifetime::Place(v),
            ExprKind::Index(a, _) |
            ExprKind::Slice([a, _, _]) |
            ExprKind::Proj(a, _) => origin = a,
            ExprKind::Error => return None,
            ExprKind::Infer(_) => {
              ctx.errors.push(hir::Spanned {span, k: TypeError::ExpectedType});
              return None
            }
            _ => {
              ctx.errors.push(hir::Spanned {span, k: TypeError::ExpectedPlace});
              return None
            }
          }
        }
      } else { lft },
      Lifetime::Infer(v) => {
        if let Some(lft) = ctx.mvars.lft.lookup(v) { return self.subst_lft(ctx, span, lft) }
        ctx.new_lft_mvar(ctx.mvars.lft[v].span)
      }
    })
  }

  fn subst_tup_pat(&mut self,
    ctx: &mut InferCtx<'a, '_>, sp: &'a FileSpan, pat: TuplePattern<'a>
  ) -> TuplePattern<'a> {
    let ty2 = self.subst_ty(ctx, sp, pat.k.ty);
    let v = pat.k.var;
    let v2 = if self.fvars.contains(&v) {
      let w = ctx.fresh_var2(v);
      self.subst.insert(v, Ok(intern!(ctx, ExprKind::Var(w))));
      w
    } else { v };
    self.fvars.insert(v2);
    let unchanged = v == v2 && pat.k.ty == ty2;
    let k = match pat.k.k {
      TuplePatternKind::Name(g) => {
        if unchanged { return pat }
        TuplePatternKind::Name(g)
      }
      TuplePatternKind::Tuple(pats, mk) => {
        let pats2 = pats.iter().map(|&pat| self.subst_tup_pat(ctx, sp, pat)).collect::<Vec<_>>();
        if unchanged && pats == pats2 { return pat }
        let pats2 = ctx.alloc.alloc_slice_fill_iter(pats2.into_iter());
        TuplePatternKind::Tuple(pats2, mk)
      }
      TuplePatternKind::Error(p) => {
        let p2 = self.subst_tup_pat(ctx, sp, p);
        if unchanged && p == p2 { return pat }
        TuplePatternKind::Error(p2)
      }
    };
    intern!(ctx, TuplePatternS { var: v2, k, ty: ty2 })
  }

  fn subst_arg(&mut self, ctx: &mut InferCtx<'a, '_>, sp: &'a FileSpan, arg: Arg<'a>) -> Arg<'a> {
    match arg.k.1 {
      ArgKind::Lam(pat) => {
        let pat2 = self.subst_tup_pat(ctx, sp, pat);
        if pat == pat2 { return arg }
        intern!(ctx, (arg.k.0, ArgKind::Lam(pat2)))
      }
      ArgKind::Let(pat, e) => {
        let e2 = self.subst_expr(ctx, sp, e);
        let pat2 = self.subst_tup_pat(ctx, sp, pat);
        if pat == pat2 && e == e2 { return arg }
        intern!(ctx, (arg.k.0, ArgKind::Let(pat2, e2)))
      }
    }
  }

  fn subst_ty(&mut self, ctx: &mut InferCtx<'a, '_>, sp: &'a FileSpan, ty: Ty<'a>) -> Ty<'a> {
    macro_rules! subst {($op:expr; $($tys:expr),*; $($es:expr),*) => {{
      let ty2 = ($(self.subst_ty(ctx, sp, $tys)),*);
      let e2 = ($(self.subst_expr(ctx, sp, $es)),*);
      if ($($tys),*) == ty2 && ($($es),*) == e2 { return ty }
      intern!(ctx, $op(ty2, e2))
    }}}
    macro_rules! substs {($op:expr; $tys:expr) => {{
      let tys2 = $tys.iter().map(|e| self.subst_ty(ctx, sp, e)).collect::<Vec<_>>();
      if $tys == tys2 { return ty }
      let tys2 = ctx.alloc.alloc_slice_fill_iter(tys2.into_iter());
      intern!(ctx, $op(tys2))
    }}}
    match ty.k {
      TyKind::Var(v) =>
        if let Some(tsubst) = &self.tsubst { tsubst[u32_as_usize(v)] } else { ty },
      TyKind::Unit |
      TyKind::True |
      TyKind::False |
      TyKind::Bool |
      TyKind::Int(_) |
      TyKind::Input |
      TyKind::Output |
      TyKind::Error => ty,
      TyKind::Array(t, e) => subst!(TyKind::Array; t; e),
      TyKind::Own(t) => subst!(|t, _| TyKind::Own(t); t;),
      TyKind::Shr(lft, t) => {
        let lft2 =
          if let Some(lft2) = self.subst_lft(ctx, sp, lft) { lft2 }
          else { return ctx.common.t_error };
        let t2 = self.subst_ty(ctx, sp, t);
        if lft == lft2 && t == t2 { return ty }
        intern!(ctx, TyKind::Shr(lft2, t2))
      }
      TyKind::Ref(lft, t) => {
        let lft2 =
          if let Some(lft2) = self.subst_lft(ctx, sp, lft) { lft2 }
          else { return ctx.common.t_error };
        let t2 = self.subst_ty(ctx, sp, t);
        if lft == lft2 && t == t2 { return ty }
        intern!(ctx, TyKind::Ref(lft2, t2))
      }
      TyKind::RefSn(p) => {
        let p2 = self.subst_place(ctx, sp, p);
        if p == p2 { return ty }
        intern!(ctx, TyKind::RefSn(p2))
      }
      TyKind::List(tys) => substs!(TyKind::List; tys),
      TyKind::Sn(e, ty) => subst!(|ty, e| TyKind::Sn(e, ty); ty; e),
      TyKind::Struct(args) => {
        let mut copy = self.clone();
        let args2 = args.iter().map(|&arg| copy.subst_arg(ctx, sp, arg)).collect::<Vec<_>>();
        if args == args2 { return ty }
        let args2 = ctx.alloc.alloc_slice_fill_iter(args2.into_iter());
        intern!(ctx, TyKind::Struct(args2))
      }
      TyKind::All(pat, t) => {
        let mut copy = self.clone();
        let pat2 = copy.subst_tup_pat(ctx, sp, pat);
        let t2 = copy.subst_ty(ctx, sp, t);
        if pat == pat2 && t == t2 { return ty }
        intern!(ctx, TyKind::All(pat2, t2))
      }
      TyKind::Imp(t1, t2) => subst!(|(t1, t2), _| TyKind::Imp(t1, t2); t1, t2;),
      TyKind::Wand(t1, t2) => subst!(|(t1, t2), _| TyKind::Wand(t1, t2); t1, t2;),
      TyKind::Not(t) => subst!(|t, _| TyKind::Not(t); t;),
      TyKind::And(tys) => substs!(TyKind::And; tys),
      TyKind::Or(tys) => substs!(TyKind::Or; tys),
      TyKind::If(e, t1, t2) => subst!(|(t1, t2), e| TyKind::If(e, t1, t2); t1, t2; e),
      TyKind::Ghost(t) => subst!(|t, _| TyKind::Ghost(t); t;),
      TyKind::Uninit(t) => subst!(|t, _| TyKind::Uninit(t); t;),
      TyKind::Pure(e) => subst!(|_, e| TyKind::Pure(e);; e),
      TyKind::User(f, tys, args) => {
        let tys2 = tys.iter().map(|e| self.subst_ty(ctx, sp, e)).collect::<Vec<_>>();
        let args2 = args.iter().map(|e| self.subst_expr(ctx, sp, e)).collect::<Vec<_>>();
        if tys == tys2 && args == args2 { return ty }
        let tys = ctx.alloc.alloc_slice_fill_iter(tys2.into_iter());
        let args = ctx.alloc.alloc_slice_fill_iter(args2.into_iter());
        intern!(ctx, TyKind::User(f, tys, args))
      }
      TyKind::Heap(e1, e2, t) => subst!(|t, (e1, e2)| TyKind::Heap(e1, e2, t); t; e1, e2),
      TyKind::HasTy(e1, t) => subst!(|t, e1| TyKind::HasTy(e1, t); t; e1),
      TyKind::Moved(t) => subst!(|t, _| TyKind::Moved(t); t;),
      TyKind::Infer(v) => {
        if let Some(ty) = ctx.mvars.ty.lookup(v) { return self.subst_ty(ctx, sp, ty) }
        let span = ctx.mvars.ty[v].span;
        ctx.errors.push(hir::Spanned {span, k: TypeError::ExpectedType});
        ctx.mvars.ty.assign(v, ctx.common.t_error);
        ctx.common.t_error
      }
    }
  }
}

struct FromGlobalCtx<'a, 'n, 'b> {
  ic: &'b mut InferCtx<'a, 'n>,
  subst: &'b [Ty<'a>],
  tr_var: HashMap<VarId, VarId>,
}

impl<'a, 'n, 'b> FromGlobalCtx<'a, 'n, 'b> {
  fn new(ic: &'b mut InferCtx<'a, 'n>, subst: &'b [Ty<'a>]) -> Self {
    Self { ic, subst, tr_var: Default::default() }
  }
}

trait FromGlobal<'a> {
  type Output: 'a;
  #[allow(clippy::wrong_self_convention)]
  fn from_global(&self, ctx: &mut FromGlobalCtx<'a, '_, '_>) -> Self::Output;
  fn inst_global(&self, ic: &mut InferCtx<'a, '_>, subst: &[Ty<'a>]) -> Self::Output {
    self.from_global(&mut FromGlobalCtx::new(ic, subst))
  }
  fn import_global(&self, ic: &mut InferCtx<'a, '_>) -> Self::Output { self.inst_global(ic, &[]) }
}

impl<'a, T: FromGlobal<'a>> FromGlobal<'a> for std::rc::Rc<T> {
  type Output = T::Output;
  fn from_global(&self, c: &mut FromGlobalCtx<'a, '_, '_>) -> Self::Output {
    (**self).from_global(c)
  }
}

impl<'a, T: FromGlobal<'a>> FromGlobal<'a> for Box<[T]> {
  type Output = &'a [T::Output];
  fn from_global(&self, c: &mut FromGlobalCtx<'a, '_, '_>) -> Self::Output {
    let vec = self.iter().map(|t| t.from_global(c)).collect::<Vec<_>>();
    c.ic.alloc.alloc_slice_fill_iter(vec.into_iter())
  }
}

impl<'a> FromGlobal<'a> for global::TuplePatternS {
  type Output = TuplePattern<'a>;
  fn from_global(&self, c: &mut FromGlobalCtx<'a, '_, '_>) -> Self::Output {
    intern!(c.ic, TuplePatternS {
      ty: self.ty.from_global(c),
      var: *c.tr_var.entry(self.var).or_insert_with(|| {
        let name = if let global::TuplePatternKind::Name(a) = self.k { a } else { Symbol::UNDER };
        c.ic.fresh_var(Spanned::dummy(name))
      }),
      k: match self.k {
        global::TuplePatternKind::Name(a) => TuplePatternKind::Name(a),
        global::TuplePatternKind::Tuple(ref pats, mk) =>
          TuplePatternKind::Tuple(pats.from_global(c), mk),
        global::TuplePatternKind::Error(ref pat) => TuplePatternKind::Error(pat.from_global(c)),
      },
    })
  }
}

impl<'a> FromGlobal<'a> for global::ArgS {
  type Output = Arg<'a>;
  fn from_global(&self, c: &mut FromGlobalCtx<'a, '_, '_>) -> Self::Output {
    intern!(c.ic, (self.0, match &self.1 {
      global::ArgKind::Lam(arg) => ArgKind::Lam(arg.from_global(c)),
      global::ArgKind::Let(arg, e) => {
        let e = e.from_global(c);
        ArgKind::Let(arg.from_global(c), e)
      }
    }))
  }
}

impl<'a> FromGlobal<'a> for global::Mm0Expr {
  type Output = Mm0Expr<'a>;
  fn from_global(&self, c: &mut FromGlobalCtx<'a, '_, '_>) -> Mm0Expr<'a> {
    Mm0Expr {
      subst: self.subst.from_global(c),
      expr: self.expr
    }
  }
}

impl<'a> FromGlobal<'a> for global::TyKind {
  type Output = Ty<'a>;
  fn from_global(&self, c: &mut FromGlobalCtx<'a, '_, '_>) -> Ty<'a> {
    intern!(c.ic, match self {
      global::TyKind::Unit => TyKind::Unit,
      global::TyKind::True => TyKind::True,
      global::TyKind::False => TyKind::False,
      global::TyKind::Bool => TyKind::Bool,
      &global::TyKind::Var(v) => return c.subst[u32_as_usize(v)],
      &global::TyKind::Int(ity) => TyKind::Int(ity),
      global::TyKind::Array(ty, n) => TyKind::Array(ty.from_global(c), n.from_global(c)),
      global::TyKind::Own(ty) => TyKind::Own(ty.from_global(c)),
      global::TyKind::Shr(lft, ty) => TyKind::Shr(*lft, ty.from_global(c)),
      global::TyKind::Ref(lft, ty) => TyKind::Ref(*lft, ty.from_global(c)),
      global::TyKind::RefSn(e) => TyKind::RefSn(e.from_global(c)),
      global::TyKind::List(tys) => TyKind::List(tys.from_global(c)),
      global::TyKind::Sn(a, ty) => TyKind::Sn(a.from_global(c), ty.from_global(c)),
      global::TyKind::Struct(args) => TyKind::Struct(args.from_global(c)),
      global::TyKind::All(pat, ty) => TyKind::All(pat.from_global(c), ty.from_global(c)),
      global::TyKind::Imp(p, q) => TyKind::Imp(p.from_global(c), q.from_global(c)),
      global::TyKind::Wand(p, q) => TyKind::Wand(p.from_global(c), q.from_global(c)),
      global::TyKind::Not(p) => TyKind::Not(p.from_global(c)),
      global::TyKind::And(ps) => TyKind::And(ps.from_global(c)),
      global::TyKind::Or(ps) => TyKind::Or(ps.from_global(c)),
      global::TyKind::If(cond, then, els) =>
        TyKind::If(cond.from_global(c), then.from_global(c), els.from_global(c)),
      global::TyKind::Ghost(ty) => TyKind::Ghost(ty.from_global(c)),
      global::TyKind::Uninit(ty) => TyKind::Uninit(ty.from_global(c)),
      global::TyKind::Pure(e) => TyKind::Pure(e.from_global(c)),
      global::TyKind::User(f, tys, es) =>
        TyKind::User(*f, tys.from_global(c), es.from_global(c)),
      global::TyKind::Heap(e, v, ty) =>
        TyKind::Heap(e.from_global(c), v.from_global(c), ty.from_global(c)),
      global::TyKind::HasTy(e, ty) => TyKind::HasTy(e.from_global(c), ty.from_global(c)),
      global::TyKind::Input => TyKind::Input,
      global::TyKind::Output => TyKind::Output,
      global::TyKind::Moved(ty) => TyKind::Moved(ty.from_global(c)),
      global::TyKind::Error => TyKind::Error,
    })
  }
}

impl<'a> FromGlobal<'a> for global::VariantType {
  type Output = hir::VariantType<'a>;
  fn from_global(&self, c: &mut FromGlobalCtx<'a, '_, '_>) -> Self::Output {
    match self {
      global::VariantType::Down => hir::VariantType::Down,
      global::VariantType::UpLt(e) => hir::VariantType::UpLt(e.from_global(c)),
      global::VariantType::UpLe(e) => hir::VariantType::UpLe(e.from_global(c)),
    }
  }
}

impl<'a> FromGlobal<'a> for global::Variant {
  type Output = hir::Variant<'a>;
  fn from_global(&self, c: &mut FromGlobalCtx<'a, '_, '_>) -> Self::Output {
    hir::Variant(self.0.from_global(c), self.1.from_global(c))
  }
}

impl<'a> FromGlobal<'a> for global::PlaceKind {
  type Output = Place<'a>;
  #[allow(clippy::many_single_char_names)]
  fn from_global(&self, c: &mut FromGlobalCtx<'a, '_, '_>) -> Self::Output {
    macro_rules! g {($e:expr) => {$e.from_global(c)}}
    intern!(c.ic, match self {
      &global::PlaceKind::Var(v) => PlaceKind::Var(v),
      global::PlaceKind::Index(a, ty, i) =>
        PlaceKind::Index(g!(a), g!(ty), g!(i)),
      global::PlaceKind::Slice(a, ty, [i, l]) =>
        PlaceKind::Slice(g!(a), g!(ty), [g!(i), g!(l)]),
      global::PlaceKind::Proj(a, ty, i) => PlaceKind::Proj(g!(a), g!(ty), *i),
      global::PlaceKind::Error => PlaceKind::Error,
    })
  }
}

impl<'a> FromGlobal<'a> for global::ExprKind {
  type Output = Expr<'a>;
  #[allow(clippy::many_single_char_names)]
  fn from_global(&self, c: &mut FromGlobalCtx<'a, '_, '_>) -> Self::Output {
    macro_rules! g {($e:expr) => {$e.from_global(c)}}
    intern!(c.ic, match self {
      global::ExprKind::Unit => ExprKind::Unit,
      global::ExprKind::Var(v) => ExprKind::Var(c.tr_var[v]),
      &global::ExprKind::Const(c) => ExprKind::Const(c),
      &global::ExprKind::Bool(b) => ExprKind::Bool(b),
      global::ExprKind::Int(n) => ExprKind::Int(c.ic.alloc.alloc(n.clone())),
      global::ExprKind::Unop(op, e) => ExprKind::Unop(*op, g!(e)),
      global::ExprKind::Binop(op, e1, e2) => ExprKind::Binop(*op, g!(e1), g!(e2)),
      global::ExprKind::Index(a, i) => ExprKind::Index(g!(a), g!(i)),
      global::ExprKind::Slice([a, i, l]) => ExprKind::Slice([g!(a), g!(i), g!(l)]),
      global::ExprKind::Proj(a, i) => ExprKind::Proj(g!(a), *i),
      global::ExprKind::UpdateIndex([a, i, v]) => ExprKind::UpdateIndex([g!(a), g!(i), g!(v)]),
      global::ExprKind::UpdateSlice([a, i, l, v]) =>
        ExprKind::UpdateSlice([g!(a), g!(i), g!(l), g!(v)]),
      global::ExprKind::UpdateProj(a, i, v) => ExprKind::UpdateProj(g!(a), *i, g!(v)),
      global::ExprKind::List(es) => ExprKind::List(g!(es)),
      global::ExprKind::Array(es) => ExprKind::Array(g!(es)),
      global::ExprKind::Sizeof(ty) => ExprKind::Sizeof(g!(ty)),
      global::ExprKind::Ref(e) => ExprKind::Ref(g!(e)),
      global::ExprKind::Mm0(e) => ExprKind::Mm0(g!(e)),
      &global::ExprKind::Call {f, ref tys, ref args} =>
        ExprKind::Call {f, tys: g!(tys), args: g!(args)},
      global::ExprKind::If {cond, then, els} => ExprKind::If {
        cond: g!(cond), then: g!(then), els: g!(els)},
      global::ExprKind::Error => ExprKind::Error,
    })
  }
}

/// The "dynamic" context, which consists of two parts:
/// * The logical context, which grows only via name scoping and does not change;
///   this is like a standard typing context in a functional language
/// * The mutations, which are accumulated moving forward along control flow;
///   this is like a linear type system, and stores the current value of all
///   variables that have been mutated.
#[derive(Clone, Debug)]
pub struct DynContext<'a> {
  /// The current generation.
  generation: GenId,
  /// A (persistent) map from variables that have been mutated at least once,
  /// to their latest type and value.
  gen_vars: im::HashMap<VarId, (GenId, Expr<'a>, Ty<'a>)>,
  /// The logical context.
  context: Context<'a>,
  /// True if we have previously hit an `unreachable` or other diverging operation,
  /// so that we are currently in dead code
  diverged: bool,
}

impl<'a> DynContext<'a> {
  fn new_context_next(&self, v: VarId, val: Expr<'a>, ty: Ty<'a>) -> ContextNext<'a> {
    ContextNext::new(self.context, v, self.generation, val, ty)
  }

  fn get_var(&self, v: VarId) -> (GenId, Expr<'a>, Ty<'a>) {
    let c = self.context.find(v).expect("variables should be well scoped");
    let val = if c.gen == GenId::LATEST {self.gen_vars.get(&v)} else {None};
    val.copied().unwrap_or((c.gen, c.val, c.ty))
  }
}

impl<'a, C: DisplayCtx<'a>> CtxDisplay<C> for DynContext<'a> {
  fn fmt(&self, ctx: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for &c in self.context.into_iter().collect::<Vec<_>>().iter().rev() {
      let (val, ty) = if_chain! {
        if c.gen == GenId::LATEST;
        if let Some(&(_, val, ty)) = self.gen_vars.get(&c.var);
        then { (val, ty) }
        else { (c.val, c.ty) }
      };
      write!(f, "{}: {}", CtxPrint(ctx, &c.var), CtxPrint(ctx, ty))?;
      if matches!(val.k, ExprKind::Var(v) if v == c.var) {
        writeln!(f)?
      } else {
        writeln!(f, " := {}", CtxPrint(ctx, val))?
      }
    }
    Ok(())
  }
}

#[derive(Debug)]
struct Counter<V> {
  vars: HashMap<V, usize>,
  max: usize
}

impl<V> Default for Counter<V> {
  fn default() -> Self { Self { vars: Default::default(), max: 0 } }
}

impl<V: Hash + Eq> Counter<V> {
  fn get(&mut self, v: V) -> usize {
    let Counter {vars, max} = self;
    *vars.entry(v).or_insert_with(|| { let n = *max; *max += 1; n })
  }
}

#[derive(Debug, Default)]
struct PrintCtxInner {
  lft_mvars: Counter<LftMVarId>,
  expr_mvars: Counter<ExprMVarId>,
  ty_mvars: Counter<TyMVarId>,
  vars: HashMap<Symbol, Counter<VarId>>,
}

/// A wrapper struct for printing error messages. It is stateful, meaning that it keeps track
/// of variables it sees so that it can number things in the order they are printed (rather than
/// using the internal numbering, which might involve a lot of temporaries). Variables and
/// metavariables are numbered consistently as long as this object is kept around.
#[derive(Debug)]
pub struct PrintCtx<'a, 'n, 'b, C: Config, I: ItemContext<C>> {
  inner: RefCell<(&'b mut InferCtx<'a, 'n>, PrintCtxInner)>,
  ctx: I::Printer,
}

impl<'a, 'n> InferCtx<'a, 'n> {
  /// Constructs a stateful printer for error messages, which should be used on all error messages
  /// in a group.
  pub fn print<C: Config, I: ItemContext<C>>(&mut self, i: &mut I) -> PrintCtx<'a, 'n, '_, C, I> {
    PrintCtx {
      ctx: i.print(),
      inner: RefCell::new((self, Default::default())),
    }
  }
}

impl<'a, C: Config, I: ItemContext<C>> DisplayCtx<'a> for PrintCtx<'a, '_, '_, C, I> {
  fn fmt_var(&self, v: VarId, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let (ic, inner) = &mut *self.inner.borrow_mut();
    let name = ic.var_name(v).k;
    let n = inner.vars.entry(name).or_default().get(v);
    if name == Symbol::UNDER {
      write!(f, "_{}", n+1)
    } else if n == 0 {
      write!(f, "{}", name)
    } else {
      write!(f, "{}_{}", name, n)
    }
  }

  fn fmt_lft_mvar(&self, v: LftMVarId, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut guard = self.inner.borrow_mut();
    let (ic, inner) = &mut *guard;
    if let Some(lft) = ic.mvars.lft.lookup(v) {
      drop(guard);
      return CtxDisplay::fmt(&lft, self, f)
    }
    write!(f, "'{}", inner.lft_mvars.get(v))
  }

  fn fmt_expr_mvar(&self, v: ExprMVarId, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut guard = self.inner.borrow_mut();
    let (ic, inner) = &mut *guard;
    if let Some(e) = ic.mvars.expr.lookup(v) {
      drop(guard);
      return CtxDisplay::fmt(e, self, f)
    }
    write!(f, "?{}", alphanumber(inner.expr_mvars.get(v)))
  }

  fn fmt_ty_mvar(&self, v: TyMVarId, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut guard = self.inner.borrow_mut();
    let (ic, inner) = &mut *guard;
    if let Some(ty) = ic.mvars.ty.lookup(v) {
      drop(guard);
      return CtxDisplay::fmt(ty, self, f)
    }
    let mut s = alphanumber(inner.ty_mvars.get(v));
    s.make_ascii_uppercase();
    write!(f, "?{}", s)
  }

  fn fmt_lambda(&self, v: LambdaId, subst: &[Expr<'a>], f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    crate::PrintLambda::fmt(&self.ctx, self, v, subst, f)
  }
}

#[derive(Debug)]
enum AgreeExpr<'a> {
  Unset,
  Set(RExpr<'a>),
}

/// The temporary data associated to a label group during elaboration.
#[derive(Debug)]
struct LabelData<'a> {
  /// The list of labels in the group.
  labels: Box<[(&'a [Arg<'a>], Option<hir::Variant<'a>>)]>,
  /// The pure expression in the break position.
  /// * `Unset` means we haven't seen any `break`s yet,
  /// * `Set(Some(e))` means all breaks have the same value `e`, and
  /// * `Set(None)` means that there are multiple exit values.
  value: AgreeExpr<'a>,
  /// True if there has been at least one jump to this label group.
  has_jump: bool,
  /// The return type of the block containing the label group.
  ret: Ty<'a>,
  /// The dynamic contexts at `break` points that need to be merged into the block exit context.
  dcs: Vec<DynContext<'a>>,
}

/// The assignments for metavariables.
#[derive(Debug, Default)]
pub(crate) struct MVars<'a> {
  /// The assignments for type metavariables.
  pub(crate) ty: Assignments<'a, TyMVarId, Ty<'a>>,
  /// The assignments for pure expression metavariables.
  pub(crate) expr: Assignments<'a, ExprMVarId, Expr<'a>>,
  /// The assignments for lifetime metavariables.
  pub(crate) lft: Assignments<'a, LftMVarId, Lifetime>,
}

impl<'a> MVars<'a> {
  pub(crate) fn get_lft_or_assign_extern(&mut self, v: LftMVarId) -> Lifetime {
    self.lft.lookup(v).unwrap_or_else(|| {
      self.lft.assign(v, Lifetime::Extern);
      Lifetime::Extern
    })
  }

  pub(crate) fn err_if_not_assigned_ty(&mut self, v: TyMVarId,
    errors: &mut Vec<hir::Spanned<'a, TypeError<'a>>>, t_error: Ty<'a>
  ) -> Ty<'a> {
    self.ty.lookup(v).unwrap_or_else(|| {
      errors.push(hir::Spanned {span: self.ty[v].span, k: TypeError::UninferredType});
      self.ty.assign(v, t_error);
      t_error
    })
  }

  pub(crate) fn err_if_not_assigned_expr(&mut self, v: ExprMVarId,
    errors: &mut Vec<hir::Spanned<'a, TypeError<'a>>>, e_error: Expr<'a>
  ) -> Expr<'a> {
    self.expr.lookup(v).unwrap_or_else(|| {
      errors.push(hir::Spanned {span: self.expr[v].span, k: TypeError::UninferredExpr});
      self.expr.assign(v, e_error);
      e_error
    })
  }
}

/// The main inference context for the type inference pass.
#[derive(Debug)]
pub struct InferCtx<'a, 'n> {
  /// The bump allocator that stores all the data structures
  /// (the `'a` in all the borrowed types).
  alloc: &'a Bump,
  /// The name map, for global variables and functions.
  names: &'n mut HashMap<Symbol, Entity>,
  /// The interner, which is used to deduplicate types and terms that are
  /// constructed multiple times.
  interner: Interner<'a>,
  /// The metavariable assignments.
  pub(crate) mvars: MVars<'a>,
  /// Some pre-interned types.
  common: Common<'a>,
  /// The dynamic context (including the logical context).
  dc: DynContext<'a>,
  /// The next generation.
  generation_count: GenId,
  /// The mapping from variables to their user-provided names.
  var_names: IdxVec<VarId, Spanned<Symbol>>,
  /// The set of labels in scope.
  labels: HashMap<VarId, LabelData<'a>>,
  /// The return type of the current function.
  returns: Option<&'a [Arg<'a>]>,
  /// The list of type errors collected so far.
  /// We delay outputting these so that we can report many errors at once,
  /// as well as waiting for all variables to be as unified as possible so that
  /// the error messages are as precise as possible.
  pub errors: Vec<hir::Spanned<'a, TypeError<'a>>>,
}

/// A relation between types, used as an argument to [`InferCtx::relate_ty`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Relation {
  /// Enforce that rvalues of type `A` can be converted to type `B`,
  /// possibly via a non-identity function.
  Coerce,
  /// Enforce that rvalues of type `A` are also of type `B`.
  Subtype,
  /// Enforce that rvalues of type `A` are also of type `B`,
  /// and they have the same bit representation.
  SubtypeEqSize,
  /// Unify types `A` and `B` exactly.
  Equal,
}

/// An expectation for a type, used to communicate top-down typing information.
#[derive(Copy, Clone)]
enum ExpectTy<'a> {
  /// No constraint. (This does not necessarily mean that any type is fine,
  /// but we don't have any particular hint to provide regarding the type;
  /// we will just signal a type error if the synthesized type is not good.)
  Any,
  /// We are expecting some `A` such that `R(A, B)`, where `B` is stored here.
  Relate(Relation, Ty<'a>),
  /// We are expecting some `B` such that `R(A, B)`, where `A` is stored here.
  RelateRev(Relation, Ty<'a>),
}

impl<'a> ExpectTy<'a> {
  // fn exactly(tgt: Option<Ty<'a>>) -> Self {
  //   tgt.map_or(Self::Any, |ty| Self::Relate(Relation::Equal, ty))
  // }
  // fn subtype(tgt: Option<Ty<'a>>) -> Self {
  //   tgt.map_or(Self::Any, |ty| Self::Relate(Relation::Subtype, ty))
  // }
  fn supertype(tgt: Option<Ty<'a>>) -> Self {
    tgt.map_or(Self::Any, |ty| Self::RelateRev(Relation::Subtype, ty))
  }
  fn coerce_to(tgt: Option<Ty<'a>>) -> Self {
    tgt.map_or(Self::Any, |ty| Self::Relate(Relation::Coerce, ty))
  }
  // fn coerce_from(tgt: Option<Ty<'a>>) -> Self {
  //   tgt.map_or(Self::Any, |ty| Self::RelateRev(Relation::Coerce, ty))
  // }

  fn to_ty(self) -> Option<Ty<'a>> {
    match self {
      ExpectTy::Any => None,
      ExpectTy::Relate(_, ty) |
      ExpectTy::RelateRev(_, ty) => Some(ty),
    }
  }
}

/// An expectation for an expression, used to communicate top-down typing information.
#[derive(Copy, Clone, Debug)]
enum ExpectExpr<'a> {
  /// This can be any expression.
  Any,
  /// This should be an expression with type (coercible to) `A`.
  HasTy(Ty<'a>),
  /// This should be an expression equal to `x` of type (coercible to) `A`.
  Sn(Expr<'a>, Ty<'a>),
}

impl<'a> From<Ty<'a>> for ExpectExpr<'a> {
  fn from(ty: Ty<'a>) -> Self {
    if let TyKind::Sn(x, ty) = ty.k {
      ExpectExpr::Sn(x, ty)
    } else { ExpectExpr::HasTy(ty) }
  }
}

impl<'a> ExpectExpr<'a> {
  fn has_ty(ty: Option<Ty<'a>>) -> Self { ty.map_or(Self::Any, Self::from) }

  fn to_ty(self) -> Option<Ty<'a>> {
    match self {
      ExpectExpr::Any => None,
      ExpectExpr::HasTy(ty) |
      ExpectExpr::Sn(_, ty) => Some(ty),
    }
  }
}

/// The result of a tuple pattern analysis, see [`InferCtx::tuple_pattern_tuple`].
#[allow(variant_size_differences)]
enum TuplePatternResult<'a> {
  /// This type cannot be destructured, or the wrong number of arguments were provided.
  /// If the bool is false, suppress the error.
  Fail(bool),
  /// There is not enough information in the type to determine what kind of
  /// destructuring is needed.
  Indeterminate,
  /// This is a valid tuple pattern, which uses the [`TupleIter::next`] interface
  /// to provide types in streaming fashion.
  Tuple(TupleMatchKind, TupleIter<'a>),
}

impl TupleMatchKind {
  /// Constructs an expression from a list of expressions for the sub-pattern matches.
  /// This will always return `Some` if the `exprs` are all `Some`, unless there is an upstream
  /// type error.
  fn build<'a>(self, ctx: &mut InferCtx<'a, '_>, exprs: Vec<Option<Expr<'a>>>) -> Option<Expr<'a>> {
    Some(match self {
      Self::Unit | Self::True => ctx.common.e_unit,
      Self::Sn => (*exprs.first()?)?,
      Self::List | Self::Struct => {
        if exprs.iter().any(Option::is_none) {return None}
        intern!(ctx, ExprKind::List(ctx.alloc.alloc_slice_fill_iter(exprs.into_iter().map(|e| {
          // Safety: we checked that all the options are Some
          unsafe { e.unwrap_unchecked() }
        }))))
      }
      Self::Array => {
        if exprs.iter().any(Option::is_none) {return None}
        intern!(ctx, ExprKind::Array(ctx.alloc.alloc_slice_fill_iter(exprs.into_iter().map(|e| {
          // Safety: we checked that all the options are Some
          unsafe { e.unwrap_unchecked() }
        }))))
      }
      Self::And => return exprs.first().copied().unwrap_or(Some(ctx.common.e_unit)),
      Self::Own | Self::Shr => (*exprs.get(1)?)?,
    })
  }

  /// Projects the value out of a tuple-like construction.
  /// Equivalent to `let (..., xi, ...) = e; xi` where `xi` is the `idx`th element in the list.
  fn proj<'a>(self, ctx: &mut InferCtx<'a, '_>,
    span: &'a FileSpan, e: Expr<'a>, num: usize, idx: u32
  ) -> Expr<'a> {
    match self {
      Self::Unit | Self::True => return ctx.common.e_unit,
      Self::Sn => return if idx == 0 { e } else { ctx.common.e_unit },
      Self::Own | Self::Shr => return if idx == 0 { ctx.as_pure(span, Err(span)) } else { e },
      Self::And => return e,
      Self::List | Self::Struct => if let ExprKind::List(es) = e.k {
        if es.len() == num { return es[idx as usize] }
      },
      Self::Array => if let ExprKind::Array(es) = e.k {
        if es.len() == num { return es[idx as usize] }
      },
    }
    intern!(ctx, ExprKind::Proj(e, idx))
  }
}

struct TupleIterArgs<'a> {
  subst: Subst<'a>,
  span: &'a FileSpan,
  first: TuplePattern<'a>,
  rest: std::slice::Iter<'a, Arg<'a>>
}

/// An "iterator" over an expected type for a tuple pattern. Unlike a regular
/// iterator, this has two methods, which must be called in an alternating
/// sequence: [`TupleIter::next`] returns the next type to be unified or `None`
/// if the iterator is done, and if it returns `Some` then the client must call
/// [`TupleIter::push`] with the expression for the tuple pattern resulting from
/// unification, after which point [`TupleIter::next`] can be called again.
enum TupleIter<'a> {
  /// A single type `{_ : T}`, or an empty iterator.
  Ty(Option<Ty<'a>>),
  /// A singleton pattern `(sn {a : T})`, which expands to the expected type
  /// `{x : T} {h : x = a}`.
  Sn(Expr<'a>, Ty<'a>),
  /// A list of types {_ : T1} {_ : T2} ... {_ : Tn}`, resulting from a pattern match
  /// on `List` or `And`.
  List(std::slice::Iter<'a, Ty<'a>>),
  /// A dependent list of types `{xi : Ti}`, resulting from a pattern match on a `Struct`.
  Args(Box<TupleIterArgs<'a>>),
  /// An `own` pattern `{(v x) : (own T)}`, which expands to the expected type
  /// `{v : T} {x : &sn v}`.
  Own(Ty<'a>),
  /// A `&` pattern `{(v x) : (& a T)}`, which expands to the expected type
  /// `{v : (ref a T)} {x : s&sn v}`.
  Shr(Lifetime, Ty<'a>),
}

impl Default for TupleIter<'_> {
  fn default() -> Self { Self::Ty(None) }
}

impl<'a> TupleIter<'a> {
  /// Construct an `Args` variant, pulling the next non-`Let` argument from the list.
  fn mk_args(ctx: &mut InferCtx<'a, '_>, span: &'a FileSpan,
    mut subst: Subst<'a>, mut rest: std::slice::Iter<'a, Arg<'a>>
  ) -> Self {
    while let Some(arg) = rest.next() {
      match arg.k.1 {
        ArgKind::Lam(first) =>
          return Self::Args(Box::new(TupleIterArgs {subst, span, first, rest})),
        ArgKind::Let(pat, e) => {
          let e = subst.subst_expr(ctx, span, e);
          subst.push_tuple_pattern_raw(ctx, span, pat, Ok(e))
        }
      }
    }
    Self::Ty(None)
  }

  /// Check if the iterator is empty, and return the next type in the sequence.
  ///
  /// **Note**: Unlike a regular iterator, `next` cannot be called twice in a row.
  /// If you get `Some(ty)` you have to either discard the iterator or call `push`
  /// to get it ready for the next `next` call.
  fn next(&mut self, ctx: &mut InferCtx<'a, '_>) -> Option<Ty<'a>> {
    match self {
      Self::Ty(ty) => ty.take(),
      &mut Self::Sn(_, ty) => Some(ty),
      Self::List(it) => it.next().copied(),
      Self::Args(args) => Some(args.subst.subst_ty(ctx, args.span, args.first.k.ty)),
      Self::Own(ty) => Some(ty),
      Self::Shr(lft, ty) => Some(intern!(ctx, TyKind::Ref(*lft, ty))),
    }
  }

  /// Finishes a call to `next` by substituting `val` into all types in the
  /// rest of the sequence of types.
  fn push(&mut self, ctx: &mut InferCtx<'a, '_>, sp: &'a FileSpan, val: Expr<'a>) {
    match self {
      Self::Ty(_) | Self::List(_) => {}
      &mut Self::Sn(e, _) => {
        *self = Self::Ty(Some(intern!(ctx, TyKind::Pure(
          intern!(ctx, ExprKind::Binop(Binop::Eq, val, e))))));
      }
      Self::Args(x) => {
        let TupleIterArgs {ref mut subst, span, first, ..} = **x;
        subst.push_tuple_pattern(ctx, span, first, Ok(val));
        let_unchecked!(Self::Args(args) = mem::take(self),
          *self = Self::mk_args(ctx, args.span, args.subst, args.rest))
      }
      Self::Own(_) | Self::Shr(_, _) => *self = Self::Ty(Some(intern!(ctx, TyKind::RefSn({
        if let ExprKind::Var(v) = val.k {
          intern!(ctx, PlaceKind::Var(v))
        } else {
          ctx.errors.push(hir::Spanned {span: sp, k: TypeError::UnsupportedPlaceMatch});
          ctx.common.p_error
        }
      })))),
    }
  }
}

/// Some common types and expressions.
#[derive(Debug)]
struct Common<'a> {
  t_unit: Ty<'a>,
  e_unit: Expr<'a>,
  t_bool: Ty<'a>,
  t_true: Ty<'a>,
  t_false: Ty<'a>,
  e_bool: [Expr<'a>; 2],
  t_uint: [Ty<'a>; 5],
  t_int: [Ty<'a>; 5],
  t_error: Ty<'a>,
  e_error: Expr<'a>,
  p_error: Place<'a>,
  e_num: [Expr<'a>; 5],
}

impl<'a> Common<'a> {
  fn new(i: &mut Interner<'a>, alloc: &'a Bump) -> Self {
    macro_rules! alloc {($e:expr) => {{let e = $e; i.intern(alloc, e)}}}
    macro_rules! allocs {($f:expr; $($e:expr),*) => {[$(alloc!($f($e))),*]}}
    use Size::*;
    Self {
      t_unit: alloc!(TyKind::Unit),
      e_unit: alloc!(ExprKind::Unit),
      t_bool: alloc!(TyKind::Bool),
      e_bool: allocs!(ExprKind::Bool; false, true),
      t_uint: allocs!(|sz| TyKind::Int(IntTy::UInt(sz)); S8, S16, S32, S64, Inf),
      t_int: allocs!(|sz| TyKind::Int(IntTy::Int(sz)); S8, S16, S32, S64, Inf),
      t_error: alloc!(TyKind::Error),
      e_error: alloc!(ExprKind::Error),
      p_error: alloc!(PlaceKind::Error),
      t_true: alloc!(TyKind::True),
      t_false: alloc!(TyKind::False),
      e_num: allocs!(|x: u32| ExprKind::Int(alloc.alloc(x.into())); 0, 1, 2, 4, 8),
    }
  }

  #[inline] const fn t_uint(&self, sz: Size) -> Ty<'a> { self.t_uint[sz as usize] }
  #[inline] const fn t_int(&self, sz: Size) -> Ty<'a> { self.t_int[sz as usize] }
  #[inline] const fn nat(&self) -> Ty<'a> { self.t_uint(Size::Inf) }
  #[inline] const fn int(&self) -> Ty<'a> { self.t_uint(Size::Inf) }
  #[inline] fn e_bool(&self, b: bool) -> Expr<'a> { self.e_bool[usize::from(b)] }

  const fn int_ty(&self, ity: IntTy) -> Ty<'a> {
    match ity {
      IntTy::Int(sz) => self.t_int(sz),
      IntTy::UInt(sz) => self.t_uint(sz),
    }
  }

  #[inline] const fn num(&self, i: u32) -> Expr<'a> {
    match i {
      0 => self.e_num[0],
      1 => self.e_num[1],
      2 => self.e_num[2],
      4 => self.e_num[3],
      8 => self.e_num[4],
      _ => const_panic!(),
    }
  }
}

impl<'a, 'n> InferCtx<'a, 'n> {
  /// Create a new `InferCtx` from the given allocator.
  pub fn new(
    alloc: &'a Bump,
    names: &'n mut HashMap<Symbol, Entity>,
    var_names: IdxVec<VarId, Spanned<Symbol>>,
  ) -> Self {
    let mut interner = Default::default();
    let common = Common::new(&mut interner, alloc);
    Self {
      alloc,
      names,
      interner,
      common,
      var_names,
      mvars: Default::default(),
      dc: DynContext {
        gen_vars: Default::default(),
        generation: GenId::ROOT,
        context: Context::ROOT,
        diverged: false,
      },
      generation_count: GenId::ROOT,
      labels: HashMap::new(),
      returns: None,
      errors: vec![],
    }
  }

  fn new_generation(&mut self) -> GenId {
    self.generation_count.0 += 1;
    self.generation_count
  }

  fn intern<T: Internable<'a>>(&mut self, t: T) -> &'a WithMeta<T> {
    self.interner.intern(self.alloc, t)
  }

  #[allow(clippy::wrong_self_convention)]
  pub(crate) fn to_global_ctx(&mut self) -> ToGlobalCtx<'a, '_> {
    ToGlobalCtx::new(&mut self.mvars, &mut self.errors, self.common.t_error, self.common.e_error)
  }

  fn var_name(&self, v: VarId) -> &Spanned<Symbol> { &self.var_names[v] }

  fn fresh_var(&mut self, name: Spanned<Symbol>) -> VarId { self.var_names.push(name) }

  fn fresh_var2(&mut self, v: VarId) -> VarId {
    let name = self.var_name(v).clone();
    self.fresh_var(name)
  }

  fn new_ty_mvar(&mut self, span: &'a FileSpan) -> Ty<'a> {
    let n = self.mvars.ty.new_mvar(span, self.dc.context);
    intern!(self, TyKind::Infer(n))
  }

  fn new_expr_mvar(&mut self, span: &'a FileSpan) -> Expr<'a> {
    let n = self.mvars.expr.new_mvar(span, self.dc.context);
    intern!(self, ExprKind::Infer(n))
  }

  fn new_lft_mvar(&mut self, span: &'a FileSpan) -> Lifetime {
    let n = self.mvars.lft.new_mvar(span, self.dc.context);
    Lifetime::Infer(n)
  }

  fn assign_ty(&mut self, v: TyMVarId, e: Ty<'a>) -> bool {
    let root = self.mvars.ty.root(v);
    if let TyKind::Infer(v2) = e.k {
      self.mvars.ty.equate(v, v2);
    } else {
      let mut cycle = false;
      e.on_mvars(|v2| cycle |= self.mvars.ty.root(v2) == root);
      if cycle { return false }
      self.mvars.ty.assign(v, e);
    }
    true
  }

  fn assign_expr(&mut self, v: ExprMVarId, e: Expr<'a>) -> bool {
    let root = self.mvars.expr.root(v);
    if let ExprKind::Infer(v2) = e.k {
      self.mvars.expr.equate(v, v2);
    } else {
      let mut cycle = false;
      e.on_mvars(|v2| cycle |= self.mvars.expr.root(v2) == root);
      if cycle { return false }
      self.mvars.expr.assign(v, e);
    }
    true
  }

  fn place_to_expr(&mut self, p: Place<'a>) -> Expr<'a> {
    intern!(self, match p.k {
      PlaceKind::Var(v) => ExprKind::Var(v),
      PlaceKind::Index(a, _, i) => ExprKind::Index(self.place_to_expr(a), i),
      PlaceKind::Slice(a, _, [i, l]) => ExprKind::Slice([self.place_to_expr(a), i, l]),
      PlaceKind::Proj(a, _, i) => ExprKind::Proj(self.place_to_expr(a), i),
      PlaceKind::Error => ExprKind::Error,
    })
  }

  fn new_context_next(&mut self, v: VarId, val: Option<Expr<'a>>, ty: Ty<'a>) -> &'a ContextNext<'a> {
    let val = val.unwrap_or_else(|| intern!(self, ExprKind::Var(v)));
    self.alloc.alloc(self.dc.new_context_next(v, val, ty))
  }

  fn merge(&mut self, span: &'a FileSpan, contexts: &mut [DynContext<'a>]) -> Vec<VarId> {
    if contexts.iter().all(|dc| {
      self.dc.diverged &= dc.diverged;
      dc.generation == self.dc.generation
    }) {return vec![]}
    if let Some(dc) =
      if let [dc] = contexts { Some(dc) }
      else if self.dc.diverged {
        if let [dc, ..] = contexts { Some(dc) } else { None }
      } else { None }
    {
      mem::swap(&mut self.dc, dc);
      return self.dc.gen_vars.iter().filter_map(|(&v, &(gen, _, _))| {
        if matches!(dc.gen_vars.get(&v), Some(&(old_gen, _, _)) if gen != old_gen) { Some(v) }
        else { None }
      }).collect()
    }
    let mut newdc = self.dc.clone();
    newdc.generation = self.new_generation();
    let mut vars = HashSet::new();
    for c in self.dc.context.into_iter().filter(|c| c.gen == GenId::LATEST) {
      let v = c.var;
      let (old_gen, old_e, old_ty) =
        self.dc.gen_vars.get(&v).copied().unwrap_or((c.gen, c.val, c.ty));
      let mut new_e = Some(old_e);
      let mut modified = false;
      for dc in &*contexts {
        if !dc.diverged {
          if let Some(&(gen, e, ty)) = dc.gen_vars.get(&v) {
            if gen != old_gen {
              new_e = new_e.filter(|new_e| self.equate_expr(new_e, e).is_ok());
              self.relate_ty(span, Some(e), ty, old_ty, Relation::Subtype).expect("todo");
              modified = true;
            }
          }
        }
      }
      if modified {
        vars.insert(v);
        let new_e = new_e.unwrap_or_else(|| intern!(self, ExprKind::Var(v)));
        newdc.gen_vars.insert(v, (newdc.generation, new_e, old_ty));
      }
    }
    if vars.is_empty() { newdc.generation = self.dc.generation }
    self.dc = newdc;
    vars.into_iter().collect()
  }

  fn whnf_unop(&mut self, sp: &'a FileSpan, op: Unop, e: Expr<'a>) -> Expr<'a> {
    if op.int_in_out() {
      if_chain! {
        if let ExprKind::Int(n) = self.whnf_expr(sp, e).k;
        if let Some(n2) = op.apply_int(n);
        let n2 = match n2 {
          Cow::Borrowed(n2) => n2,
          Cow::Owned(n2) => self.alloc.alloc(n2)
        };
        then { return intern!(self, ExprKind::Int(n2)) }
      }
    } else if let ExprKind::Bool(b) = self.whnf_expr(sp, e).k {
      return self.common.e_bool(op.apply_bool(b))
    }
    intern!(self, ExprKind::Unop(op, e))
  }

  fn whnf_binop(&mut self, sp: &'a FileSpan, op: Binop, e1: Expr<'a>, e2: Expr<'a>) -> Expr<'a> {
    if op.ty().int_in() {
      if_chain! {
        if let ExprKind::Int(n1) = self.whnf_expr(sp, e1).k;
        if let ExprKind::Int(n2) = self.whnf_expr(sp, e2).k;
        then {
          if op.ty().int_out() {
            if let Some(n) = op.apply_int_int(n1, n2) {
              return intern!(self, ExprKind::Int(self.alloc.alloc(n)))
            }
          } else {
            return self.common.e_bool(op.apply_int_bool(n1, n2))
          }
        }
      }
    } else {
      if_chain! {
        if let ExprKind::Bool(b1) = self.whnf_expr(sp, e1).k;
        if let ExprKind::Bool(b2) = self.whnf_expr(sp, e2).k;
        then { return self.common.e_bool(op.apply_bool_bool(b1, b2)) }
      }
    }
    intern!(self, ExprKind::Binop(op, e1, e2))
  }

  fn whnf_expr(&mut self, sp: &'a FileSpan, e: Expr<'a>) -> Expr<'a> {
    match e.k {
      ExprKind::Unit |
      ExprKind::Bool(_) |
      ExprKind::Int(_) |
      ExprKind::Const(_) | // TODO
      ExprKind::List(_) |
      ExprKind::Array(_) |
      ExprKind::Ref(_) |
      ExprKind::Mm0(_) |
      ExprKind::Error => e,
      ExprKind::Var(v) => {
        let (_, e2, _) = self.dc.get_var(v);
        if e == e2 { return e }
        self.whnf_expr(sp, e2)
      }
      ExprKind::Unop(op, e) => self.whnf_unop(sp, op, e),
      ExprKind::Binop(op, e1, e2) => self.whnf_binop(sp, op, e1, e2),
      ExprKind::Index(a, i) => if_chain! {
        if let ExprKind::Array(es) = self.whnf_expr(sp, a).k;
        if let ExprKind::Int(i) = self.whnf_expr(sp, i).k;
        if let Ok(i) = usize::try_from(i);
        if i < es.len();
        then { self.whnf_expr(sp, es[i]) }
        else { e }
      },
      ExprKind::Slice([a, i, l]) => if_chain! {
        if let ExprKind::Array(es) = self.whnf_expr(sp, a).k;
        if let ExprKind::Int(i) = self.whnf_expr(sp, i).k;
        if let Ok(i) = usize::try_from(i);
        if let ExprKind::Int(l) = self.whnf_expr(sp, l).k;
        if let Ok(l) = l.try_into();
        if let Some(il) = i.checked_add(l);
        if il < es.len();
        then { intern!(self, ExprKind::Array(&es[i..il])) }
        else { e }
      },
      ExprKind::Proj(p, i) => if_chain! {
        if let ExprKind::List(es) = self.whnf_expr(sp, p).k;
        let i = u32_as_usize(i);
        if i < es.len();
        then { self.whnf_expr(sp, es[i]) }
        else { e }
      },
      ExprKind::UpdateIndex([a, i, val]) => if_chain! {
        if let ExprKind::Array(es) = self.whnf_expr(sp, a).k;
        if let ExprKind::Int(i) = self.whnf_expr(sp, i).k;
        if let Ok(i) = usize::try_from(i);
        if i < es.len();
        then {
          let es2 = self.alloc.alloc_slice_copy(es);
          es2[i] = val;
          intern!(self, ExprKind::Array(es2))
        }
        else { e }
      },
      ExprKind::UpdateSlice([a, i, l, val]) => if_chain! {
        if let ExprKind::Array(es) = self.whnf_expr(sp, a).k;
        if let ExprKind::Int(i) = self.whnf_expr(sp, i).k;
        if let Ok(i) = usize::try_from(i);
        if let ExprKind::Int(l) = self.whnf_expr(sp, l).k;
        if let Ok(l) = l.try_into();
        if let Some(il) = i.checked_add(l);
        if il < es.len();
        if let ExprKind::Array(val2) = self.whnf_expr(sp, val).k;
        if l == val2.len();
        then {
          let es2 = self.alloc.alloc_slice_copy(es);
          es2[i..il].clone_from_slice(val2);
          intern!(self, ExprKind::Array(es2))
        }
        else { e }
      },
      ExprKind::UpdateProj(p, i, val) => if_chain! {
        if let ExprKind::List(es) = self.whnf_expr(sp, p).k;
        let i = u32_as_usize(i);
        if i < es.len();
        then {
          let es2 = self.alloc.alloc_slice_copy(es);
          es2[i] = val;
          intern!(self, ExprKind::List(es2))
        }
        else { e }
      },
      ExprKind::Sizeof(ty) => self.whnf_sizeof(sp, Default::default(), ty),
      ExprKind::Call {f, tys, args: es} =>
        match let_unchecked!(Some(Entity::Proc(ty)) = self.names.get(&f), ty).k.ty() {
          None => self.common.e_error,
          Some(&ProcTy {kind, tyargs, ref args, ref rets, ..}) => {
            assert_eq!(tys.len(), u32_as_usize(tyargs));
            match kind {
              ProcKind::Proc | ProcKind::Main => unreachable!(),
              ProcKind::Func => {
                let (args, rets) = (args.clone(), rets.clone());
                let args = args.inst_global(self, tys);
                let rets = rets.inst_global(self, tys);
                let _ = (args, rets, es);
                todo!()
              }
            }
          }
        },
      ExprKind::If {cond, then, els} =>
        if let ExprKind::Bool(b) = self.whnf_expr(sp, cond).k {
          self.whnf_expr(sp, if b {then} else {els})
        } else { e },
      ExprKind::Infer(v) =>
        if let Some(e) = self.mvars.expr.lookup(v) { self.whnf_expr(sp, e) } else { e }
    }
  }

  fn whnf_ty(&mut self, sp: &'a FileSpan, wty: WhnfTy<'a>) -> WhnfTy<'a> {
    wty.map(intern!(self, match wty.ty.k {
      TyKind::List(es) if es.is_empty() => return wty.map(self.common.t_unit),
      TyKind::Struct(es) if es.is_empty() => return wty.map(self.common.t_unit),
      TyKind::And(es) if es.is_empty() => return wty.map(self.common.t_true),
      TyKind::Or(es) if es.is_empty() => return wty.map(self.common.t_false),
      TyKind::Unit |
      TyKind::True |
      TyKind::False |
      TyKind::Bool |
      TyKind::Var(_) |
      TyKind::Int(_) |
      TyKind::Array(_, _) |
      TyKind::Own(_) |
      TyKind::Shr(_, _) |
      TyKind::RefSn(_) |
      TyKind::List(_) |
      TyKind::Sn(_, _) |
      TyKind::Struct(_) |
      TyKind::All(_, _) |
      TyKind::Imp(_, _) |
      TyKind::Wand(_, _) |
      TyKind::Not(_) |
      TyKind::And(_) |
      TyKind::Or(_) |
      TyKind::Heap(_, _, _) |
      TyKind::Input |
      TyKind::Output |
      TyKind::Error => return wty,
      TyKind::Ref(_, ty) => return wty.map(ty), // FIXME
      TyKind::User(f, tys, es) => {
        match let_unchecked!(Some(Entity::Type(tc)) = self.names.get(&f), tc).k {
          TypeTc::ForwardDeclared => return self.common.t_error.into(),
          TypeTc::Typed(ref tyty) => {
            let TypeTy {tyargs, args, val, ..} = tyty.clone();
            assert_eq!(tys.len(), u32_as_usize(tyargs));
            let args = args.inst_global(self, tys);
            debug_assert!(es.len() ==
              args.iter().filter(|&a| matches!(a.k.1, ArgKind::Lam(_))).count());
            let mut subst = Subst::default();
            let mut es_it = es.iter();
            for &arg in args {
              match arg.k.1 {
                ArgKind::Lam(arg) => {
                  let e = es_it.next().expect("checked");
                  subst.push_tuple_pattern(self, sp, arg, Ok(e))
                }
                ArgKind::Let(arg, e) => {
                  let e = subst.subst_expr(self, sp, e);
                  subst.push_tuple_pattern_raw(self, sp, arg, Ok(e))
                }
              }
            }
            let val = val.inst_global(self, tys);
            let val = subst.subst_ty(self, sp, val);
            return self.whnf_ty(sp, wty.map(val))
          }
        }
      }
      TyKind::If(e, t1, t2) => {
        let e2 = self.whnf_expr(sp, e);
        match e2.k {
          ExprKind::Bool(true) => return self.whnf_ty(sp, wty.map(t1)),
          ExprKind::Bool(false) => return self.whnf_ty(sp, wty.map(t2)),
          _ if e == e2 => return wty,
          _ => TyKind::If(e2, t1, t2),
        }
      }
      TyKind::HasTy(x, ty) => {
        let wty = WhnfTy::from(ty);
        if wty.uninit {return wty}
        let wty2 = self.whnf_ty(sp, wty);
        match wty2.ty.k {
          TyKind::List(tys) => TyKind::List(self.alloc.alloc_slice_fill_iter(
            tys.iter().map(|&ty| intern!(self, TyKind::HasTy(x, ty))))),
          TyKind::And(tys) => TyKind::And(self.alloc.alloc_slice_fill_iter(
            tys.iter().map(|&ty| intern!(self, TyKind::HasTy(x, ty))))),
          TyKind::Or(tys) => TyKind::Or(self.alloc.alloc_slice_fill_iter(
            tys.iter().map(|&ty| intern!(self, TyKind::HasTy(x, ty))))),
          TyKind::Error => TyKind::Error,
          TyKind::Moved(_) |
          TyKind::Ghost(_) |
          TyKind::Uninit(_) => unreachable!(),
          _ => {
            if wty == wty2 { return wty }
            TyKind::HasTy(x, wty2.to_ty(self))
          }
        }
      }
      TyKind::Pure(e) => {
        let e2 = self.whnf_expr(sp, e);
        if e == e2 {return wty}
        TyKind::Pure(e2)
      }
      TyKind::Infer(v) => {
        if let Some(ty) = self.mvars.ty.lookup(v) {
          return self.whnf_ty(sp, ty.into())
        }
        return wty
      }
      TyKind::Ghost(_) |
      TyKind::Uninit(_) |
      TyKind::Moved(_) => unreachable!(),
    }))
  }

  fn whnf_sizeof(&mut self, sp: &'a FileSpan,
    mut qvars: im::HashSet<VarId>, ty: Ty<'a>
  ) -> Expr<'a> {
    let wty = self.whnf_ty(sp, ty.into());
    macro_rules! fail {() => { intern!(self, ExprKind::Sizeof(wty.to_ty(self))) }}
    match wty.ty.k {
      TyKind::Unit |
      TyKind::True |
      TyKind::False |
      TyKind::Ref(_, _) |
      TyKind::Imp(_, _) |
      TyKind::Wand(_, _) |
      TyKind::Not(_) |
      TyKind::Pure(_) |
      TyKind::Heap(_, _, _) |
      TyKind::HasTy(_, _) |
      TyKind::Input |
      TyKind::Output |
      TyKind::Ghost(_) => self.common.num(0),
      TyKind::Bool => self.common.num(1),
      TyKind::Own(_) |
      TyKind::Shr(_, _) |
      TyKind::RefSn(_) => self.common.num(8),
      TyKind::User(_, _, _) | // TODO
      TyKind::Infer(_) |
      TyKind::Var(_) => fail!(),
      TyKind::Sn(_, ty) |
      TyKind::Uninit(ty) |
      TyKind::Moved(ty) => self.whnf_sizeof(sp, qvars, ty),
      TyKind::Int(i_ty) =>
        if let Some(n) = i_ty.size().bytes() { self.common.num(n.into()) }
        else { fail!() },
      TyKind::Array(ty, n) => {
        let mut has_qvar = false;
        n.on_vars(|v| has_qvar |= qvars.contains(&v));
        let size = self.whnf_sizeof(sp, qvars, ty);
        if has_qvar {
          if size == self.common.num(0) { size } else { fail!() }
        } else {
          self.whnf_binop(sp, Binop::Mul, size, n)
        }
      }
      TyKind::List(tys) => {
        let this = RefCell::new(&mut *self);
        tys.iter()
          .map(|ty| this.borrow_mut().whnf_sizeof(sp, qvars.clone(), ty))
          .reduce(|e, e2| this.borrow_mut().whnf_binop(sp, Binop::Add, e, e2))
          .unwrap_or_else(|| self.common.num(0))
      }
      TyKind::Struct(args) => {
        let this = RefCell::new(&mut *self);
        args.iter()
          .filter_map(|arg| match arg.k.1 {
            ArgKind::Lam(pat) => {
              let e = this.borrow_mut().whnf_sizeof(sp, qvars.clone(), pat.k.ty);
              pat.k.on_vars(&mut |_, v| { qvars.insert(v); });
              Some(e)
            }
            ArgKind::Let(pat, _) => {
              pat.k.on_vars(&mut |_, v| { qvars.insert(v); });
              None
            }
          })
          .reduce(|e, e2| this.borrow_mut().whnf_binop(sp, Binop::Add, e, e2))
          .unwrap_or_else(|| self.common.num(0))
      }
      TyKind::All(pat, ty) => {
        pat.k.on_vars(&mut |_, v| { qvars.insert(v); });
        self.whnf_sizeof(sp, qvars, ty)
      }
      TyKind::And(tys) |
      TyKind::Or(tys) => {
        let this = RefCell::new(&mut *self);
        tys.iter()
          .map(|ty| this.borrow_mut().whnf_sizeof(sp, qvars.clone(), ty))
          .reduce(|e, e2| this.borrow_mut().whnf_binop(sp, Binop::Max, e, e2))
          .unwrap_or_else(|| self.common.num(0))
      }
      TyKind::If(_, ty1, ty2) => {
        let e1 = self.whnf_sizeof(sp, qvars.clone(), ty1);
        let e2 = self.whnf_sizeof(sp, qvars.clone(), ty2);
        self.whnf_binop(sp, Binop::Max, e1, e2) // TODO: this is wrong if sizeof e1 != sizeof e2
      }
      TyKind::Error => self.common.e_error,
    }
  }

  fn equate_lft(&mut self, a: Lifetime, b: Lifetime) -> Result<(), ()> {
    if a == b { return Ok(()) }
    match (a, b) {
      (Lifetime::Infer(v), _) => {
        if let Some(e) = self.mvars.lft.lookup(v) { return self.equate_lft(e, b) }
        self.mvars.lft.assign(v, b)
      }
      (_, Lifetime::Infer(v)) => {
        if let Some(e) = self.mvars.lft.lookup(v) { return self.equate_lft(a, e) }
        self.mvars.lft.assign(v, a)
      }
      _ => return Err(())
    }
    Ok(())
  }

  fn equate_expr(&mut self, a: Expr<'a>, b: Expr<'a>) -> Result<(), ()> {
    if a == b { return Ok(()) }
    match (a.k, b.k) {
      (ExprKind::Error, _) | (_, ExprKind::Error) => {}
      (ExprKind::Unop(op_a, a1), ExprKind::Unop(op_b, b1)) if op_a == op_b =>
        self.equate_expr(a1, b1)?,
      (ExprKind::Binop(op_a, a1, a2), ExprKind::Binop(op_b, b1, b2)) if op_a == op_b =>
        {self.equate_expr(a1, b1)?; self.equate_expr(a2, b2)?}
      (ExprKind::Index(a1, a2), ExprKind::Index(b1, b2)) =>
        {self.equate_expr(a1, b1)?; self.equate_expr(a2, b2)?}
      (ExprKind::Slice([a1, a2, a3]), ExprKind::Slice([b1, b2, b3])) |
      (ExprKind::If {cond: a1, then: a2, els: a3}, ExprKind::If {cond: b1, then: b2, els: b3}) =>
        {self.equate_expr(a1, b1)?; self.equate_expr(a2, b2)?; self.equate_expr(a3, b3)?}
      (ExprKind::Proj(a1, p_a), ExprKind::Proj(b1, p_b)) if p_a == p_b => self.equate_expr(a1, b1)?,
      (ExprKind::List(ls_a), ExprKind::List(ls_b)) if ls_a.len() == ls_b.len() =>
        for (&a1, &b1) in ls_a.iter().zip(ls_b) {self.equate_expr(a1, b1)?},
      (ExprKind::Mm0(a1), ExprKind::Mm0(b1)) if a1.expr == b1.expr =>
        for (&a1, &b1) in a1.subst.iter().zip(b1.subst) {self.equate_expr(a1, b1)?},
      (ExprKind::Call {f: f_a, tys: tys_a, args: args_a},
       ExprKind::Call {f: f_b, tys: tys_b, args: args_b}) if f_a == f_b && tys_a == tys_b =>
        for (&a1, &b1) in args_a.iter().zip(args_b) {self.equate_expr(a1, b1)?},
      (ExprKind::Infer(v), _) => {
        if let Some(e) = self.mvars.expr.lookup(v) { return self.equate_expr(e, b) }
        if !self.assign_expr(v, b) { return Err(()) }
      }
      (_, ExprKind::Infer(v)) => {
        if let Some(e) = self.mvars.expr.lookup(v) { return self.equate_expr(a, e) }
        if !self.assign_expr(v, a) { return Err(()) }
      }
      (ExprKind::Var(_), _) | (_, ExprKind::Var(_)) => {
        if let ExprKind::Var(va) = a.k {
          let (_, a2, _) = self.dc.get_var(va);
          if a != a2 { return self.equate_expr(a2, b) }
        }
        if let ExprKind::Var(vb) = b.k {
          let (_, b2, _) = self.dc.get_var(vb);
          if b != b2 { return self.equate_expr(a, b2) }
        }
        return Err(())
      }
      (ExprKind::Const(c), _) => {
        match let_unchecked!(Some(Entity::Const(tc)) = self.names.get(&c), tc).k {
          ConstTc::ForwardDeclared => {}
          ConstTc::Checked {ref whnf, ..} => {
            let a = whnf.clone().import_global(self);
            return self.equate_expr(a, b)
          }
        }
      }
      (_, ExprKind::Const(_)) => return self.equate_expr(b, a),
      _ => return Err(())
    }
    Ok(())
  }

  fn equate_place(&mut self, a: Place<'a>, b: Place<'a>) -> Result<(), ()> {
    if a == b { return Ok(()) }
    match (a.k, b.k) {
      (PlaceKind::Error, _) | (_, PlaceKind::Error) => {}
      (PlaceKind::Index(a1, ty_a, a2), PlaceKind::Index(b1, ty_b, b2)) if ty_a == ty_b => {
        self.equate_place(a1, b1)?;
        self.equate_expr(a2, b2)?
      }
      (PlaceKind::Slice(a1, ty_a, [a2, a3]), PlaceKind::Slice(b1, ty_b, [b2, b3]))
      if ty_a == ty_b => {
        self.equate_place(a1, b1)?;
        self.equate_expr(a2, b2)?;
        self.equate_expr(a3, b3)?
      }
      (PlaceKind::Proj(a1, ty_a, p_a), PlaceKind::Proj(b1, ty_b, p_b))
      if p_a == p_b && ty_a == ty_b => self.equate_place(a1, b1)?,
      _ => return Err(())
    }
    Ok(())
  }

  fn relate_whnf_ty(&mut self,
    from: WhnfTy<'a>, to: WhnfTy<'a>, mut rel: Relation
  ) -> Result<Vec<Coercion<'a>>, ()> {
    macro_rules! check {($($i:ident),*) => {{
      $(if from.$i != to.$i { return Err(()) })*
    }}}
    if from.ty == to.ty {
      check!(uninit, ghost, moved);
      return Ok(vec![])
    }
    match (from.ty.k, to.ty.k) {
      (TyKind::Error, _) | (_, TyKind::Error) => {}
      (TyKind::Int(ity_a), TyKind::Int(ity_b))
      if matches!(rel, Relation::Subtype | Relation::Coerce) && ity_a <= ity_b =>
        return Ok(vec![]),
      (TyKind::Array(ty_a, e_a), TyKind::Array(ty_b, e_b)) => {
        if rel == Relation::Subtype { rel = Relation::SubtypeEqSize }
        let coes = self.relate_whnf_ty(from.map(ty_a), to.map(ty_b), rel)?;
        self.equate_expr(e_a, e_b)?;
        if !coes.is_empty() {
          unimplemented!()
          // coes = vec![Coercion::Array(coes)]
        }
        return Ok(coes)
      }
      (TyKind::Own(a1), TyKind::Own(b1)) => {
        if let Relation::Subtype | Relation::Coerce = rel { rel = Relation::SubtypeEqSize }
        check!(uninit, ghost, moved);
        let coes = self.relate_whnf_ty(a1.into(), b1.into(), rel)?;
        if !coes.is_empty() { unimplemented!() }
        return Ok(coes)
      }
      (TyKind::Shr(lft_a, a1), TyKind::Shr(lft_b, b1)) |
      (TyKind::Ref(lft_a, a1), TyKind::Ref(lft_b, b1)) => {
        check!(uninit, ghost);
        self.equate_lft(lft_a, lft_b)?;
        if let Relation::Subtype | Relation::Coerce = rel { rel = Relation::SubtypeEqSize }
        let coes = self.relate_whnf_ty(a1.into(), b1.into(), rel)?;
        if !coes.is_empty() { unimplemented!() }
        return Ok(coes)
      }
      (TyKind::RefSn(a1), TyKind::RefSn(b1)) => {
        check!(uninit, ghost);
        self.equate_place(a1, b1)?;
      }
      (TyKind::List(tys_a), TyKind::List(tys_b)) if tys_a.len() == tys_b.len() => {
        for (&ty_a, &ty_b) in tys_a.iter().zip(tys_b) {
          let coes = self.relate_whnf_ty(from.map(ty_a), to.map(ty_b), rel)?;
          if !coes.is_empty() { unimplemented!() }
        }
      }
      (TyKind::Sn(e_a, ty_a), TyKind::Sn(e_b, ty_b)) => {
        self.equate_expr(e_a, e_b)?;
        let coes = self.relate_whnf_ty(from.map(ty_a), to.map(ty_b), rel)?;
        if !coes.is_empty() { unimplemented!() }
      }
      (TyKind::Struct(argsa), TyKind::Struct(argsb)) if argsa.len() == argsb.len() => {
        check!(uninit, ghost, moved);
        for (&arga, &argb) in argsa.iter().zip(argsb) {
          if arga != argb { return Err(()) } // TODO: alpha conversion
        }
      }
      (TyKind::All(a1, a2), TyKind::All(b1, b2)) => {
        check!(uninit);
        let coe1 = self.relate_whnf_ty(b1.k.ty.into(), a1.k.ty.into(), rel)?;
        if !coe1.is_empty() { unimplemented!() }
        let coe2 = if a1.k.ty.is_copy() && b1.k.ty.is_copy() {
          self.relate_whnf_ty(from.map(a2), to.map(b2), rel)?
        } else {
          check!(moved);
          self.relate_whnf_ty(a2.into(), b2.into(), rel)?
        };
        if !coe2.is_empty() { unimplemented!() }
      }
      (TyKind::Imp(a1, a2), TyKind::Imp(b1, b2)) |
      (TyKind::Wand(a1, a2), TyKind::Wand(b1, b2)) => {
        check!(uninit);
        let coe1 = self.relate_whnf_ty(b1.into(), a1.into(), rel)?;
        if !coe1.is_empty() { unimplemented!() }
        let coe2 = if a1.is_copy() && b1.is_copy() {
          self.relate_whnf_ty(from.map(a2), to.map(b2), rel)?
        } else {
          check!(moved);
          self.relate_whnf_ty(a2.into(), b2.into(), rel)?
        };
        if !coe2.is_empty() { unimplemented!() }
      }
      (TyKind::Not(a1), TyKind::Not(b1)) => {
        check!(uninit);
        if !a1.is_copy() || !b1.is_copy() { check!(moved) }
        let coe1 = self.relate_whnf_ty(b1.into(), a1.into(), rel)?;
        if !coe1.is_empty() { unimplemented!() }
      }
      (TyKind::And(tys_a), TyKind::And(tys_b)) if tys_a.len() == tys_b.len() => {
        for (&ty_a, &ty_b) in tys_a.iter().zip(tys_b) {
          let coes = self.relate_whnf_ty(from.map(ty_a), to.map(ty_b), rel)?;
          if !coes.is_empty() { unimplemented!() }
        }
      }
      (TyKind::Or(tys_a), TyKind::Or(tys_b)) if tys_a.len() == tys_b.len() => {
        for (&ty_a, &ty_b) in tys_a.iter().zip(tys_b) {
          let coes = self.relate_whnf_ty(from.map(ty_a), to.map(ty_b), rel)?;
          if !coes.is_empty() { unimplemented!() }
        }
      }
      (TyKind::If(ca, ta, fa), TyKind::If(cb, tb, fb)) => {
        check!(uninit);
        self.equate_expr(ca, cb)?;
        let t_coes = self.relate_whnf_ty(from.map(ta), to.map(tb), rel)?;
        if !t_coes.is_empty() { unimplemented!() }
        let f_coes = self.relate_whnf_ty(from.map(fa), to.map(fb), rel)?;
        if !f_coes.is_empty() { unimplemented!() }
      }
      (TyKind::Pure(e_a), TyKind::Pure(e_b)) => {
        check!(uninit);
        self.equate_expr(e_a, e_b)?
      }
      (TyKind::User(fa, tys_a, argsa), TyKind::User(fb, tys_b, argsb))
      if fa == fb && tys_a.len() == tys_b.len() && argsa.len() == argsb.len() => {
        check!(uninit, ghost, moved);
        for (&ty_a, &ty_b) in tys_a.iter().zip(tys_b) {
          self.relate_whnf_ty(ty_a.into(), ty_b.into(), Relation::Equal)?;
        }
        for (&a1, &b1) in argsa.iter().zip(argsb) {self.equate_expr(a1, b1)?}
      }
      (TyKind::Heap(a1, a2, ty_a), TyKind::Heap(b1, b2, ty_b)) => {
        check!(uninit, moved);
        self.equate_expr(a1, b1)?;
        self.equate_expr(a2, b2)?;
        let coes = self.relate_whnf_ty(
          WhnfTy::from(ty_a).moved(true),
          WhnfTy::from(ty_b).moved(true), rel)?;
        if !coes.is_empty() { unimplemented!() }
      }
      (TyKind::HasTy(a1, ty_a), TyKind::HasTy(b1, ty_b)) => {
        check!(uninit);
        self.equate_expr(a1, b1)?;
        let coes = self.relate_whnf_ty(
          WhnfTy::from(ty_a).moved(from.moved),
          WhnfTy::from(ty_b).moved(to.moved), rel)?;
        if !coes.is_empty() { unimplemented!() }
      }
      (TyKind::Infer(v), _) => {
        if let Some(ty) = self.mvars.ty.lookup(v) {
          return self.relate_whnf_ty(ty.into(), to, rel)
        }
        let to = to.to_ty(self);
        if !self.assign_ty(v, to) { return Err(()) }
      }
      (_, TyKind::Infer(v)) => {
        if let Some(ty) = self.mvars.ty.lookup(v) {
          return self.relate_whnf_ty(from, ty.into(), rel)
        }
        let from = from.to_ty(self);
        if !self.assign_ty(v, from) { return Err(()) }
      }
      _ => return Err(())
    }
    Ok(vec![])
  }

  fn relate_ty(&mut self, span: &'a FileSpan,
    pe: Option<Expr<'a>>, from: Ty<'a>, to: Ty<'a>, rel: Relation
  ) -> Result<(), Vec<Coercion<'a>>> {
    if from == to { return Ok(()) }
    match self.relate_whnf_ty(from.into(), to.into(), rel) {
      Ok(coes) if coes.is_empty() => Ok(()),
      Ok(coes) => Err(coes),
      Err(()) => {
        if let Some(pe) = pe {
          // ignore the original type and just try to check the value at the target
          if self.try_check_pure_expr(span, pe, to) {
            return Err(vec![Coercion::TypedPure(to)])
          }
        }
        self.errors.push(hir::Spanned {span, k: TypeError::Relate(from, to, rel)});
        Err(vec![Coercion::Error])
      }
    }
  }

  fn lower_tuple_pattern(&mut self, span: &'a FileSpan,
    pat: &'a ast::TuplePatternKind,
    expect_e: Option<Expr<'a>>,
    expect_t: Option<Ty<'a>>,
  ) -> (UnelabTupPat<'a>, Option<Expr<'a>>) {
    match pat {
      &ast::TuplePatternKind::Name(g, n, v) => {
        let ty = expect_t.unwrap_or_else(|| self.new_ty_mvar(span));
        let ctx = self.new_context_next(v, expect_e, ty);
        self.dc.context = ctx.into();
        (UnelabTupPat {span, ctx, k: UnelabTupPatKind::Name(g, n)},
         Some(intern!(self, ExprKind::Var(v))))
      }
      ast::TuplePatternKind::Typed(pat, ty) => {
        let ty = self.lower_ty(ty, ExpectTy::supertype(expect_t));
        let pat = self.lower_tuple_pattern(&pat.span, &pat.k, expect_e, Some(ty));
        if let Some(tgt) = expect_t {
          if self.relate_ty(pat.0.span, expect_e, tgt, ty, Relation::Subtype).is_err() {
            let v = self.fresh_var2(pat.0.ctx.var);
            let ctx = self.new_context_next(v, None, tgt);
            self.dc.context = ctx.into();
            return (UnelabTupPat {span, ctx, k: UnelabTupPatKind::Error(Box::new(pat.0))}, None)
          }
        }
        pat
      }
      ast::TuplePatternKind::Tuple(pats) => {
        let tgt = expect_t.unwrap_or_else(|| self.new_ty_mvar(span));
        let v = self.fresh_var(Spanned { span: span.clone(), k: Symbol::UNDER });
        let (k, e) = match self.tuple_pattern_tuple(span, pats.len(), tgt) {
          TuplePatternResult::Indeterminate => {
            let (pats, _) = self.lower_tuple_pattern_tuple_with(pats, TupleIter::Ty(None));
            (UnelabTupPatKind::Tuple(pats), None)
          }
          TuplePatternResult::Fail(report) => {
            let (pats, _) = self.lower_tuple_pattern_tuple_with(pats, TupleIter::Ty(None));
            let ty = intern!(self, TyKind::List(
              self.alloc.alloc_slice_fill_iter(pats.iter().map(|pat| pat.ctx.ty))));
            if report {
              self.errors.push(hir::Spanned {span, k: TypeError::PatternMatch(tgt, ty)});
            }
            let v1 = self.fresh_var(Spanned { span: span.clone(), k: Symbol::UNDER });
            let ctx = self.new_context_next(v1, None, ty);
            self.dc.context = ctx.into();
            let pat = Box::new(UnelabTupPat {span, ctx, k: UnelabTupPatKind::Tuple(pats)});
            (UnelabTupPatKind::Error(pat), Some(self.common.e_error))
          }
          TuplePatternResult::Tuple(mk, it) => {
            // let mut it = tys.iter();
            let (pats, es) = self.lower_tuple_pattern_tuple_with(pats, it);
            (UnelabTupPatKind::Tuple(pats), mk.build(self, es))
          }
        };
        let ctx = self.new_context_next(v, expect_e, tgt);
        self.dc.context = ctx.into();
        (UnelabTupPat {span, ctx, k}, e)
      }
    }
  }

  /// Get a plausible type for the given expression. (This is only heuristic,
  /// as a lot of information is lost in translating `hir::Expr` to `ty::Expr`,
  /// the latter of which is only weakly typed.
  /// It gives correct results for lvalues though.)
  fn expr_type(&mut self, sp: &'a FileSpan, e: Expr<'a>) -> Option<Ty<'a>> {
    Some(match e.k {
      ExprKind::Var(v) => self.dc.get_var(v).2,
      ExprKind::Index(a, _) => match self.expr_type(sp, a)?.k {
        TyKind::Array(ty, _) => ty,
        _ => return None,
      }
      ExprKind::Slice([a, _, len]) => match self.expr_type(sp, a)?.k {
        TyKind::Array(ty, _) => intern!(self, TyKind::Array(ty, len)),
        _ => return None,
      }
      ExprKind::Proj(a, i) => match self.expr_type(sp, a)?.k {
        TyKind::List(tys) => *tys.get(u32_as_usize(i))?,
        TyKind::Struct(args) => {
          let ty = args.get(u32_as_usize(i))?.k.1.var().k.ty;
          let mut subst = Subst::default();
          subst.add_fvars(Ok(a));
          for (j, &arg) in args.iter().enumerate().take(u32_as_usize(i)) {
            let pat = &arg.k.1.var().k;
            if !pat.k.is_name() { unimplemented!("subfields") }
            subst.push_raw(pat.var, Ok(intern!(self,
              ExprKind::Proj(a, j.try_into().expect("overflow")))))
          }
          subst.subst_ty(self, sp, ty)
        }
        _ => return None,
      }
      ExprKind::Unit => self.common.t_unit,
      ExprKind::Const(c) =>
        match &let_unchecked!(Some(Entity::Const(tc)) = self.names.get(&c), tc).k {
          ConstTc::ForwardDeclared => return None,
          ConstTc::Checked {ty, ..} => ty.clone().import_global(self),
        },
      ExprKind::Bool(_) => self.common.t_bool,
      ExprKind::Int(n) => if n.is_negative() {self.common.int()} else {self.common.nat()},
      ExprKind::Unop(op, _) => op.ret_ty(self),
      ExprKind::Binop(op, e1, e2) => if op.ty().int_out() {
        if op.preserves_nat() &&
          matches!(self.expr_type(sp, e1)?.k, TyKind::Int(IntTy::UInt(_))) &&
          matches!(self.expr_type(sp, e2)?.k, TyKind::Int(IntTy::UInt(_))) {
          self.common.nat()
        } else { self.common.int() }
      } else { self.common.t_bool },
      ExprKind::List(es) => {
        let tys = es.iter().map(|e| self.expr_type(sp, e)).collect::<Option<Vec<_>>>()?;
        intern!(self, TyKind::List(self.alloc.alloc_slice_fill_iter(tys.into_iter())))
      }
      ExprKind::Array(es) => if let Some(&e) = es.first() {
        intern!(self, TyKind::Array(self.expr_type(sp, e)?,
          intern!(self, ExprKind::Int(self.alloc.alloc(es.len().into())))))
      } else { self.common.t_unit },
      ExprKind::Sizeof(_) => self.common.nat(),
      ExprKind::Error => self.common.t_error,
      _ => return None,
    })
  }

  /// Get the type of the given place.
  fn place_type(&mut self, sp: &'a FileSpan, e: Place<'a>) -> Option<Ty<'a>> {
    Some(match e.k {
      PlaceKind::Var(v) => self.dc.get_var(v).2,
      PlaceKind::Index(a, _, _) => match self.place_type(sp, a)?.k {
        TyKind::Array(ty, _) => ty,
        _ => return None,
      }
      PlaceKind::Slice(a, _, [_, len]) => match self.place_type(sp, a)?.k {
        TyKind::Array(ty, _) => intern!(self, TyKind::Array(ty, len)),
        _ => return None,
      }
      PlaceKind::Proj(a, _, i) => {
        let aty = self.place_type(sp, a)?;
        match aty.k {
          TyKind::List(tys) => *tys.get(u32_as_usize(i))?,
          TyKind::Struct(args) => {
            let ty = args.get(u32_as_usize(i))?.k.1.var().k.ty;
            let mut subst = Subst::default();
            subst.add_fvars_place(a);
            let a = self.place_to_expr(a);
            for (j, &arg) in args.iter().enumerate().take(u32_as_usize(i)) {
              let pat = &arg.k.1.var().k;
              if !pat.k.is_name() { unimplemented!("subfields") }
              subst.push_raw(pat.var, Ok(intern!(self,
                ExprKind::Proj(a, j.try_into().expect("overflow")))))
            }
            subst.subst_ty(self, sp, ty)
          }
          _ => return None,
        }
      }
      PlaceKind::Error => self.common.t_error,
    })
  }

  /// Check if a pure expression can be typed without any additional information.
  /// (This is only heuristic, and can be incorrect sometimes; this is only used when we would
  /// otherwise yield a type error anyway.)
  fn try_check_pure_expr(&mut self, sp: &'a FileSpan, e: Expr<'a>, tgt: Ty<'a>) -> bool {
    let e = self.whnf_expr(sp, e);
    match (&e.k, &self.whnf_ty(sp, tgt.into()).ty.k) {
      (&ExprKind::Int(n), &TyKind::Int(ity)) => ity.contains(n),
      (&ExprKind::List(es), &TyKind::List(tys)) => es.len() == tys.len() &&
        es.iter().zip(tys).all(|(&e, &ty)| self.try_check_pure_expr(sp, e, ty)),
      (&ExprKind::If {then, els, ..}, _) =>
        self.try_check_pure_expr(sp, then, tgt) &&
        self.try_check_pure_expr(sp, els, tgt),
      // TODO: more heuristics?
      _ => self.expr_type(sp, e).map_or(false, |ty| self.relate_whnf_ty(
        ty.into(), tgt.into(), Relation::Subtype).is_ok()),
    }
  }

  fn tuple_pattern_tuple(&mut self,
    sp: &'a FileSpan, nargs: usize, expect: Ty<'a>
  ) -> TuplePatternResult<'a> {
    macro_rules! expect {($n:expr) => {{
      if nargs != $n { return TuplePatternResult::Fail(true) }
    }}}
    let wty = self.whnf_ty(sp, expect.into());
    match wty.ty.k {
      TyKind::Ghost(_) |
      TyKind::Uninit(_) |
      TyKind::Moved(_) => unreachable!(),
      TyKind::Infer(_) => TuplePatternResult::Indeterminate,
      TyKind::Error => TuplePatternResult::Fail(true),
      TyKind::Unit => {
        expect!(0);
        TuplePatternResult::Tuple(TupleMatchKind::Unit, TupleIter::Ty(None))
      }
      TyKind::True => {
        expect!(0);
        TuplePatternResult::Tuple(TupleMatchKind::True, TupleIter::Ty(None))
      }
      TyKind::Array(ty, n) => {
        #[allow(clippy::never_loop)]
        let n_tgt: Option<usize> = match self.whnf_expr(sp, n).k {
          ExprKind::Int(n) => n.try_into().ok(),
          _ => None
        };
        if let Some(n_tgt) = n_tgt { expect!(n_tgt) }
        let e_nargs = intern!(self, ExprKind::Int(self.alloc.alloc(nargs.into())));
        if self.equate_expr(n, e_nargs).is_err() {
          return TuplePatternResult::Fail(true)
        }
        TuplePatternResult::Tuple(TupleMatchKind::Array,
          TupleIter::List(self.alloc.alloc_slice_fill_copy(nargs, ty).iter()))
      }
      TyKind::Own(ty) => {
        expect!(2);
        TuplePatternResult::Tuple(TupleMatchKind::Own, TupleIter::Own(ty))
      }
      TyKind::Shr(lft, ty) => {
        expect!(2);
        TuplePatternResult::Tuple(TupleMatchKind::Shr, TupleIter::Shr(lft, ty))
      }
      TyKind::List(tys) | TyKind::And(tys) => {
        expect!(tys.len());
        let tys = if wty.is_ty() { tys } else {
          let tys = tys.iter().map(|ty| wty.map(ty).to_ty(self)).collect::<Vec<_>>();
          self.alloc.alloc_slice_fill_iter(tys.into_iter())
        };
        let mk = if matches!(wty.ty.k, TyKind::List(_)) {TupleMatchKind::List} else {TupleMatchKind::And};
        TuplePatternResult::Tuple(mk, TupleIter::List(tys.iter()))
      }
      TyKind::Sn(e, ty) => {
        expect!(2);
        TuplePatternResult::Tuple(TupleMatchKind::Sn, TupleIter::Sn(e, ty))
      }
      TyKind::Struct(args) => {
        expect!(args.iter().filter(|&arg| matches!(arg.k.1, ArgKind::Lam(_))).count());
        TuplePatternResult::Tuple(TupleMatchKind::Struct,
          TupleIter::mk_args(self, sp, Subst::default(), args.iter()))
      }
      _ => TuplePatternResult::Fail(false),
    }
  }

  fn lower_tuple_pattern_tuple_with(&mut self,
    pats: &'a [(VarId, ast::TuplePattern)],
    it: TupleIter<'a>,
  ) -> (Vec<UnelabTupPat<'a>>, Vec<Option<Expr<'a>>>) {
    let mut es = Vec::with_capacity(pats.len());
    let mut opt_it = Some(it);
    let pats = pats.iter().map(|&(_, Spanned {ref span, k: ref pat})| {
      let tgt = opt_it.as_mut().and_then(|it| it.next(self));
      let (pat, e) = self.lower_tuple_pattern(span, pat, None, tgt);
      if let Some(it) = &mut opt_it {
        if let Some(e) = e { it.push(self, span, e) }
        else { opt_it = None }
      }
      es.push(e);
      pat
    }).collect();
    (pats, es)
  }

  fn finish_tuple_pattern_inner(&mut self,
    pat: &UnelabTupPat<'a>, tgt: Option<Ty<'a>>,
  ) -> (TuplePattern<'a>, Expr<'a>) {
    let err = tgt.filter(|tgt|
      self.relate_ty(pat.span, None, pat.ctx.ty, tgt, Relation::Equal).is_err());
    let (k, e) = match &pat.k {
      &UnelabTupPatKind::Name(_, n) => {
        self.dc.context = pat.ctx.into();
        (TuplePatternKind::Name(n), intern!(self, ExprKind::Var(pat.ctx.var)))
      }
      UnelabTupPatKind::Error(pat) => {
        let (pat2, e) = self.finish_tuple_pattern_inner(pat, Some(pat.ctx.ty));
        (TuplePatternKind::Error(pat2), e)
      }
      UnelabTupPatKind::Tuple(pats) => {
        let mut res = self.tuple_pattern_tuple(pat.span, pats.len(), pat.ctx.ty);
        if let TuplePatternResult::Indeterminate = res {
          let tys = self.alloc.alloc_slice_fill_iter(pats.iter().map(|pat| pat.ctx.ty));
          res = TuplePatternResult::Tuple(TupleMatchKind::List, TupleIter::List(tys.iter()))
        }
        match res {
          TuplePatternResult::Indeterminate => unreachable!(),
          TuplePatternResult::Fail(_) => {
            let ty = intern!(self, TyKind::List(
              self.alloc.alloc_slice_fill_iter(pats.iter().map(|pat| pat.ctx.ty))));
            let pats = pats.iter().map(|pat| {
              self.finish_tuple_pattern_inner(pat, None).0
            }).collect::<Vec<_>>();
            let pats = self.alloc.alloc_slice_fill_iter(pats.into_iter());
            let v = self.fresh_var2(pat.ctx.var);
            let k = TuplePatternKind::Tuple(pats, TupleMatchKind::List);
            let pat = intern!(self, TuplePatternS { var: v, k, ty });
            (TuplePatternKind::Error(pat), self.common.e_error)
          }
          TuplePatternResult::Tuple(mk, mut it) => {
            let mut es = Vec::with_capacity(pats.len());
            let pats = pats.iter().map(|u_pat| {
              let tgt = it.next(self);
              let (pat, e) = self.finish_tuple_pattern_inner(u_pat, tgt);
              it.push(self, u_pat.span, e);
              es.push(Some(e));
              pat
            }).collect::<Vec<_>>();
            let pats = self.alloc.alloc_slice_fill_iter(pats.into_iter());
            let e = mk.build(self, es).unwrap_or(self.common.e_error);
            (TuplePatternKind::Tuple(pats, mk), e)
          }
        }
      }
    };
    let var = pat.ctx.var;
    let (k, ty) = match err {
      None => (k, pat.ctx.ty),
      Some(tgt) => {
        let v = self.fresh_var2(var);
        let pat = TuplePatternS { var: v, k, ty: pat.ctx.ty };
        (TuplePatternKind::Error(intern!(self, pat)), tgt)
      }
    };
    (intern!(self, TuplePatternS { var, k, ty }), e)
  }

  fn finish_tuple_pattern(&mut self,
    pat: &UnelabTupPat<'a>
  ) -> hir::Spanned<'a, TuplePattern<'a>> {
    self.dc.context = pat.ctx.parent;
    let base = self.dc.context;
    let (res, _) = self.finish_tuple_pattern_inner(pat, None);
    self.dc.context = base;
    hir::Spanned { span: pat.span, k: res }
  }

  fn lower_opt_lft(&mut self, sp: &'a FileSpan, lft: &Option<Box<Spanned<ast::Lifetime>>>) -> Lifetime {
    self.lower_lft(sp, match lft {
      None => ast::Lifetime::Infer,
      Some(lft) => lft.k,
    })
  }

  fn lower_lft(&mut self, sp: &'a FileSpan, lft: ast::Lifetime) -> Lifetime {
    match lft {
      ast::Lifetime::Extern => Lifetime::Extern,
      ast::Lifetime::Place(v) => Lifetime::Place(v),
      ast::Lifetime::Infer => self.new_lft_mvar(sp)
    }
  }

  fn lower_ty(&mut self, ty: &'a ast::Type, expect: ExpectTy<'a>) -> Ty<'a> {
    match &ty.k {
      ast::TypeKind::Unit => self.common.t_unit,
      ast::TypeKind::True => self.common.t_true,
      ast::TypeKind::False => self.common.t_false,
      ast::TypeKind::Bool => self.common.t_bool,
      &ast::TypeKind::Var(v) => intern!(self, TyKind::Var(v)),
      &ast::TypeKind::Int(sz) => self.common.t_int(sz),
      &ast::TypeKind::UInt(sz) => self.common.t_uint(sz),
      ast::TypeKind::Array(ty, n) => {
        let ty = self.lower_ty(ty, ExpectTy::Any);
        let (n, _) = self.lower_pure_expr(n, ExpectExpr::HasTy(self.common.nat()));
        intern!(self, TyKind::Array(ty, n))
      }
      ast::TypeKind::Own(ty) => {
        let ty = self.lower_ty(ty, ExpectTy::Any);
        intern!(self, TyKind::Own(ty))
      }
      ast::TypeKind::Shr(lft, ty) => {
        let lft = self.lower_opt_lft(&ty.span, lft);
        let ty = self.lower_ty(ty, ExpectTy::Any);
        intern!(self, TyKind::Shr(lft, ty))
      }
      ast::TypeKind::Ref(lft, ty) => {
        let lft = self.lower_opt_lft(&ty.span, lft);
        let ty = self.lower_ty(ty, ExpectTy::Any);
        intern!(self, TyKind::Ref(lft, ty))
      }
      ast::TypeKind::RefSn(e) => {
        let (e, pe) = self.lower_place(e);
        intern!(self, TyKind::RefSn(self.as_pure_place(e.span, pe)))
      }
      ast::TypeKind::List(tys) => {
        let tys = self.alloc.alloc_slice_fill_iter(
          tys.iter().map(|ty| self.lower_ty(ty, ExpectTy::Any)));
        intern!(self, TyKind::List(tys))
      }
      ast::TypeKind::Sn(e) => {
        let (e, ty) = self.lower_pure_expr(e, ExpectExpr::Any);
        intern!(self, TyKind::Sn(e, ty))
      }
      ast::TypeKind::Struct(args) => {
        let args = args.iter()
          .map(|arg| self.lower_arg(&arg.span, ArgAttr::empty(), &arg.k.1)).collect();
        let args = self.finish_args(args);
        let args = self.alloc.alloc_slice_fill_iter(
          args.iter().map(|(attr, arg)| intern!(self, (*attr, arg.into()))));
        intern!(self, TyKind::Struct(args))
      }
      ast::TypeKind::All(pats, ty) => {
        let pats = pats.iter().map(|pat| {
          self.lower_tuple_pattern(&pat.span, &pat.k, None, None).0
        }).collect::<Vec<_>>();
        let mut ty = self.lower_ty(ty, ExpectTy::Any);
        for pat in pats.into_iter().rev() {
          let pat = self.finish_tuple_pattern(&pat).k;
          ty = intern!(self, TyKind::All(pat, ty))
        }
        ty
      }
      ast::TypeKind::Imp(p, q) => intern!(self, TyKind::Imp(
        self.lower_ty(p, ExpectTy::Any), self.lower_ty(q, ExpectTy::Any))),
      ast::TypeKind::Wand(p, q) => intern!(self, TyKind::Wand(
        self.lower_ty(p, ExpectTy::Any), self.lower_ty(q, ExpectTy::Any))),
      ast::TypeKind::Not(p) =>
        intern!(self, TyKind::Not(self.lower_ty(p, ExpectTy::Any))),
      ast::TypeKind::And(tys) => {
        let tys = tys.iter().map(|ty| self.lower_ty(ty, ExpectTy::Any)).collect::<Vec<_>>();
        let tys = self.alloc.alloc_slice_fill_iter(tys.into_iter());
        intern!(self, TyKind::And(tys))
      }
      ast::TypeKind::Or(tys) => {
        let tys = tys.iter().map(|ty| self.lower_ty(ty, ExpectTy::Any)).collect::<Vec<_>>();
        let tys = self.alloc.alloc_slice_fill_iter(tys.into_iter());
        intern!(self, TyKind::Or(tys))
      }
      ast::TypeKind::If(e, t, f) => {
        let e = self.check_pure_expr(e, self.common.t_bool);
        let t = self.lower_ty(t, ExpectTy::Any);
        let f = self.lower_ty(f, ExpectTy::Any);
        intern!(self, TyKind::If(e, t, f))
      }
      ast::TypeKind::Ghost(ty) =>
        intern!(self, TyKind::Ghost(self.lower_ty(ty, ExpectTy::Any))),
      ast::TypeKind::Uninit(ty) =>
        intern!(self, TyKind::Uninit(self.lower_ty(ty, ExpectTy::Any))),
      ast::TypeKind::Pure(e) =>
        intern!(self, TyKind::Pure(self.check_pure_expr(e, self.common.t_bool))),
      ast::TypeKind::User(f, tys, es) => {
        let tys = tys.iter().map(|ty| self.lower_ty(ty, ExpectTy::Any)).collect::<Vec<_>>();
        let tys = self.alloc.alloc_slice_fill_iter(tys.into_iter());
        let args = match &let_unchecked!(Some(Entity::Type(tc)) = self.names.get(f), tc).k {
          TypeTc::ForwardDeclared => return self.common.t_error,
          TypeTc::Typed(TypeTy {tyargs, args, ..}) => {
            assert_eq!(tys.len(), u32_as_usize(*tyargs));
            args.clone().inst_global(self, tys)
          }
        };
        let pes = self.check_args(&ty.span, es, args, |x| x.k).1;
        let pes = self.alloc.alloc_slice_fill_iter({
          pes.into_iter().map(|pe| pe.unwrap_or_else(|sp| {
            self.errors.push(hir::Spanned {span: &ty.span, k: TypeError::ExpectedPure(sp)});
            self.common.e_error
          }))
        });
        intern!(self, TyKind::User(*f, tys, pes))
      }
      ast::TypeKind::Heap(e1, e2) => {
        let (e1, _) = self.lower_pure_expr(e1, ExpectExpr::Any);
        let (e2, ty) = self.lower_pure_expr(e2, ExpectExpr::Any);
        intern!(self, TyKind::Heap(e1, e2, ty))
      }
      ast::TypeKind::HasTy(e, ty) => {
        let (e, _) = self.lower_pure_expr(e, ExpectExpr::Any);
        let ty = self.lower_ty(ty, ExpectTy::Any);
        intern!(self, TyKind::HasTy(e, ty))
      }
      ast::TypeKind::Input => intern!(self, TyKind::Input),
      ast::TypeKind::Output => intern!(self, TyKind::Output),
      ast::TypeKind::Moved(ty) => intern!(self, TyKind::Moved(self.lower_ty(ty, ExpectTy::Any))),
      ast::TypeKind::Infer => expect.to_ty().unwrap_or_else(|| self.new_ty_mvar(&ty.span)),
      ast::TypeKind::Error => self.common.t_error,
    }
  }

  fn lower_pure_expr(&mut self, e: &'a ast::Expr, expect: ExpectExpr<'a>) -> (Expr<'a>, Ty<'a>) {
    let (hir::Spanned {k: (_, (_, ty)), ..}, pe) = self.lower_expr(e, expect);
    (self.as_pure(&e.span, pe), ty)
  }

  fn apply_coe(&mut self, c: Coercion<'a>, e: Expr<'a>) -> Expr<'a> {
    match c {
      Coercion::TypedPure(_) => e,
      Coercion::Error => self.common.e_error,
    }
  }

  fn apply_coe_expr(&mut self, c: Coercion<'a>, e: hir::Expr<'a>) -> hir::Expr<'a> {
    match c {
      Coercion::TypedPure(ty) => {
        let pe = e.k.1 .0;
        hir::Spanned {
          span: e.span,
          k: (hir::ExprKind::Cast(Box::new(e), ty, CastKind::Wand(None)), (pe, ty))
        }
      }
      Coercion::Error => e.map_into(|_|
        (hir::ExprKind::Error, (Some(self.common.e_error), self.common.t_error))),
    }
  }

  fn coerce_pure_expr(&mut self,
    sp: &'a FileSpan, mut e: Expr<'a>, from: Ty<'a>, to: Ty<'a>
  ) -> Expr<'a> {
    if let Err(coe) = self.relate_ty(sp, Some(e), from, to, Relation::Coerce) {
      for c in coe { e = self.apply_coe(c, e) }
    }
    e
  }

  fn check_pure_expr(&mut self, e: &'a ast::Expr, tgt: Ty<'a>) -> Expr<'a> {
    let (pe, ty) = self.lower_pure_expr(e, ExpectExpr::HasTy(tgt));
    self.coerce_pure_expr(&e.span, pe, ty, tgt)
  }

  fn lower_arg(&mut self, sp: &'a FileSpan, attr: ArgAttr, arg: &'a ast::ArgKind) -> UnelabArg<'a> {
    (attr, match arg {
      ast::ArgKind::Lam(pat) => {
        let mut expect_t = if_chain! {
          if attr.contains(ArgAttr::GLOBAL);
          if let ast::TuplePatternKind::Name(_, name, _) = pat;
          if let Some(Entity::Global(tc)) = self.names.get_mut(name);
          if let GlobalTc::Checked(ty) = &tc.k;
          then { Some(ty.clone().import_global(self)) }
          else { None }
        };
        if attr.contains(ArgAttr::MUT) {
          let ty = expect_t.unwrap_or_else(|| self.new_ty_mvar(sp));
          expect_t = Some(intern!(self, TyKind::Ref(Lifetime::Extern, ty)));
        }
        UnelabArgKind::Lam(self.lower_tuple_pattern(sp, pat, None, expect_t).0)
      },
      ast::ArgKind::Let(Spanned {span, k: pat}, e) => {
        let ctx1 = self.dc.context;
        let pat = self.lower_tuple_pattern(span, pat, None, None).0;
        let ctx2 = mem::replace(&mut self.dc.context, ctx1);
        let pe = self.check_pure_expr(e, pat.ctx.ty);
        self.dc.context = ctx2;
        UnelabArgKind::Let(pat, pe, self.eval_expr(&e.span, pe).map(Box::new))
      }
    })
  }

  fn finish_arg(&mut self,
    (mut attr, arg): UnelabArg<'a>, fvars: &mut HashSet<VarId>
  ) -> hir::Arg<'a> {
    let mut dep = false;
    arg.var().on_vars_rev(&mut |v| dep |= fvars.remove(&v));
    if !dep { attr |= ArgAttr::NONDEP }
    let ty = arg.var().ctx.ty;
    ty.on_vars(|v| { fvars.insert(v); });
    if ty.ghostly() { attr |= ArgAttr::GHOST }
    (attr, match arg {
      UnelabArgKind::Lam(pat) => {
        hir::ArgKind::Lam(self.finish_tuple_pattern(&pat))
      }
      UnelabArgKind::Let(pat, pe, e) => {
        let pat = self.finish_tuple_pattern(&pat);
        pe.on_vars(|v| { fvars.insert(v); });
        hir::ArgKind::Let(pat, pe, e)
      }
    })
  }

  fn finish_args2<T>(&mut self, args: Vec<UnelabArg<'a>>,
    mut f: impl FnMut(&mut Self, hir::Arg<'a>) -> T
  ) -> Box<[T]> {
    let mut fvars = HashSet::new();
    let mut args = args.into_iter().rev().map(|arg| {
      let r = self.finish_arg(arg, &mut fvars);
      f(self, r)
    }).collect::<Box<[_]>>();
    args.reverse();
    args
  }

  fn finish_args(&mut self, args: Vec<UnelabArg<'a>>) -> Box<[hir::Arg<'a>]> {
    self.finish_args2(args, |_, x| x)
  }

  fn args_to_ty_args(&mut self, args: &[hir::Arg<'a>]) -> &'a [Arg<'a>] {
    let args = args.iter().map(|(attr, arg)| intern!(self, (*attr, arg.into())))
      .collect::<Vec<_>>();
    self.alloc.alloc_slice_fill_iter(args.into_iter())
  }

  fn lower_variant(&mut self, variant: &'a Option<Box<ast::Variant>>) -> Option<hir::Variant<'a>> {
    variant.as_deref().map(|Spanned {k: (e, vt), ..}| match vt {
      ast::VariantType::Down => {
        let e = self.check_pure_expr(e, self.common.nat());
        hir::Variant(e, hir::VariantType::Down)
      }
      ast::VariantType::UpLt(e2) => {
        let e = self.check_pure_expr(e, self.common.int());
        let e2 = self.check_pure_expr(e2, self.common.int());
        hir::Variant(e, hir::VariantType::UpLt(e2))
      }
      ast::VariantType::UpLe(e2) => {
        let e = self.check_pure_expr(e, self.common.int());
        let e2 = self.check_pure_expr(e2, self.common.int());
        hir::Variant(e, hir::VariantType::UpLe(e2))
      }
    })
  }

  fn check_array(&mut self, span: &'a FileSpan,
    a: &'a ast::Expr, ty: Ty<'a>, n: Expr<'a>
  ) -> (Ty<'a>, hir::Expr<'a>, RExpr<'a>) {
    let arrty = intern!(self, TyKind::Array(ty, n));
    let (mut e_a, a) = self.lower_expr(a, ExpectExpr::HasTy(arrty));
    while let TyKind::Ref(_, aty2) = e_a.ty().k {
      e_a = hir::Expr {span, k: (hir::ExprKind::Rval(Box::new(e_a)), (a.ok(), aty2))};
    }
    (arrty, self.coerce_expr(e_a, a, arrty), a)
  }

  fn build_lens(mut origin: Place<'a>
  ) -> Option<(VarId, impl FnOnce(&mut InferCtx<'a, 'n>, Expr<'a>) -> Expr<'a>)> {
    enum Projection<'a> {
      Index(Expr<'a>),
      Slice(Expr<'a>, Expr<'a>),
      Proj(u32),
    }
    let mut lens = vec![];
    let v = loop {
      match origin.k {
        PlaceKind::Var(v) => break v,
        PlaceKind::Index(a, _, i) => {lens.push(Projection::Index(i)); origin = a}
        PlaceKind::Slice(a, _, [i, l]) => {lens.push(Projection::Slice(i, l)); origin = a}
        PlaceKind::Proj(a, _, i) => {lens.push(Projection::Proj(i)); origin = a}
        PlaceKind::Error => return None
      }
    };
    Some((v, move |this: &mut InferCtx<'a, 'n>, mut val| {
      let mut elhs = intern!(this, ExprKind::Var(v));
      for l in lens {
        match l {
          Projection::Index(i) => {
            val = intern!(this, ExprKind::UpdateIndex([elhs, i, val]));
            elhs = intern!(this, ExprKind::Index(elhs, i));
          }
          Projection::Slice(i, l) => {
            val = intern!(this, ExprKind::UpdateSlice([elhs, i, l, val]));
            elhs = intern!(this, ExprKind::Slice([elhs, i, l]));
          }
          Projection::Proj(i) => {
            val = intern!(this, ExprKind::UpdateProj(elhs, i, val));
            elhs = intern!(this, ExprKind::Proj(elhs, i));
          }
        }
      }
      val
    }))
  }

  fn check_call(&mut self,
    &Spanned {ref span, k: f}: &'a Spanned<Symbol>,
    tys: &'a [ast::Type],
    es: &'a [ast::Expr],
    pf: Option<&'a ast::Expr>
  ) -> Option<(hir::Call<'a>, RExprTy<'a>)> {
    let tys = tys.iter().map(|ty| self.lower_ty(ty, ExpectTy::Any)).collect::<Vec<_>>();
    let tys = &*self.alloc.alloc_slice_fill_iter(tys.into_iter());
    let ty = let_unchecked!(Some(Entity::Proc(ty)) = self.names.get(&f), ty).k.ty()?;
    let ProcTy {kind, tyargs, args, outs, rets, variant, ..} = ty.clone();
    assert_eq!(tys.len(), u32_as_usize(tyargs));
    let mut gctx = FromGlobalCtx::new(self, tys);
    let args = args.from_global(&mut gctx);
    let (es, pes, mut subst) = gctx.ic.check_args(span, es, args, |x| x.k);
    let variant = variant.map(|v| v.from_global(&mut gctx));
    let variant = gctx.ic.check_variant_use(&mut subst, pf, variant);
    if !outs.is_empty() {
      let newgen = gctx.ic.new_generation();
      for (&i, ret) in outs.iter().zip(&*rets) {
        let ret = ret.from_global(&mut gctx);
        let ret = subst.subst_arg(gctx.ic, span, ret);
        let arg = match pes.get(u32_as_usize(i)) {
          Some(Ok(&WithMeta {k: ExprKind::Ref(p), ..})) => p,
          _ => unreachable!()
        };
        let w = ret.k.1.var().k.var;
        let (origin, lens) = Self::build_lens(arg)?;
        let (_, _, ty) = gctx.ic.dc.get_var(origin);
        let w2 = gctx.ic.fresh_var2(w);
        let ctx = gctx.ic.new_context_next(w2, None, ty); // FIXME: ty is not correct here
        let new_val = intern!(gctx.ic, ExprKind::Var(w2));
        let new_val = lens(gctx.ic, new_val);
        subst.add_fvars(Ok(new_val));
        subst.push_raw(w, Ok(new_val));
        gctx.ic.dc.context = ctx.into();
      }
      gctx.ic.dc.generation = newgen;
    }
    let gen = gctx.ic.dc.generation;
    let rets = rets[outs.len()..].iter().map(|arg| {
      let arg = arg.from_global(&mut gctx);
      subst.subst_arg(gctx.ic, span, arg)
    }).collect::<Vec<_>>();
    drop(gctx);
    let rets = &*self.alloc.alloc_slice_fill_iter(rets.into_iter());
    let (mut rk, ret) = match rets.len() {
      0 => (ReturnKind::Unit, self.common.t_unit),
      1 => match rets[0].k.1 {
        ArgKind::Lam(pat) => (ReturnKind::One, pat.k.ty),
        ArgKind::Let(..) => (ReturnKind::Unit, self.common.t_unit),
      }
      // TODO: support {x := a, _ : T x} returns as `One`
      _ => {
        let n = rets.iter().filter(|&a| matches!(a.k.1, ArgKind::Lam(_))).count()
          .try_into().expect("too many args");
        (ReturnKind::Struct(n), intern!(self, TyKind::Struct(rets)))
      }
    };
    if ret.k == TyKind::False { rk = ReturnKind::Unreachable }
    let (side_effect, pe) = match kind {
      ProcKind::Func => (false, pes.into_iter().collect::<Result<Vec<_>, _>>()
        .map(|pes| intern!(self, ExprKind::Call {f, tys,
          args: self.alloc.alloc_slice_fill_iter(pes.into_iter())}))),
      ProcKind::Proc | ProcKind::Main => (true, Err(span)),
    };
    let call = hir::Call {
      f: hir::Spanned {span, k: f},
      side_effect, tys, args: es, variant, gen, rk,
    };
    Some((call, (pe, ret)))
  }

  fn prop_to_expr(&mut self, sp: &'a FileSpan, p: Ty<'a>) -> Option<Expr<'a>> {
    Some(match self.whnf_ty(sp, p.into()).ty.k {
      TyKind::True | TyKind::Unit => self.common.e_bool(true),
      TyKind::False => self.common.e_bool(false),
      TyKind::Imp(p, q) | TyKind::Wand(p, q) =>
        intern!(self, ExprKind::Binop(Binop::Or,
          intern!(self, ExprKind::Unop(Unop::Not, self.prop_to_expr(sp, p)?)),
          self.prop_to_expr(sp, q)?)),
      TyKind::Not(p) =>
        intern!(self, ExprKind::Unop(Unop::Not, self.prop_to_expr(sp, p)?)),
      TyKind::And(ps) | TyKind::List(ps) => {
        let mut ret = None;
        for p in ps {
          let p = self.prop_to_expr(sp, p)?;
          ret = Some(ret.map_or(p, |r| intern!(self, ExprKind::Binop(Binop::And, r, p))))
        }
        ret.unwrap_or_else(|| self.common.e_bool(false))
      }
      TyKind::Or(ps) => {
        let mut ret = None;
        for p in ps {
          let p = self.prop_to_expr(sp, p)?;
          ret = Some(ret.map_or(p, |r| intern!(self, ExprKind::Binop(Binop::Or, r, p))))
        }
        ret.unwrap_or_else(|| self.common.e_bool(true))
      }
      TyKind::Pure(e) => e,
      TyKind::Infer(v) => {
        let w = self.new_expr_mvar(self.mvars.ty[v].span);
        let p = intern!(self, TyKind::Pure(w));
        self.mvars.ty.assign(v, p);
        w
      }
      _ => return None,
    })
  }

  fn binop_ty(&mut self, op: Binop,
    ty1: impl FnOnce(&mut Self) -> Option<IntTy>,
    ty2: impl FnOnce(&mut Self) -> Option<IntTy>,
  ) -> (IntTy, Ty<'a>) {
    let opty = op.ty();
    if opty.int_out() {
      let ity = (|| {
        if !op.preserves_nat() {return IntTy::INT}
        let sz1 = if let Some(IntTy::UInt(sz1)) = ty1(self) {sz1} else {return IntTy::INT};
        let sz2 = if let Some(IntTy::UInt(sz2)) = ty2(self) {sz2} else {return IntTy::INT};
        if op.preserves_usize() { IntTy::UInt(std::cmp::max(sz1, sz2)) }
        else { IntTy::NAT }
      })();
      (ity, self.common.int_ty(ity))
    } else {
      (IntTy::INT, self.common.t_bool)
    }
  }

  fn whnf_expect(&mut self, sp: &'a FileSpan, expect: ExpectExpr<'a>) -> Option<Ty<'a>> {
    Some(self.whnf_ty(sp, expect.to_ty()?.into()).ty)
  }

  fn as_int_ty(&mut self, sp: &'a FileSpan, expect: ExpectExpr<'a>) -> Option<IntTy> {
    self.whnf_expect(sp, expect)?.as_int_ty()
  }

  fn lower_expr_sn(&mut self, span: &'a FileSpan, expect: ExpectExpr<'a>,
    x: &'a ast::Expr, h: Option<&'a ast::Expr>,
  ) -> (hir::ExprKind<'a>, Expr<'a>, Ty<'a>) {
    let expect2 = ExpectExpr::has_ty(self.whnf_expect(span, expect));
    let (e, pe) = self.lower_expr(x, expect2);
    let ty = e.ty();
    let y = self.as_pure(&x.span, pe);
    let (x, h) = if let Some(h) = h {
      let x = if let ExpectExpr::Sn(x, _) = expect {x} else {self.new_expr_mvar(span)};
      let ty = intern!(self, TyKind::Pure(intern!(self, ExprKind::Binop(Binop::Eq, y, x))));
      (x, Some(Box::new(self.check_expr(h, ty).0)))
    } else {
      (y, None)
    };
    (hir::ExprKind::Sn(Box::new(e), h), y, intern!(self, TyKind::Sn(x, ty)))
  }

  #[allow(clippy::similar_names)]
  fn lower_expr_kind(&mut self, span: &'a FileSpan,
    e: &'a ast::ExprKind, expect: ExpectExpr<'a>
  ) -> (hir::Expr<'a>, RExpr<'a>) {
    macro_rules! unit {() => {self.common.e_unit}}
    macro_rules! ret {($k:expr, $pe:expr, $ty:expr) => {{
      let pe: RExpr<'a> = $pe;
      (hir::Expr {span, k: {#[allow(unused)] use hir::ExprKind::*; ($k, (pe.ok(), $ty))}}, pe)
    }}}
    macro_rules! error {($($sp:expr, $es:expr),*) => {{
      $({
        use TypeError::*; let k = $es;
        self.errors.push(hir::Spanned {span: $sp, k});
      })*
      return ret![Error, Ok(self.common.e_error), self.common.t_error]
    }}}
    macro_rules! eval_expr {($sp:expr, $e:expr, $ty:expr) => {{
      if let Some(n) = self.eval_expr($sp, $e) { n }
      else { error!($sp, UnsupportedSynthesis(Box::new(self.dc.clone()), $e, $ty)) }
    }}}

    match e {
      ast::ExprKind::Unit => ret![Unit, Ok(unit!()), self.common.t_unit],

      &ast::ExprKind::Var(v) => {
        let (gen, val, ty) = self.dc.get_var(v);
        ret![Var(v, gen), Ok(val), ty]
      }

      &ast::ExprKind::Const(c) =>
        match &let_unchecked!(Some(Entity::Const(tc)) = self.names.get(&c), tc).k {
          ConstTc::ForwardDeclared => error!(),
          ConstTc::Checked {ty, ..} => {
            let ty = ty.clone().import_global(self);
            ret![Const(c), Ok(intern!(self, ExprKind::Const(c))), ty]
          }
        },

      &ast::ExprKind::Bool(b) =>
        ret![Bool(b), Ok(self.common.e_bool(b)), self.common.t_bool],

      ast::ExprKind::Int(n) => {
        #[allow(clippy::map_unwrap_or)]
        let ty = self.as_int_ty(span, expect)
          .filter(|ity| ity.contains(n))
          .map(|ity| self.common.int_ty(ity))
          .unwrap_or_else(|| {
            if n.is_negative() { self.common.int() }
            else { self.common.nat() }
          });
        ret![Int(n), Ok(intern!(self, ExprKind::Int(n))), ty]
      }

      ast::ExprKind::Unop(Unop::Neg, e) => {
        let (e, pe) = self.check_expr(e, self.common.int());
        ret![Unop(hir::Unop::Neg(IntTy::INT), Box::new(e)),
          pe.map(|pe| intern!(self, ExprKind::Unop(Unop::Neg, pe))),
          self.common.int()]
      }

      ast::ExprKind::Unop(Unop::Not, e) => {
        let (e, pe) = self.check_expr(e, self.common.t_bool);
        ret![Unop(hir::Unop::Not, Box::new(e)),
          pe.map(|pe| intern!(self, ExprKind::Unop(Unop::Not, pe))),
          self.common.t_bool]
      }

      ast::ExprKind::Unop(Unop::BitNot(_), e) => {
        let ity = self.as_int_ty(span, expect).unwrap_or(IntTy::INT);
        let ty = self.common.int_ty(ity);
        let (e, pe) = self.check_expr(e, ty);
        let sz = if let IntTy::UInt(sz) = ity { sz } else { Size::Inf };
        ret![Unop(hir::Unop::BitNot(ity), Box::new(e)),
          pe.map(|pe| intern!(self, ExprKind::Unop(Unop::BitNot(sz), pe))),
          ty]
      }

      ast::ExprKind::Unop(Unop::As(_), _) =>
        unreachable!("parsed as-conversions are not emitted by the front end"),

      &ast::ExprKind::Binop(op, ref e1, ref e2) => {
        if let Binop::Eq | Binop::Ne = op {
          let (e1, pe1) = self.lower_expr(e1, ExpectExpr::Any);
          let ty = e1.ty();
          let (e2, pe2) = self.lower_expr(e2, ExpectExpr::HasTy(ty));
          return ret![
            hir::ExprKind::Eq(ty, op == types::Binop::Ne, Box::new(e1), Box::new(e2)),
            pe1.and_then(|pe1| Ok(intern!(self, ExprKind::Binop(op, pe1, pe2?)))),
            self.common.t_bool]
        }
        let opty = op.ty();
        let (ity, (e1, pe1), (e2, pe2), tyout) = if opty.int_in() {
          let ityin = self.as_int_ty(span, expect).unwrap_or(IntTy::INT);
          let tyin1 = self.common.int_ty(ityin);
          let (e1, pe1) = self.lower_expr(e1, ExpectExpr::HasTy(tyin1));
          let tyin2 = if let (BinopType::IntNatInt, IntTy::Int(sz)) = (opty, ityin) {
            self.common.t_uint(sz)
          } else { tyin1 };
          let (e2, pe2) = self.lower_expr(e2, ExpectExpr::HasTy(tyin2));
          let (ityin2, tyout) = self.binop_ty(op,
            |this| this.as_int_ty(span, ExpectExpr::HasTy(e1.ty())),
            |this| this.as_int_ty(span, ExpectExpr::HasTy(e2.ty())));
          let tyin2 = self.common.int_ty(ityin2);
          let e1 = self.coerce_expr(e1, pe1, tyin1);
          let e2 = self.coerce_expr(e2, pe2, tyin2);
          (ityin2, (e1, pe1), (e2, pe2), tyout)
        } else {
          (IntTy::INT,
           self.check_expr(e1, self.common.t_bool),
           self.check_expr(e2, self.common.t_bool),
           self.common.t_bool)
        };
        ret![Binop(op.as_hir(ity), Box::new(e1), Box::new(e2)),
          pe1.and_then(|pe1| pe2.map(|pe2|
            intern!(self, ExprKind::Binop(op, pe1, pe2)))),
          tyout]
      }

      ast::ExprKind::Sn(x, h) => {
        let (ek, pe, ty) = self.lower_expr_sn(span, expect, x, h.as_deref());
        ret![ek, Ok(pe), ty]
      }

      ast::ExprKind::Index(arr, idx, hyp) => {
        let ty = expect.to_ty().unwrap_or_else(|| self.new_ty_mvar(span));
        let n = self.new_expr_mvar(span);
        let (arrty, e_a, arr) = self.check_array(span, arr, ty, n);
        let (e_i, idx) = self.check_expr(idx, self.common.nat());
        let hyp = match hyp {
          Some(h) => {
            let idx = self.as_pure(e_i.span, idx);
            let ty = intern!(self, TyKind::Pure(
              intern!(self, ExprKind::Binop(Binop::Lt, idx, n))));
            Ok(self.check_expr(h, ty).0)
          }
          None => Err(eval_expr!(span, n, self.common.nat())),
        };
        ret![Index(Box::new((arrty, [e_a, e_i], hyp))),
          arr.and_then(|a| Ok(intern!(self, ExprKind::Index(a, idx?)))),
          ty]
      }

      ast::ExprKind::Slice(args, hyp) => {
        let (arr, idx, len) = &**args;
        let ty = self.whnf_expect(span, expect)
          .and_then(|ty| if let TyKind::Array(ty, _) = ty.k {Some(ty)} else {None})
          .unwrap_or_else(|| self.new_ty_mvar(span));
        let n = self.new_expr_mvar(span);
        let (arrty, e_a, arr) = self.check_array(span, arr, ty, n);
        let (e_i, idx) = self.check_expr(idx, self.common.nat());
        let (e_l, len) = self.check_expr(len, self.common.nat());
        let pe_l = self.as_pure(e_l.span, len);
        let hyp = match hyp {
          Some(hyp) => {
            let e_i = self.as_pure(e_i.span, idx);
            let ty = intern!(self, TyKind::Pure(
              intern!(self, ExprKind::Binop(Binop::Le,
                intern!(self, ExprKind::Binop(Binop::Add, e_i, pe_l)), n))));
            Ok(self.check_expr(hyp, ty).0)
          }
          None => Err(eval_expr!(span, n, self.common.nat())),
        };
        ret![Slice(Box::new((arrty, [e_a, e_i, e_l], hyp))),
          arr.and_then(|a| Ok(intern!(self, ExprKind::Slice([a, idx?, pe_l])))),
          intern!(self, TyKind::Array(ty, pe_l))]
      }

      ast::ExprKind::Proj(e, field) => {
        enum ProjKind<'a> {
          And(&'a [Ty<'a>]),
          List(&'a [Ty<'a>]),
          Struct(&'a [Arg<'a>]),
        }
        let (mut e2, pe) = self.lower_expr(e, ExpectExpr::Any);
        let mut wty = self.whnf_ty(span, e2.ty().into()).ty;
        let tys = loop {
          match wty.k {
            TyKind::Ref(_, ty2) => {
              e2 = hir::Expr {span, k: (hir::ExprKind::Rval(Box::new(e2)), (pe.ok(), ty2))};
              wty = ty2;
            }
            TyKind::List(tys) => break ProjKind::List(tys),
            TyKind::And(tys) => break ProjKind::And(tys),
            TyKind::Struct(args) => break ProjKind::Struct(args),
            TyKind::Error => error!(),
            _ => error!(e2.span, ExpectedStruct(wty))
          }
        };
        let ret = |lk, i, pe, ty| ret![Proj(lk, Box::new((wty, e2)), i), pe, ty];
        #[allow(clippy::never_loop)] loop { // try block, not a loop
          match tys {
            ProjKind::List(tys) => if let FieldName::Number(i) = field.k {
              if let Some(&ty) = tys.get(u32_as_usize(i)) {
                break ret(ListKind::List, i,
                  pe.map(|pe| intern!(self, ExprKind::Proj(pe, i))), ty)
              }
            }
            ProjKind::And(tys) => if let FieldName::Number(i) = field.k {
              if let Some(&ty) = tys.get(u32_as_usize(i)) {
                break ret(ListKind::And, i, pe, ty)
              }
            }
            ProjKind::Struct(args) => {
              if let Some((i, vec)) = match field.k {
                FieldName::Number(i) if u32_as_usize(i) < args.len() => Some((i, vec![])),
                FieldName::Number(_) => None,
                FieldName::Named(f) => ArgKind::find_field(args, f),
              } {
                if !vec.is_empty() { unimplemented!("subfields") }
                let ty = args[u32_as_usize(i)].k.1.var().k.ty;
                let mut subst = Subst::default();
                subst.add_fvars(pe);
                for (j, &arg) in args.iter().enumerate().take(u32_as_usize(i)) {
                  let pat = &arg.k.1.var().k;
                  if !pat.k.is_name() { unimplemented!("subfields") }
                  subst.push_raw(pat.var, pe.map(|pe| intern!(self,
                    ExprKind::Proj(pe, j.try_into().expect("overflow")))))
                }
                let ty = subst.subst_ty(self, span, ty);
                break ret(ListKind::Struct, i,
                  pe.map(|pe| intern!(self, ExprKind::Proj(pe, i))), ty)
              }
            }
          }
          error!(&field.span, FieldMissing(wty, field.k))
        }
      }

      ast::ExprKind::Deref(e) => {
        let e2 = self.lower_expr(e, ExpectExpr::Any).0;
        let ty = e2.ty();
        let wty = self.whnf_ty(span, ty.into()).ty;
        match wty.k {
          TyKind::RefSn(e) => if let Some(ty) = self.place_type(span, e) {
            ret![Deref(Box::new((wty, e2))), Ok(self.place_to_expr(e)), ty]
          } else {
            error!(e2.span, ExpectedPlace)
          }
          TyKind::Error => error!(),
          _ => {
            let tgt = intern!(self, TyKind::RefSn(self.common.p_error));
            error!(e2.span, Relate(ty, tgt, Relation::Equal))
          }
        }
      }

      ast::ExprKind::List(es) => {
        let tgt = expect.to_ty()
          .map(|ty| self.whnf_ty(span, ty.into()).ty)
          .filter(|&ty| matches!(ty.k,
            TyKind::True |
            TyKind::Unit |
            TyKind::Array(_, _) |
            TyKind::Own(_) |
            TyKind::Shr(_, _) |
            TyKind::List(_) |
            TyKind::Sn(_, _) |
            TyKind::Struct(_) |
            TyKind::And(_) |
            TyKind::Error))
          .unwrap_or_else(|| {
            let tys = es.iter().map(|e| self.new_ty_mvar(&e.span)).collect::<Vec<_>>();
            let tys = self.alloc.alloc_slice_fill_iter(tys.into_iter());
            intern!(self, TyKind::List(tys))
          });
        macro_rules! expect {($n:expr) => {{
          let n = $n;
          if es.len() != n { error!(span, NumArgs(n, es.len())) }
        }}}
        match tgt.k {
          TyKind::Unit => {
            expect!(0);
            ret![Unit, Ok(unit!()), self.common.t_unit]
          }
          TyKind::True => {
            expect!(0);
            ret![ITrue, Ok(unit!()), self.common.t_unit]
          }
          TyKind::Array(tgt1, n_tgt) => {
            let n = intern!(self, ExprKind::Int(self.alloc.alloc(es.len().into())));
            let ty = intern!(self, TyKind::Array(tgt1, n));
            #[allow(clippy::never_loop)]
            let n_tgt = loop {
              if let ExprKind::Int(n) = self.whnf_expr(span, n_tgt).k {
                if let Ok(n) = n.try_into() { break n }
              }
              error!(span, Relate(ty, tgt, Relation::Equal))
            };
            expect!(n_tgt);
            let mut pes = Ok(Vec::with_capacity(n_tgt));
            let es = es.iter().map(|e| {
              let (e, pe) = self.check_expr(e, tgt1);
              if let Ok(vec) = &mut pes {
                match pe {
                  Ok(pe) => vec.push(pe),
                  Err(err) => pes = Err(err),
                }
              }
              e
            }).collect();
            let pes = pes.map(|pes| intern!(self, ExprKind::Array(
              self.alloc.alloc_slice_fill_iter(pes.into_iter()))));
            ret![List(ListKind::Array, es), pes, ty]
          }
          TyKind::List(tgts) => {
            expect!(tgts.len());
            let mut pes = Ok(Vec::with_capacity(tgts.len()));
            let es = es.iter().zip(tgts).map(|(e, &tgt)| {
              let (e, pe) = self.check_expr(e, tgt);
              if let Ok(vec) = &mut pes {
                match pe {
                  Ok(pe) => vec.push(pe),
                  Err(err) => pes = Err(err),
                }
              }
              e
            }).collect();
            let pes = pes.map(|pes| intern!(self, ExprKind::List(
              self.alloc.alloc_slice_fill_iter(pes.into_iter()))));
            ret![List(ListKind::List, es), pes, tgt]
          }
          TyKind::And(tgts) => {
            expect!(tgts.len());
            let mut val = None;
            let es = es.iter().zip(tgts).map(|(e, &tgt)| {
              let (e, pe) = self.check_expr(e, tgt);
              let pe = self.as_pure(e.span, pe);
              if let Some(v) = val {
                self.equate_expr(v, pe).unwrap_or_else(|_| {
                  self.errors.push(hir::Spanned {span, k: TypeError::IAndUnify(v, pe)});
                });
              } else { val = Some(pe) };
              e
            }).collect();
            if let Some(val) = val {
              ret![List(ListKind::And, es), Ok(val), tgt]
            } else {
              ret![ITrue, Ok(unit!()), self.common.t_unit]
            }
          }
          TyKind::Struct(args) => {
            expect!(args.iter().filter(|&arg| matches!(arg.k.1, ArgKind::Lam(_))).count());
            let (es, pes, _) = self.check_args(span, es, args, |x| x.k);
            let val = pes.into_iter().collect::<Result<Vec<_>, _>>()
              .map(|pes| intern!(self, ExprKind::List(
                self.alloc.alloc_slice_fill_iter(pes.into_iter()))));
            ret![List(ListKind::Struct, es), val, tgt]
          }
          TyKind::Own(_) => unimplemented!("malloc"),
          TyKind::Shr(_, _) => unimplemented!("&T constructor"),
          TyKind::Sn(_, _) => {
            expect!(2);
            let_unchecked!((x, h) as [x, h] = &**es);
            let (ek, pe, ty) = self.lower_expr_sn(span, expect, x, Some(h));
            ret![ek, Ok(pe), ty]
          }
          _ => error!()
        }
      }

      ast::ExprKind::Ghost(e) => {
        let mut f = |ty: Ty<'a>| {
          let mut wty = self.whnf_ty(span, ty.into());
          wty.ghost = false;
          wty.to_ty(self)
        };
        let expect2 = match expect {
          ExpectExpr::Any => ExpectExpr::Any,
          ExpectExpr::HasTy(ty) => ExpectExpr::HasTy(f(ty)),
          ExpectExpr::Sn(a, ty) => ExpectExpr::Sn(a, f(ty))
        };
        let (e, pe) = self.lower_expr(e, expect2);
        let mut wty = WhnfTy::from(e.ty());
        wty.ghost = true;
        ret![Ghost(Box::new(e)), pe, wty.to_ty(self)]
      }

      ast::ExprKind::Ref(e) => {
        let (e, pe) = self.lower_place(e);
        let ty = intern!(self, TyKind::Ref(Lifetime::Extern, e.ty()));
        ret![Ref(Box::new(e)), pe.map(|pe| self.place_to_expr(pe)), ty]
      }

      ast::ExprKind::Borrow(e) => {
        let (e, pe) = self.lower_place(e);
        let pe = self.as_pure_place(e.span, pe);
        ret![Borrow(Box::new(e)),
          Ok(intern!(self, ExprKind::Ref(pe))),
          intern!(self, TyKind::RefSn(pe))]
      }

      &ast::ExprKind::Mm0(types::Mm0Expr {ref subst, expr}) => {
        let mut p_subst = Vec::with_capacity(subst.len());
        let subst = subst.iter().map(|e| {
          let (e, pe) = self.lower_expr(e, ExpectExpr::Any); // TODO: better expected type
          p_subst.push(self.as_pure(e.span, pe));
          e
        }).collect();
        let tgt = expect.to_ty().unwrap_or_else(|| self.common.nat());
        let pe = self.alloc.alloc_slice_fill_iter(p_subst.into_iter());
        let pe = intern!(self, ExprKind::Mm0(Mm0Expr {subst: pe, expr }));
        ret![Mm0(types::Mm0Expr { subst, expr }), Ok(pe), tgt]
      }

      ast::ExprKind::Typed(e, ty) => {
        let ty = self.lower_ty(ty, ExpectTy::coerce_to(expect.to_ty()));
        self.check_expr(e, ty)
      }

      ast::ExprKind::As(e, tgt) => {
        let tgt = self.lower_ty(tgt, ExpectTy::coerce_to(expect.to_ty()));
        let (e, pe) = self.lower_expr(e, ExpectExpr::Any);
        let ty = e.ty();
        macro_rules! fail {() => {error!(span, UnsupportedAs(ty, tgt))}}
        let ty = self.whnf_ty(span, ty.into()).ty;
        if_chain! {
          if let TyKind::Int(ity) = ty.k;
          if let TyKind::Int(ity2) = tgt.k;
          then {
            if ity <= ity2 {
              ret![Cast(Box::new(e), ty, hir::CastKind::Int), pe, tgt]
            } else if ity2 == IntTy::NAT {
              fail!()
            } else {
              let pe = pe.map(|e| intern!(self, ExprKind::Unop(Unop::As(ity2), e)));
              ret![Unop(hir::Unop::As(ity, ity2), Box::new(e)), pe, tgt]
            }
          }
          else {
            if matches!(ty.k, TyKind::Own(_) | TyKind::Shr(_, _) | TyKind::RefSn(_)) &&
              matches!(tgt.k, TyKind::Int(ity) if IntTy::UInt(Size::S64) <= ity) {
              let tgt = self.common.t_uint(Size::S64);
              ret![Cast(Box::new(e), ty, hir::CastKind::Ptr), pe, tgt]
            } else { fail!() }
          }
        }
      }

      ast::ExprKind::Cast(e, h) => {
        let (e, pe) = self.lower_expr(e, ExpectExpr::Any);
        let ty = e.ty();
        let tgt = expect.to_ty().unwrap_or_else(|| self.new_ty_mvar(span));
        let ck = if let Ok(x) = pe {
          hir::CastKind::Wand(h.as_deref().map(|h| Box::new({
            // [x: ty] -* [x: tgt]
            let hty = intern!(self, TyKind::Wand(
              intern!(self, TyKind::HasTy(x, ty)),
              intern!(self, TyKind::HasTy(x, tgt))));
            self.check_expr(h, hty).0
          })))
        } else {
          hir::CastKind::subtype(h.as_deref().map(|h| Box::new({
            let v = self.fresh_var(Spanned { span: span.clone(), k: Symbol::UNDER });
            let x = intern!(self, ExprKind::Var(v));
            // A. x: ty, [x: ty] -* [x: tgt]
            let hty = intern!(self, TyKind::All(
              intern!(self, TuplePatternS {var: v, k: TuplePatternKind::Name(Symbol::UNDER), ty}),
              intern!(self, TyKind::Wand(
                intern!(self, TyKind::HasTy(x, ty)),
                intern!(self, TyKind::HasTy(x, tgt))))));
            self.check_expr(h, hty).0
          })))
        };
        ret![Cast(Box::new(e), ty, ck), pe, tgt]
      }

      ast::ExprKind::Pun(e, h) => {
        let (e, pe) = self.lower_expr(e, ExpectExpr::Any);
        let ty = e.ty();
        let pe = self.as_pure(e.span, pe);
        let tgt = expect.to_ty().unwrap_or_else(|| self.new_ty_mvar(span));
        let ck = hir::CastKind::mem(h.as_deref().map(|h| Box::new({
          // [x: tgt]
          let hty = intern!(self, TyKind::HasTy(pe, tgt));
          self.check_expr(h, hty).0
        })));
        ret![Cast(Box::new(e), ty, ck), Ok(pe), tgt]
      }

      ast::ExprKind::Uninit => {
        let mut tgt = WhnfTy::from(expect.to_ty().unwrap_or_else(|| self.new_ty_mvar(span)));
        tgt.uninit = false;
        let tgt = tgt.to_ty(self);
        let u_tgt = intern!(self, TyKind::Uninit(tgt));
        ret![Uninit, Ok(unit!()), u_tgt]
      }

      ast::ExprKind::Sizeof(ty) => {
        let ty = self.lower_ty(ty, ExpectTy::Any);
        let pe = intern!(self, ExprKind::Sizeof(ty));
        ret![Sizeof(ty), Ok(pe), self.common.nat()]
      }

      ast::ExprKind::Typeof(e) => {
        let (e, pe) = self.lower_expr(e, ExpectExpr::Any);
        let pe = self.as_pure(e.span, pe);
        let ty = intern!(self, TyKind::HasTy(pe, e.ty()));
        ret![Typeof(Box::new(e)), Ok(unit!()), ty]
      }

      ast::ExprKind::Assert(p) => {
        let tgt = expect.to_ty();
        let b = tgt.and_then(|ty| self.prop_to_expr(span, ty));
        let (e, pe) = self.lower_expr(p, match b {
          Some(b) => ExpectExpr::Sn(b, self.common.t_bool),
          None => ExpectExpr::HasTy(self.common.t_bool)
        });
        let tgt = intern!(self, pe.map_or(TyKind::True, TyKind::Pure));
        ret![Assert(Box::new(e)), Ok(unit!()), tgt]
      }

      ast::ExprKind::Assign {lhs, rhs, oldmap} => {
        let (lhs, plhs) = self.lower_place(lhs);
        let plhs = self.as_pure_place(lhs.span, plhs);
        let (v, lens) = if let Some(x) = Self::build_lens(plhs) { x } else { error!() };
        let (rhs, prhs) = self.lower_expr(rhs, ExpectExpr::HasTy(lhs.ty()));
        let (_, _, ty) = self.dc.get_var(v);
        let old = if let Some((_, old)) = oldmap.iter().find(|p| p.0.k == v) {old} else {
          error!(span, MissingAssignWith(v))
        };
        let e = Some(intern!(self, ExprKind::Var(old.k)));
        self.dc.context = self.new_context_next(old.k, e, ty).into();
        let newgen = self.new_generation();
        let val = if let Ok(val) = prhs {
          lens(self, val)
        } else {
          intern!(self, ExprKind::Var(v))
        };
        self.dc.gen_vars.insert(v, (newgen, val, ty)); // FIXME: ty is not correct here
        let v = lhs.map(|_| v);
        let e = hir::ExprKind::Assign {
          lhs: Box::new(lhs),
          rhs: Box::new(rhs),
          map: Box::new([(v, old.as_ref(), (Some(val), ty))]),
          gen: newgen,
        };
        ret![e, Ok(unit!()), self.common.t_unit]
      }

      ast::ExprKind::Call {f, tys, args, variant} =>
        match self.check_call(f, tys, args, variant.as_deref()) {
          None => error!(),
          Some((call, (pe, mut ret))) => {
            if let ReturnKind::Unreachable = call.rk {
              self.dc.diverged = true;
              if let Some(ty) = expect.to_ty() { ret = ty }
            }
            ret![Call(call), pe, ret]
          }
        }

      ast::ExprKind::Entail(pf, ps) => {
        let tgt = expect.to_ty().unwrap_or_else(|| self.new_ty_mvar(span));
        let mut is_copy = tgt.is_copy();
        let mut tys = Vec::with_capacity(ps.len());
        let ps = ps.iter().map(|p| {
          let (p, _) = self.lower_expr(p, ExpectExpr::Any);
          is_copy &= p.ty().is_copy();
          tys.push(p.ty());
          p
        }).collect::<Vec<_>>();
        let pr = if ps.is_empty() {
          return (self.elab_proof(tgt, pf), Ok(unit!()))
        } else if is_copy {
          let from = intern!(self, TyKind::And(self.alloc.alloc_slice_fill_iter(tys.into_iter())));
          let ty = intern!(self, TyKind::Imp(from, tgt));
          let e = Box::new(hir::Spanned {span, k:
            (hir::ExprKind::List(ListKind::List, ps), (Some(unit!()), from))});
          let ck = hir::CastKind::Subtype(Box::new(self.elab_proof(ty, pf)));
          hir::ExprKind::Cast(e, from, ck)
        } else {
          let from = intern!(self, TyKind::List(self.alloc.alloc_slice_fill_iter(tys.into_iter())));
          let ty = intern!(self, TyKind::Wand(from, tgt));
          let e = Box::new(hir::Spanned {span, k:
            (hir::ExprKind::List(ListKind::List, ps), (Some(unit!()), from))});
          let ck = hir::CastKind::Wand(Some(Box::new(self.elab_proof(ty, pf))));
          hir::ExprKind::Cast(e, from, ck)
        };
        ret![pr, Ok(unit!()), tgt]
      }

      ast::ExprKind::Block(bl) => {
        let (bl, (pe, ty)) = self.lower_block(span, bl, expect);
        ret![Block(bl), pe, ty]
      }

      &ast::ExprKind::If {ik, ref hyp, ref cond, ref then, ref els} => {
        let (cond, pe) = self.check_expr(cond, self.common.t_bool);
        let tgt = expect.to_ty().unwrap_or_else(|| self.new_ty_mvar(span));
        let (dc1, dc2, e1, e2);
        let base = self.dc.clone();
        let hyp = if let Some([v1, v2]) = hyp {
          let pe = self.as_pure(cond.span, pe);
          let ty = intern!(self, TyKind::Pure(pe));
          let ctx1 = self.new_context_next(v1.k, Some(unit!()), ty);
          self.dc.context = ctx1.into();
          e1 = self.check_expr(then, tgt);
          dc1 = mem::replace(&mut self.dc, base.clone());
          let ty = intern!(self, TyKind::Pure(intern!(self, ExprKind::Unop(Unop::Not, pe))));
          let ctx2 = self.new_context_next(v2.k, Some(unit!()), ty);
          self.dc.context = ctx2.into();
          Some([v1.as_ref(), v2.as_ref()])
        } else {
          e1 = self.check_expr(then, tgt);
          dc1 = mem::replace(&mut self.dc, base.clone());
          None
        };
        e2 = self.check_expr(els, tgt);
        dc2 = mem::replace(&mut self.dc, base);
        let muts = self.merge(span, &mut [dc1, dc2]);
        let ((then, p_then), (els, p_els)) = (e1, e2);
        let cases = Box::new([then, els]);
        let pe = pe.and_then(|cond| Ok(match ik {
          ast::IfKind::If => intern!(self, ExprKind::If {cond, then: p_then?, els: p_els?}),
          ast::IfKind::And => intern!(self, ExprKind::Binop(Binop::And, cond, p_els?)),
          ast::IfKind::Or => intern!(self, ExprKind::Binop(Binop::Or, cond, p_then?)),
        }));
        ret![If {hyp, cond: Box::new(cond), cases, gen: self.dc.generation, muts}, pe, tgt]
      }

      &ast::ExprKind::While {label, ref hyp, ref cond, ref muts, ref var, ref body, has_break} => {
        if !muts.is_empty() {
          let newgen = self.new_generation();
          for &v in &**muts {
            let e = intern!(self, ExprKind::Var(v));
            let ty = self.dc.get_var(v).2;
            self.dc.gen_vars.insert(v, (newgen, e, ty));
          }
        }
        let variant = self.check_variant(var.as_deref());
        let base = self.dc.clone();
        self.labels.insert(label, LabelData {
          labels: Box::new([(&[], variant)]),
          value: AgreeExpr::Set(Err(span)),
          has_jump: false,
          ret: self.common.t_unit,
          dcs: vec![],
        });
        let (cond, pe) = self.check_expr(cond, self.common.t_bool);
        let mut after = self.dc.clone();
        self.labels.get_mut(&label).expect("just added").dcs.push(after.clone());
        let mut vhyp = hyp.as_ref().map(|h| h.k);
        let trivial = if_chain! {
          if let Ok(e) = pe;
          if let ExprKind::Bool(b) = self.whnf_expr(cond.span, e).k;
          then {
            if vhyp.is_none() {
              vhyp = Some(self.fresh_var(Spanned { span: cond.span.clone(), k: Symbol::UNDER }))
            }
            Some(b)
          }
          else { None }
        };
        if let Some(v) = vhyp {
          let pe = self.as_pure(cond.span, pe);
          let ty = intern!(self, TyKind::Pure(pe));
          let ctx1 = self.new_context_next(v, Some(unit!()), ty);
          self.dc.context = ctx1.into();
          self.dc.diverged |= trivial == Some(false);
        }
        let hyp = hyp.as_ref().map(|hyp| hyp.as_ref());
        let ret = if has_break { self.common.t_unit } else {
          pe.ok().map_or(self.common.t_unit, |pe| {
            after.diverged |= trivial == Some(true);
            intern!(self, TyKind::Pure(intern!(self, ExprKind::Unop(Unop::Not, pe))))
          })
        };
        let ret_ty =
          if crate::proof::VERIFY_TERMINATION { self.common.t_false }
          else { self.common.t_unit };
        let body = Box::new(self.check_block(span, body, ret_ty).0);
        let LabelData {labels, dcs, ..} =
          self.labels.remove(&label).expect("labels should be well scoped");

        // TODO: remove this when the typechecker is complete, this isn't needed for inference
        let missing = || self.dc.gen_vars.iter()
          .chain(dcs.iter().flat_map(|dc| dc.gen_vars.iter()))
          .filter(|&(v, &(gen, _, _))| {
            base.gen_vars.get(v).map_or(true, |&(gen2, _, _)| gen != gen2) &&
            !muts.contains(v)
          });
        if missing().next().is_some() {
          error!(span, MissingMuts(missing().map(|(&v, _)| v).collect()))
        }

        self.dc = after;
        let (_, variant) = labels.into_vec().into_iter().next().expect("while label");
        ret![
          While(Box::new(hir::While {
            label, hyp, cond: Box::new(cond), variant, body,
            gen: self.dc.generation, muts: muts.clone(), trivial
          })),
          Ok(unit!()), ret]
      }

      ast::ExprKind::Unreachable(h) => {
        let tgt = expect.to_ty().unwrap_or(self.common.t_false);
        let (h, _) = self.check_expr(h, self.common.t_false);
        self.dc.diverged = true;
        ret![Unreachable(Box::new(h)), Ok(unit!()), tgt]
      }

      &ast::ExprKind::Jump(ast::LabelId(lab, i), ref args, ref pf) => {
        let label_data = self.labels.get_mut(&lab).expect("well formed");
        label_data.has_jump = true;
        let (tgt, variant) = label_data.labels[i as usize];
        let num_args = tgt.iter().filter(|&arg| matches!(arg.k.1, ArgKind::Lam(_))).count();
        if args.len() != num_args { error!(span, NumArgs(num_args, args.len())) }
        let (args, _, mut subst) = self.check_args(span, args, tgt, |x| x.k);
        let variant = self.check_variant_use(&mut subst, pf.as_deref(), variant);
        let tgt = expect.to_ty().unwrap_or(self.common.t_false);
        self.dc.diverged = true;
        ret![Jump(lab, i, args, variant), Ok(unit!()), tgt]
      }

      ast::ExprKind::Break(lab, e) => {
        let ty = self.labels[lab].ret;
        let tgt = expect.to_ty().unwrap_or(self.common.t_false);
        let (e, pe) = self.check_expr(e, ty);
        if !self.dc.diverged {
          let LabelData {value: old_pe, dcs, ..} = self.labels.get_mut(lab).expect("well formed");
          dcs.push(self.dc.clone());
          match *old_pe {
            AgreeExpr::Unset => *old_pe = AgreeExpr::Set(pe),
            AgreeExpr::Set(Ok(pe_1)) => match pe {
              Ok(pe) if self.equate_expr(pe_1, pe).is_ok() => {}
              _ => self.labels.get_mut(lab).expect("well formed").value =
                AgreeExpr::Set(Err(pe.err().unwrap_or(e.span))),
            }
            AgreeExpr::Set(Err(_)) => {}
          }
          self.dc.diverged = true;
        }
        ret![Break(*lab, Box::new(e)), Ok(unit!()), tgt]
      }

      ast::ExprKind::Return(args) =>
        if let Some(tys) = self.returns {
          let num_args = tys.iter().filter(|&arg| matches!(arg.k.1, ArgKind::Lam(_))).count();
          if args.len() != num_args { error!(span, NumArgs(num_args, args.len())) }
          let (args, _, _) = self.check_args(span, args, tys, |x| x.k);
          let tgt = expect.to_ty().unwrap_or(self.common.t_false);
          self.dc.diverged = true;
          ret![Return(args), Ok(unit!()), tgt]
        } else { error!(span, InvalidReturn) }

      &ast::ExprKind::Infer(_user) => if let ExpectExpr::Sn(pe, ty) = expect {
        if let Some(e) = self.eval_expr(span, pe) { (e, Ok(pe)) }
        else { error!(span, UnsupportedSynthesis(Box::new(self.dc.clone()), pe, ty)) }
      } else { error!(span, Hole(Box::new(self.dc.clone()), expect.to_ty())) }

      ast::ExprKind::Rc(e) => self.lower_expr(e, expect),

      ast::ExprKind::Error => error!(),
    }
  }

  fn elab_proof(&mut self, ty: Ty<'a>,
    &Spanned {ref span, k: pf}: &'a Spanned<ProofId>
  ) -> hir::Expr<'a> {
    hir::Spanned {span, k: (hir::ExprKind::Mm0Proof(pf), (Some(self.common.e_unit), ty))}
  }

  fn eval_expr(&mut self, span: &'a FileSpan, e: Expr<'a>) -> Option<hir::Expr<'a>> {
    macro_rules! error {($($es:expr),*) => {{
      $({
        use TypeError::*; let k = $es;
        self.errors.push(hir::Spanned {span, k});
      })*
      return Some(hir::Spanned {span, k:
        (hir::ExprKind::Error, (Some(self.common.e_error), self.common.t_error))})
    }}}
    let (k, ty) = match e.k {
      ExprKind::Unit => (hir::ExprKind::Unit, self.common.t_unit),
      ExprKind::Var(v) => {
        let (gen, _, ty) = self.dc.get_var(v);
        (hir::ExprKind::Var(v, gen), ty)
      },
      ExprKind::Const(c) =>
        match &let_unchecked!(Some(Entity::Const(tc)) = self.names.get(&c), tc).k {
          ConstTc::ForwardDeclared => error!(),
          ConstTc::Checked {ty, ..} => {
            let ty = ty.clone().import_global(self);
            (hir::ExprKind::Const(c), ty)
          }
        },
      ExprKind::Bool(b) => (hir::ExprKind::Bool(b), self.common.t_bool),
      ExprKind::Int(n) => (
        hir::ExprKind::Int(n),
        if n.is_negative() { self.common.int() } else { self.common.nat() }
      ),
      ExprKind::Unop(op, e) => {
        let e = Box::new(self.eval_expr(span, e)?); let ty = e.ty();
        let (op, ty) = match op {
          Unop::Neg => (hir::Unop::Neg(IntTy::INT), self.common.int()),
          Unop::Not => (hir::Unop::Not, self.common.t_bool),
          Unop::BitNot(sz) => {
            let ity = ty.as_int_ty().unwrap_or_else(|| {
              if sz == Size::Inf { IntTy::Int(sz) } else { IntTy::UInt(sz) }
            });
            (hir::Unop::BitNot(ity), self.common.int_ty(ity))
          }
          Unop::As(ity2) => {
            let ity = ty.as_int_ty().unwrap_or(IntTy::INT);
            (hir::Unop::As(ity, ity2), self.common.int_ty(ity2))
          }
        };
        (hir::ExprKind::Unop(op, e), ty)
      }
      ExprKind::Binop(op, e1, e2) => {
        let e1 = Box::new(self.eval_expr(span, e1)?); let ty1 = e1.ty();
        let e2 = Box::new(self.eval_expr(span, e2)?); let ty2 = e2.ty();
        let (ity, ty) = self.binop_ty(op, |_| ty1.as_int_ty(), |_| ty2.as_int_ty());
        (hir::ExprKind::Binop(op.as_hir(ity), e1, e2), ty)
      }
      ExprKind::Sizeof(ty) => {
        let e2 = self.whnf_expr(span, e);
        if e != e2 { return self.eval_expr(span, e2) }
        if let ExprKind::Infer(_) = e2.k { error!(UninferredType) }
        (hir::ExprKind::Sizeof(ty), self.common.nat())
      }
      ExprKind::If {cond, then, els} => {
        let cond = Box::new(self.eval_expr(span, cond)?);
        let cases = Box::new([self.eval_expr(span, then)?, self.eval_expr(span, els)?]);
        let ty1 = cases[0].ty();
        let ty2 = cases[1].ty();
        if self.relate_ty(span, None, ty1, ty2, Relation::Equal).is_err() { return None }
        (hir::ExprKind::If {hyp: None, cond, cases, gen: self.dc.generation, muts: vec![]}, ty1)
      }
      ExprKind::Index(_, _) |
      ExprKind::Slice(_) |
      ExprKind::Proj(_, _) |
      ExprKind::UpdateIndex(_) |
      ExprKind::UpdateSlice(_) |
      ExprKind::UpdateProj(_, _, _) |
      ExprKind::List(_) |
      ExprKind::Array(_) |
      ExprKind::Ref(_) |
      ExprKind::Mm0(_) |
      ExprKind::Call {..} |
      ExprKind::Infer(_) => return None,
      ExprKind::Error => error!(),
    };
    Some(hir::Spanned {span, k: (k, (Some(e), ty))})
  }

  fn lower_expr(&mut self,
    Spanned {span, k}: &'a ast::Expr, expect: ExpectExpr<'a>
  ) -> (hir::Expr<'a>, RExpr<'a>) {
    self.lower_expr_kind(span, k, expect)
  }

  fn coerce_expr(&mut self, mut e: hir::Expr<'a>, pe: RExpr<'a>, to: Ty<'a>) -> hir::Expr<'a> {
    if let Err(coe) = self.relate_ty(e.span, pe.ok(), e.ty(), to, Relation::Coerce) {
      for c in coe { e = self.apply_coe_expr(c, e) }
    }
    e
  }

  fn check_expr(&mut self, e: &'a ast::Expr, tgt: Ty<'a>) -> (hir::Expr<'a>, RExpr<'a>) {
    let (e, pe) = self.lower_expr(e, ExpectExpr::HasTy(tgt));
    (self.coerce_expr(e, pe, tgt), pe)
  }

  fn check_args<'b, A>(&'b mut self,
    sp: &'a FileSpan, es: &'a [ast::Expr], tgt: &'b [A],
    f: impl Fn(&'b A) -> ArgS<'a>
  ) -> (Vec<hir::Expr<'a>>, Vec<Result<Expr<'a>, &'a FileSpan>>, Subst<'a>) {
    debug_assert!(es.len() ==
      tgt.iter().filter(|&a| matches!(f(a).1, ArgKind::Lam(_))).count());
    let mut es_out = Vec::with_capacity(es.len());
    let mut pes = vec![];
    let mut es_it = es.iter();
    let mut subst = Subst::default();
    for arg in tgt {
      match f(arg) {
        (attr, ArgKind::Lam(arg)) => {
          let e = es_it.next().expect("checked");
          let ty = subst.subst_ty(self, &e.span, arg.k.ty);
          let (e, pe) = if attr.contains(ArgAttr::MUT) {
            let (e, pe) = self.lower_place(e);
            let pe = intern!(self, ExprKind::Ref(self.as_pure_place(e.span, pe)));
            let ty = intern!(self, TyKind::Ref(self.new_lft_mvar(sp), e.ty()));
            let e = hir::ExprKind::ArgRef(Box::new(e));
            (hir::Spanned {span: sp, k: (e, (Some(pe), ty))}, Ok(pe))
          } else {
            self.check_expr(e, ty)
          };
          pes.push(pe);
          subst.push_tuple_pattern(self, sp, arg, pe);
          es_out.push(e);
        }
        (_, ArgKind::Let(arg, e)) => {
          let e = subst.subst_expr(self, sp, e);
          subst.push_tuple_pattern_raw(self, sp, arg, Ok(e))
        }
      }
    }
    (es_out, pes, subst)
  }

  fn check_variant(&mut self, variant: Option<&'a ast::Variant>) -> Option<hir::Variant<'a>> {
    let variant = variant?;
    let (e, vt) = &variant.k;
    Some(match vt {
      ast::VariantType::Down =>
        hir::Variant(self.check_pure_expr(e, self.common.nat()), hir::VariantType::Down),
      ast::VariantType::UpLt(ub) => {
        let e = self.check_pure_expr(e, self.common.int());
        hir::Variant(e, hir::VariantType::UpLt(self.check_pure_expr(ub, self.common.int())))
      },
      ast::VariantType::UpLe(ub) => {
        let e = self.check_pure_expr(e, self.common.int());
        hir::Variant(e, hir::VariantType::UpLe(self.check_pure_expr(ub, self.common.int())))
      },
    })
  }

  fn check_variant_use(&mut self,
    subst: &mut Subst<'a>, variant: Option<&'a ast::Expr>, tgt: Option<hir::Variant<'a>>,
  ) -> Option<Box<hir::Expr<'a>>> {
    let variant = variant?;
    if let Some(hir::Variant(e, vt)) = tgt {
      let e2 = subst.subst_expr(self, &variant.span, e);
      let ty = intern!(self, TyKind::Pure(intern!(self, match vt {
        hir::VariantType::Down => ExprKind::Binop(Binop::Lt, e2, e),
        hir::VariantType::UpLt(ub) => ExprKind::Binop(Binop::And,
          intern!(self, ExprKind::Binop(Binop::Lt, e, e2)),
          intern!(self, ExprKind::Binop(Binop::Lt, e2, ub))),
        hir::VariantType::UpLe(ub) => ExprKind::Binop(Binop::And,
          intern!(self, ExprKind::Binop(Binop::Lt, e, e2)),
          intern!(self, ExprKind::Binop(Binop::Le, e2, ub))),
      })));
      Some(Box::new(self.check_expr(variant, ty).0))
    } else {
      self.errors.push(hir::Spanned {span: &variant.span, k: TypeError::UnexpectedVariant});
      None
    }
  }

  fn as_pure(&mut self, span: &'a FileSpan, pe: RExpr<'a>) -> Expr<'a> {
    pe.unwrap_or_else(|sp| {
      self.errors.push(hir::Spanned {span, k: TypeError::ExpectedPure(sp)});
      self.common.e_error
    })
  }

  fn as_pure_place(&mut self, span: &'a FileSpan, pe: RPlace<'a>) -> Place<'a> {
    pe.unwrap_or_else(|sp| {
      self.errors.push(hir::Spanned {span, k: TypeError::ExpectedPure(sp)});
      self.common.p_error
    })
  }

  #[allow(clippy::similar_names)]
  fn lower_place(&mut self, Spanned {span, k}: &'a ast::Expr) -> (hir::Place<'a>, RPlace<'a>) {
    macro_rules! ret {($k:expr, $pe:expr, $ty:expr) => {
      (hir::Place {span, k: {#[allow(unused)] use hir::PlaceKind::*; ($k, $ty)}}, $pe)
    }}
    macro_rules! error {($($sp:expr, $es:expr),*) => {{
      $({
        use TypeError::*; let k = $es;
        self.errors.push(hir::Spanned {span: $sp, k});
      })*
      return ret![Error, Ok(self.common.p_error), self.common.t_error]
    }}}
    macro_rules! eval_expr {($sp:expr, $e:expr, $ty:expr) => {{
      if let Some(n) = self.eval_expr($sp, $e) { n }
      else { error!($sp, UnsupportedSynthesis(Box::new(self.dc.clone()), $e, $ty)) }
    }}}
    match k {
      &ast::ExprKind::Var(v) => {
        let (_, _, ty) = self.dc.get_var(v);
        ret![Var(v), Ok(intern!(self, PlaceKind::Var(v))), ty]
      }

      ast::ExprKind::Index(arr, idx, hyp) => {
        let (e_a, arr) = self.lower_place(arr);
        let arrty = self.whnf_ty(span, e_a.ty().into()).ty;
        let (ty, n) = match arrty.k {
          TyKind::Array(ty, n) => (ty, n),
          TyKind::Error => error!(),
          _ => {
            let ty2 = TyKind::Array(self.new_ty_mvar(span), self.new_expr_mvar(span));
            error!(span, Relate(arrty, intern!(self, ty2), Relation::Equal))
          }
        };
        let (e_i, idx) = self.check_expr(idx, self.common.nat());
        let hyp = match hyp {
          Some(h) => {
            let idx = self.as_pure(e_i.span, idx);
            let ty = intern!(self, TyKind::Pure(
              intern!(self, ExprKind::Binop(Binop::Lt, idx, n))));
            Ok(self.check_expr(h, ty).0)
          }
          None => Err(eval_expr!(span, n, self.common.nat())),
        };
        ret![Index(Box::new((arrty, e_a, e_i, hyp))),
          arr.and_then(|a| Ok(intern!(self, PlaceKind::Index(a, arrty, idx?)))),
          ty]
      }

      ast::ExprKind::Slice(args, hyp) => {
        let (arr, idx, len) = &**args;
        let (e_a, arr) = self.lower_place(arr);
        let arrty = self.whnf_ty(span, e_a.ty().into()).ty;
        let (ty, n) =  match arrty.k {
          TyKind::Array(ty, n) => (ty, n),
          TyKind::Error => error!(),
          _ => {
            let ty2 = TyKind::Array(self.new_ty_mvar(span), self.new_expr_mvar(span));
            error!(span, Relate(arrty, intern!(self, ty2), Relation::Equal))
          }
        };
        let (e_i, idx) = self.check_expr(idx, self.common.nat());
        let (e_l, len) = self.check_expr(len, self.common.nat());
        let pe_l = self.as_pure(e_l.span, len);
        let hyp = match hyp {
          Some(hyp) => {
            let e_i = self.as_pure(e_i.span, idx);
            let ty = intern!(self, TyKind::Pure(
              intern!(self, ExprKind::Binop(Binop::Le,
                intern!(self, ExprKind::Binop(Binop::Add, e_i, pe_l)), n))));
            Ok(self.check_expr(hyp, ty).0)
          }
          None => Err(eval_expr!(span, n, self.common.nat())),
        };
        ret![Slice(Box::new((arrty, e_a, [e_i, e_l], hyp))),
          arr.and_then(|a| Ok(intern!(self, PlaceKind::Slice(a, arrty, [idx?, pe_l])))),
          intern!(self, TyKind::Array(ty, pe_l))]
      }

      ast::ExprKind::Deref(e) => {
        let e2 = self.lower_expr(e, ExpectExpr::Any).0;
        let ty = e2.ty();
        let wty = self.whnf_ty(span, ty.into()).ty;
        match wty.k {
          TyKind::RefSn(e) => if let Some(ty) = self.place_type(span, e) {
            ret![Deref(Box::new((wty, e2))), Ok(e), ty]
          } else {
            error!(e2.span, ExpectedPlace)
          }
          TyKind::Error => error!(),
          _ => {
            let tgt = intern!(self, TyKind::RefSn(self.common.p_error));
            error!(e2.span, Relate(ty, tgt, Relation::Equal))
          }
        }
      }

      _ => error!(span, ExpectedPlace),
    }
  }

  fn lower_stmt(&mut self, Spanned {span, k: stmt}: &'a ast::Stmt, tgt: Ty<'a>) -> UnelabStmt<'a> {
    match stmt {
      ast::StmtKind::Let {lhs, rhs} => {
        let ctx = self.dc.context;
        let lhs1 = self.lower_tuple_pattern(&lhs.span, &lhs.k, None, None).0;
        self.dc.context = ctx;
        let rhs = self.check_expr(rhs, lhs1.ctx.ty).0;
        // lower the LHS again to unify the types better
        let lhs = self.lower_tuple_pattern(&lhs.span, &lhs.k, rhs.k.1 .0, Some(rhs.k.1 .1)).0;
        UnelabStmt::Let {lhs, rhs}
      }
      ast::StmtKind::Expr(e) => UnelabStmt::Expr(
        self.lower_expr_kind(span, e, ExpectExpr::Any).0.k),
      &ast::StmtKind::Label(v, ref labs) => {
        let mut todo = Vec::with_capacity(labs.len());
        let labs2 = labs.iter().map(|ast::Label {args, variant, body}| {
          let args = args.iter()
            .map(|arg| self.lower_arg(&arg.span, arg.k.0, &arg.k.1)).collect::<Vec<_>>();
          let variant = self.lower_variant(variant);
          let ctx = self.dc.context;
          let args = self.finish_args(args);
          let args2 = self.args_to_ty_args(&args);
          todo.push(UnelabLabelData {ctx, body, args});
          (args2, variant)
        }).collect::<Box<[_]>>();
        let data = LabelData {
          labels: labs2,
          has_jump: false, value: AgreeExpr::Unset,
          ret: tgt, dcs: vec![]
        };
        assert!(self.labels.insert(v, data).is_none());
        UnelabStmt::Label(v, todo.into())
      }
    }
  }

  fn finish_stmt(&mut self,
    hir::Spanned {span, k: stmt}: hir::Spanned<'a, UnelabStmt<'a>>,
    tgt: &mut RExprTy<'a>,
    breaks: &mut Vec<DynContext<'a>>,
  ) -> hir::Stmt<'a> {
    hir::Spanned {span, k: match stmt {
      UnelabStmt::Let {lhs, rhs} => {
        let lhs = self.finish_tuple_pattern(&lhs);
        hir::StmtKind::Let {lhs, rhs}
      }
      UnelabStmt::Expr(e) => hir::StmtKind::Expr(e),
      UnelabStmt::Label(v, labs) => {
        let has_jump = self.labels[&v].has_jump;
        let blocks = labs.into_vec().into_iter().map(|UnelabLabelData {ctx, body, args}| {
          self.dc.context = ctx;
          let (bl2, pe2) = self.check_block(&body.span, &body.k, tgt.1);
          if let Ok(e_tgt) = tgt.0 {
            if !matches!(pe2, Ok(pe) if self.equate_expr(pe, e_tgt).is_ok()) {
              tgt.0 = Err(pe2.err().unwrap_or(&body.span))
            }
          }
          (body.map_hir(|_| bl2), args)
        }).collect::<Vec<_>>();
        let LabelData {labels, dcs, value, ..} =
          self.labels.remove(&v).expect("missing label group");
        breaks.extend_from_slice(&dcs);
        if let AgreeExpr::Set(pe2) = value {
          if let Ok(e_tgt) = tgt.0 {
            if !matches!(pe2, Ok(pe) if self.equate_expr(pe, e_tgt).is_ok()) {
              tgt.0 = Err(pe2.err().unwrap_or(span))
            }
          }
        }
        hir::StmtKind::Label(v, has_jump, labels.into_vec().into_iter().zip(blocks)
          .map(|((_, variant), (body, args))| hir::Label {args, variant, body}).collect())
      }
    }}
  }

  fn lower_block(&mut self, sp: &'a FileSpan,
    ast::Block {stmts, expr}: &'a ast::Block,
    expect: ExpectExpr<'a>
  ) -> (hir::Block<'a>, RExprTy<'a>) {
    let ty = expect.to_ty().unwrap_or_else(|| {
      if expr.is_some() { self.new_ty_mvar(sp) } else { self.common.t_unit }
    });
    let base = self.dc.clone();
    let stmts = stmts.iter()
      .map(|stmt| stmt.map_hir(|_| self.lower_stmt(stmt, ty))).collect::<Vec<_>>();
    let (expr, mut ety) = if let Some(e) = expr {
      let (e, pe) = self.check_expr(e, ty);
      (Some(Box::new(e)), (pe, ty))
    } else {
      (None, (Ok(self.common.e_unit), ty))
    };
    let mut breaks = vec![];
    let mut stmts = stmts.into_iter().rev()
      .map(|stmt| self.finish_stmt(stmt, &mut ety, &mut breaks)).collect::<Vec<_>>();
    stmts.reverse();
    breaks.push(mem::replace(&mut self.dc, base));
    let n = breaks.len() - 1;
    breaks.swap(0, n);
    let muts = self.merge(sp, &mut {breaks});
    (hir::Block {stmts, expr, gen: self.dc.generation, muts}, ety)
  }

  fn check_block(&mut self, span: &'a FileSpan, bl: &'a ast::Block, tgt: Ty<'a>) -> (hir::Block<'a>, RExpr<'a>) {
    let (mut bl, (pe, ty)) = self.lower_block(span, bl, ExpectExpr::HasTy(tgt));
    if let Err(coe) = self.relate_ty(span, pe.ok(), ty, tgt, Relation::Coerce) {
      let mut e = bl.expr.take().map_or_else(|| hir::Spanned {span, k:
        (hir::ExprKind::Unit, (Some(self.common.e_unit), self.common.t_unit))}, |e| *e);
      for c in coe { e = self.apply_coe_expr(c, e) }
      bl.expr = Some(Box::new(e))
    }
    (bl, pe)
  }

  /// Construct the HIR for a top level item, performing type inference.
  pub fn lower_item(&mut self, Spanned {span, k: item}: &'a ast::Item) -> Option<hir::Item<'a>> {
    let item = match item {
      &ast::ItemKind::Proc {
        intrinsic, kind, ref name, tyargs, ref args, ref outs, ref rets, ref variant, ref body
      } => {
        let name = hir::Spanned {span: &name.span, k: name.k};
        let args2 = args.iter()
          .map(|arg| self.lower_arg(&arg.span, arg.k.0, &arg.k.1)).collect::<Vec<_>>();
        let mut subst = Subst::default();
        let gen = self.new_generation();
        let mut rets2 = vec![];
        let outs = outs.iter().map(|out| {
          let i_usize = u32_as_usize(out.input);
          let span = &args[i_usize].span;
          let ty = if let Some(ty) = &out.ty {
            self.lower_ty(ty, ExpectTy::Any)
          } else {
            subst.subst_ty(self, span, args2[i_usize].1.var().ctx.ty)
          };
          let ctx = self.new_context_next(out.var, None, ty);
          self.dc.context = ctx.into();
          rets2.push((ArgAttr::GHOST, UnelabArgKind::Lam(UnelabTupPat {
            span: &out.name.span,
            ctx,
            k: UnelabTupPatKind::Name(false, out.name.k)
          })));
          out.input
        }).collect::<Box<[_]>>();
        rets2.extend(rets.iter().map(|pat| (ArgAttr::empty(), UnelabArgKind::Lam(
          self.lower_tuple_pattern(&pat.span, &pat.k, None, None).0))));
        let rets = self.finish_args(rets2);
        let t_rets = self.args_to_ty_args(&rets);
        self.returns = Some(t_rets);
        let ctx = self.dc.context;
        let variant = self.lower_variant(variant);
        let args = self.finish_args(args2);
        let t_args = self.args_to_ty_args(&args);
        let mut gctx = self.to_global_ctx();
        let item = Entity::Proc(Spanned {
          span: span.clone(),
          k: ProcTc::Typed(ProcTy {
            kind, intrinsic, tyargs,
            args: t_args.to_global(&mut gctx),
            outs: outs.clone(),
            rets: t_rets.to_global(&mut gctx),
            variant: variant.to_global(&mut gctx),
          })
        });
        match self.names.entry(name.k) {
          Entry::Occupied(mut e) => {
            assert!(
              matches!(e.get(), Entity::Proc(Spanned {k: ProcTc::ForwardDeclared, ..})),
              "procedure {} declared twice", name.k);
            e.insert(item);
          }
          Entry::Vacant(e) => { e.insert(item); }
        }
        if intrinsic.is_some() { return None }
        self.dc.context = ctx;
        let sigma = match *t_rets {
          [] => self.common.t_unit,
          [arg] => arg.k.1.var().k.ty,
          _ => intern!(self, TyKind::Struct(t_rets)),
        };
        let mut body = self.check_block(span, body, sigma).0;
        let e = body.expr.take().map_or_else(|| hir::Spanned {span, k:
          (hir::ExprKind::Unit, (Some(self.common.e_unit), self.common.t_unit))}, |e| *e);
        let (span, k) = match t_rets.len() {
          0 => {
            body.stmts.push(e.map_into(hir::StmtKind::Expr));
            (span, hir::ExprKind::Return(vec![]))
          }
          1 => (span, hir::ExprKind::Return(vec![e])),
          _ => if let hir::Spanned {span, k: (hir::ExprKind::List(_, es), _)} = e {
            (span, hir::ExprKind::Return(es))
          } else {
            (span, hir::ExprKind::UnpackReturn(Box::new((sigma, e))))
          }
        };
        body.expr = Some(Box::new(hir::Spanned {span, k:
          (k, (Some(self.common.e_unit), self.common.t_false))}));
        hir::ItemKind::Proc {kind, name, tyargs, args, gen, outs, rets, variant, body}
      }
      ast::ItemKind::Global(intrinsic, lhs, rhs) => {
        if let Some(intrinsic) = intrinsic { match *intrinsic {} }
        let ctx = self.dc.context;
        let lhs_span = &lhs.span;
        let lhs = self.lower_tuple_pattern(lhs_span, &lhs.k, None, None).0;
        self.dc.context = ctx;
        let (rhs, _) = self.check_expr(rhs, lhs.ctx.ty);
        let lhs = self.finish_tuple_pattern_inner(&lhs, None).0;
        if let TuplePatternKind::Name(name) = lhs.k.k {
          let mut gctx = self.to_global_ctx();
          let item = Entity::Global(Spanned {
            span: span.clone(),
            k: GlobalTc::Checked(lhs.k.ty.to_global(&mut gctx))
          });
          match self.names.entry(name) {
            Entry::Occupied(mut e) => {
              assert!(
                matches!(e.get(), Entity::Global(Spanned {k: GlobalTc::ForwardDeclared, ..})),
                "global {} declared twice", name);
              e.insert(item);
            }
            Entry::Vacant(e) => { e.insert(item); }
          }
        } else { todo!() }
        hir::ItemKind::Global { lhs: hir::Spanned { span: lhs_span, k: lhs }, rhs }
      }
      ast::ItemKind::Const(intrinsic, lhs, rhs) => {
        if let Some(intrinsic) = intrinsic { match *intrinsic {} }
        let ctx = self.dc.context;
        let lhs_sp = &lhs.span;
        let lhs = self.lower_tuple_pattern(lhs_sp, &lhs.k, None, None).0;
        self.dc.context = ctx;
        let rhs_sp = &rhs.span;
        let rhs = self.check_pure_expr(rhs, lhs.ctx.ty);
        let lhs = self.finish_tuple_pattern_inner(&lhs, None).0;
        if let TuplePatternKind::Name(name) = lhs.k.k {
          let ty = self.whnf_ty(lhs_sp, lhs.k.ty.into()).to_ty(self);
          let whnf = self.whnf_expr(rhs_sp, rhs);
          let mut gctx = self.to_global_ctx();
          let item = Entity::Const(Spanned {
            span: span.clone(),
            k: ConstTc::Checked {
              ty: ty.to_global(&mut gctx),
              e: rhs.to_global(&mut gctx),
              whnf: whnf.to_global(&mut gctx),
            }
          });
          match self.names.entry(name) {
            Entry::Occupied(mut e) => {
              assert!(
                matches!(e.get(), Entity::Const(Spanned {k: ConstTc::ForwardDeclared, ..})),
                "const {} declared twice", name);
              e.insert(item);
            }
            Entry::Vacant(e) => { e.insert(item); }
          }
        } else { todo!() }
        return None
      }
      &ast::ItemKind::Typedef {intrinsic, ref name, tyargs, ref args, ref val} => {
        let name = hir::Spanned {span: &name.span, k: name.k};
        let args2 = args.iter()
          .map(|arg| self.lower_arg(&arg.span, arg.k.0, &arg.k.1)).collect::<Vec<_>>();
        let val = self.lower_ty(val, ExpectTy::Any);
        let args = self.finish_args2(args2,
          |this, (attr, arg)| intern!(this, (attr, (&arg).into())));
        let mut gctx = self.to_global_ctx();
        let args = (&*args).to_global(&mut gctx);
        let val = val.to_global(&mut gctx);
        let item = Entity::Type(Spanned {
          span: span.clone(),
          k: TypeTc::Typed(TypeTy {intrinsic, tyargs, args, val})
        });
        match self.names.entry(name.k) {
          Entry::Occupied(mut e) => {
            assert!(
              matches!(e.get(), Entity::Type(Spanned {k: TypeTc::ForwardDeclared, ..})),
              "type {} declared twice", name.k);
            e.insert(item);
          }
          Entry::Vacant(e) => { e.insert(item); }
        }
        return None
      }
    };
    Some(hir::Spanned {span, k: item})
  }
}
