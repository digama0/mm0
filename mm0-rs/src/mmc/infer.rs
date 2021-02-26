//! Type inference and elaboration
#![allow(unused)]
#![allow(clippy::unused_self)]
#![allow(clippy::needless_collect)]
#![allow(clippy::match_same_arms)]

use std::{borrow::Borrow, fmt::Debug, hash::{Hash, Hasher}, mem, ops::Index};
use std::result::Result as StdResult;
use std::convert::{TryFrom, TryInto};
use bumpalo::Bump;
use hashbrown::{HashMap, HashSet, hash_map::RawEntryMut};
use hir::{Context, ContextNext};
use num::{BigInt, Signed};
use types::IntTy;
use crate::{AtomId, LispVal, FormatEnv, u32_as_usize, FileSpan};
use super::{parser::try_get_fspan, types::{self, Binop, FieldName, Size, Spanned, Unop, VarId,
  ast, hir::{self, GenId}}};
use super::types::entity::{Entity, ConstTc, GlobalTc, ProcTc, TypeTy};
use super::union_find::{UnifyCtx, UnifyKey, UnificationTable};
#[allow(clippy::wildcard_imports)] use super::types::ty::*;

#[derive(Debug)]
enum TypeError<'a> {
  /// Failed to pattern match type T with the given pattern of type U
  PatternMatch(Ty<'a>, Ty<'a>),
  /// Failed to relate type T to type U according to the relation
  Relate(Ty<'a>, Ty<'a>, Relation),
  /// Expected a pure expression
  ExpectedPure,
  /// Expected a struct expression
  ExpectedStruct(Ty<'a>),
  /// Expected a pointer expression
  ExpectedPtr,
  /// Expected a place expression
  ExpectedPlace,
  /// Expected a type ascription
  ExpectedType,
  /// Struct does not have this field
  FieldMissing(Ty<'a>, FieldName),
  /// Expected `x` args, found `y`
  NumArgs(usize, usize),
  /// `as` conversion from `T` to `U` not supported
  UnsupportedAs(Ty<'a>, Ty<'a>),
  /// Cannot assign to this lvalue
  UnsupportedAssign,
  /// Missing `with` clause for assignment
  MissingAssignWith(AtomId),
  /// Provided expressions x and y do not unify in an and-intro expression
  IAndUnify(Expr<'a>, Expr<'a>),
  /// An explicit hole expression, which queries for the full type context.
  /// (This form assumes we don't have an expected expression, else we would just fill it in.)
  Hole(Box<DynContext<'a>>, Option<Ty<'a>>),
  /// Don't know how to evaluate this expression
  UnsupportedSynthesis(Box<DynContext<'a>>, Expr<'a>, Ty<'a>),
  /// Can't use return in this position
  InvalidReturn,
  /// While loop mutates a value without marking it as `mut` in the loop header
  MissingMuts(Vec<VarId>),
  /// A `(variant h)` clause was provided to a function or label that does not declare a variant
  UnexpectedVariant,
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

type InternedSet<T> = HashMap<Interned<T>, ()>;

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
  tups: TuplePatternKind,
  args: ArgKind,
  pats: PatternKind,
  tys: TyKind,
  exprs: ExprKind,
}

impl<'a> Interner<'a> {
  fn intern<T: Internable<'a>>(&mut self, alloc: &'a Bump, t: T) -> &'a WithMeta<T> {
    match T::get_mut(self).raw_entry_mut().from_key(&t) {
      RawEntryMut::Occupied(e) => e.key().0,
      RawEntryMut::Vacant(e) =>
        e.insert(Interned(alloc.alloc(WithMeta::new(t))), ()).0 .0,
    }
  }
}

macro_rules! intern {($ctx:expr, $t:expr) => {{let t = $t; $ctx.intern(t)}}}

#[derive(Debug)]
struct MVarData<'a> {
  span: &'a FileSpan,
}

#[derive(Copy, Clone, Debug)]
enum MVarValue<'a, T> {
  Assigned(T),
  Unassigned(Context<'a>),
}

impl<'a, T: PartialEq + Copy> UnifyCtx<MVarValue<'a, T>> for () {
  type Error = (T, T);

  fn unify_values(&mut self, &value1: &MVarValue<'a, T>, &value2: &MVarValue<'a, T>) -> StdResult<MVarValue<'a, T>, Self::Error> {
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
struct Assignments<'a, K, V> {
  mvars: Vec<MVarData<'a>>,
  table: UnificationTable<K, MVarValue<'a, V>>,
}
impl<K, V> Default for Assignments<'_, K, V> {
  fn default() -> Self { Self { mvars: vec![], table: Default::default() } }
}

impl<'a, K: UnifyKey, V> Assignments<'a, K, V> {
  fn new_mvar(&mut self, span: &'a FileSpan, ctx: Context<'a>) -> K {
    let n = K::from_index(self.mvars.len().try_into().expect("overflow"));
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

  fn lookup(&mut self, k: K) -> Option<V> where V: Copy {
    match self.table.probe_value(k) {
      MVarValue::Assigned(v) => Some(*v),
      MVarValue::Unassigned(_) => None,
    }
  }
}

impl<'a, K: UnifyKey, V> Index<K> for Assignments<'a, K, V> {
  type Output = MVarData<'a>;
  fn index(&self, k: K) -> &Self::Output { &self.mvars[u32_as_usize(k.index())] }
}

impl IntTy {
  fn to_ty<'a>(self, ctx: &mut InferCtx<'a>) -> Ty<'a> { intern!(ctx, self.into()) }
}

impl Unop {
  #[must_use] fn arg_ty<'a>(self, ctx: &mut InferCtx<'a>) -> Ty<'a> {
    match self {
      Unop::Not => ctx.common.t_bool,
      Unop::Neg | Unop::BitNot(Size::Inf) => ctx.common.int(),
      Unop::BitNot(sz) => ctx.common.t_uint(sz),
    }
  }
  #[must_use] fn ret_ty<'a>(self, ctx: &mut InferCtx<'a>) -> Ty<'a> {
    match self {
      Unop::Not => ctx.common.t_bool,
      Unop::Neg | Unop::BitNot(Size::Inf) => ctx.common.int(),
      Unop::BitNot(sz) => ctx.common.t_uint(sz),
    }
  }
}

/// A partially elaborated tuple pattern.
#[derive(Debug, DeepSizeOf)]
struct UnelabTupPat<'a> {
  /// The span of the pattern.
  span: &'a FileSpan,
  /// The pattern kind, see [`UnelabTupPatKind`].
  k: UnelabTupPatKind<'a>,
}

/// A partially elaborated tuple pattern.
#[derive(Debug, DeepSizeOf)]
enum UnelabTupPatKind<'a> {
  /// A simple pattern, containing the actual binding in the [`ContextNext`].
  Name(bool, AtomId, &'a ContextNext<'a>),
  /// An unelaborated tuple pattern match. The subpatterns are elaborated with metavariable types,
  /// but we don't yet know how to connect this list of types to the target type - for example
  /// the target type could be a metavariable, and propagating our default guess of a nondependent
  /// tuple could cause a type error if it turns out to be a dependent tuple.
  Tuple(Vec<UnelabTupPat<'a>>, Ty<'a>),
  /// A failed tuple pattern match.
  Error(Box<UnelabTupPat<'a>>, Ty<'a>),
}

impl<'a> UnelabTupPat<'a> {
  /// The type of the values matched by this tuple pattern.
  #[must_use] fn ty(&self) -> Ty<'a> {
    match self.k {
      UnelabTupPatKind::Name(_, _, &ContextNext {ty, ..}) |
      UnelabTupPatKind::Tuple(_, ty) |
      UnelabTupPatKind::Error(_, ty) => ty,
    }
  }

  /// The context before introducing the bindings in this tuple pattern.
  fn base_context(&self, ctx: &mut InferCtx<'a>) {
    match &self.k {
      UnelabTupPatKind::Name(_, _, &ContextNext {parent, ..}) => ctx.dc.context = parent,
      UnelabTupPatKind::Tuple(pats, _) =>
        if let Some(pat) = pats.first() { pat.base_context(ctx) }
      UnelabTupPatKind::Error(pat, _) => pat.base_context(ctx),
    }
  }
}

/// An argument in a `struct` or function parameters.
#[derive(Debug)]
enum UnelabArg<'a> {
  /// The usual lambda binder: `x: T`.
  Lam(UnelabTupPat<'a>),
  /// A definition binder: `x: T := e`.
  Let(UnelabTupPat<'a>, Expr<'a>),
}

impl<'a> UnelabArg<'a> {
  /// The variable part of the argument.
  #[must_use] fn var(&self) -> &UnelabTupPat<'a> {
    match self { UnelabArg::Lam(pat) | UnelabArg::Let(pat, _) => pat }
  }
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
  Expr(hir::ExprKind<'a>),
  /// A label, which looks exactly like a local function but has no independent stack frame.
  /// They are called like regular functions but can only appear in tail position.
  Label(VarId, Box<[(Context<'a>, &'a Spanned<ast::Block>)]>),
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct WhnfTy<'a> {
  uninit: bool,
  ghost: bool,
  moved: bool,
  ty: Ty<'a>,
}

impl<'a> WhnfTy<'a> {
  fn to_ty(mut self, ctx: &mut InferCtx<'a>) -> Ty<'a> {
    if self.moved { self.ty = intern!(ctx, TyKind::Moved(self.ty)) }
    if self.ghost { self.ty = intern!(ctx, TyKind::Ghost(self.ty)) }
    if self.uninit { self.ty = intern!(ctx, TyKind::Uninit(self.ty)) }
    self.ty
  }
  fn is_ty(self) -> bool { !self.uninit && !self.moved && !self.ghost }
  fn moved(mut self, m: bool) -> Self { self.moved |= m; self }
  fn ghost(mut self) -> Self { self.ghost = true; self }
  fn uninit(mut self) -> Self { self.uninit = true; self }
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

  fn push(&mut self, v: VarId, e: Result<Expr<'a>, &'a FileSpan>) {
    self.add_fvars(e);
    self.push_raw(v, e);
  }

  fn push_tuple_pattern_raw(&mut self,
    ctx: &mut InferCtx<'a>, pat: TuplePattern<'a>, e: Result<Expr<'a>, &'a FileSpan>
  ) {
    match pat.k {
      TuplePatternKind::Name(_, v, _) => self.push_raw(v, e),
      TuplePatternKind::Error(pat, _) => self.push_tuple_pattern_raw(ctx, pat, e),
      TuplePatternKind::Tuple(pats, mk, _) => {
        for (i, &pat) in pats.iter().enumerate() {
          let e = e.map(|e| mk.proj(ctx, e, pats.len(), i.try_into().expect("overflow")));
          self.push_tuple_pattern_raw(ctx, pat, e)
        }
      }
    }
  }

  fn push_tuple_pattern(&mut self,
    ctx: &mut InferCtx<'a>, pat: TuplePattern<'a>, e: Result<Expr<'a>, &'a FileSpan>
  ) {
    self.add_fvars(e);
    self.push_tuple_pattern_raw(ctx, pat, e);
  }

  fn subst_var(&mut self, ctx: &mut InferCtx<'a>, v: VarId) -> Option<Expr<'a>> {
    if let im::hashmap::Entry::Occupied(mut e) = self.subst.entry(v) {
      let res = e.get_mut();
      Some(match *res {
        Ok(val) => val,
        Err(span) => {
          ctx.errors.push(hir::Spanned {span, k: TypeError::ExpectedPure});
          *res = Ok(ctx.common.e_error);
          ctx.common.e_error
        }
      })
    } else { None }
  }

  fn subst_expr(&mut self, ctx: &mut InferCtx<'a>, sp: &'a FileSpan, e: Expr<'a>) -> Expr<'a> {
    macro_rules! subst {($op:expr, $($es:expr),*) => {{
      let e2 = ($(self.subst_expr(ctx, sp, $es)),*);
      if ($($es),*) == e2 { return e }
      intern!(ctx, $op(e2))
    }}}
    match e.k {
      ExprKind::Var(v) => self.subst_var(ctx, v).unwrap_or(e),
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
      ExprKind::Slice(e1, e2, e3) =>
        subst!(|(e1, e2, e3)| ExprKind::Slice(e1, e2, e3), e1, e2, e3),
      ExprKind::Proj(e, i) =>
        subst!(|e| ExprKind::Proj(e, i), e),
      ExprKind::UpdateIndex(e1, e2, e3) =>
        subst!(|(e1, e2, e3)| ExprKind::UpdateIndex(e1, e2, e3), e1, e2, e3),
      ExprKind::UpdateSlice(e1, e2, e3, e4) =>
        subst!(|(e1, e2, e3, e4)| ExprKind::UpdateSlice(e1, e2, e3, e4), e1, e2, e3, e4),
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
      ExprKind::As(e, ak@AsKind::Mod(_)) => subst!(|e| ExprKind::As(e, ak), e),
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
        if let Some(ty) = ctx.expr_mvars.lookup(v) { return self.subst_expr(ctx, sp, ty) }
        let span = ctx.expr_mvars[v].span;
        ctx.errors.push(hir::Spanned {span, k: TypeError::ExpectedType});
        ctx.expr_mvars.assign(v, ctx.common.e_error);
        ctx.common.e_error
      }
    }
  }

  fn subst_lft(&mut self,
    ctx: &mut InferCtx<'a>, span: &'a FileSpan, lft: Lifetime
  ) -> Option<Lifetime> {
    Some(match lft {
      Lifetime::Extern => lft,
      Lifetime::Place(v) => if let Some(mut origin) = self.subst_var(ctx, v) {
        loop {
          match origin.k {
            ExprKind::Var(v) => break Lifetime::Place(v),
            ExprKind::Index(a, i) => origin = a,
            ExprKind::Slice(a, i, l) => origin = a,
            ExprKind::Proj(a, i) => origin = a,
            ExprKind::Error => return None,
            ExprKind::Infer(v) => {
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
        if let Some(lft) = ctx.lft_mvars.lookup(v) { return self.subst_lft(ctx, span, lft) }
        ctx.new_lft_mvar(ctx.lft_mvars[v].span)
      }
    })
  }

  fn subst_tup_pat(&mut self,
    ctx: &mut InferCtx<'a>, sp: &'a FileSpan, pat: TuplePattern<'a>
  ) -> TuplePattern<'a> {
    match pat.k {
      TuplePatternKind::Name(g, v, ty) => {
        let ty2 = self.subst_ty(ctx, sp, ty);
        let v2 = if self.fvars.contains(&v) {
          let w = ctx.fresh_var();
          self.subst.insert(v, Ok(intern!(ctx, ExprKind::Var(w))));
          w
        } else { v };
        self.fvars.insert(v2);
        if v == v2 && ty == ty2 { return pat }
        intern!(ctx, TuplePatternKind::Name(g, v2, ty2))
      }
      TuplePatternKind::Tuple(pats, mk, ty) => {
        let ty2 = self.subst_ty(ctx, sp, ty);
        let pats2 = pats.iter().map(|&pat| self.subst_tup_pat(ctx, sp, pat)).collect::<Vec<_>>();
        if ty == ty2 && pats == pats2 { return pat }
        let pats2 = ctx.alloc.alloc_slice_fill_iter(pats2.into_iter());
        intern!(ctx, TuplePatternKind::Tuple(pats2, mk, ty2))
      }
      TuplePatternKind::Error(p, ty) => {
        let ty2 = self.subst_ty(ctx, sp, ty);
        let p2 = self.subst_tup_pat(ctx, sp, p);
        if ty == ty2 && p == p2 { return pat }
        intern!(ctx, TuplePatternKind::Error(p2, ty2))
      }
    }
  }

  fn subst_arg(&mut self, ctx: &mut InferCtx<'a>, sp: &'a FileSpan, arg: Arg<'a>) -> Arg<'a> {
    match arg.k {
      ArgKind::Lam(pat) => {
        let pat2 = self.subst_tup_pat(ctx, sp, pat);
        if pat == pat2 { return arg }
        intern!(ctx, ArgKind::Lam(pat2))
      }
      ArgKind::Let(pat, e) => {
        let e2 = self.subst_expr(ctx, sp, e);
        let pat2 = self.subst_tup_pat(ctx, sp, pat);
        if pat == pat2 && e == e2 { return arg }
        intern!(ctx, ArgKind::Let(pat2, e2))
      }
    }
  }

  fn subst_ty(&mut self, ctx: &mut InferCtx<'a>, sp: &'a FileSpan, ty: Ty<'a>) -> Ty<'a> {
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
      TyKind::UInt(_) |
      TyKind::Input |
      TyKind::Output |
      TyKind::Error => ty,
      TyKind::Array(t, e) => subst!(|t, e| TyKind::Array(t, e); t; e),
      TyKind::Own(t) => subst!(|t, _| TyKind::Own(t); t;),
      TyKind::Ref(lft, t) => {
        let lft2 =
          if let Some(lft2) = self.subst_lft(ctx, sp, lft) { lft2 }
          else { return ctx.common.t_error };
        let t2 = self.subst_ty(ctx, sp, t);
        if lft == lft2 && t == t2 { return ty }
        intern!(ctx, TyKind::Ref(lft2, t2))
      }
      TyKind::Shr(lft, t) => {
        let lft2 =
          if let Some(lft2) = self.subst_lft(ctx, sp, lft) { lft2 }
          else { return ctx.common.t_error };
        let t2 = self.subst_ty(ctx, sp, t);
        if lft == lft2 && t == t2 { return ty }
        intern!(ctx, TyKind::Shr(lft2, t2))
      }
      TyKind::RefSn(e) => subst!(|_, e| TyKind::RefSn(e);; e), // FIXME: verify this is correct
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
        if let Some(ty) = ctx.ty_mvars.lookup(v) { return self.subst_ty(ctx, sp, ty) }
        let span = ctx.ty_mvars[v].span;
        ctx.errors.push(hir::Spanned {span, k: TypeError::ExpectedType});
        ctx.ty_mvars.assign(v, ctx.common.t_error);
        ctx.common.t_error
      }

    }
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

#[derive(Debug)]
enum AgreeExpr<'a> {
  Unset,
  Set(Option<Expr<'a>>),
}

/// The temporary data associated to a label group during elaboration.
#[derive(Debug)]
struct LabelData<'a> {
  /// The list of labels in the group. (Note that the `body` field of
  /// labels is not set during type inference)
  labels: Box<[hir::Label<'a>]>,
  /// The pure expression in the break position.
  /// * `Unset` means we haven't seen any `break`s yet,
  /// * `Set(Some(e))` means all breaks have the same value `e`, and
  /// * `Set(None)` means that there are multiple exit values.
  value: AgreeExpr<'a>,
  /// The return type of the block containing the label group.
  ret: Ty<'a>,
}

/// The main inference context for the type inference pass.
#[derive(Debug)]
pub struct InferCtx<'a> {
  /// The formatting environment, so we can print things.
  fe: FormatEnv<'a>,
  /// The bump allocator that stores all the data structures
  /// (the `'a` in all the borrowed types).
  alloc: &'a Bump,
  /// The name map, for global variables and functions.
  names: &'a HashMap<AtomId, Entity>,
  /// The largest allocated variable so far, for fresh naming.
  max_var: VarId,
  /// The interner, which is used to deduplicate types and terms that are
  /// constructed multiple times.
  interner: Interner<'a>,
  // tasks: Vec<Task>,
  /// The assignments for type metavariables.
  ty_mvars: Assignments<'a, TyMVarId, Ty<'a>>,
  /// The assignments for pure expression metavariables.
  expr_mvars: Assignments<'a, ExprMVarId, Expr<'a>>,
  /// The assignments for lifetime metavariables.
  lft_mvars: Assignments<'a, LftMVarId, Lifetime>,
  /// Some pre-interned types.
  common: Common<'a>,
  /// The dynamic context (including the logical context).
  dc: DynContext<'a>,
  /// The next generation.
  generation_count: GenId,
  /// The mapping from variables to their user-provided names.
  var_names: HashMap<VarId, AtomId>,
  /// The set of labels in scope.
  labels: HashMap<VarId, LabelData<'a>>,
  /// The return type of the current function.
  returns: Option<&'a [Arg<'a>]>,
  /// The list of type errors collected so far.
  /// We delay outputting these so that we can report many errors at once,
  /// as well as waiting for all variables to be as unified as possible so that
  /// the error messages are as precise as possible.
  errors: Vec<hir::Spanned<'a, TypeError<'a>>>,
}

/// A relation between types, used as an argument to [`InferCtx::relate_ty`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Relation {
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
  fn exactly(tgt: Option<Ty<'a>>) -> Self {
    tgt.map_or(Self::Any, |ty| Self::Relate(Relation::Equal, ty))
  }
  fn subtype(tgt: Option<Ty<'a>>) -> Self {
    tgt.map_or(Self::Any, |ty| Self::Relate(Relation::Subtype, ty))
  }
  fn supertype(tgt: Option<Ty<'a>>) -> Self {
    tgt.map_or(Self::Any, |ty| Self::RelateRev(Relation::Subtype, ty))
  }
  fn coerce_to(tgt: Option<Ty<'a>>) -> Self {
    tgt.map_or(Self::Any, |ty| Self::Relate(Relation::Coerce, ty))
  }
  fn coerce_from(tgt: Option<Ty<'a>>) -> Self {
    tgt.map_or(Self::Any, |ty| Self::RelateRev(Relation::Coerce, ty))
  }

  fn to_ty(self) -> Option<Ty<'a>> {
    match self {
      ExpectTy::Any => None,
      ExpectTy::Relate(_, ty) |
      ExpectTy::RelateRev(_, ty) => Some(ty),
    }
  }
}

/// An expectation for an expression, used to communicate top-down typing information.
#[derive(Copy, Clone)]
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
  fn build<'a>(self, ctx: &mut InferCtx<'a>, exprs: Vec<Option<Expr<'a>>>) -> Option<Expr<'a>> {
    Some(match self {
      Self::Unit | Self::True => ctx.common.e_unit,
      Self::Sn => (*exprs.first()?)?,
      Self::List | Self::Struct => {
        if exprs.iter().any(Option::is_none) {return None}
        intern!(ctx, ExprKind::List(ctx.alloc.alloc_slice_fill_iter(
          exprs.into_iter().map(|e| unwrap_unchecked!(e)))))
      }
      Self::Array => {
        if exprs.iter().any(Option::is_none) {return None}
        intern!(ctx, ExprKind::Array(ctx.alloc.alloc_slice_fill_iter(
          exprs.into_iter().map(|e| unwrap_unchecked!(e)))))
      }
      Self::And => return exprs.first().copied().unwrap_or(Some(ctx.common.e_unit)),
    })
  }

  /// Constructs an expression from a list of expressions for the sub-pattern matches.
  /// This will always return `Some` if the `exprs` are all `Some`, unless there is an upstream
  /// type error.
  fn proj<'a>(self, ctx: &mut InferCtx<'a>, e: Expr<'a>, num: usize, idx: u32) -> Expr<'a> {
    match self {
      Self::Unit | Self::True => return ctx.common.e_unit,
      Self::Sn => return if idx == 0 { e } else { ctx.common.e_unit },
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
  /// A singleton pattern `{a : T}`, which expands to the expected type
  /// `{x : T} {h : x = a}`.
  Sn(Expr<'a>, Ty<'a>),
  /// A list of types {_ : T1} {_ : T2} ... {_ : Tn}`, resulting from a pattern match
  /// on `List` or `And`.
  List(std::slice::Iter<'a, Ty<'a>>),
  /// A dependent list of types `{xi : Ti}`, resulting from a pattern match on a `Struct`.
  Args(Box<TupleIterArgs<'a>>),
}

impl Default for TupleIter<'_> {
  fn default() -> Self { Self::Ty(None) }
}

impl<'a> TupleIter<'a> {
  /// Construct an `Args` variant, pulling the next non-`Let` argument from the list.
  fn mk_args(ctx: &mut InferCtx<'a>, span: &'a FileSpan,
    mut subst: Subst<'a>, mut rest: std::slice::Iter<'a, Arg<'a>>
  ) -> Self {
    while let Some(arg) = rest.next() {
      match arg.k {
        ArgKind::Lam(first) =>
          return Self::Args(Box::new(TupleIterArgs {subst, span, first, rest})),
        ArgKind::Let(pat, e) => {
          let e = subst.subst_expr(ctx, span, e);
          subst.push_tuple_pattern_raw(ctx, pat, Ok(e))
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
  fn next(&mut self, ctx: &mut InferCtx<'a>) -> Option<Ty<'a>> {
    match self {
      Self::Ty(ty) => ty.take(),
      &mut Self::Sn(e, ty) => Some(ty),
      Self::List(it) => it.next().copied(),
      Self::Args(args) => Some(args.subst.subst_ty(ctx, args.span, args.first.k.ty())),
    }
  }

  /// Finishes a call to `next` by substituting `val` into all types in the
  /// rest of the sequence of types.
  fn push(&mut self, ctx: &mut InferCtx<'a>, val: Expr<'a>) {
    match self {
      Self::Ty(_) | Self::List(_) => {}
      &mut Self::Sn(e, ty) => {
        *self = Self::Ty(Some(intern!(ctx, TyKind::Pure(
          intern!(ctx, ExprKind::Binop(Binop::Eq, val, e))))));
      }
      Self::Args(x) => {
        let TupleIterArgs {ref mut subst, first, ..} = **x;
        subst.push_tuple_pattern(ctx, first, Ok(val));
        let_unchecked!(Self::Args(args) = mem::take(self),
          *self = Self::mk_args(ctx, args.span, args.subst, args.rest))
      }
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
}

impl<'a> Common<'a> {
  fn new(i: &mut Interner<'a>, alloc: &'a Bump) -> Self {
    macro_rules! alloc {($e:expr) => {i.intern(alloc, $e)}}
    macro_rules! allocs {($f:expr; $($e:expr),*) => {[$(alloc!($f($e))),*]}}
    #[allow(clippy::enum_glob_use)] use Size::*;
    Self {
      t_unit: alloc!(TyKind::Unit),
      e_unit: alloc!(ExprKind::Unit),
      t_bool: alloc!(TyKind::Bool),
      e_bool: allocs!(ExprKind::Bool; false, true),
      t_uint: allocs!(TyKind::UInt; S8, S16, S32, S64, Inf),
      t_int: allocs!(TyKind::UInt; S8, S16, S32, S64, Inf),
      t_error: alloc!(TyKind::Error),
      e_error: alloc!(ExprKind::Error),
      t_true: alloc!(TyKind::True),
      t_false: alloc!(TyKind::False),
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
}

impl<'a> InferCtx<'a> {
  /// Create a new `InferCtx` from the given allocator.
  pub fn new(
    fe: FormatEnv<'a>,
    alloc: &'a Bump,
    names: &'a HashMap<AtomId, Entity>,
    var_names: HashMap<VarId, AtomId>,
    max_var: VarId,
  ) -> Self {
    let mut interner = Default::default();
    let common = Common::new(&mut interner, alloc);
    Self {
      fe,
      alloc,
      names,
      interner,
      common,
      max_var,
      var_names,
      // tasks: vec![],
      ty_mvars: Default::default(),
      expr_mvars: Default::default(),
      lft_mvars: Default::default(),
      dc: DynContext {
        gen_vars: Default::default(),
        generation: GenId::ROOT,
        context: Context::ROOT,
      },
      generation_count: GenId::ROOT,
      labels: HashMap::new(),
      returns: None,
      errors: vec![],
    }
  }

  fn new_generation(&mut self) -> GenId {
    let n = self.generation_count;
    self.generation_count.0 += 1;
    n
  }

  fn intern<T: Internable<'a>>(&mut self, t: T) -> &'a WithMeta<T> {
    self.interner.intern(self.alloc, t)
  }

  fn fresh_var(&mut self) -> VarId {
    let n = self.max_var;
    self.max_var.0 += 1;
    n
  }

  fn new_ty_mvar(&mut self, span: &'a FileSpan) -> Ty<'a> {
    let n = self.ty_mvars.new_mvar(span, self.dc.context);
    intern!(self, TyKind::Infer(n))
  }

  fn new_expr_mvar(&mut self, span: &'a FileSpan) -> Expr<'a> {
    let n = self.expr_mvars.new_mvar(span, self.dc.context);
    intern!(self, ExprKind::Infer(n))
  }

  fn new_lft_mvar(&mut self, span: &'a FileSpan) -> Lifetime {
    let n = self.lft_mvars.new_mvar(span, self.dc.context);
    Lifetime::Infer(n)
  }

  fn assign_ty(&mut self, v: TyMVarId, e: Ty<'a>) -> bool {
    let root = self.ty_mvars.root(v);
    if let TyKind::Infer(v2) = e.k {
      self.ty_mvars.equate(v, v2);
    } else {
      let mut cycle = false;
      e.on_mvars(|v2| cycle |= self.ty_mvars.root(v2) == root);
      if cycle { return false }
      self.ty_mvars.assign(v, e);
    }
    true
  }

  fn assign_expr(&mut self, v: ExprMVarId, e: Expr<'a>) -> bool {
    let root = self.expr_mvars.root(v);
    if let ExprKind::Infer(v2) = e.k {
      self.expr_mvars.equate(v, v2);
    } else {
      let mut cycle = false;
      e.on_mvars(|v2| cycle |= self.expr_mvars.root(v2) == root);
      if cycle { return false }
      self.expr_mvars.assign(v, e);
    }
    true
  }

  fn new_context_next(&mut self, v: VarId, val: Option<Expr<'a>>, ty: Ty<'a>) -> &'a ContextNext<'a> {
    let val = val.unwrap_or_else(|| intern!(self, ExprKind::Var(v)));
    self.alloc.alloc(self.dc.new_context_next(v, val, ty))
  }

  fn merge(&mut self, span: &'a FileSpan, contexts: &mut [(DynContext<'a>, Vec<(VarId, GenId)>)]) -> bool {
    if contexts.iter().all(|(dc, _)| dc.generation == self.dc.generation) {return false}
    if let [(dc, _)] = contexts {
      mem::swap(&mut self.dc, dc);
      return true
    }
    let mut newdc = self.dc.clone();
    newdc.generation = self.new_generation();
    for c in self.dc.context.into_iter().filter(|c| c.gen == GenId::LATEST) {
      let v = c.var;
      let (old_gen, old_e, old_ty) = self.dc.gen_vars.get(&v).copied().unwrap_or((c.gen, c.val, c.ty));
      let mut new_e = Some(old_e);
      let mut modified = false;
      for (dc, vec) in &mut *contexts {
        if let Some(&(gen, e, ty)) = dc.gen_vars.get(&v) {
          if gen != old_gen {
            new_e = new_e.filter(|new_e| self.equate_expr(new_e, e).is_ok());
            self.relate_ty(span, ty, old_ty, Relation::Subtype);
            vec.push((v, gen));
            modified = true;
          }
        }
      }
      if modified {
        let new_e = new_e.unwrap_or_else(|| intern!(self, ExprKind::Var(v)));
        newdc.gen_vars.insert(v, (newdc.generation, new_e, old_ty));
      }
    }
    self.dc = newdc;
    true
  }

  fn whnf_expr(&self, e: Expr<'a>, ty: Ty<'a>) -> Expr<'a> {
    e // FIXME
  }

  fn whnf_ty(&mut self, wty: WhnfTy<'a>) -> WhnfTy<'a> {
    wty.map(intern!(self, match wty.ty.k {
      TyKind::Unit |
      TyKind::True |
      TyKind::False |
      TyKind::Bool |
      TyKind::Var(_) |
      TyKind::Int(_) |
      TyKind::UInt(_) |
      TyKind::Array(_, _) |
      TyKind::Own(_) |
      TyKind::Ref(_, _) |
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
      TyKind::User(f, tys, es) => {
        let_unchecked!(ty as Some(Entity::Type(ty)) = self.names.get(&f));
        let_unchecked!(args as Some(TypeTy {args, ..}) = ty.k.ty());
        todo!()
      }
      TyKind::If(e, t1, t2) => {
        let e2 = self.whnf_expr(e, self.common.t_bool);
        match e2.k {
          ExprKind::Bool(false) => return self.whnf_ty(wty.map(t1)),
          ExprKind::Bool(true) => return self.whnf_ty(wty.map(t2)),
          _ if e == e2 => return wty,
          _ => TyKind::If(e2, t1, t2),
        }
      }
      TyKind::HasTy(x, ty) => {
        let wty = WhnfTy::from(ty);
        if wty.uninit {return wty}
        let wty2 = self.whnf_ty(wty);
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
        let e2 = self.whnf_expr(e, self.common.t_bool);
        if e == e2 {return wty}
        TyKind::Pure(e2)
      }
      TyKind::Infer(v) => {
        if let Some(ty) = self.ty_mvars.lookup(v) {
          return self.whnf_ty(ty.into())
        }
        return wty
      }
      TyKind::Ghost(_) |
      TyKind::Uninit(_) |
      TyKind::Moved(_) => unreachable!(),
    }))
  }

  fn equate_lft(&mut self, a: Lifetime, b: Lifetime) -> StdResult<(), ()> {
    if a == b { return Ok(()) }
    match (a, b) {
      (Lifetime::Infer(v), _) => {
        if let Some(e) = self.lft_mvars.lookup(v) { return self.equate_lft(e, b) }
        self.lft_mvars.assign(v, b)
      }
      (_, Lifetime::Infer(v)) => {
        if let Some(e) = self.lft_mvars.lookup(v) { return self.equate_lft(a, e) }
        self.lft_mvars.assign(v, a)
      }
      _ => return Err(())
    }
    Ok(())
  }

  fn equate_expr(&mut self, a: Expr<'a>, b: Expr<'a>) -> StdResult<(), ()> {
    if a == b { return Ok(()) }
    match (a.k, b.k) {
      (ExprKind::Error, _) | (_, ExprKind::Error) => {}
      (ExprKind::Unop(op_a, a1), ExprKind::Unop(op_b, b1)) if op_a == op_b =>
        self.equate_expr(a1, b1)?,
      (ExprKind::Binop(op_a, a1, a2), ExprKind::Binop(op_b, b1, b2)) if op_a == op_b =>
        {self.equate_expr(a1, b1)?; self.equate_expr(a2, b2)?}
      (ExprKind::Index(a1, a2), ExprKind::Index(b1, b2)) =>
        {self.equate_expr(a1, b1)?; self.equate_expr(a2, b2)?}
      (ExprKind::Slice(a1, a2, a3), ExprKind::Slice(b1, b2, b3)) =>
        {self.equate_expr(a1, b1)?; self.equate_expr(a2, b2)?; self.equate_expr(a3, b3)?}
      (ExprKind::Proj(a1, p_a), ExprKind::Proj(b1, p_b)) if p_a == p_b => self.equate_expr(a1, b1)?,
      (ExprKind::List(ls_a), ExprKind::List(ls_b)) if ls_a.len() == ls_b.len() =>
        for (&a1, &b1) in ls_a.iter().zip(ls_b) {self.equate_expr(a1, b1)?},
      (ExprKind::Mm0(a1), ExprKind::Mm0(b1)) if std::ptr::eq(a1.expr, b1.expr) =>
        for (&a1, &b1) in a1.subst.iter().zip(b1.subst) {self.equate_expr(a1, b1)?},
      (ExprKind::Call {f: f_a, tys: tys_a, args: args_a},
       ExprKind::Call {f: f_b, tys: tys_b, args: args_b}) if f_a == f_b && tys_a == tys_b =>
        for (&a1, &b1) in args_a.iter().zip(args_b) {self.equate_expr(a1, b1)?},
      (ExprKind::If {cond: a1, then: a2, els: a3}, ExprKind::If {cond: b1, then: b2, els: b3}) =>
        {self.equate_expr(a1, b1)?; self.equate_expr(a2, b2)?; self.equate_expr(a3, b3)?}
      (ExprKind::Infer(v), _) => {
        if let Some(e) = self.expr_mvars.lookup(v) { return self.equate_expr(e, b) }
        if !self.assign_expr(v, b) { return Err(()) }
      }
      (_, ExprKind::Infer(v)) => {
        if let Some(e) = self.expr_mvars.lookup(v) { return self.equate_expr(a, e) }
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
        let_unchecked!(c as Some(Entity::Const(c)) = self.names.get(&c));
        match c.k {
          ConstTc::Unchecked => {}
        }
      }
      (_, ExprKind::Const(b1)) => return self.equate_expr(b, a),
      _ => return Err(())
    }
    Ok(())
  }

  fn relate_whnf_ty(&mut self, from: WhnfTy<'a>, to: WhnfTy<'a>, mut rel: Relation) -> StdResult<Vec<Coercion<'a>>, ()> {
    macro_rules! check {($($i:ident),*) => {{
      $(if from.$i != to.$i { return Err(()) })*
    }}}
    if from.ty == to.ty {
      check!(uninit, ghost, moved);
      return Ok(vec![])
    }
    match (from.ty.k, to.ty.k) {
      (TyKind::Error, _) | (_, TyKind::Error) => {}
      (TyKind::Array(ty_a, e_a), TyKind::Array(ty_b, e_b)) => {
        if let Relation::Subtype = rel { rel = Relation::SubtypeEqSize }
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
      (TyKind::Ref(lft_a, a1), TyKind::Ref(lft_b, b1)) |
      (TyKind::Shr(lft_a, a1), TyKind::Shr(lft_b, b1)) => {
        check!(uninit, ghost);
        self.equate_lft(lft_a, lft_b)?;
        if let Relation::Subtype | Relation::Coerce = rel { rel = Relation::SubtypeEqSize }
        let coes = self.relate_whnf_ty(a1.into(), b1.into(), rel)?;
        if !coes.is_empty() { unimplemented!() }
        return Ok(coes)
      }
      (TyKind::RefSn(a1), TyKind::RefSn(b1)) => {
        check!(uninit, ghost);
        self.equate_expr(a1, b1)?;
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
        let (a1, b1) = (a1.k.ty(), b1.k.ty());
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
        if let Some(ty) = self.ty_mvars.lookup(v) {
          return self.relate_whnf_ty(ty.into(), to, rel)
        }
        let to = to.to_ty(self);
        if !self.assign_ty(v, to) { return Err(()) }
      }
      (_, TyKind::Infer(v)) => {
        if let Some(ty) = self.ty_mvars.lookup(v) {
          return self.relate_whnf_ty(from, ty.into(), rel)
        }
        let from = from.to_ty(self);
        if !self.assign_ty(v, from) { return Err(()) }
      }
      _ => return Err(())
    }
    Ok(vec![])
  }

  fn relate_ty(&mut self, span: &'a FileSpan, from: Ty<'a>, to: Ty<'a>, rel: Relation) -> Option<Vec<Coercion<'a>>> {
    if from == to { return None }
    match self.relate_whnf_ty(from.into(), to.into(), rel) {
      Ok(coes) if coes.is_empty() => None,
      Ok(coes) => Some(coes),
      Err(()) => {
        self.errors.push(hir::Spanned {span, k: TypeError::Relate(from, to, rel)});
        Some(vec![Coercion::Error])
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
        (UnelabTupPat {span, k: UnelabTupPatKind::Name(g, n, ctx)},
         Some(intern!(self, ExprKind::Var(v))))
      }
      ast::TuplePatternKind::Typed(pat, ty) => {
        let ty = self.lower_ty(ty, ExpectTy::supertype(expect_t));
        let pat = self.lower_tuple_pattern(&pat.span, &pat.k, expect_e, Some(ty));
        if let Some(tgt) = expect_t {
          assert!(self.relate_ty(pat.0.span, tgt, ty, Relation::Subtype).is_none());
        }
        pat
      }
      ast::TuplePatternKind::Tuple(pats) => {
        let ty = expect_t.unwrap_or_else(|| self.new_ty_mvar(span));
        let res = self.tuple_pattern_tuple(span, pats.len(), ty);
        self.lower_tuple_pattern_tuple_result(span, pats, res, ty)
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
      ExprKind::Slice(a, _, len) => match self.expr_type(sp, a)?.k {
        TyKind::Array(ty, _) => intern!(self, TyKind::Array(ty, len)),
        _ => return None,
      }
      ExprKind::Proj(a, i) => match self.expr_type(sp, a)?.k {
        TyKind::List(tys) => *tys.get(u32_as_usize(i))?,
        TyKind::Struct(args) => {
          let ty = args.get(u32_as_usize(i))?.k.var().k.ty();
          let mut subst = Subst::default();
          subst.add_fvars(Ok(a));
          for (j, &arg) in args.iter().enumerate().take(u32_as_usize(i)) {
            match arg.k.var().k {
              TuplePatternKind::Name(_, v, _) =>
                subst.push_raw(v, Ok(intern!(self,
                  ExprKind::Proj(a, j.try_into().expect("overflow"))))),
              _ => unimplemented!("subfields"),
            }
          }
          subst.subst_ty(self, sp, ty)
        }
        _ => return None,
      }
      ExprKind::Unit => self.common.t_unit,
      ExprKind::Const(c) => {
        let_unchecked!(c as Some(Entity::Const(c)) = self.names.get(&c));
        match c.k {
          ConstTc::Unchecked => return None,
        }
      }
      ExprKind::Bool(_) => self.common.t_bool,
      ExprKind::Int(n) => if n.is_negative() {self.common.int()} else {self.common.nat()},
      ExprKind::Unop(op, _) => op.ret_ty(self),
      ExprKind::Binop(op, e1, e2) => if op.int_out() {
        if op.preserves_nat() &&
          matches!(self.expr_type(sp, e1)?.k, TyKind::UInt(_)) &&
          matches!(self.expr_type(sp, e2)?.k, TyKind::UInt(_)) {
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
      ExprKind::As(_, AsKind::Mod(ity)) => self.common.int_ty(ity),
      ExprKind::Sizeof(_) => self.common.nat(),
      _ => return None,
      ExprKind::Error => self.common.t_error,
    })
  }

  fn tuple_pattern_tuple(&mut self,
    sp: &'a FileSpan, nargs: usize, expect: Ty<'a>
  ) -> TuplePatternResult<'a> {
    macro_rules! expect {($n:expr) => {{
      if nargs != $n { return TuplePatternResult::Fail(true) }
    }}}
    let wty = self.whnf_ty(expect.into());
    match wty.ty.k {
      TyKind::Ghost(_) |
      TyKind::Uninit(_) |
      TyKind::Moved(_) => unreachable!(),
      TyKind::Infer(_) => TuplePatternResult::Indeterminate,
      TyKind::Error => TuplePatternResult::Fail(false),
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
        let n_tgt: Option<usize> = match self.whnf_expr(n, self.common.nat()).k {
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
      TyKind::Own(_) => todo!(),
      TyKind::Ref(_, _) => todo!(),
      TyKind::Shr(_, _) => todo!(),
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
        expect!(args.iter().filter(|&arg| matches!(arg.k, ArgKind::Lam(_))).count());
        TuplePatternResult::Tuple(TupleMatchKind::Struct,
          TupleIter::mk_args(self, sp, Subst::default(), args.iter()))
      }
      _ => TuplePatternResult::Fail(false),
    }
  }

  fn lower_tuple_pattern_tuple_result(&mut self, span: &'a FileSpan,
    pats: &'a [(VarId, ast::TuplePattern)],
    res: TuplePatternResult<'a>, tgt: Ty<'a>
  ) -> (UnelabTupPat<'a>, Option<Expr<'a>>) {
    let (k, e) = match res {
      TuplePatternResult::Indeterminate => {
        let (pats, _) = self.lower_tuple_pattern_tuple_with(pats, TupleIter::Ty(None));
        (UnelabTupPatKind::Tuple(pats, tgt), None)
      }
      TuplePatternResult::Fail(report) => {
        let (pats, _) = self.lower_tuple_pattern_tuple_with(pats, TupleIter::Ty(None));
        let ty = intern!(self, TyKind::List(
          self.alloc.alloc_slice_fill_iter(pats.iter().map(UnelabTupPat::ty))));
        if report {
          self.errors.push(hir::Spanned {span, k: TypeError::PatternMatch(tgt, ty)});
        }
        let pat = Box::new(UnelabTupPat {span, k: UnelabTupPatKind::Tuple(pats, ty)});
        (UnelabTupPatKind::Error(pat, tgt), Some(self.common.e_error))
      }
      TuplePatternResult::Tuple(mk, it) => {
        // let mut it = tys.iter();
        let (pats, es) = self.lower_tuple_pattern_tuple_with(pats, it);
        (UnelabTupPatKind::Tuple(pats, tgt), mk.build(self, es))
      }
    };
    (UnelabTupPat {span, k}, e)
  }

  fn lower_tuple_pattern_tuple_with(&mut self,
    pats: &'a [(VarId, ast::TuplePattern)],
    it: TupleIter<'a>,
  ) -> (Vec<UnelabTupPat<'a>>, Vec<Option<Expr<'a>>>) {
    let mut es = Vec::with_capacity(pats.len());
    let mut opt_it = Some(it);
    let pats = pats.iter().map(|&(v, Spanned {ref span, k: ref pat})| {
      let tgt = opt_it.as_mut().and_then(|it| it.next(self));
      let (pat, e) = self.lower_tuple_pattern(span, pat, None, tgt);
      if let Some(it) = &mut opt_it {
        if let Some(e) = e { it.push(self, e) }
        else { opt_it = None }
      }
      es.push(e);
      pat
    }).collect();
    (pats, es)
  }

  fn finish_tuple_pattern_inner(&mut self, pat: &UnelabTupPat<'a>) -> (TuplePattern<'a>, Expr<'a>) {
    let (k, e) = match &pat.k {
      &UnelabTupPatKind::Name(_, n, c) => {
        self.dc.context = c.into();
        (TuplePatternKind::Name(n, c.var, c.ty), intern!(self, ExprKind::Var(c.var)))
      }
      UnelabTupPatKind::Error(pat, tgt) => {
        let (pat, e) = self.finish_tuple_pattern_inner(pat);
        (TuplePatternKind::Error(pat, tgt), e)
      }
      UnelabTupPatKind::Tuple(pats, tgt) => {
        let mut res = self.tuple_pattern_tuple(pat.span, pats.len(), tgt);
        if let TuplePatternResult::Indeterminate = res {
          let tys = self.alloc.alloc_slice_fill_iter(pats.iter().map(UnelabTupPat::ty));
          res = TuplePatternResult::Tuple(TupleMatchKind::List, TupleIter::List(tys.iter()))
        }
        match res {
          TuplePatternResult::Indeterminate => unreachable!(),
          TuplePatternResult::Fail(_) => {
            let ty = intern!(self, TyKind::List(
              self.alloc.alloc_slice_fill_iter(pats.iter().map(UnelabTupPat::ty))));
            let pats = pats.iter().map(|pat| self.finish_tuple_pattern_inner(pat).0).collect::<Vec<_>>();
            let pats = self.alloc.alloc_slice_fill_iter(pats.into_iter());
            let pat = intern!(self, TuplePatternKind::Tuple(pats, TupleMatchKind::List, ty));
            (TuplePatternKind::Error(pat, tgt), self.common.e_error)
          }
          TuplePatternResult::Tuple(mk, mut it) => {
            let mut es = Vec::with_capacity(pats.len());
            let pats = pats.iter().map(|pat| {
              let tgt = it.next(self);
              let (pat, e) = self.finish_tuple_pattern_inner(pat);
              it.push(self, e);
              es.push(Some(e));
              pat
            }).collect::<Vec<_>>();
            let pats = self.alloc.alloc_slice_fill_iter(pats.into_iter());
            let e = mk.build(self, es).unwrap_or(self.common.e_error);
            (TuplePatternKind::Tuple(pats, mk, tgt), e)
          }
        }
      }
    };
    (intern!(self, k), e)
  }

  fn finish_tuple_pattern(&mut self, pat: &UnelabTupPat<'a>) -> TuplePattern<'a> {
    pat.base_context(self);
    let base = self.dc.context;
    let (res, _) = self.finish_tuple_pattern_inner(pat);
    self.dc.context = base;
    res
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
      ast::TypeKind::Ref(lft, n) => {
        let lft = self.lower_opt_lft(&ty.span, lft);
        let ty = self.lower_ty(ty, ExpectTy::Any);
        intern!(self, TyKind::Ref(lft, ty))
      }
      ast::TypeKind::Shr(lft, n) => {
        let lft = self.lower_opt_lft(&ty.span, lft);
        let ty = self.lower_ty(ty, ExpectTy::Any);
        intern!(self, TyKind::Shr(lft, ty))
      }
      ast::TypeKind::RefSn(e) => {
        let (e, _) = self.lower_pure_expr(e, ExpectExpr::Any);
        intern!(self, TyKind::RefSn(e))
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
        let args = args.iter().map(|arg| self.lower_arg(&arg.span, &arg.k.1)).collect();
        let args = self.finish_args(args);
        intern!(self, TyKind::Struct(args))
      }
      ast::TypeKind::All(pats, ty) => {
        let pats = pats.iter().map(|pat| {
          self.lower_tuple_pattern(&pat.span, &pat.k, None, None).0
        }).collect::<Vec<_>>();
        let mut ty = self.lower_ty(ty, ExpectTy::Any);
        for pat in pats.into_iter().rev() {
          let pat = self.finish_tuple_pattern(&pat);
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
        let f_ty = let_unchecked!(Some(Entity::Type(ty)) = self.names.get(f),
          unwrap_unchecked!(ty.k.ty()));
        todo!()
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
      ast::TypeKind::Infer => self.new_ty_mvar(&ty.span),
      ast::TypeKind::Error => self.common.t_error,
    }
  }

  fn lower_pure_expr(&mut self, e: &'a ast::Expr, expect: ExpectExpr<'a>) -> (Expr<'a>, Ty<'a>) {
    let (_, pe, ty) = self.lower_expr(e, expect);
    (self.as_pure(&e.span, pe), ty)
  }

  fn apply_coe(&mut self, c: Coercion<'a>, e: Expr<'a>) -> Expr<'a> {
    match c {
      Coercion::Error => self.common.e_error,
      Coercion::Phantom(_) => unreachable!()
    }
  }

  fn apply_coe_expr(&mut self, c: Coercion<'a>, e: hir::Expr<'a>) -> hir::Expr<'a> {
    match c {
      Coercion::Error => e.map_into(|_| hir::ExprKind::Error),
      Coercion::Phantom(_) => unreachable!()
    }
  }

  fn coerce_pure_expr(&mut self, sp: &'a FileSpan, mut e: Expr<'a>, from: Ty<'a>, to: Ty<'a>) -> Expr<'a> {
    if let Some(coe) = self.relate_ty(sp, from, to, Relation::Coerce) {
      for c in coe { e = self.apply_coe(c, e) }
    }
    e
  }

  fn check_pure_expr(&mut self, e: &'a ast::Expr, tgt: Ty<'a>) -> Expr<'a> {
    let (pe, ty) = self.lower_pure_expr(e, ExpectExpr::HasTy(tgt));
    self.coerce_pure_expr(&e.span, pe, ty, tgt)
  }

  fn lower_arg(&mut self, sp: &'a FileSpan, arg: &'a ast::ArgKind) -> UnelabArg<'a> {
    match arg {
      ast::ArgKind::Lam(pat) => UnelabArg::Lam(self.lower_tuple_pattern(sp, pat, None, None).0),
      ast::ArgKind::Let(Spanned {span, k: pat}, e) => {
        let ctx1 = self.dc.context;
        let pat = self.lower_tuple_pattern(span, pat, None, None).0;
        let ctx2 = mem::replace(&mut self.dc.context, ctx1);
        let e = self.check_pure_expr(e, pat.ty());
        self.dc.context = ctx2;
        UnelabArg::Let(pat, e)
      }
    }
  }

  fn finish_arg(&mut self, arg: UnelabArg<'a>) -> Arg<'a> {
    intern!(self, match arg {
      UnelabArg::Lam(pat) => ArgKind::Lam(self.finish_tuple_pattern(&pat)),
      UnelabArg::Let(pat, e) => ArgKind::Let(self.finish_tuple_pattern(&pat), e),
    })
  }

  fn finish_args(&mut self, args: Vec<UnelabArg<'a>>) -> &'a [Arg<'a>] {
    let args = args.into_iter().rev().map(|arg| self.finish_arg(arg)).collect::<Vec<_>>();
    self.alloc.alloc_slice_fill_iter(args.into_iter().rev())
  }

  fn lower_variant(&mut self, variant: &'a Option<Box<ast::Variant>>) -> Option<hir::Variant<'a>> {
    variant.as_deref().map(|Spanned {span, k: (e, vt)}| match vt {
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
  ) -> (hir::Expr<'a>, Option<Expr<'a>>) {
    let arrty = intern!(self, TyKind::Array(ty, n));
    let (mut e_a, a, mut ty_a) = self.lower_expr(a, ExpectExpr::HasTy(arrty));
    while let TyKind::Ref(_, aty2) = ty_a.k {
      e_a = hir::Expr {span, k: hir::ExprKind::Rval(Box::new(e_a))};
      ty_a = aty2;
    }
    (self.coerce_expr(e_a, ty_a, arrty), a)
  }

  fn prop_to_expr(&mut self, p: Ty<'a>) -> Option<Expr<'a>> {
    Some(match self.whnf_ty(p.into()).ty.k {
      TyKind::True | TyKind::Unit => self.common.e_bool(true),
      TyKind::False => self.common.e_bool(false),
      TyKind::Imp(p, q) | TyKind::Wand(p, q) =>
        intern!(self, ExprKind::Binop(Binop::Or,
          intern!(self, ExprKind::Unop(Unop::Not, self.prop_to_expr(p)?)),
          self.prop_to_expr(q)?)),
      TyKind::Not(p) =>
        intern!(self, ExprKind::Unop(Unop::Not, self.prop_to_expr(p)?)),
      TyKind::And(ps) | TyKind::List(ps) => {
        let mut ret = None;
        for p in ps {
          let p = self.prop_to_expr(p)?;
          ret = Some(ret.map_or(p, |r| intern!(self, ExprKind::Binop(Binop::And, r, p))))
        }
        ret.unwrap_or_else(|| self.common.e_bool(false))
      }
      TyKind::Or(ps) => {
        let mut ret = None;
        for p in ps {
          let p = self.prop_to_expr(p)?;
          ret = Some(ret.map_or(p, |r| intern!(self, ExprKind::Binop(Binop::Or, r, p))))
        }
        ret.unwrap_or_else(|| self.common.e_bool(true))
      }
      TyKind::Pure(e) => e,
      TyKind::Infer(v) => {
        let w = self.new_expr_mvar(self.ty_mvars[v].span);
        let p = intern!(self, TyKind::Pure(w));
        self.ty_mvars.assign(v, p);
        w
      }
      _ => return None,
    })
  }

  fn lower_expr_kind(&mut self, span: &'a FileSpan,
    e: &'a ast::ExprKind, expect: ExpectExpr<'a>
  ) -> (hir::Expr<'a>, Option<Expr<'a>>, Ty<'a>) {

    fn whnf_expect<'a>(ctx: &mut InferCtx<'a>, expect: ExpectExpr<'a>) -> Option<Ty<'a>> {
      Some(ctx.whnf_ty(expect.to_ty()?.into()).ty)
    }

    fn as_int_ty<'a>(ctx: &mut InferCtx<'a>, expect: ExpectExpr<'a>) -> Option<IntTy> {
      match whnf_expect(ctx, expect)?.k {
        TyKind::Int(sz) => Some(IntTy::Int(sz)),
        TyKind::UInt(sz) => Some(IntTy::UInt(sz)),
        _ => None,
      }
    }

    macro_rules! ret {($k:expr, $pe:expr, $e:expr) => {
      (hir::Expr {span, k: {use hir::ExprKind::*; $k}}, $pe, $e)
    }}
    macro_rules! error {($($sp:expr, $es:expr),*) => {{
      $({
        use TypeError::*; let k = $es;
        self.errors.push(hir::Spanned {span: $sp, k});
      })*
      return ret![Error, None, self.common.t_error]
    }}}

    match e {
      ast::ExprKind::Unit => ret![Unit, Some(self.common.e_unit), self.common.t_unit],

      &ast::ExprKind::Var(v) => {
        let (gen, val, ty) = self.dc.get_var(v);
        ret![Var(v, gen), Some(val), ty]
      },

      &ast::ExprKind::Const(c) => {
        let_unchecked!(c as Some(Entity::Const(c)) = self.names.get(&c));
        match c.k {
          ConstTc::Unchecked => error!()
        }
      },

      &ast::ExprKind::Global(g) => {
        let_unchecked!(g as Some(Entity::Global(g)) = self.names.get(&g));
        match g.k {
          GlobalTc::Unchecked => error!()
        }
      },

      &ast::ExprKind::Bool(b) =>
        ret![Bool(b), Some(self.common.e_bool(b)), self.common.t_bool],

      ast::ExprKind::Int(n) => {
        #[allow(clippy::map_unwrap_or)]
        let ty = as_int_ty(self, expect)
          .filter(|ity| ity.in_range(n))
          .map(|ity| ity.to_ty(self))
          .unwrap_or_else(|| {
            if n.is_negative() { self.common.int() }
            else { self.common.nat() }
          });
        ret![Int(n), Some(intern!(self, ExprKind::Int(n))), ty]
      }

      ast::ExprKind::Unop(Unop::Neg, e) => {
        let (e, pe) = self.check_expr(e, self.common.int());
        ret![Unop(self::Unop::Neg, Box::new(e)),
          pe.map(|pe| intern!(self, ExprKind::Unop(Unop::Neg, pe))),
          self.common.int()]
      }

      ast::ExprKind::Unop(Unop::Not, e) => {
        let (e, pe) = self.check_expr(e, self.common.t_bool);
        ret![Unop(self::Unop::Neg, Box::new(e)),
          pe.map(|pe| intern!(self, ExprKind::Unop(Unop::Not, pe))),
          self.common.t_bool]
      }

      ast::ExprKind::Unop(Unop::BitNot(_), e) => {
        let sz = as_int_ty(self, expect)
          .and_then(|ty| if let IntTy::UInt(sz) = ty { Some(sz) } else { None })
          .unwrap_or(Size::Inf);
        let ty =
          if let Size::Inf = sz { self.common.int() }
          else { self.common.t_uint(sz) };
        let (e, pe) = self.check_expr(e, ty);
        ret![Unop(self::Unop::BitNot(sz), Box::new(e)),
          pe.map(|pe| intern!(self, ExprKind::Unop(Unop::BitNot(sz), pe))),
          ty]
      }

      &ast::ExprKind::Binop(op, ref e1, ref e2) => {
        let ((e1, pe1), (e2, pe2), tyout) = if op.int_in() {
          let tyin = as_int_ty(self, expect).unwrap_or(IntTy::Int(Size::Inf)).to_ty(self);
          let (e1, pe1, ty1) = self.lower_expr(e1, ExpectExpr::HasTy(tyin));
          let (e2, pe2, ty2) = self.lower_expr(e2, ExpectExpr::HasTy(tyin));
          let (tyin2, tyout) = if op.int_out() {
            let ty = (|| -> Option<_> {
              if !op.preserves_nat() {return None}
              let sz1 = if let Some(IntTy::UInt(sz1)) =
                as_int_ty(self, ExpectExpr::HasTy(ty1)) {sz1} else {return None};
              let sz2 = if let Some(IntTy::UInt(sz2)) =
                as_int_ty(self, ExpectExpr::HasTy(ty2)) {sz2} else {return None};
              Some(if op.preserves_usize() {
                intern!(self, TyKind::UInt(std::cmp::max(sz1, sz2)))
              } else {
                self.common.nat()
              })
            }()).unwrap_or_else(|| self.common.int());
            (ty, ty)
          } else {
            (self.common.int(), self.common.t_bool)
          };
          let e1 = self.coerce_expr(e1, ty1, tyin2);
          let e2 = self.coerce_expr(e2, ty2, tyin2);
          ((e1, pe1), (e2, pe2), tyout)
        } else {
          (self.check_expr(e1, self.common.t_bool),
           self.check_expr(e2, self.common.t_bool),
           self.common.t_bool)
        };
        ret![Binop(op, Box::new(e1), Box::new(e2)),
          pe1.and_then(|pe1| pe2.map(|pe2|
            intern!(self, ExprKind::Binop(op, pe1, pe2)))),
          tyout]
      }

      ast::ExprKind::Sn(x, h) => {
        let expect2 = ExpectExpr::has_ty(whnf_expect(self, expect));
        let (e, pe, ty) = self.lower_expr(x, expect2);
        let y = self.as_pure(&x.span, pe);
        let x = if let ExpectExpr::Sn(x, _) = expect {x} else {self.new_expr_mvar(span)};
        let h = h.as_deref().map(|h| Box::new({
          let ty = intern!(self, TyKind::Pure(intern!(self, ExprKind::Binop(Binop::Eq, x, y))));
          self.check_expr(h, ty).0
        }));
        ret![Sn(Box::new(e), h), Some(y), intern!(self, TyKind::Sn(x, ty))]
      }

      ast::ExprKind::Index(arr, idx, hyp) => {
        let ty = expect.to_ty().unwrap_or_else(|| self.new_ty_mvar(span));
        let n = self.new_expr_mvar(span);
        let (e_a, arr) = self.check_array(span, arr, ty, n);
        let (e_i, idx) = self.check_expr(idx, self.common.nat());
        let hyp = hyp.as_deref().map(|h| Box::new({
          let idx = self.as_pure(e_i.span, idx);
          let ty = intern!(self, TyKind::Pure(
            intern!(self, ExprKind::Binop(Binop::Lt, idx, n))));
          self.check_expr(h, ty).0
        }));
        ret![Index(Box::new(e_a), Box::new(e_i), hyp),
          arr.and_then(|a| Some(intern!(self, ExprKind::Index(a, idx?)))),
          ty]
      }

      ast::ExprKind::Slice(args, hyp) => {
        let (arr, idx, len) = &**args;
        let ty = whnf_expect(self, expect)
          .and_then(|ty| if let TyKind::Array(ty, _) = ty.k {Some(ty)} else {None})
          .unwrap_or_else(|| self.new_ty_mvar(span));
        let n = self.new_expr_mvar(span);
        let (e_a, arr) = self.check_array(span, arr, ty, n);
        let (e_i, idx) = self.check_expr(idx, self.common.nat());
        let (e_l, len) = self.check_expr(len, self.common.nat());
        let e_l = self.as_pure(e_l.span, len);
        let hyp = hyp.as_deref().map(|hyp| Box::new({
          let e_i = self.as_pure(e_i.span, idx);
          let ty = intern!(self, TyKind::Pure(
            intern!(self, ExprKind::Binop(Binop::Le,
              intern!(self, ExprKind::Binop(Binop::Add, e_i, e_l)), n))));
          self.check_expr(hyp, ty).0
        }));
        ret![Index(Box::new(e_a), Box::new(e_i), hyp),
          arr.and_then(|a| Some(intern!(self, ExprKind::Slice(a, idx?, e_l)))),
          intern!(self, TyKind::Array(ty, e_l))]
      },

      ast::ExprKind::Proj(e, field) => {
        enum ProjKind<'a> {
          And(&'a [Ty<'a>]),
          List(&'a [Ty<'a>]),
          Struct(&'a [Arg<'a>]),
        }
        let (mut e2, pe, ty) = self.lower_expr(e, ExpectExpr::Any);
        let mut wty = self.whnf_ty(ty.into()).ty;
        let tys = loop {
          match wty.k {
            TyKind::Ref(_, ty2) => {
              e2 = hir::Expr {span, k: hir::ExprKind::Rval(Box::new(e2))};
              wty = ty2;
            }
            TyKind::List(tys) => break ProjKind::List(tys),
            TyKind::And(tys) => break ProjKind::And(tys),
            TyKind::Struct(args) => break ProjKind::Struct(args),
            TyKind::Error => error!(),
            _ => error!(e2.span, ExpectedStruct(wty))
          }
        };
        let ret = |i, pe, ty| ret![Proj(Box::new(e2), i), pe, ty];
        #[allow(clippy::never_loop)] loop { // try block, not a loop
          match tys {
            ProjKind::List(tys) => if let FieldName::Number(i) = field.k {
              if let Some(&ty) = tys.get(u32_as_usize(i)) {
                break ret(i, pe.map(|pe| intern!(self, ExprKind::Proj(pe, i))), ty)
              }
            },
            ProjKind::And(tys) => if let FieldName::Number(i) = field.k {
              if let Some(&ty) = tys.get(u32_as_usize(i)) {
                break ret(i, pe, ty)
              }
            },
            ProjKind::Struct(args) => {
              if let Some((i, vec)) = match field.k {
                FieldName::Number(i) if u32_as_usize(i) < args.len() => Some((i, vec![])),
                FieldName::Number(i) => None,
                FieldName::Named(f) => ArgKind::find_field(args, f),
              } {
                if !vec.is_empty() { unimplemented!("subfields") }
                let ty = args[u32_as_usize(i)].k.var().k.ty();
                let mut subst = Subst::default();
                let per = pe.ok_or(&e.span);
                subst.add_fvars(per);
                for (j, &arg) in args.iter().enumerate().take(u32_as_usize(i)) {
                  match arg.k.var().k {
                    TuplePatternKind::Name(_, v, _) =>
                      subst.push_raw(v, per.map(|pe| intern!(self,
                        ExprKind::Proj(pe, j.try_into().expect("overflow"))))),
                    _ => unimplemented!("subfields"),
                  }
                }
                let ty = subst.subst_ty(self, span, ty);
                break ret(i, pe.map(|pe| intern!(self, ExprKind::Proj(pe, i))), ty)
              }
            }
          }
          error!(&field.span, FieldMissing(wty, field.k))
        }
      },

      ast::ExprKind::Deref(e) => {
        let expect2 = match expect {
          ExpectExpr::Sn(a, _) => ExpectExpr::HasTy(intern!(self, TyKind::RefSn(a))),
          _ => ExpectExpr::Any
        };
        let (e2, pe, ty) = self.lower_expr(e, expect2);
        let wty = self.whnf_ty(ty.into()).ty;
        match wty.k {
          TyKind::RefSn(e) => if let Some(ty) = self.expr_type(span, e) {
            ret![Deref(Box::new(e2)), Some(e), ty]
          } else {
            error!(e2.span, ExpectedPlace)
          }
          TyKind::Error => error!(),
          _ => {
            let tgt = intern!(self, TyKind::RefSn(self.new_expr_mvar(e2.span)));
            error!(e2.span, Relate(ty, tgt, Relation::Equal))
          }
        }
      }

      ast::ExprKind::List(es) => {
        let tgt = expect.to_ty()
          .map(|ty| self.whnf_ty(ty.into()).ty)
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
        macro_rules! proof {($e:expr, $ty:expr) => {
          ret![Proof({use hir::Proof::*; $e}), Some(self.common.e_unit), $ty]
        }}
        match tgt.k {
          TyKind::Unit => {
            expect!(0);
            ret![Unit, Some(self.common.e_unit), self.common.t_unit]
          }
          TyKind::True => {
            expect!(0);
            proof![ITrue, self.common.t_unit]
          }
          TyKind::Array(tgt1, n_tgt) => {
            let n = intern!(self, ExprKind::Int(self.alloc.alloc(es.len().into())));
            let ty = intern!(self, TyKind::Array(tgt1, n));
            #[allow(clippy::never_loop)]
            let n_tgt = loop {
              if let ExprKind::Int(n) = self.whnf_expr(n_tgt, self.common.nat()).k {
                if let Ok(n) = n.try_into() { break n }
              }
              error!(span, Relate(ty, tgt, Relation::Equal))
            };
            expect!(n_tgt);
            let mut pes = Vec::with_capacity(n_tgt);
            let es = es.iter().map(|e| {
              let (e, pe) = self.check_expr(e, tgt1);
              if let Some(pe) = pe {pes.push(pe)}
              e
            }).collect();
            let pes = if pes.len() == n_tgt {
              Some(intern!(self, ExprKind::Array(
                self.alloc.alloc_slice_fill_iter(pes.into_iter()))))
            } else { None };
            ret![List(es, ty), pes, ty]
          }
          TyKind::List(tgts) => {
            expect!(tgts.len());
            let mut pes = Vec::with_capacity(tgts.len());
            let es = es.iter().zip(tgts).map(|(e, &tgt)| {
              let (e, pe) = self.check_expr(e, tgt);
              if let Some(pe) = pe {pes.push(pe)}
              e
            }).collect();
            let pes = if pes.len() == tgts.len() {
              Some(intern!(self, ExprKind::Array(
                self.alloc.alloc_slice_fill_iter(pes.into_iter()))))
            } else { None };
            ret![List(es, tgt), pes, tgt]
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
              ret![List(es, tgt), Some(val), tgt]
            } else {
              proof![ITrue, self.common.t_unit]
            }
          }
          TyKind::Struct(args) => {
            expect!(args.iter().filter(|&arg| matches!(arg.k, ArgKind::Lam(_))).count());
            let (es, pes, _) = self.check_args(span, es, args);
            let val = pes.map(|pes| intern!(self, ExprKind::List(
              self.alloc.alloc_slice_fill_iter(pes.into_iter()))));
            ret![List(es, tgt), val, tgt]
          }
          TyKind::Own(_) |
          TyKind::Shr(_, _) |
          TyKind::Sn(_, _) => { expect!(2); todo!() }
          _ => error!()
        }
      }

      ast::ExprKind::Ghost(e) => {
        let mut f = |ty: Ty<'a>| {
          let mut wty = self.whnf_ty(ty.into());
          wty.ghost = false;
          wty.to_ty(self)
        };
        let expect2 = match expect {
          ExpectExpr::Any => ExpectExpr::Any,
          ExpectExpr::HasTy(ty) => ExpectExpr::HasTy(f(ty)),
          ExpectExpr::Sn(a, ty) => ExpectExpr::Sn(a, f(ty))
        };
        let (e, pe, ty) = self.lower_expr(e, expect2);
        let mut wty = WhnfTy::from(ty);
        wty.ghost = true;
        ret![Ghost(Box::new(e)), pe, wty.to_ty(self)]
      }

      ast::ExprKind::Place(e) => {
        let (e, pe, ty) = self.lower_expr(e, expect);
        ret![Place(Box::new(e)), pe, ty]
      }

      ast::ExprKind::Ref(e) => {
        let (e, pe, ty) = self.lower_expr(e, expect);
        ret![Place(Box::new(e)), pe, ty]
      }

      ast::ExprKind::Mm0(types::Mm0Expr {subst, expr}) => {
        let mut p_subst = Vec::with_capacity(subst.len());
        let subst = subst.iter().map(|e| {
          let (e, pe, ty) = self.lower_expr(e, ExpectExpr::Any); // TODO: better expected type
          p_subst.push(self.as_pure(e.span, pe));
          e
        }).collect();
        let tgt = expect.to_ty().unwrap_or_else(|| self.common.nat());
        let pe = self.alloc.alloc_slice_fill_iter(p_subst.into_iter());
        let pe = intern!(self, ExprKind::Mm0(Mm0Expr {subst: pe, expr }));
        ret![Mm0(types::Mm0Expr { subst, expr: expr.clone() }, tgt), Some(pe), tgt]
      }

      ast::ExprKind::Typed(e, ty) => {
        let ty = self.lower_ty(ty, ExpectTy::coerce_to(expect.to_ty()));
        let (e, pe) = self.check_expr(e, ty);
        (e, pe, ty)
      }

      ast::ExprKind::As(e, tgt) => {
        let tgt = self.lower_ty(tgt, ExpectTy::Any);
        let (e, pe, ty) = self.lower_expr(e, ExpectExpr::Any);
        macro_rules! fail {() => {error!(span, UnsupportedAs(ty, tgt))}}
        let ty = self.whnf_ty(ty.into()).ty;
        if let (Ok(ity), Ok(ity2)) = (IntTy::try_from(ty), IntTy::try_from(tgt)) {
          if ity <= ity2 {
            ret![Cast(Box::new(e), ty, tgt, hir::CastKind::Subtype(None)), pe, tgt]
          } else if let IntTy::UInt(Size::Inf) = ity2 {
            fail!()
          } else {
            let ak = AsKind::Mod(ity2);
            let pe = pe.map(|e| intern!(self, ExprKind::As(e, ak)));
            ret![As(Box::new(e), ty, tgt, ak), pe, tgt]
          }
        } else if
          matches!(ty.k, TyKind::Own(_) | TyKind::Shr(_, _) | TyKind::RefSn(_)) &&
          matches!(tgt.k, TyKind::UInt(Size::S64)) {
          ret![Cast(Box::new(e), ty, tgt, hir::CastKind::Subtype(None)), pe, tgt]
        } else { fail!() }
      }

      ast::ExprKind::Cast(e, h) => {
        let (e, pe, ty) = self.lower_expr(e, ExpectExpr::Any);
        let tgt = expect.to_ty().unwrap_or_else(|| self.new_ty_mvar(span));
        let ck = if let Some(x) = pe {
          hir::CastKind::Wand(x, h.as_deref().map(|h| Box::new({
            // [x: ty] -* [x: tgt]
            let hty = intern!(self, TyKind::Wand(
              intern!(self, TyKind::HasTy(x, ty)),
              intern!(self, TyKind::HasTy(x, tgt))));
            self.check_expr(h, hty).0
          })))
        } else {
          hir::CastKind::Subtype(h.as_deref().map(|h| Box::new({
            let v = self.fresh_var();
            let x = intern!(self, ExprKind::Var(v));
            // A. x: ty, [x: ty] -* [x: tgt]
            let hty = intern!(self, TyKind::All(
              intern!(self, TuplePatternKind::Name(AtomId::UNDER, v, ty)),
              intern!(self, TyKind::Wand(
                intern!(self, TyKind::HasTy(x, ty)),
                intern!(self, TyKind::HasTy(x, tgt))))));
            self.check_expr(h, hty).0
          })))
        };
        ret![Cast(Box::new(e), ty, tgt, ck), pe, tgt]
      }

      ast::ExprKind::Pun(e, h) => {
        let (e, pe, ty) = self.lower_expr(e, ExpectExpr::Any);
        let pe = self.as_pure(e.span, pe);
        let tgt = expect.to_ty().unwrap_or_else(|| self.new_ty_mvar(span));
        let ck = hir::CastKind::Mem(pe, h.as_deref().map(|h| Box::new({
          // [x: tgt]
          let hty = intern!(self, TyKind::HasTy(pe, tgt));
          self.check_expr(h, hty).0
        })));
        ret![Cast(Box::new(e), ty, tgt, ck), Some(pe), tgt]
      }

      ast::ExprKind::Uninit => {
        let mut tgt = WhnfTy::from(expect.to_ty().unwrap_or_else(|| self.new_ty_mvar(span)));
        tgt.uninit = false;
        let tgt = tgt.to_ty(self);
        let u_tgt = intern!(self, TyKind::Uninit(tgt));
        ret![Uninit(tgt), None, u_tgt]
      }

      ast::ExprKind::Sizeof(ty) => {
        let ty = self.lower_ty(ty, ExpectTy::Any);
        let pe = intern!(self, ExprKind::Sizeof(ty));
        ret![Sizeof(ty), Some(pe), self.common.nat()]
      }

      ast::ExprKind::Typeof(e) => {
        let (e, pe, ty) = self.lower_expr(e, ExpectExpr::Any);
        let pe = self.as_pure(e.span, pe);
        let ty = intern!(self, TyKind::HasTy(pe, ty));
        ret![Typeof(Box::new(e), ty), Some(self.common.e_unit), ty]
      }

      ast::ExprKind::Assert(p) => {
        let tgt = expect.to_ty();
        let b = tgt.and_then(|ty| self.prop_to_expr(ty));
        let (e, pe, _) = self.lower_expr(p, match b {
          Some(b) => ExpectExpr::Sn(b, self.common.t_bool),
          None => ExpectExpr::HasTy(self.common.t_bool)
        });
        let tgt = tgt.unwrap_or_else(|| intern!(self, pe.map_or(TyKind::True, TyKind::Pure)));
        ret![Assert(Box::new(e), tgt), Some(self.common.e_unit), tgt]
      }

      ast::ExprKind::Assign {lhs, rhs, oldmap} => {
        enum Lens<'a> {
          Index(Expr<'a>),
          Slice(Expr<'a>, Expr<'a>),
          Proj(u32),
        }
        let (lhs, plhs, lty) = self.lower_expr(lhs, ExpectExpr::Any);
        let plhs = self.as_pure(lhs.span, plhs);
        let mut origin = plhs;
        let mut lens = vec![];
        let v = loop {
          match origin.k {
            ExprKind::Var(v) => break v,
            ExprKind::Index(a, i) => {lens.push((a, Lens::Index(i))); origin = a}
            ExprKind::Slice(a, i, l) => {lens.push((a, Lens::Slice(i, l))); origin = a}
            ExprKind::Proj(a, i) => {lens.push((a, Lens::Proj(i))); origin = a}
            ExprKind::Error => error!(),
            ExprKind::Infer(v) => error!(lhs.span, ExpectedType),
            _ => error!(lhs.span, UnsupportedAssign),
          }
        };
        let (rhs, prhs, _) = self.lower_expr(rhs, ExpectExpr::HasTy(lty));
        let (gen, e, ty) = self.dc.get_var(v);
        let old = if let Some(&(_, old)) = oldmap.iter().find(|p| p.0 == v) {old} else {
          let name = self.var_names.get(&v).copied().unwrap_or(AtomId::UNDER);
          error!(span, MissingAssignWith(name))
        };
        let e = Some(intern!(self, ExprKind::Var(old)));
        self.dc.context = self.new_context_next(old, e, ty).into();
        let newgen = self.new_generation();
        let val = if let Some(mut val) = prhs {
          for (a, l) in lens {
            val = intern!(self, match l {
              Lens::Index(i) => ExprKind::UpdateIndex(a, i, val),
              Lens::Slice(i, l) => ExprKind::UpdateSlice(a, i, l, val),
              Lens::Proj(i) => ExprKind::UpdateProj(a, i, val),
            })
          }
          val
        } else {
          intern!(self, ExprKind::Var(v))
        };
        self.dc.gen_vars.insert(v, (newgen, val, ty)); // FIXME: ty is not correct here
        let e = hir::ExprKind::Assign {
          lhs: Box::new(lhs),
          rhs: Box::new(rhs),
          oldmap: Box::new([(v, old)]),
          gen: newgen
        };
        ret![e, Some(self.common.e_unit), self.common.t_unit]
      }

      ast::ExprKind::Call {f: Spanned {span, k: f}, tys, args, variant} => {
        let tys = tys.iter().map(|ty| self.lower_ty(ty, ExpectTy::Any)).collect::<Vec<_>>();
        let tys = self.alloc.alloc_slice_fill_iter(tys.into_iter());
        let f_ty = let_unchecked!(Some(Entity::Proc(ty)) = self.names.get(f),
          unwrap_unchecked!(ty.k.ty()));
        todo!()
      }

      ast::ExprKind::Entail(pf, ps) => {
        let tgt = expect.to_ty().unwrap_or_else(|| self.new_ty_mvar(span));
        let mut is_copy = tgt.is_copy();
        let mut tys = Vec::with_capacity(ps.len());
        let ps = ps.iter().map(|p| {
          let (p, _, ty) = self.lower_expr(p, ExpectExpr::Any);
          is_copy &= ty.is_copy();
          tys.push(ty);
          p
        }).collect::<Vec<_>>();
        let pr = if ps.is_empty() {
          return (self.elab_proof(span, tgt, pf), Some(self.common.e_unit), tgt)
        } else if is_copy {
          let from = intern!(self, TyKind::And(self.alloc.alloc_slice_fill_iter(tys.into_iter())));
          let ty = intern!(self, TyKind::Imp(from, tgt));
          let e = Box::new(hir::Spanned {span, k: hir::ExprKind::List(ps, from)});
          let ck = hir::CastKind::Subtype(Some(Box::new(self.elab_proof(span, ty, pf))));
          hir::ExprKind::Cast(e, from, tgt, ck)
        } else {
          let from = intern!(self, TyKind::List(self.alloc.alloc_slice_fill_iter(tys.into_iter())));
          let ty = intern!(self, TyKind::Wand(from, tgt));
          let e = Box::new(hir::Spanned {span, k: hir::ExprKind::List(ps, from)});
          let ck = hir::CastKind::Wand(self.common.e_unit, Some(Box::new(self.elab_proof(span, ty, pf))));
          hir::ExprKind::Cast(e, from, tgt, ck)
        };
        ret![pr, Some(self.common.e_unit), tgt]
      }

      ast::ExprKind::Block(bl) => {
        let (bl, (pe, ty)) = self.lower_block(span, bl, expect);
        ret![Block(bl), pe, ty]
      }

      &ast::ExprKind::If {hyp, ref cond, ref then, ref els} => {
        let (cond, pe) = self.check_expr(cond, self.common.t_bool);
        let tgt = expect.to_ty().unwrap_or_else(|| self.new_ty_mvar(span));
        let (dc1, dc2, e1, e2);
        let mut base = self.dc.clone();
        if let Some(v) = hyp {
          let pe = self.as_pure(cond.span, pe);
          let ty = intern!(self, TyKind::Pure(pe));
          let ctx1 = self.new_context_next(v, Some(self.common.e_unit), ty);
          self.dc.context = ctx1.into();
          e1 = self.check_expr(then, tgt);
          dc1 = mem::replace(&mut self.dc, base.clone());
          let ty = intern!(self, TyKind::Pure(intern!(self, ExprKind::Unop(Unop::Not, pe))));
          let ctx2 = self.new_context_next(v, Some(self.common.e_unit), ty);
          self.dc.context = ctx2.into();
          e2 = self.check_expr(els, tgt);
          dc2 = mem::replace(&mut self.dc, base);
        } else {
          e1 = self.check_expr(then, tgt);
          dc1 = mem::replace(&mut self.dc, base.clone());
          e2 = self.check_expr(els, tgt);
          dc2 = mem::replace(&mut self.dc, base);
        }
        let mut branches = [(dc1, vec![]), (dc2, vec![])];
        self.merge(span, &mut branches);
        let [(_, vec1), (_, vec2)] = branches;
        let ((then, p_then), (els, p_els)) = (e1, e2);
        let cases = Box::new([(then, vec1.into()), (els, vec2.into())]);
        ret![If {hyp, cond: Box::new(cond), cases, gen: self.dc.generation},
          pe.and_then(|cond| Some(intern!(self, ExprKind::If {cond, then: p_then?, els: p_els?}))),
          tgt]
    }

      &ast::ExprKind::While {label, hyp, ref cond, ref muts, ref var, ref body} => {
        if !muts.is_empty() {
          let newgen = self.new_generation();
          for &v in &**muts {
            let e = intern!(self, ExprKind::Var(v));
            let ty = self.dc.get_var(v).2;
            self.dc.gen_vars.insert(v, (newgen, e, ty));
          }
        }
        let variant = self.check_variant(var.as_deref());
        let mut base = self.dc.clone();
        self.labels.insert(label, LabelData {
          labels: Box::new([hir::Label { args: &[], variant, body: Default::default() }]),
          value: AgreeExpr::Set(None),
          ret: self.common.t_unit,
        });
        let (cond, pe) = self.check_expr(cond, self.common.t_bool);
        let mut split = self.dc.clone();
        let (body, ctx2) = if let Some(v) = hyp {
          let pe = self.as_pure(cond.span, pe);
          let ty = intern!(self, TyKind::Pure(pe));
          let ctx1 = self.new_context_next(v, Some(self.common.e_unit), ty);
          self.dc.context = ctx1.into();
          let body = Box::new(self.check_block(span, body, self.common.t_unit).0);
          let ty = intern!(self, TyKind::Pure(intern!(self, ExprKind::Unop(Unop::Not, pe))));
          (body, self.new_context_next(v, Some(self.common.e_unit), ty).into())
        } else {
          (Box::new(self.check_block(span, body, self.common.t_unit).0), self.dc.context)
        };

        // TODO: remove this when the typechecker is complete, this isn't needed for inference
        let missing = || self.dc.gen_vars.iter()
          .filter(|&(v, &(gen, _, _))| {
            base.gen_vars.get(v).map_or(true, |&(gen2, _, _)| gen != gen2) &&
            !muts.contains(v)
          });
        if missing().next().is_some() {
          error!(span, MissingMuts(missing().map(|(&v, _)| v).collect()))
        }

        self.dc.context = ctx2;
        let hir::Label {variant, ..} =
          self.labels.remove(&label).expect("labels should be well scoped")
            .labels.into_vec().into_iter().next().expect("while label");
        ret![While {label, hyp, cond: Box::new(cond), var: variant, body},
          Some(self.common.e_unit), self.common.t_unit]
      }

      ast::ExprKind::Unreachable(h) => {
        let tgt = expect.to_ty().unwrap_or(self.common.t_false);
        let (h, _) = self.check_expr(h, self.common.t_false);
        ret![Unreachable(Box::new(h)), Some(self.common.e_unit), tgt]
      }

      &ast::ExprKind::Jump(lab, i, ref args, ref pf) => {
        let hir::Label {args: tgt, variant, ..} = self.labels[&lab].labels[i as usize];
        let num_args = tgt.iter().filter(|&arg| matches!(arg.k, ArgKind::Lam(_))).count();
        if args.len() != num_args { error!(span, NumArgs(num_args, args.len())) }
        let (args, _, subst) = self.check_args(span, args, tgt);
        let variant = self.check_variant_use(subst, pf.as_deref(), variant);
        let tgt = expect.to_ty().unwrap_or(self.common.t_false);
        ret![Jump(lab, i, args, variant), Some(self.common.e_unit), tgt]
      }

      ast::ExprKind::Break(lab, e) => {
        let ty = self.labels[lab].ret;
        let tgt = expect.to_ty().unwrap_or(self.common.t_false);
        let (e, pe) = self.check_expr(e, ty);
        let old_pe = &mut self.labels.get_mut(lab).expect("well formed").value;
        match *old_pe {
          AgreeExpr::Unset => *old_pe = AgreeExpr::Set(pe),
          AgreeExpr::Set(Some(pe_1)) => match pe {
            Some(pe) if self.equate_expr(pe_1, pe).is_ok() => {}
            _ => self.labels.get_mut(lab).expect("well formed").value = AgreeExpr::Set(None),
          },
          AgreeExpr::Set(None) => {}
        }
        ret![Break(*lab, Box::new(e)), Some(self.common.e_unit), tgt]
      }

      ast::ExprKind::Return(args) => {
        if let Some(tys) = self.returns {
          let num_args = tys.iter().filter(|&arg| matches!(arg.k, ArgKind::Lam(_))).count();
          if args.len() != num_args { error!(span, NumArgs(num_args, args.len())) }
          let (args, _, _) = self.check_args(span, args, tys);
          let tgt = expect.to_ty().unwrap_or(self.common.t_false);
          ret![Return(args), Some(self.common.e_unit), tgt]
        } else {
          error!(span, InvalidReturn)
        }
      }

      &ast::ExprKind::Infer(user) => if let ExpectExpr::Sn(pe, ty) = expect {
        if let Some(e) = self.eval_expr(span, pe, ty) {
          (e, Some(pe), ty)
        } else {
          error!(span, UnsupportedSynthesis(Box::new(self.dc.clone()), pe, ty))
        }
      } else {
        error!(span, Hole(Box::new(self.dc.clone()), expect.to_ty()))
      },

      ast::ExprKind::Rc(e) => self.lower_expr(e, expect),

      ast::ExprKind::Error => error!(),
    }
  }

  fn elab_proof(&mut self, base: &'a FileSpan, ty: Ty<'a>, pf: &'a LispVal) -> hir::Expr<'a> {
    let span = try_get_fspan(base, pf);
    hir::Spanned {span: self.alloc.alloc(span), k: hir::ExprKind::Proof(hir::Proof::Mm0(pf, ty))}
  }

  fn eval_expr(&mut self, span: &'a FileSpan, e: Expr<'a>, ty: Ty<'a>) -> Option<hir::Expr<'a>> {
    macro_rules! error {($($es:expr),*) => {{
      $({
        use TypeError::*; let k = $es;
        self.errors.push(hir::Spanned {span, k});
      })*
      return Some(hir::Spanned {span, k: hir::ExprKind::Error})
    }}}
    Some(hir::Spanned {span, k: match e.k {
      ExprKind::Unit => hir::ExprKind::Unit,
      ExprKind::Var(v) => hir::ExprKind::Var(v, self.dc.get_var(v).0),
      ExprKind::Const(c) => hir::ExprKind::Const(c),
      ExprKind::Bool(b) => hir::ExprKind::Bool(b),
      ExprKind::Int(n) => hir::ExprKind::Int(n),
      ExprKind::Unop(op, e) => {
        let ty = op.arg_ty(self);
        hir::ExprKind::Unop(op, Box::new(self.eval_expr(span, e, ty)?))
      }
      ExprKind::Binop(op, e1, e2) => {
        let ty = if op.int_in() {self.common.int()} else {self.common.t_bool};
        let e1 = Box::new(self.eval_expr(span, e1, ty)?);
        let e2 = Box::new(self.eval_expr(span, e2, ty)?);
        hir::ExprKind::Binop(op, e1, e2)
      }
      ExprKind::As(e, AsKind::Mod(ity)) => {
        let e = Box::new(self.eval_expr(span, e, self.common.int())?);
        hir::ExprKind::As(e, self.common.int(), self.common.int_ty(ity), AsKind::Mod(ity))
      }
      ExprKind::Sizeof(ty) => {
        let e2 = self.whnf_expr(e, ty);
        if e != e2 { return self.eval_expr(span, e2, ty) }
        hir::ExprKind::Sizeof(ty)
      }
      ExprKind::If {cond, then, els} => hir::ExprKind::If {
        hyp: None,
        cond: Box::new(self.eval_expr(span, cond, self.common.t_bool)?),
        cases: Box::new([
          (self.eval_expr(span, then, ty)?, [].into()),
          (self.eval_expr(span, els, ty)?, [].into()),
        ]),
        gen: self.dc.generation,
      },
      ExprKind::Index(_, _) |
      ExprKind::Slice(_, _, _) |
      ExprKind::Proj(_, _) |
      ExprKind::UpdateIndex(_, _, _) |
      ExprKind::UpdateSlice(_, _, _, _) |
      ExprKind::UpdateProj(_, _, _) |
      ExprKind::List(_) |
      ExprKind::Array(_) |
      ExprKind::Mm0(_) |
      ExprKind::Call {..} |
      ExprKind::Infer(_) => return None,
      ExprKind::Error => error!(),
    }})
  }

  fn lower_expr(&mut self,
    Spanned {span, k}: &'a ast::Expr, expect: ExpectExpr<'a>
  ) -> (hir::Expr<'a>, Option<Expr<'a>>, Ty<'a>) {
    self.lower_expr_kind(span, k, expect)
  }

  fn coerce_expr(&mut self, mut e: hir::Expr<'a>, from: Ty<'a>, to: Ty<'a>) -> hir::Expr<'a> {
    if let Some(coe) = self.relate_ty(e.span, from, to, Relation::Coerce) {
      for c in coe { e = self.apply_coe_expr(c, e) }
    }
    e
  }

  fn check_expr(&mut self, e: &'a ast::Expr, tgt: Ty<'a>) -> (hir::Expr<'a>, Option<Expr<'a>>) {
    let (mut e, pe, ty) = self.lower_expr(e, ExpectExpr::HasTy(tgt));
    (self.coerce_expr(e, ty, tgt), pe)
  }

  fn check_args(&mut self,
    sp: &'a FileSpan, es: &'a [ast::Expr], tgt: &'a [Arg<'a>]
  ) -> (Vec<hir::Expr<'a>>, Option<Vec<Expr<'a>>>, Subst<'a>) {
    debug_assert!(es.len() == tgt.iter().filter(|&a| matches!(a.k, ArgKind::Lam(_))).count());
    let mut es_out = Vec::with_capacity(es.len());
    let mut pes = Some(vec![]);
    let mut es_it = es.iter();
    let mut subst = Subst::default();
    for &arg in tgt {
      match arg.k {
        ArgKind::Lam(arg) => {
          let e = es_it.next().expect("checked");
          let ty = subst.subst_ty(self, &e.span, arg.k.ty());
          let (e, pe) = self.check_expr(e, ty);
          let pr = pe.ok_or(e.span);
          if let Some(ref mut vec) = pes {
            if let Some(pe) = pe { vec.push(pe) }
            else { pes = None }
          }
          subst.push_tuple_pattern(self, arg, pr);
          es_out.push(e);
        }
        ArgKind::Let(arg, e) => {
          let e = subst.subst_expr(self, sp, e);
          subst.push_tuple_pattern_raw(self, arg, Ok(e))
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
    mut subst: Subst<'a>, variant: Option<&'a ast::Expr>, tgt: Option<hir::Variant<'a>>,
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

  fn as_pure(&mut self, span: &'a FileSpan, pe: Option<Expr<'a>>) -> Expr<'a> {
    pe.unwrap_or_else(|| {
      self.errors.push(hir::Spanned {span, k: TypeError::ExpectedPure});
      self.common.e_error
    })
  }

  fn lower_stmt(&mut self, Spanned {span, k: stmt}: &'a ast::Stmt, tgt: Ty<'a>) -> UnelabStmt<'a> {
    match stmt {
      ast::StmtKind::Let {lhs, rhs} => {
        let mut ctx = self.dc.context;
        let lhs = self.lower_tuple_pattern(&lhs.span, &lhs.k, None, None).0;
        mem::swap(&mut ctx, &mut self.dc.context);
        let (rhs, _) = self.check_expr(rhs, lhs.ty());
        self.dc.context = ctx;
        UnelabStmt::Let {lhs, rhs}
      }
      ast::StmtKind::Expr(e) => UnelabStmt::Expr(
        self.lower_expr_kind(span, e, ExpectExpr::Any).0.k),
      &ast::StmtKind::Label(v, ref labs) => {
        let mut todo = Vec::with_capacity(labs.len());
        let labs2 = labs.iter().map(|ast::Label {args, variant, body}| {
          let args = args.iter().map(|arg| self.lower_arg(&arg.span, &arg.k.1)).collect::<Vec<_>>();
          let variant = self.lower_variant(variant);
          todo.push((self.dc.context, body));
          let args = self.finish_args(args);
          hir::Label {args, variant, body: Default::default()}
        }).collect::<Box<[_]>>();
        let data = LabelData {labels: labs2, value: AgreeExpr::Unset, ret: tgt};
        assert!(self.labels.insert(v, data).is_none());
        UnelabStmt::Label(v, todo.into())
      }
    }
  }

  fn finish_stmt(&mut self,
    stmt: hir::Spanned<'a, UnelabStmt<'a>>,
    tgt: &mut ExprTy<'a>
  ) -> hir::Stmt<'a> {
    stmt.map_into(|stmt| match stmt {
      UnelabStmt::Let {lhs, rhs} => {
        let lhs = self.finish_tuple_pattern(&lhs);
        hir::StmtKind::Let {lhs, rhs}
      }
      UnelabStmt::Expr(e) => hir::StmtKind::Expr(e),
      UnelabStmt::Label(v, labs) => {
        let blocks = labs.into_vec().into_iter().map(|(ctx, bl)| {
          self.dc.context = ctx;
          let (bl, pe2) = self.check_block(&bl.span, &bl.k, tgt.1);
          if !matches!((pe2, tgt.0), (Some(pe), Some(tgt)) if self.equate_expr(pe, tgt).is_ok()) {
            tgt.0 = None
          }
          bl
        }).collect::<Vec<_>>();
        let LabelData {mut labels, value, ..} = self.labels.remove(&v).expect("missing label group");
        if let AgreeExpr::Set(pe2) = value {
          if !matches!((pe2, tgt.0), (Some(pe), Some(tgt)) if self.equate_expr(pe, tgt).is_ok()) {
            tgt.0 = None
          }
        }
        for (bl, lab) in blocks.into_iter().zip(labels.iter_mut()) { lab.body = bl }
        hir::StmtKind::Label(v, labels)
      }
    })
  }

  fn lower_block(&mut self, sp: &'a FileSpan,
    ast::Block {stmts, expr}: &'a ast::Block,
    expect: ExpectExpr<'a>
  ) -> (hir::Block<'a>, ExprTy<'a>) {
    let ty = expect.to_ty().unwrap_or_else(|| {
      if expr.is_some() { self.new_ty_mvar(sp) } else { self.common.t_unit }
    });
    let stmts = stmts.iter().map(|stmt| stmt.map_hir(|_| self.lower_stmt(stmt, ty))).collect::<Vec<_>>();
    let (expr, mut ety) = if let Some(e) = expr {
      let (e, pe) = self.check_expr(e, ty);
      (Some(Box::new(e)), (pe, ty))
    } else {
      (None, (None, ty))
    };
    let mut stmts = stmts.into_iter().rev().map(|stmt| self.finish_stmt(stmt, &mut ety)).collect::<Vec<_>>();
    stmts.reverse();
    (hir::Block {stmts, expr}, ety)
  }

  fn check_block(&mut self, span: &'a FileSpan, bl: &'a ast::Block, tgt: Ty<'a>) -> (hir::Block<'a>, Option<Expr<'a>>) {
    let (mut bl, (pe, ty)) = self.lower_block(span, bl, ExpectExpr::HasTy(tgt));
    if let Some(coe) = self.relate_ty(span, ty, tgt, Relation::Coerce) {
      let mut e = bl.expr.take().map_or_else(|| hir::Spanned {span, k: hir::ExprKind::Unit}, |e| *e);
      for c in coe { e = self.apply_coe_expr(c, e) }
      bl.expr = Some(Box::new(e))
    }
    (bl, pe)
  }

  fn lower_item(&mut self, Spanned {span, k: item}: &'a ast::Item) -> hir::Item<'a> {
    let item = match item {
      &ast::ItemKind::Proc {kind, ref name, tyargs, ref args, ref rets, ref variant, ref body} => {
        let name = hir::Spanned {span: &name.span, k: name.k};
        let args2 = args.iter().map(|arg| self.lower_arg(&arg.span, &arg.k.1)).collect::<Vec<_>>();
        let mut subst = Subst::default();
        let rets = rets.iter().map(|ret| UnelabArg::Lam(match ret {
          ast::Ret::Reg(pat) => self.lower_tuple_pattern(&pat.span, &pat.k, None, None).0,
          &ast::Ret::Out(g, i, n, v, ref ty) => {
            let i = u32_as_usize(i);
            let span = &args[i].span;
            let ty = if let Some(ty) = ty {
              self.lower_ty(ty, ExpectTy::Any)
            } else {
              subst.subst_ty(self, span, args2[i].var().ty())
            };
            let ctx = self.new_context_next(v, None, ty);
            self.dc.context = ctx.into();
            UnelabTupPat { span, k: UnelabTupPatKind::Name(g, n, ctx) }
          }
        })).collect();
        let rets = self.finish_args(rets);
        let ctx = self.dc.context;
        let variant = self.lower_variant(variant);
        let args = self.finish_args(args2);
        self.dc.context = ctx;
        let sigma =
          if let [arg] = *args { arg.k.var().k.ty() }
          else { intern!(self, TyKind::Struct(args)) };
        let mut body = self.check_block(span, body, sigma).0;
        let e = body.expr.take().map_or_else(|| hir::Spanned {span, k: hir::ExprKind::Unit}, |e| *e);
        body.expr = Some(Box::new(if args.len() == 1 {
          hir::Spanned {span, k: hir::ExprKind::Return(vec![e])}
        } else if let hir::Spanned {span, k: hir::ExprKind::List(es, _)} = e {
          hir::Spanned {span, k: hir::ExprKind::Return(es)}
        } else {
          hir::Spanned {span, k: hir::ExprKind::UnpackReturn(Box::new(e))}
        }));
        hir::ItemKind::Proc {kind, name, tyargs, args, rets, variant, body}
      }
      ast::ItemKind::Global {lhs, rhs} => {
        let mut ctx = self.dc.context;
        let lhs = self.lower_tuple_pattern(&lhs.span, &lhs.k, None, None).0;
        self.dc.context = ctx;
        let (rhs, _) = self.check_expr(rhs, lhs.ty());
        let lhs = self.finish_tuple_pattern_inner(&lhs).0;
        hir::ItemKind::Global {lhs, rhs}
      }
      ast::ItemKind::Const {lhs, rhs} => {
        let mut ctx = self.dc.context;
        let lhs = self.lower_tuple_pattern(&lhs.span, &lhs.k, None, None).0;
        self.dc.context = ctx;
        let rhs = self.check_pure_expr(rhs, lhs.ty());
        let lhs = self.finish_tuple_pattern_inner(&lhs).0;
        hir::ItemKind::Const {lhs, rhs}
      }
      &ast::ItemKind::Typedef {ref name, tyargs, ref args, ref val} => {
        let name = hir::Spanned {span: &name.span, k: name.k};
        let args2 = args.iter().map(|arg| self.lower_arg(&arg.span, &arg.k.1)).collect::<Vec<_>>();
        let val = self.lower_ty(val, ExpectTy::Any);
        let args = self.finish_args(args2);
        hir::ItemKind::Typedef {name, tyargs, args, val}
      }
    };
    hir::Spanned {span, k: item}
  }
}