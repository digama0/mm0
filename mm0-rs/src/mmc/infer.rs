//! Type inference and elaboration
#![allow(unused)]
#![allow(clippy::unused_self)]

use std::{borrow::Borrow, fmt::Debug, hash::{Hash, Hasher}};
use std::result::Result as StdResult;
use std::convert::TryInto;
use bumpalo::Bump;
use hashbrown::{HashMap, hash_map::RawEntryMut};
use hir::{Context, ContextNext};
use super::{types::{Size, Spanned, VarId}, union_find::{UnifyCtx, UnifyKey, UnificationTable}};
use crate::elab::{environment::AtomId, lisp::print::FormatEnv};
use crate::util::FileSpan;
use super::types::{ast, hir::{self, GenId}};
use super::types::entity::Entity;
#[allow(clippy::wildcard_imports)] use super::types::ty::*;

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
  props: PropKind,
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

// #[derive(Debug)]
// enum Task {
// }

// impl Task {
//   fn trigger(&mut self) -> bool {
//     match *self {
//     }
//   }
//   fn run(&mut self) {
//     match *self {
//     }
//   }
// }

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
}

#[derive(Debug)]
enum TypeError<'a> {
  /// Failed to pattern match type T with the given pattern of type U
  PatternMatch(&'a FileSpan, Ty<'a>, Ty<'a>),
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
  /// The interner, which is used to deduplicate types and terms that are
  /// constructed multiple times.
  interner: Interner<'a>,
  // tasks: Vec<Task>,
  /// The assignments for type metavariables.
  ty_mvars: Assignments<'a, TyMVarId, Ty<'a>>,
  /// The assignments for proposition metavariables.
  prop_mvars: Assignments<'a, PropMVarId, Prop<'a>>,
  /// The assignments for pure expression metavariables.
  expr_mvars: Assignments<'a, ExprMVarId, Expr<'a>>,
  /// The assignments for lifetime metavariables.
  lft_mvars: Assignments<'a, LftMVarId, Lifetime>,
  /// Some pre-interned types.
  common: Common<'a>,
  /// The number of type variables in the current declaration.
  tyargs: u32,
  /// A vector indexed by `GenId`, which maps each generation to its parent.
  /// The first two entries are reserved for `GenId::LATEST` and `GenId::ROOT`,
  /// which are considered their own parents.
  generations: Vec<GenId>,
  /// The current generation.
  generation: GenId,
  /// The current context.
  context: Context<'a>,
  /// The list of type errors collected so far.
  /// We delay outputting these so that we can report many errors at once,
  /// as well as waiting for all variables to be as unified as possible so that
  /// the error messages are as precise as possible.
  errors: Vec<TypeError<'a>>,
}

/// A relation between types, used as an argument to [`InferCtx::relate_ty`].
#[derive(Copy, Clone)]
enum Relation {
  /// Unify types `A` and `B` exactly.
  Equal,
  /// Enforce that rvalues of type `A` can be converted to type `B`,
  /// possibly via a non-identity function.
  Coerce,
  /// Enforce that rvalues of type `A` are also of type `B`.
  Subtype,
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

/// An expectation for a proposition, used to communicate top-down typing information.
#[derive(Copy, Clone)]
enum ExpectProp<'a> {
  /// No constraint.
  Any,
  /// We are expecting some `A` such that `R(A, B)`, where `B` is stored here.
  Relate(Relation, Prop<'a>),
  /// We are expecting some `B` such that `R(A, B)`, where `A` is stored here.
  RelateRev(Relation, Prop<'a>),
}

impl<'a> ExpectProp<'a> {
  fn exactly(tgt: Option<Prop<'a>>) -> Self {
    tgt.map_or(Self::Any, |p| Self::Relate(Relation::Equal, p))
  }
  fn subtype(tgt: Option<Prop<'a>>) -> Self {
    tgt.map_or(Self::Any, |p| Self::Relate(Relation::Subtype, p))
  }
  fn supertype(tgt: Option<Prop<'a>>) -> Self {
    tgt.map_or(Self::Any, |p| Self::RelateRev(Relation::Subtype, p))
  }
  fn coerce_to(tgt: Option<Prop<'a>>) -> Self {
    tgt.map_or(Self::Any, |p| Self::Relate(Relation::Coerce, p))
  }
  fn coerce_from(tgt: Option<Prop<'a>>) -> Self {
    tgt.map_or(Self::Any, |p| Self::RelateRev(Relation::Coerce, p))
  }

  fn to_prop(self) -> Option<Prop<'a>> {
    match self {
      ExpectProp::Any => None,
      ExpectProp::Relate(_, p) |
      ExpectProp::RelateRev(_, p) => Some(p),
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
}

impl<'a> ExpectExpr<'a> {
  fn has_ty(ty: Option<Ty<'a>>) -> Self { ty.map_or(Self::Any, Self::HasTy) }
}

/// The result of a tuple pattern analysis, see [`InferCtx::tuple_pattern_tuple`].
#[derive(Copy, Clone)]
enum TuplePatternResult<'a> {
  /// This type cannot be destructured, or the wrong number of arguments were provided.
  Fail,
  /// There is not enough information in the type to determine what kind of
  /// destructuring is needed.
  Indeterminate,
  /// This is a nondependent list of length matching the pattern list.
  List(&'a [Ty<'a>]),
}

/// Some common types and expressions.
#[derive(Debug)]
struct Common<'a> {
  unit: Ty<'a>,
  bool: Ty<'a>,
  nat: Ty<'a>,
  error_ty: Ty<'a>,
  error_expr: Expr<'a>,
}

impl<'a> Common<'a> {
  fn new(i: &mut Interner<'a>, alloc: &'a Bump) -> Self {
    Self {
      unit: i.intern(alloc, TyKind::Unit),
      bool: i.intern(alloc, TyKind::Bool),
      nat: i.intern(alloc, TyKind::UInt(Size::Inf)),
      error_ty: i.intern(alloc, TyKind::Error),
      error_expr: i.intern(alloc, ExprKind::Error),
    }
  }
}

impl<'a> InferCtx<'a> {
  /// Create a new `InferCtx` from the given allocator.
  pub fn new(
    fe: FormatEnv<'a>,
    alloc: &'a Bump,
    names: &'a HashMap<AtomId, Entity>
  ) -> Self {
    let mut interner = Default::default();
    let common = Common::new(&mut interner, alloc);
    Self {
      fe,
      alloc,
      names,
      interner,
      common,
      // tasks: vec![],
      ty_mvars: Default::default(),
      prop_mvars: Default::default(),
      expr_mvars: Default::default(),
      lft_mvars: Default::default(),
      tyargs: 0,
      generations: vec![GenId::LATEST, GenId::ROOT],
      generation: GenId::ROOT,
      context: Context::ROOT,
      errors: vec![],
    }
  }

  fn new_generation(&mut self, parent: GenId) -> GenId {
    let n = self.generations.len().try_into().expect("overflow");
    self.generations.push(parent);
    GenId(n)
  }

  fn intern<T: Internable<'a>>(&mut self, t: T) -> &'a WithMeta<T> {
    self.interner.intern(self.alloc, t)
  }

  fn new_ty_mvar(&mut self, span: &'a FileSpan) -> Ty<'a> {
    let n = self.ty_mvars.new_mvar(span, self.context);
    self.intern(TyKind::Infer(n))
  }

  fn new_prop_mvar(&mut self, span: &'a FileSpan) -> Prop<'a> {
    let n = self.prop_mvars.new_mvar(span, self.context);
    self.intern(PropKind::Infer(n))
  }

  fn new_expr_mvar(&mut self, span: &'a FileSpan) -> Expr<'a> {
    let n = self.expr_mvars.new_mvar(span, self.context);
    self.intern(ExprKind::Infer(n))
  }

  fn new_lft_mvar(&mut self, span: &'a FileSpan) -> Lifetime {
    let n = self.lft_mvars.new_mvar(span, self.context);
    Lifetime::Infer(n)
  }

  fn new_context_next(&self, var: VarId, ty: Ty<'a>) -> &'a ContextNext<'a> {
    self.alloc.alloc(ContextNext::new(self.context, var, self.generation, ty))
  }

  fn relate_ty(&self, from: Ty<'a>, to: Ty<'a>, rel: Relation) -> Option<Vec<Coercion<'a>>> {
    todo!()
  }

  fn subst_ty(&self, ty: Ty<'a>, subst: &HashMap<VarId, Expr<'a>>) -> Ty<'a> {
    if subst.is_empty() { ty } else { self.subst_ty_inner(ty, subst) }
  }

  fn subst_ty_inner(&self, ty: Ty<'a>, subst: &HashMap<VarId, Expr<'a>>) -> Ty<'a> {
    todo!()
  }

  fn lower_tuple_pattern(&mut self, span: &'a FileSpan,
    pat: &'a ast::TuplePatternKind, expect: Option<Ty<'a>>
  ) -> hir::TuplePattern<'a> {
    match pat {
      &ast::TuplePatternKind::Name(g, v) => {
        let ty = expect.unwrap_or_else(|| self.new_ty_mvar(span));
        let ctx = self.new_context_next(v, ty);
        self.context = ctx.into();
        hir::TuplePattern {span, k: hir::TuplePatternKind::Name(g, ctx)}
      }
      ast::TuplePatternKind::Typed(pat, ty) => {
        let ty = self.lower_ty(ty, ExpectTy::coerce_from(expect));
        let pat = self.lower_tuple_pattern(&pat.span, &pat.k, Some(ty));
        if let Some(tgt) = expect {
          if let Some(coe) = self.relate_ty(tgt, ty, Relation::Coerce) {
            let coe = self.alloc.alloc_slice_copy(&coe);
            let k = hir::TuplePatternKind::Coercion(Box::new(pat), coe, tgt);
            return hir::TuplePattern {span, k}
          }
        }
        pat
      }
      ast::TuplePatternKind::Tuple(pats) => {
        let ty = expect.unwrap_or_else(|| self.new_ty_mvar(span));
        let res = self.tuple_pattern_tuple(pats.len(), ty);
        self.lower_tuple_pattern_tuple_result(span, pats, res, ty)
      }
    }
  }

  fn tuple_pattern_tuple(&mut self, nargs: usize, expect: Ty<'a>) -> TuplePatternResult<'a> {
    todo!()
  }

  fn lower_tuple_pattern_tuple_result(&mut self, span: &'a FileSpan,
    pats: &'a [(VarId, ast::TuplePattern)],
    res: TuplePatternResult<'a>, tgt: Ty<'a>
  ) -> hir::TuplePattern<'a> {
    let k = match res {
      TuplePatternResult::Indeterminate => {
        let pats = self.lower_tuple_pattern_tuple_with(pats, |_| None);
        hir::TuplePatternKind::UnelaboratedTuple(pats, tgt)
      }
      TuplePatternResult::Fail => {
        let pats = self.lower_tuple_pattern_tuple_with(pats, |_| None);
        let tys = self.alloc.alloc_slice_fill_iter(pats.iter().map(hir::TuplePattern::ty));
        let ty = self.intern(TyKind::List(tys));
        let pat = hir::TuplePattern {span, k: hir::TuplePatternKind::Tuple(pats, ty)};
        self.errors.push(TypeError::PatternMatch(span, tgt, ty));
        hir::TuplePatternKind::Coercion(Box::new(pat), &[Coercion::Error], tgt)
      }
      TuplePatternResult::List(tys) => {
        let mut it = tys.iter();
        let pats = self.lower_tuple_pattern_tuple_with(pats, |_| it.next().copied());
        hir::TuplePatternKind::Tuple(pats, tgt)
      }
    };
    hir::TuplePattern {span, k}
  }

  fn lower_tuple_pattern_tuple_with(&mut self,
    pats: &'a [(VarId, ast::TuplePattern)],
    mut f: impl FnMut(&mut Self) -> Option<Ty<'a>>
  ) -> &'a [hir::TuplePattern<'a>] {
    let pats = pats.iter().map(|&(v, Spanned {ref span, k: ref pat})| {
      let expect = f(self);
      self.lower_tuple_pattern(span, pat, expect)
    }).collect::<Vec<_>>();
    self.alloc.alloc_slice_fill_iter(pats.into_iter())
  }

  fn finish_tuple_pattern(&mut self, pat: &hir::TuplePattern<'a>) -> TuplePattern<'a> {
    let k = match pat.k {
      hir::TuplePatternKind::Name(_, &ContextNext {var, ty, parent, ..}) => {
        self.context = parent;
        TuplePatternKind::Name(var, ty)
      }
      hir::TuplePatternKind::Coercion(ref pat, coe, ty) =>
        TuplePatternKind::Coercion(self.finish_tuple_pattern(pat), coe, ty),
      hir::TuplePatternKind::Tuple(pats, tgt) => {
        let pats = pats.iter().rev().map(|pat| self.finish_tuple_pattern(pat)).collect::<Vec<_>>();
        let pats = self.alloc.alloc_slice_fill_iter(pats.into_iter().rev());
        TuplePatternKind::Tuple(pats, tgt)
      }
      hir::TuplePatternKind::UnelaboratedTuple(pats, tgt) => {
        let mut res = self.tuple_pattern_tuple(pats.len(), tgt);
        if let TuplePatternResult::Indeterminate = res {
          let tys = self.alloc.alloc_slice_fill_iter(pats.iter().map(hir::TuplePattern::ty));
          res = TuplePatternResult::List(tys)
        }
        let ty = match res {
          TuplePatternResult::Fail => {
            let tys = self.alloc.alloc_slice_fill_iter(pats.iter().map(hir::TuplePattern::ty));
            self.intern(TyKind::List(tys))
          }
          TuplePatternResult::Indeterminate => unreachable!(),
          TuplePatternResult::List(tys) => self.intern(TyKind::List(tys)),
        };
        let coe = self.relate_ty(tgt, ty, Relation::Coerce);
        let pats = pats.iter().rev().map(|pat| self.finish_tuple_pattern(pat)).collect::<Vec<_>>();
        let pats = self.alloc.alloc_slice_fill_iter(pats.into_iter().rev());
        let pat = TuplePatternKind::Tuple(pats, ty);
        if let Some(coe) = coe {
          let coe = self.alloc.alloc_slice_copy(&coe);
          TuplePatternKind::Coercion(self.intern(pat), coe, tgt)
        } else {
          pat
        }
      }
    };
    self.intern(k)
  }

  fn lower_pattern(&mut self, pat: &'a ast::Pattern, tgt: Ty<'a>) -> Pattern<'a> {
    todo!()
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
      ast::TypeKind::Unit => self.common.unit,
      ast::TypeKind::Bool => self.common.bool,
      &ast::TypeKind::Var(v) => self.intern(TyKind::Var(v)),
      &ast::TypeKind::Int(sz) => self.intern(TyKind::Int(sz)),
      &ast::TypeKind::UInt(sz) => self.intern(TyKind::UInt(sz)),
      ast::TypeKind::Array(ty, n) => {
        let ty = self.lower_ty(ty, ExpectTy::Any);
        let (n, _) = self.lower_pure_expr(n, ExpectExpr::HasTy(self.common.nat));
        self.intern(TyKind::Array(ty, n))
      }
      ast::TypeKind::Own(ty) => {
        let ty = self.lower_ty(ty, ExpectTy::Any);
        self.intern(TyKind::Own(ty))
      }
      ast::TypeKind::Ref(lft, n) => {
        let lft = self.lower_opt_lft(&ty.span, lft);
        let ty = self.lower_ty(ty, ExpectTy::Any);
        self.intern(TyKind::Ref(lft, ty))
      }
      ast::TypeKind::Shr(lft, n) => {
        let lft = self.lower_opt_lft(&ty.span, lft);
        let ty = self.lower_ty(ty, ExpectTy::Any);
        self.intern(TyKind::Shr(lft, ty))
      }
      ast::TypeKind::RefSn(e) => {
        let (e, _) = self.lower_pure_expr(e, ExpectExpr::Any);
        self.intern(TyKind::RefSn(e))
      }
      ast::TypeKind::List(tys) => {
        let tys = self.alloc.alloc_slice_fill_iter(
          tys.iter().map(|ty| self.lower_ty(ty, ExpectTy::Any)));
        self.intern(TyKind::List(tys))
      }
      ast::TypeKind::Sn(e) => {
        let (e, ty) = self.lower_pure_expr(e, ExpectExpr::Any);
        self.intern(TyKind::Sn(e, ty))
      }
      ast::TypeKind::Struct(args) => {
        let args = args.iter().map(|arg| self.lower_arg(&arg.span, &arg.k.1)).collect::<Vec<_>>();
        let args = args.into_iter().rev().map(|arg| self.finish_arg(arg)).collect::<Vec<_>>();
        let args = self.alloc.alloc_slice_fill_iter(args.into_iter().rev());
        self.intern(TyKind::Struct(args))
      }
      ast::TypeKind::And(tys) => {
        let tys = tys.iter().map(|ty| self.lower_ty(ty, ExpectTy::Any)).collect::<Vec<_>>();
        let tys = self.alloc.alloc_slice_fill_iter(tys.into_iter());
        self.intern(TyKind::And(tys))
      }
      ast::TypeKind::Or(tys) => {
        let tys = tys.iter().map(|ty| self.lower_ty(ty, ExpectTy::Any)).collect::<Vec<_>>();
        let tys = self.alloc.alloc_slice_fill_iter(tys.into_iter());
        self.intern(TyKind::Or(tys))
      }
      ast::TypeKind::If(e, t, f) => {
        let e = self.check_pure_expr(e, self.common.bool);
        let t = self.lower_ty(t, ExpectTy::Any);
        let f = self.lower_ty(f, ExpectTy::Any);
        self.intern(TyKind::If(e, t, f))
      }
      ast::TypeKind::Match(e, brs) => {
        let (e, ety) = self.lower_pure_expr(e, ExpectExpr::Any);
        let ctx = self.context;
        let brs = brs.iter().map(|(pat, ty)| {
          let pat = self.lower_pattern(pat, ety);
          let ty = self.lower_ty(ty, expect);
          self.context = ctx;
          (pat, ty)
        }).collect::<Vec<_>>();
        let brs = self.alloc.alloc_slice_fill_iter(brs.into_iter().rev());
        self.intern(TyKind::Match(e, ety, brs))
      }
      ast::TypeKind::Ghost(ty) => {
        let ty = self.lower_ty(ty, ExpectTy::Any);
        self.intern(TyKind::Ghost(ty))
      }
      ast::TypeKind::Uninit(ty) => {
        let ty = self.lower_ty(ty, ExpectTy::Any);
        self.intern(TyKind::Uninit(ty))
      }
      ast::TypeKind::Prop(p) => {
        let ty = self.lower_ty(ty, ExpectTy::Any);
        self.intern(TyKind::Uninit(ty))
      }
      ast::TypeKind::User(f, tys, es) => {
        let tys = tys.iter().map(|ty| self.lower_ty(ty, ExpectTy::Any)).collect::<Vec<_>>();
        let tys = self.alloc.alloc_slice_fill_iter(tys.into_iter());
        let f_ty = let_unchecked!(Some(Entity::Type(ty)) = self.names.get(f),
          unwrap_unchecked!(ty.k.ty()));
        todo!()
      }
      ast::TypeKind::Input => self.intern(TyKind::Input),
      ast::TypeKind::Output => self.intern(TyKind::Output),
      ast::TypeKind::Moved(ty) => {
        let ty = self.lower_ty(ty, ExpectTy::Any);
        self.intern(TyKind::Moved(ty))
      }
      ast::TypeKind::Infer => self.new_ty_mvar(&ty.span),
      ast::TypeKind::Error => self.common.error_ty,
    }
  }

  fn subst_exprs(&mut self, e: &'a ast::Expr, ty_subst: &'a [Ty<'a>], tgt: &'a [ast::Expr]) -> Vec<Expr<'a>> {
    todo!()
  }

  fn lower_pure_expr(&mut self, e: &'a ast::Expr, expect: ExpectExpr<'a>) -> (Expr<'a>, Ty<'a>) {
    todo!()
  }

  fn apply_coe(&mut self, c: Coercion<'a>, e: Expr<'a>) -> Expr<'a> {
    match c {
      Coercion::Error => self.common.error_expr,
      Coercion::Phantom(_) => unreachable!()
    }
  }

  fn check_pure_expr(&mut self, e: &'a ast::Expr, tgt: Ty<'a>) -> Expr<'a> {
    let (mut e, ty) = self.lower_pure_expr(e, ExpectExpr::HasTy(tgt));
    if let Some(coe) = self.relate_ty(ty, tgt, Relation::Coerce) {
      for c in coe { e = self.apply_coe(c, e) }
    }
    e
  }

  fn lower_arg(&mut self, sp: &'a FileSpan, arg: &'a ast::ArgKind) -> hir::Arg<'a> {
    match arg {
      ast::ArgKind::Lam(pat) => hir::Arg::Lam(self.lower_tuple_pattern(sp, pat, None)),
      ast::ArgKind::Let(Spanned {span, k: pat}, e) => {
        let ctx1 = self.context;
        let pat = self.lower_tuple_pattern(span, pat, None);
        let ctx2 = std::mem::replace(&mut self.context, ctx1);
        let e = self.check_pure_expr(e, pat.ty());
        self.context = ctx2;
        hir::Arg::Let(pat, e)
      }
    }
  }

  fn finish_arg(&mut self, arg: hir::Arg<'a>) -> Arg<'a> {
    let arg = match arg {
      hir::Arg::Lam(pat) => ArgKind::Lam(self.finish_tuple_pattern(&pat)),
      hir::Arg::Let(pat, e) => ArgKind::Let(self.finish_tuple_pattern(&pat), e),
    };
    self.intern(arg)
  }

  fn elab_item(&mut self, a: &'a ast::Item) {
    match &a.k {
      ast::ItemKind::Proc {kind, name, tyargs, args, rets, variant, body} => {
        self.tyargs = *tyargs;
        let args2 = args.iter().map(|arg| self.lower_arg(&arg.span, &arg.k.1)).collect::<Vec<_>>();
        let subst = HashMap::new();
        let rets = rets.iter().map(|ret| match ret {
          ast::Ret::Reg(pat) => hir::Arg::Lam(self.lower_tuple_pattern(&pat.span, &pat.k, None)),
          &ast::Ret::OutAnon(g, i, v) => {
            let ty = self.subst_ty(args2[i as usize].var().ty(), &subst);
            let ctx = self.new_context_next(v, ty);
            self.context = ctx.into();
            hir::Arg::Lam(hir::TuplePattern {
              span: &args[i as usize].span,
              k: hir::TuplePatternKind::Name(g, ctx)
            })
          }
          ast::Ret::Out(_, _, _) => todo!(),
        }).collect::<Vec<_>>();
        let rets = rets.into_iter().rev().map(|arg| self.finish_arg(arg)).collect::<Vec<_>>();
        let rets = self.alloc.alloc_slice_fill_iter(rets.into_iter().rev());
        let ctx = self.context;
        let args = args2.into_iter().rev().map(|arg| self.finish_arg(arg)).collect::<Vec<_>>();
        let args = self.alloc.alloc_slice_fill_iter(args.into_iter().rev());
        if variant.is_some() { unimplemented!("recursive functions not supported yet") }
        self.context = ctx;
        todo!()
      }
      ast::ItemKind::Global { lhs, rhs } |
      ast::ItemKind::Const { lhs, rhs } => todo!(),
      ast::ItemKind::Typedef { name, tyargs, args, val } => todo!(),
    }
  }
}