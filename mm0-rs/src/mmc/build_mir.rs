//! Build the mid-level IR from HIR
#![allow(unused)]
#![allow(clippy::unused_self, clippy::match_same_arms)]

use std::borrow::{Borrow, Cow};
use std::{cell::RefCell, rc::Rc, fmt::Debug, hash::{Hash, Hasher}, mem, ops::Index};
use std::result::Result as StdResult;
use std::convert::{TryFrom, TryInto};
use std::collections::{HashMap, HashSet, hash_map::Entry};
use arrayvec::ArrayVec;
use bumpalo::Bump;
use itertools::Itertools;
use num::Signed;
use types::IntTy;
use crate::{AtomId, FileSpan, FormatEnv, LispVal, lisp::print::alphanumber, u32_as_usize};
use super::{Compiler, parser::try_get_fspan, types};
use types::{Binop, BinopType, FieldName, Mm0ExprNode, Size, Spanned, Unop,
  VarId as HVarId, hir, ty, mir};
use types::entity::{Entity, ConstTc, GlobalTc, ProcTy, ProcTc, TypeTc, TypeTy};
use hir::{Context, ContextNext, GenId};
use ty::{TuplePattern, TuplePatternKind, TupleMatchKind};
use super::union_find::{UnifyCtx, UnifyKey, UnificationTable};
#[allow(clippy::wildcard_imports)] use mir::*;

struct GenMap {
  dominator: GenId,
  value: HashMap<HVarId, VarId>,
  cache: HashMap<HVarId, VarId>,
}

type TrMap<K, V> = HashMap<K, Result<V, HashMap<GenId, V>>>;
#[derive(Default)]
struct Translator<'a> {
  tys: TrMap<ty::Ty<'a>, Ty>,
  exprs: TrMap<ty::Expr<'a>, Expr>,
  gen_vars: HashMap<GenId, GenMap>,
  next_var: VarId,
  cur_gen: GenId,
  subst: HashMap<HVarId, Expr>,
}

trait Translate<'a> {
  type Output;
  fn tr(self, _: &'_ mut Translator<'a>) -> Self::Output;
}
trait TranslateBase<'a>: Sized {
  type Output;
  fn get_mut<'b>(_: &'b mut Translator<'a>) ->
    &'b mut TrMap<&'a ty::WithMeta<Self>, Rc<Self::Output>>;
  fn make(&'a self, _: &mut Translator<'a>) -> Self::Output;
}

impl<'a> TranslateBase<'a> for ty::TyKind<'a> {
  type Output = TyKind;
  fn get_mut<'b>(t: &'b mut Translator<'a>) -> &'b mut TrMap<ty::Ty<'a>, Ty> { &mut t.tys }
  fn make(&'a self, tr: &mut Translator<'a>) -> TyKind {
    match *self {
      ty::TyKind::Unit => TyKind::Unit,
      ty::TyKind::True => TyKind::True,
      ty::TyKind::False => TyKind::False,
      ty::TyKind::Bool => TyKind::Bool,
      ty::TyKind::Var(v) => TyKind::Var(v),
      ty::TyKind::Int(ity) => TyKind::Int(ity),
      ty::TyKind::Array(ty, n) => TyKind::Array(ty.tr(tr), n.tr(tr)),
      ty::TyKind::Own(ty) => TyKind::Own(ty.tr(tr)),
      ty::TyKind::Ref(lft, ty) => TyKind::Ref(lft, ty.tr(tr)),
      ty::TyKind::RefSn(e) => TyKind::RefSn(e.tr(tr)),
      ty::TyKind::List(tys) => tr.tr_list(tys),
      ty::TyKind::Sn(a, ty) => TyKind::Sn(a.tr(tr), ty.tr(tr)),
      ty::TyKind::Struct(args) => tr.tr_struct(args),
      ty::TyKind::All(pat, ty) => tr.tr_all(pat, ty),
      ty::TyKind::Imp(p, q) => TyKind::Imp(p.tr(tr), q.tr(tr)),
      ty::TyKind::Wand(p, q) => TyKind::Wand(p.tr(tr), q.tr(tr)),
      ty::TyKind::Not(p) => TyKind::Not(p.tr(tr)),
      ty::TyKind::And(ps) => TyKind::And(ps.tr(tr)),
      ty::TyKind::Or(ps) => TyKind::Or(ps.tr(tr)),
      ty::TyKind::If(c, t, e) => TyKind::If(c.tr(tr), t.tr(tr), e.tr(tr)),
      ty::TyKind::Ghost(ty) => TyKind::Ghost(ty.tr(tr)),
      ty::TyKind::Uninit(ty) => TyKind::Uninit(ty.tr(tr)),
      ty::TyKind::Pure(e) => TyKind::Pure(e.tr(tr)),
      ty::TyKind::User(f, tys, es) => TyKind::User(f, tys.tr(tr), es.tr(tr)),
      ty::TyKind::Heap(e, v, ty) => TyKind::Heap(e.tr(tr), v.tr(tr), ty.tr(tr)),
      ty::TyKind::HasTy(e, ty) => TyKind::HasTy(e.tr(tr), ty.tr(tr)),
      ty::TyKind::Input => TyKind::Input,
      ty::TyKind::Output => TyKind::Output,
      ty::TyKind::Moved(ty) => TyKind::Moved(ty.tr(tr)),
      ty::TyKind::Infer(_) |
      ty::TyKind::Error => unreachable!(),
    }
  }
}
impl<'a> TranslateBase<'a> for ty::ExprKind<'a> {
  type Output = ExprKind;
  fn get_mut<'b>(t: &'b mut Translator<'a>) -> &'b mut TrMap<ty::Expr<'a>, Expr> { &mut t.exprs }
  fn make(&'a self, tr: &mut Translator<'a>) -> ExprKind {
    match *self {
      ty::ExprKind::Unit => ExprKind::Unit,
      ty::ExprKind::Var(v) => ExprKind::Var(v.tr(tr)),
      ty::ExprKind::Const(c) => ExprKind::Const(c),
      ty::ExprKind::Bool(b) => ExprKind::Bool(b),
      ty::ExprKind::Int(n) => ExprKind::Int(n.clone()),
      ty::ExprKind::Unop(op, e) => ExprKind::Unop(op, e.tr(tr)),
      ty::ExprKind::Binop(op, e1, e2) => ExprKind::Binop(op, e1.tr(tr), e2.tr(tr)),
      ty::ExprKind::Index(a, i) => ExprKind::Index(a.tr(tr), i.tr(tr)),
      ty::ExprKind::Slice(a, i, l) => ExprKind::Slice(a.tr(tr), i.tr(tr), l.tr(tr)),
      ty::ExprKind::Proj(a, i) => ExprKind::Proj(a.tr(tr), i),
      ty::ExprKind::UpdateIndex(a, i, v) => ExprKind::UpdateIndex(a.tr(tr), i.tr(tr), v.tr(tr)),
      ty::ExprKind::UpdateSlice(a, i, l, v) =>
        ExprKind::UpdateSlice(a.tr(tr), i.tr(tr), l.tr(tr), v.tr(tr)),
      ty::ExprKind::UpdateProj(a, i, v) => ExprKind::UpdateProj(a.tr(tr), i, v.tr(tr)),
      ty::ExprKind::List(es) => ExprKind::List(es.tr(tr)),
      ty::ExprKind::Array(es) => ExprKind::Array(es.tr(tr)),
      ty::ExprKind::Sizeof(ty) => ExprKind::Sizeof(ty.tr(tr)),
      ty::ExprKind::Ref(e) => ExprKind::Ref(e.tr(tr)),
      ty::ExprKind::Mm0(ref e) => ExprKind::Mm0(e.tr(tr)),
      ty::ExprKind::Call {f, tys, args} => ExprKind::Call {f, tys: tys.tr(tr), args: args.tr(tr)},
      ty::ExprKind::If {cond, then, els} =>
        ExprKind::If {cond: cond.tr(tr), then: then.tr(tr), els: els.tr(tr)},
      ty::ExprKind::Infer(_) |
      ty::ExprKind::Error => unreachable!(),
    }
  }
}

impl<'a, T: TranslateBase<'a>> Translate<'a> for &'a ty::WithMeta<T> {
  type Output = Rc<T::Output>;
  fn tr(self, tr: &mut Translator<'a>) -> Rc<T::Output> {
    if tr.subst.is_empty() {
      let gen = tr.cur_gen;
      if let Some(v) = T::get_mut(tr).get(self) {
        match v {
          Ok(r) => return r.clone(),
          Err(m) => if let Some(r) = m.get(&gen) { return r.clone() }
        }
      }
      let r = Rc::new(T::make(&self.k, tr));
      match T::get_mut(tr).entry(self) {
        Entry::Occupied(mut e) => match e.get_mut() {
          Ok(_) => unreachable!(),
          Err(m) => { m.insert(gen, r.clone()); }
        }
        Entry::Vacant(mut e) => {
          e.insert(if self.flags.contains(ty::Flags::HAS_VAR) {
            let mut m = HashMap::new();
            m.insert(gen, r.clone());
            Err(m)
          } else {
            Ok(r.clone())
          });
        }
      }
      r
    } else {
      Rc::new(T::make(&self.k, tr))
    }
  }
}

impl<'a, T: Translate<'a> + Copy> Translate<'a> for &'a [T] {
  type Output = Box<[T::Output]>;
  fn tr(self, tr: &mut Translator<'a>) -> Box<[T::Output]> {
    self.iter().map(|&e| e.tr(tr)).collect()
  }
}

impl<'a> Translate<'a> for ty::ExprTy<'a> {
  type Output = ExprTy;
  fn tr(self, tr: &mut Translator<'a>) -> Self::Output {
    (self.0.map(|e| e.tr(tr)), self.1.tr(tr))
  }
}

impl<'a> Translate<'a> for &'a ty::Mm0Expr<'a> {
  type Output = Mm0Expr;
  fn tr(self, tr: &mut Translator<'a>) -> Mm0Expr {
    Mm0Expr { subst: self.subst.tr(tr), expr: self.expr.clone() }
  }
}

impl<'a> Translate<'a> for HVarId {
  type Output = VarId;
  fn tr(self, tr: &mut Translator<'a>) -> VarId {
    tr.tr_var(self, tr.cur_gen)
  }
}

impl<'a> Translate<'a> for PreVar {
  type Output = VarId;
  fn tr(self, tr: &mut Translator<'a>) -> VarId {
    match self {
      PreVar::Ok(v) => v,
      PreVar::Pre(v) => v.tr(tr),
      PreVar::Fresh => tr.fresh_var(),
    }
  }
}

#[must_use] #[inline] fn fresh_var(next_var: &mut VarId) -> VarId {
  let n = *next_var;
  next_var.0 += 1;
  n
}

impl ty::TyS<'_> {
  fn is_unit_dest(&self) -> bool {
    matches!(self.k,
      ty::TyKind::Unit |
      ty::TyKind::True |
      ty::TyKind::Pure(&ty::WithMeta {k: ty::ExprKind::Bool(true), ..}) |
      ty::TyKind::Uninit(_))
  }
}

impl<'a> Translator<'a> {
  #[must_use] fn fresh_var(&mut self) -> VarId { fresh_var(&mut self.next_var) }

  fn tr_var(&mut self, v: HVarId, gen: GenId) -> VarId {
    let gm = self.gen_vars.get(&gen).expect("unknown generation");
    if let Some(&val) = gm.cache.get(&v) { return val }
    let val =
      if let Some(&val) = gm.value.get(&v) { val }
      else if gen == GenId::ROOT { fresh_var(&mut self.next_var) }
      else { let dom = gm.dominator; self.tr_var(v, dom) };
    self.gen_vars.get_mut(&gen).expect("unknown generation").cache.insert(v, val);
    val
  }

  fn tr_opt_var(&mut self, var: Option<HVarId>) -> VarId {
    if let Some(v) = var { v.tr(self) } else { self.fresh_var() }
  }

  fn add_gen(&mut self, dominator: GenId, gen: GenId, vars: &[HVarId]) {
    let value = vars.iter().map(|&v| (v, self.fresh_var())).collect();
    assert!(self.gen_vars.insert(gen,
      GenMap { dominator, value, cache: Default::default() }).is_none())
  }

  fn with_gen<R>(&mut self, mut gen: GenId, f: impl FnOnce(&mut Self) -> R) -> R {
    mem::swap(&mut self.cur_gen, &mut gen);
    let r = f(self);
    self.cur_gen = gen;
    r
  }

  fn tr_tup_pat(&mut self, pat: ty::TuplePattern<'a>, e: Expr) {
    match pat.k {
      TuplePatternKind::Name(_, v, _) => assert!(self.subst.insert(v, e).is_none()),
      TuplePatternKind::Tuple(pats, mk, _) => match mk {
        TupleMatchKind::Unit | TupleMatchKind::True => {}
        TupleMatchKind::List | TupleMatchKind::Struct =>
          for (i, &pat) in pats.iter().enumerate() {
            self.tr_tup_pat(pat,
              Rc::new(ExprKind::Proj(e.clone(), i.try_into().expect("overflow"))))
          }
        TupleMatchKind::Array =>
          for (i, &pat) in pats.iter().enumerate() {
            self.tr_tup_pat(pat,
              Rc::new(ExprKind::Index(e.clone(), Rc::new(ExprKind::Int(i.into())))))
          }
        TupleMatchKind::And => for pat in pats { self.tr_tup_pat(pat, e.clone()) }
        TupleMatchKind::Sn => {
          self.tr_tup_pat(pats[0], e);
          self.tr_tup_pat(pats[1], Rc::new(ExprKind::Unit));
        }
        TupleMatchKind::Own => panic!("existential pattern match in proof relevant position")
      }
      TuplePatternKind::Error(_, _) => unreachable!()
    }
  }
  fn finish_tup_pat(&mut self, pat: ty::TuplePattern<'a>) {
    match pat.k {
      TuplePatternKind::Name(_, v, _) => { self.subst.remove(&v); }
      TuplePatternKind::Tuple(pats, _, _) =>
        for pat in pats.iter().rev() { self.finish_tup_pat(pat) }
      TuplePatternKind::Error(_, _) => unreachable!()
    }
  }

  fn tr_all(&mut self, pat: ty::TuplePattern<'a>, ty: ty::Ty<'a>) -> TyKind {
    if let Some(v) = pat.k.var() {
      TyKind::All(v.tr(self), pat.k.ty().tr(self), ty.tr(self))
    } else {
      let v = self.fresh_var();
      let tgt = pat.k.ty().tr(self);
      self.tr_tup_pat(pat, Rc::new(ExprKind::Var(v)));
      let ty = ty.tr(self);
      self.finish_tup_pat(pat);
      TyKind::All(v, tgt, ty)
    }
  }

  fn tr_list(&mut self, tys: &'a [ty::Ty<'a>]) -> TyKind {
    TyKind::Struct(tys.iter().map(|&ty| {
      Arg {attr: ArgAttr::NONDEP, var: self.fresh_var(), ty: ty.tr(self)}
    }).collect())
  }

  fn tr_struct(&mut self, args: &'a [ty::Arg<'a>]) -> TyKind {
    let mut args2 = Vec::with_capacity(args.len());
    for &arg in args {
      match arg.k {
        (attr, ty::ArgKind::Lam(pat)) => {
          let mut attr2 = ArgAttr::empty();
          if attr.contains(ty::ArgAttr::NONDEP) { attr2 |= ArgAttr::NONDEP }
          if let Some(v) = pat.k.var() {
            args2.push(Arg {attr: attr2, var: v.tr(self), ty: pat.k.ty().tr(self)})
          } else {
            let v = self.fresh_var();
            let ty = pat.k.ty().tr(self);
            self.tr_tup_pat(pat, Rc::new(ExprKind::Var(v)));
            args2.push(Arg {attr: attr2, var: v, ty})
          }
        }
        (_, ty::ArgKind::Let(pat, e)) => {
          let e = e.tr(self);
          self.tr_tup_pat(pat, e)
        }
      }
    }
    for &arg in args {
      if !matches!(arg.k.1, ty::ArgKind::Lam(pat) if pat.k.var().is_some()) {
        self.finish_tup_pat(arg.k.1.var())
      }
    }
    TyKind::Struct(args2.into_boxed_slice())
  }
}

/// A `PreVar` is used as the destination for rvalues, because sometimes we don't know in advance
/// the generation as of the end of evaluation, when the destination variable is actually filled.
/// We need to know the generation to translate [`HVarId`] into [`VarId`]. But in some cases we
/// don't have a variable in the source and just need a fresh variable, in which case we can use
/// `Ok` or `Fresh` to create an unused fresh variable, or a variable that was generated beforehand.
#[derive(Copy, Clone, Debug)]
enum PreVar {
  /// Use this variable
  Ok(VarId),
  /// Translate this variable at the current generation
  Pre(HVarId),
  /// Make up some fresh variable
  Fresh,
}

/// A destination designator for expressions that are to be placed in a memory location.
/// See [`PreVar`].
type Dest = Option<PreVar>;

/// A variant on `Dest` for values that are going out of a block via `break`.
type BlockDest = Option<VarId>;

/// A `JoinBlock` represents a potential jump location, together with the information needed to
/// correctly pass all the updated values of mutable variables from the current context.
#[derive(Clone)]
struct JoinBlock {
  /// The block to jump to
  tgt: BlockId,
  /// The generation on entry to the target
  gen: GenId,
  /// The variables that could potentially have been mutated between when this `JoinBlock` was
  /// created and the context we are jumping from. These lists are calculated during type inference
  /// and are mostly syntax directed.
  muts: Rc<[HVarId]>,
}

struct LabelData {
  /// This is `Some((gen, labs, muts))` if jumping to this label is valid. `gen, muts` are
  /// parameters to the [`JoinBlock`] (which are shared between all labels), and
  /// `labs[i] = (tgt, args)` give the target block and the list of variable names to pass
  jumps: Option<(GenId, Rc<[(BlockId, Rc<[VarId]>)]>, Rc<[HVarId]>)>,
  /// The [`JoinBlock`] for breaking to this label, as well as a `BlockDest` which receives the
  /// `break e` expression.
  brk: Option<(JoinBlock, BlockDest)>,
}

/// The main context struct for the MIR builder.
struct BuildMir<'a> {
  /// The global compiler data structures
  compiler: &'a mut Compiler,
  /// The allocator for HIR data
  alloc: &'a Bump,
  /// The main data structure, the MIR control flow graph
  cfg: Cfg,
  /// Contains the current generation and other information relevant to the [`tr`](Self::tr)
  /// function
  tr: Translator<'a>,
  /// The stack of labels in scope
  labels: Vec<(HVarId, LabelData)>,
  /// If this is `Some((gen, muts, args))` then `gen, muts` are the `BlockDest` parameters for the
  /// jump and `args` are the list of variables for the argument. There is no block ID because
  /// [`Return`](Terminator::Return) doesn't jump to a block.
  returns: Option<(GenId, Rc<[HVarId]>, Rc<[HVarId]>)>,
  /// Some variables are replaced by places when referenced; this keeps track of them.
  vars: HashMap<VarId, Place>,
  /// The current block, which is where new statements from functions like [`Self::expr()`] are
  /// inserted.
  cur_block: BlockId,
  /// The current context, which contains typing information about the variables that are in scope.
  cur_ctx: CtxId,
}

struct Diverged;

type Block<T> = Result<T, Diverged>;

impl<'a> BuildMir<'a> {
  fn new(compiler: &'a mut Compiler, alloc: &'a Bump, var_names: &[AtomId]) -> Self {
    let mut tr = Translator {
      next_var: VarId(var_names.len().try_into().expect("overflow")),
      cur_gen: GenId::ROOT,
      ..Default::default()
    };
    tr.add_gen(GenId::ROOT, GenId::ROOT, &[]);
    Self {
      compiler, alloc,
      cfg: Cfg::default(),
      labels: vec![],
      returns: None,
      tr,
      vars: Default::default(),
      cur_block: BlockId::ENTRY,
      cur_ctx: CtxId::ROOT,
    }
  }

  fn fresh_var(&mut self) -> VarId { self.tr.fresh_var() }

  #[inline] fn cur(&self) -> (BlockId, CtxId, GenId) {
    (self.cur_block, self.cur_ctx, self.tr.cur_gen)
  }

  #[inline] fn set(&mut self, (block, ctx, gen): (BlockId, CtxId, GenId)) {
    self.cur_block = block; self.cur_ctx = ctx; self.tr.cur_gen = gen;
  }

  fn cur_block(&mut self) -> &mut BasicBlock { &mut self.cfg[self.cur_block] }

  fn new_block(&mut self) -> BlockId { self.cfg.new_block(self.cur_ctx) }

  fn extend_ctx(&mut self, var: VarId, ty: ExprTy) {
    self.cur_ctx = self.cfg.ctxs.extend(self.cur_ctx, var, ty)
  }

  fn push_stmt(&mut self, stmt: Statement) {
    match stmt {
      Statement::Let(v, ref ty, _) => self.extend_ctx(v, ty.clone()),
      Statement::ExElim(ExElimKind::Own([(v, ref ty), (h, ref ty2)]), _, _) => {
        self.extend_ctx(v, (None, ty.clone()));
        self.extend_ctx(h, (Some(Rc::new(ExprKind::Unit)), ty2.clone()));
      }
    }
    self.cur_block().stmts.push(stmt);
  }

  fn tr<T: Translate<'a>>(&mut self, t: T) -> T::Output { t.tr(&mut self.tr) }

  fn tr_gen<T: Translate<'a>>(&mut self, t: T, gen: GenId) -> T::Output {
    self.tr.with_gen(gen, |tr| t.tr(tr))
  }

  fn as_temp(&mut self, e: hir::Expr<'a>) -> Block<VarId> {
    let v = self.fresh_var();
    self.expr(e, Some(PreVar::Ok(v)))?;
    Ok(v)
  }

  fn assert(&mut self, vcond: Operand, cond: Expr) -> VarId {
    let vh = self.fresh_var();
    self.extend_ctx(vh, (None, Rc::new(TyKind::Pure(cond))));
    let tgt = self.new_block();
    self.cur_block().terminate(Terminator::Assert(vcond, vh, tgt));
    self.cur_block = tgt;
    vh
  }

  fn place(&mut self, e: hir::Expr<'a>) -> Block<Place> {
    Ok(match e.k.0 {
      hir::ExprKind::Var(v, gen) => {
        let v = self.tr_gen(v, gen);
        self.vars.get(&v).cloned().unwrap_or_else(|| v.into())
      }
      hir::ExprKind::Index(args) => {
        let ([a, i], h) = *args;
        let mut pl = self.place(a)?;
        let vi = self.as_temp(i)?;
        let vh = match h {
          Ok(h) => self.as_temp(h)?,
          Err(n) => {
            let vn = self.as_temp(n)?;
            let vb = self.fresh_var();
            let cond = Rc::new(ExprKind::Binop(Binop::Lt,
              Rc::new(ExprKind::Var(vi)),
              Rc::new(ExprKind::Var(vn))));
            self.push_stmt(Statement::Let(vb,
              (Some(cond.clone()), Rc::new(TyKind::Bool)),
              RValue::Binop(Binop::Lt, Operand::Copy(vi.into()), vn.into())));
            self.assert(vb.into(), cond)
          }
        };
        pl.proj.push(Projection::Index(vi, vh));
        pl
      }
      hir::ExprKind::Slice(args) => {
        let ([a, i, l], h) = *args;
        let mut pl = self.place(a)?;
        let vi = self.as_temp(i)?;
        let vl = self.as_temp(l)?;
        let vh = match h {
          Ok(h) => self.as_temp(h)?,
          Err(n) => {
            let vn = self.as_temp(n)?;
            let vadd = self.fresh_var();
            let add = Rc::new(ExprKind::Binop(Binop::Add,
              Rc::new(ExprKind::Var(vi)),
              Rc::new(ExprKind::Var(vl))));
            self.push_stmt(Statement::Let(vadd,
              (Some(add.clone()), Rc::new(TyKind::Int(IntTy::Int(Size::Inf)))),
              RValue::Binop(Binop::Add, Operand::Copy(vi.into()), Operand::Copy(vl.into()))));
            let vcond = self.fresh_var();
            let cond = Rc::new(ExprKind::Binop(Binop::Le,
              add, Rc::new(ExprKind::Var(vn))));
            self.push_stmt(Statement::Let(vcond,
              (Some(cond.clone()), Rc::new(TyKind::Bool)),
              RValue::Binop(Binop::Le, vadd.into(), vn.into())));
            self.assert(vcond.into(), cond)
          }
        };
        pl.proj.push(Projection::Slice(vi, vl, vh));
        pl
      }
      hir::ExprKind::Proj(pk, e, i) => {
        let mut pl = self.place(*e)?;
        pl.proj.push(Projection::Proj(pk.into(), i));
        pl
      }
      hir::ExprKind::Ref(e) => self.place(*e)?,
      hir::ExprKind::Deref(e) => {
        let mut pl = self.place(*e)?;
        pl.proj.push(Projection::Deref);
        pl
      }
      _ => Place::local(self.as_temp(e)?)
    })
  }

  fn copy_or_move(&mut self, e: hir::Expr<'a>) -> Block<Operand> {
    let copy = e.ty().is_copy();
    let p = self.place(e)?;
    Ok(if copy {Operand::Copy(p)} else {Operand::Move(p)})
  }

  fn copy_or_ref(&mut self, e: hir::Expr<'a>) -> Block<Operand> {
    let copy = e.ty().is_copy();
    let p = self.place(e)?;
    Ok(if copy {Operand::Copy(p)} else {Operand::Ref(p)})
  }

  fn operand(&mut self, e: hir::Expr<'a>) -> Block<Operand> {
    Ok(match e.k.0 {
      hir::ExprKind::Var(_, _) |
      hir::ExprKind::Index(_) |
      hir::ExprKind::Slice(_) |
      hir::ExprKind::Proj(_, _, _) |
      hir::ExprKind::Deref(_) => self.copy_or_move(e)?,
      hir::ExprKind::Rval(e) => self.copy_or_move(*e)?,
      hir::ExprKind::Ref(e) => self.copy_or_ref(*e)?,
      hir::ExprKind::Unit => Constant::unit().into(),
      hir::ExprKind::Bool(b) => Constant::bool(b).into(),
      hir::ExprKind::Int(n) => let_unchecked!(ty::TyKind::Int(ity) = e.ty().k,
        Constant::int(ity, n.clone()).into()),
      hir::ExprKind::Const(a) => Constant {ety: self.tr(e.k.1), k: ConstKind::Const(a)}.into(),
      _ => self.as_temp(e)?.into()
    })
  }

  fn rvalue(&mut self, e: hir::Expr<'a>) -> Block<RValue> {
    Ok(match e.k.0 {
      hir::ExprKind::Var(_, _) |
      hir::ExprKind::Index(_) |
      hir::ExprKind::Slice(_) |
      hir::ExprKind::Proj(_, _, _) |
      hir::ExprKind::Deref(_) |
      hir::ExprKind::Rval(_) |
      hir::ExprKind::Ref(_) |
      hir::ExprKind::Unit |
      hir::ExprKind::Bool(_) |
      hir::ExprKind::Int(_) |
      hir::ExprKind::Const(_) => self.operand(e)?.into(),
      hir::ExprKind::Unop(op, e) => {
        let v = self.as_temp(*e)?;
        RValue::Unop(op, v.into())
      }
      hir::ExprKind::Binop(op, e1, e2) => {
        let v1 = self.as_temp(*e1)?;
        let v2 = self.as_temp(*e2)?;
        RValue::Binop(op, v1.into(), v2.into())
      }
      hir::ExprKind::Sn(x, h) => {
        let vx = self.as_temp(*x)?;
        let vh = h.map(|h| self.as_temp(*h)).transpose()?.map(|h| h.into());
        RValue::Cast(vx.into(), CastKind::Sn(vh))
      }
      hir::ExprKind::List(es) => todo!(),
      hir::ExprKind::Ghost(e) => RValue::Ghost(self.copy_or_move(*e)?),
      hir::ExprKind::Borrow(e) => todo!(),
      hir::ExprKind::Mm0(_, _) => todo!(),
      hir::ExprKind::Cast(_, _, _, _) => todo!(),
      hir::ExprKind::Pun(_, _) => todo!(),
      hir::ExprKind::Uninit(_) => todo!(),
      hir::ExprKind::Sizeof(_) => todo!(),
      hir::ExprKind::Typeof(_) => todo!(),
      hir::ExprKind::Assert(_) => todo!(),
      hir::ExprKind::Assign {..} => {
        self.expr(e, None)?;
        Constant::unit().into()
      }
      hir::ExprKind::Proof(_) => todo!(),
      hir::ExprKind::While(while_) =>
        self.rvalue_while(*while_, e.k.1)?,
      hir::ExprKind::Unreachable(_) |
      hir::ExprKind::Jump(_, _, _, _) |
      hir::ExprKind::Break(_, _) |
      hir::ExprKind::Return(_) |
      hir::ExprKind::UnpackReturn(_) => {
        self.expr(e, None)?;
        unreachable!()
      }
      hir::ExprKind::If {..} | hir::ExprKind::Block(_) | hir::ExprKind::Call {..} |
      hir::ExprKind::Infer(_) | hir::ExprKind::Error => unreachable!()
    })
  }

  fn as_unit_const(&mut self, ty: ty::Ty<'a>) -> Constant {
    match ty.k {
      ty::TyKind::Unit => Constant::unit(),
      ty::TyKind::Pure(&ty::WithMeta {k: ty::ExprKind::Bool(true), ..}) |
      ty::TyKind::True => Constant::itrue(),
      ty::TyKind::Uninit(ty) => Constant::uninit(self.tr(ty)),
      _ => panic!("call is_unit_dest first"),
    }
  }

  fn fulfill_unit_dest<R>(&mut self, ety: ty::ExprTy<'a>,
    dest: Dest, f: impl FnOnce(&mut Self, Dest) -> Block<R>
  ) -> Block<R> {
    if let Some(v) = dest {
      if !ety.1.is_unit_dest() { return f(self, dest) }
      let r = f(self, None)?;
      let rv = self.as_unit_const(ety.1);
      let v = self.tr(v);
      let ety = self.tr(ety);
      self.push_stmt(Statement::Let(v, ety, rv.into()));
      Ok(r)
    } else { f(self, dest) }
  }

  fn expr_unit(&mut self, dest: Dest) {
    if let Some(v) = dest {
      let rv = Constant::unit();
      let v = self.tr(v);
      self.push_stmt(Statement::Let(v, rv.ety.clone(), rv.into()));
    }
  }

  fn expr(&mut self, e: hir::Expr<'a>, dest: Dest) -> Block<()> {
    self.fulfill_unit_dest(e.k.1, dest, |this, dest| {
      match e.k.0 {
        hir::ExprKind::If {hyp, cond, cases, gen, muts} =>
          return this.expr_if(hyp, *cond, *cases, gen, muts, dest),
        hir::ExprKind::Block(bl) => return this.block(bl, dest),
        hir::ExprKind::Call {f, tys, args, variant} =>
          return this.expr_call(f, tys, args, variant, dest),
        _ => {}
      }
      match dest {
        None => match e.k.0 {
          hir::ExprKind::Unit |
          hir::ExprKind::Var(_, _) |
          hir::ExprKind::Const(_) |
          hir::ExprKind::Bool(_) |
          hir::ExprKind::Int(_) |
          hir::ExprKind::Uninit(_) |
          hir::ExprKind::Sizeof(_) => {}
          hir::ExprKind::Unop(_, e) |
          hir::ExprKind::Proj(_, e, _) |
          hir::ExprKind::Rval(e) |
          hir::ExprKind::Deref(e) |
          hir::ExprKind::Ghost(e) |
          hir::ExprKind::Ref(e) |
          hir::ExprKind::Borrow(e) |
          hir::ExprKind::Cast(e, _, _, _) |
          hir::ExprKind::Typeof(e) => return this.expr(*e, None),
          hir::ExprKind::Binop(_, e1, e2) => {
            this.expr(*e1, None)?;
            this.expr(*e2, None)?;
          }
          hir::ExprKind::Sn(e1, h) |
          hir::ExprKind::Pun(e1, h) => {
            this.expr(*e1, None)?;
            if let Some(h) = h { this.expr(*h, None)?; }
          }
          hir::ExprKind::Index(args) => {
            let ([a, i], h) = *args;
            this.expr(a, None)?;
            this.expr(i, None)?;
            if let Ok(h) = h { this.expr(h, None)?; }
          }
          hir::ExprKind::Slice(args) => {
            let ([a, i, l], h) = *args;
            this.expr(a, None)?;
            this.expr(i, None)?;
            this.expr(l, None)?;
            if let Ok(h) = h { this.expr(h, None)?; }
          }
          hir::ExprKind::List(es) => for e in es { this.expr(e, None)? }
          hir::ExprKind::Mm0(e, _) => for e in e.subst { this.expr(e, None)? }
          hir::ExprKind::Assert(_) => {
            this.expr(e, Some(PreVar::Fresh))?;
          }
          hir::ExprKind::Assign {lhs, rhs, oldmap, gen} => {
            todo!()
          }
          hir::ExprKind::Proof(_) |
          hir::ExprKind::While {..} => { this.rvalue(e)?; }
          hir::ExprKind::Unreachable(h) => {
            let h = this.as_temp(*h)?;
            this.cur_block().terminate(Terminator::Unreachable(h.into()));
            return Err(Diverged)
          }
          hir::ExprKind::Jump(lab, i, es, _variant) => {
            let (gen, jumps, muts) = this.labels.iter()
              .rfind(|p| p.0 == lab).expect("missing label")
              .1.jumps.as_ref().expect("label does not expect break");
            let (tgt, args) = jumps[usize::from(i)].clone();
            let jb = JoinBlock {tgt, gen: *gen, muts: muts.clone()};
            let args = args.iter().zip(es).map(|(&v, e)| {
              Ok((v, this.operand(e)?))
            }).collect::<Block<Vec<_>>>()?;
            this.join(&jb, args)
          }
          hir::ExprKind::Break(lab, e) => {
            let (jb, dest) = this.labels.iter()
              .rfind(|p| p.0 == lab).expect("missing label")
              .1.brk.as_ref().expect("label does not expect break").clone();
            let args = match dest {
              None => { this.expr(*e, None)?; vec![] }
              Some(v) => vec![(v, this.operand(*e)?)]
            };
            this.join(&jb, args)
          }
          hir::ExprKind::Return(es) =>
            match this.expr_return(|_| es.into_iter(), |this, e| this.place(e))? {}
          hir::ExprKind::UnpackReturn(e) => {
            let pl = this.place(*e)?;
            match this.expr_return(|n| 0..n as u32, |this, i| Ok({
              let mut pl = pl.clone();
              pl.proj.push(Projection::Proj(ProjectionKind::Struct, i));
              pl
            }))? {}
          }
          hir::ExprKind::If {..} | hir::ExprKind::Block(_) | hir::ExprKind::Call {..} |
          hir::ExprKind::Infer(_) | hir::ExprKind::Error => unreachable!()
        }
        Some(dest) => {
          let ety = e.k.1;
          let rv = this.rvalue(e)?;
          let dest = this.tr(dest);
          let ety = this.tr(ety);
          this.push_stmt(Statement::Let(dest, ety, rv))
        }
      }
      Ok(())
    })
  }

  fn tup_pat(&mut self, pat: TuplePattern<'a>, src: &mut Place) {
    match pat.k {
      TuplePatternKind::Name(_, v, _) => {
        let v = self.tr(v);
        self.vars.insert(v, src.clone());
      }
      TuplePatternKind::Tuple(pats, mk, ty) => {
        let pk = match mk {
          TupleMatchKind::Unit | TupleMatchKind::True => return,
          TupleMatchKind::List | TupleMatchKind::Struct => ProjectionKind::Struct,
          TupleMatchKind::Array => ProjectionKind::Array,
          TupleMatchKind::And => ProjectionKind::And,
          TupleMatchKind::Sn => ProjectionKind::Sn,
          TupleMatchKind::Own => let_unchecked!([vpat, hpat] = *pats, {
            let tgt = self.tr(pat.k.ty());
            let v = self.tr.tr_opt_var(vpat.k.var());
            let h = self.tr.tr_opt_var(hpat.k.var());
            let ek = ExElimKind::Own([(v, self.tr(vpat.k.ty())), (h, self.tr(hpat.k.ty()))]);
            self.push_stmt(Statement::ExElim(ek, tgt, src.clone().into()));
            self.tup_pat(vpat, &mut v.into());
            self.tup_pat(hpat, &mut h.into());
            return
          }),
        };
        for (i, &pat) in pats.iter().enumerate() {
          src.proj.push(Projection::Proj(pk, i.try_into().expect("overflow")));
          self.tup_pat(pat, src);
          src.proj.pop();
        }
      }
      TuplePatternKind::Error(_, _) => unreachable!()
    }
  }

  fn push_args(&mut self, args: Box<[hir::Arg<'a>]>) -> (BlockId, Rc<[VarId]>) {
    let mut vs = Vec::with_capacity(args.len());
    for arg in &*args {
      if let hir::ArgKind::Lam(pat) = arg.1 {
        let var = self.tr(pat.k.var().map_or(PreVar::Fresh, PreVar::Pre));
        vs.push(var);
        let ty = self.tr(pat.k.ty());
        self.extend_ctx(var, (None, ty));
      }
    }
    let bl = self.new_block();
    self.cur_block = bl;
    let mut pats = vec![];
    (|| -> Block<()> {
      let mut it = vs.iter();
      for arg in args.into_vec() {
        match arg.1 {
          hir::ArgKind::Lam(pat) => {
            let v = *unwrap_unchecked!(it.next());
            self.tr.tr_tup_pat(pat, Rc::new(ExprKind::Var(v)));
            self.tup_pat(pat, &mut v.into());
            pats.push(pat);
          }
          hir::ArgKind::Let(pat, pe, e) => {
            if let Some(e) = e {
              let v = self.tr(pat.k.var().map_or(PreVar::Fresh, PreVar::Pre));
              self.expr(*e, Some(PreVar::Ok(v)))?;
              self.tup_pat(pat, &mut v.into());
            }
            let pe = self.tr(pe);
            self.tr.tr_tup_pat(pat, pe);
            pats.push(pat);
          }
        }
      }
      Ok(())
    })();
    for pat in pats.into_iter().rev() { self.tr.finish_tup_pat(pat) }
    (bl, vs.into())
  }

  fn join(&mut self,
    &JoinBlock {tgt, gen, ref muts}: &JoinBlock,
    mut args: Vec<(VarId, Operand)>
  ) {
    let ctx = self.cfg[tgt].ctx;
    args.extend(muts.iter().filter_map(|&v| {
      let from = self.tr(v);
      let to = self.tr_gen(v, gen);
      if from == to || self.cfg.ctxs.rev_iter(ctx).all(|&(u, _)| from != u) {return None}
      Some((to, from.into()))
    }));
    self.cur_block().terminate(Terminator::Jump(tgt, args))
  }

  fn stmt(&mut self, stmt: hir::Stmt<'a>, brk: Option<&(JoinBlock, BlockDest)>) -> Block<()> {
    match stmt.k {
      hir::StmtKind::Let { lhs, rhs } => {
        let v = lhs.k.var().map_or_else(|| PreVar::Ok(self.fresh_var()), PreVar::Pre);
        self.expr(rhs, Some(v))?;
        let v = self.tr(v);
        self.tup_pat(lhs, &mut v.into());
        Ok(())
      }
      hir::StmtKind::Expr(e) => self.expr(hir::Spanned {span: stmt.span, k: e}, None),
      hir::StmtKind::Label(v, labs) => {
        let base_ctx = self.cur_ctx;
        let base_bl = self.cur_block;
        let base_gen = self.tr.cur_gen;
        let &(ref brk, dest) = brk.expect("we need a join point for the break here");
        let mut bodies = vec![];
        let jumps = labs.into_vec().into_iter().map(|lab| {
          let (bl, args) = self.push_args(lab.args);
          bodies.push(lab.body);
          self.cur_ctx = base_ctx;
          (bl, args)
        }).collect();
        self.labels.push((v, LabelData {
          jumps: Some((base_gen, Rc::clone(&jumps), brk.muts.clone())),
          brk: Some((brk.clone(), dest))
        }));
        for (&(bl, _), body) in jumps.iter().zip(bodies) {
          self.cur_ctx = self.cfg[bl].ctx;
          self.cur_block = bl;
          self.tr.cur_gen = base_gen;
          if let Ok(()) = self.block(body, dest.map(PreVar::Ok)) {
            self.join(brk, match dest { None => vec![], Some(v) => vec![(v, v.into())] })
          }
        }
        self.cur_ctx = base_ctx;
        self.cur_block = base_bl;
        self.tr.cur_gen = base_gen;
        Ok(())
      }
    }
  }

  fn block(&mut self, hir::Block {stmts, expr, gen, muts}: hir::Block<'a>, dest: Dest) -> Block<()> {
    let reset = self.labels.len();
    let jp = if stmts.iter().any(|s| matches!(s.k, hir::StmtKind::Label(..))) {
      let dest2 = dest.map(|v| self.tr_gen(v, gen));
      Some((JoinBlock {tgt: self.new_block(), gen, muts: muts.into()}, dest2))
    } else { None };
    let r = (|| {
      for stmt in stmts { self.stmt(stmt, jp.as_ref())? }
      if let Some(e) = expr { self.expr(*e, dest) }
      else { self.expr_unit(dest); Ok(()) }
    })();
    self.labels.truncate(reset);
    if let Some((JoinBlock {tgt, gen, ..}, _)) = jp {
      self.set((tgt, self.cfg[tgt].ctx, gen));
      Ok(())
    } else { r }
  }

  fn expr_if(&mut self,
    hyp: Option<HVarId>,
    cond: hir::Expr<'a>,
    [e_tru, e_fal]: [hir::Expr<'a>; 2],
    gen: GenId,
    muts: Vec<HVarId>,
    dest: Dest,
  ) -> Block<()> {
    // In the general case, we generate:
    //   vcond := cond
    //   if vcond {h. goto tru(h)} else {h. goto fal(h)}
    // tru(h: cond):
    //   v := e_tru
    //   goto after(v)
    // fal(h: !cond):
    //   v := e_fal
    //   goto after(v)
    // after(dest: T):
    let pe = cond.k.1 .0;
    //   vcond := cond
    let vcond = self.as_temp(cond)?;
    let pe = pe.map_or_else(|| Rc::new(ExprKind::Var(vcond)), |e| self.tr(e));
    let vhyp = self.tr(hyp.map_or(PreVar::Fresh, PreVar::Pre));
    let (_, base_ctx, base_gen) = self.cur();
    // tru_ctx is the current context with `vhyp: cond`
    let tru_ctx = self.cfg.ctxs.extend(base_ctx, vhyp,
      (Some(Rc::new(ExprKind::Unit)), Rc::new(TyKind::Pure(pe.clone()))));
    let tru = self.cfg.new_block(tru_ctx);
    // fal_ctx is the current context with `vhyp: !cond`
    let fal_ctx = self.cfg.ctxs.extend(base_ctx, vhyp,
      (Some(Rc::new(ExprKind::Unit)), Rc::new(TyKind::Not(Rc::new(TyKind::Pure(pe))))));
    let fal = self.cfg.new_block(fal_ctx);
    //   if vcond {vhyp. goto tru(vhyp)} else {vhyp. goto fal(vhyp)}
    self.cur_block().terminate(Terminator::If(vcond.into(), [(vhyp, tru), (vhyp, fal)]));

    let (trans, dest) = match dest {
      None => (None, None),
      Some(v) => {
        let v = self.tr_gen(v, gen);
        (Some(v), Some(PreVar::Ok(v)))
      }
    };
    // tru(h: cond):
    //   dest := e_tru
    self.set((tru, tru_ctx, base_gen));
    let tru_res = self.expr(e_tru, dest);
    let tru = self.cur();
    // fal(h: !cond):
    //   dest := e_fal
    self.set((fal, fal_ctx, base_gen));
    let fal_res = self.expr(e_fal, dest);
    let fal = self.cur();

    // Either `e_tru` or `e_fal` may have diverged before getting to the end of the block.
    // * If they both diverged, then the if statement diverges
    // * If one of them diverges, then the if statement degenerates:
    //     vcond := cond
    //     if vcond {h. goto tru(h)} else {h. goto fal(h)}
    //   tru(h: cond):
    //     e_tru -> diverge
    //   fal(h: !cond):
    //     dest := e_fal
    match (tru_res, fal_res) {
      (Err(Diverged), Err(Diverged)) => return Err(Diverged),
      (Ok(()), Err(Diverged)) => { self.set(tru) }
      (Err(Diverged), Ok(())) => { self.set(fal) }
      (Ok(()), Ok(())) => {
        // If neither diverges, we put `goto after` at the end of each block
        let join = JoinBlock {tgt: self.new_block(), gen, muts: muts.into()};
        self.set(tru);
        self.join(&join, match trans { None => vec![], Some(v) => vec![(v, v.into())] });
        self.set(fal);
        self.join(&join, match trans { None => vec![], Some(v) => vec![(v, v.into())] });
        // And the after block is the end of the statement
        self.set((join.tgt, base_ctx, gen));
      }
    }
    Ok(())
  }

  fn rvalue_while(&mut self,
    hir::While { label, hyp, cond, var, body, gen, muts, trivial }: hir::While<'a>,
    ret: ty::ExprTy<'a>,
  ) -> Block<RValue> {
    // If `has_break` is true, then this looks like
    //   dest: () := (while cond body)
    // otherwise
    //   dest: !cond := (while cond body).
    // We don't actually have `dest` here, we're making an rvalue that could potentially be placed
    // in a destination.
    let has_break = matches!(ret.1.k, ty::TyKind::Unit);

    // If `cond` evaluates to `false`, then we generate the code
    // _ := cond; dest: !cond := itrue
    // since we know that `!cond` is defeq to true
    if let Some(false) = trivial {
      // ~>
      self.expr(*cond, None)?;
      return Ok(if has_break {Constant::unit()} else {Constant::itrue()}.into())
    }

    // Otherwise we actually have a loop. Generally we want to produce:
    //
    //   jump base
    // base:
    //   v := cond
    //   if v {h. goto main(h)} else {h'. goto after(h')}
    // main(h: cond):
    //   _ := body
    //   goto base
    // after(h': !cond):
    //   dest := h'
    //
    // If `has_break` is true, then we use an extra block `fal` to drop `!cond`:
    //
    //   jump base
    // base:
    //   v := cond
    //   if v {h. goto main(h)} else {h'. goto fal(h')}
    // fal(h': !cond):
    //   goto after
    // main(h: cond):
    //   _ := body
    //   goto base
    // after:
    //   dest := ()
    let base_bl = self.new_block();
    self.cur_block().terminate(Terminator::Jump(base_bl, vec![]));
    self.cur_block = base_bl;
    let base_gen = self.tr.cur_gen;
    let base_ctx = self.cur_ctx;
    let muts: Rc<[HVarId]> = muts.into();

    // if `has_break` then we need to be prepared to jump to `after` from inside the loop.
    let brk = if has_break {
      Some((JoinBlock {tgt: self.new_block(), gen, muts: muts.clone()}, None))
    } else { None };

    // Set things up so that `(continue label)` jumps to `base`,
    // and `(break label)` jumps to `after`
    self.labels.push((label, LabelData {
      jumps: Some((base_gen, Rc::new([(base_bl, Rc::new([]))]), muts.clone())),
      brk: brk.clone()
    }));

    // `res` captures the exit condition produced from inside the loop.
    let mut res = Err(Diverged);
    // This is the body of the loop. We catch divergence here because if the execution of `cond` or
    // `body` diverges we still have to construct `after` and anything after that, provided that
    // `after` itself is reachable (which we signal by `res` having a value).
    (|| -> Block<()> {
      let pe: Option<ty::Expr<'_>> = cond.k.1 .0;
      if let Some(true) = trivial {
        // If `cond` evaluates to `true`, then this is an infinite loop and `after` is not
        // reachable, unless it is accessed indirectly via `break`.
        // We generate the following code:
        //   jump base
        // base:
        //   _ := cond   (we know it is true so no point in capturing the result)
        //   h: cond := itrue    (force cond = true by defeq)
        //   _ := body
        //   goto base
        //
        // We never set `res`, so it remains `Err(Diverged)` because it is unreachable.
        self.expr(*cond, None)?;
        if let (Some(pe), Some(hyp)) = (pe, hyp) {
          let pe = self.tr(pe);
          let vhyp = self.tr(hyp);
          self.push_stmt(Statement::Let(vhyp,
            (Some(Rc::new(ExprKind::Unit)), Rc::new(TyKind::Pure(pe))),
            Constant::itrue().into()));
        }
      } else {
        // Otherwise, this is a proper while loop.
        //   vcond := cond
        let vcond = self.as_temp(*cond)?;
        let pe = pe.map_or_else(|| Rc::new(ExprKind::Var(vcond)), |e| self.tr(e));
        let vhyp = self.tr(hyp.map_or(PreVar::Fresh, PreVar::Pre));
        let test = self.cur();
        // tru_ctx is the current context with `vhyp: cond`
        let tru_ctx = self.cfg.ctxs.extend(test.1, vhyp,
          (Some(Rc::new(ExprKind::Unit)), Rc::new(TyKind::Pure(pe.clone()))));
        let tru = self.cfg.new_block(tru_ctx);
        // fal_ctx is the current context with `vhyp: !cond`
        let fal_ctx = self.cfg.ctxs.extend(test.1, vhyp,
          (Some(Rc::new(ExprKind::Unit)), Rc::new(TyKind::Not(Rc::new(TyKind::Pure(pe))))));
        let fal = self.cfg.new_block(fal_ctx);
        //   if vcond {vhyp. goto main(vhyp)} else {vhyp. goto after(vhyp)}
        self.cur_block().terminate(Terminator::If(vcond.into(), [(vhyp, tru), (vhyp, fal)]));

        // If `brk` is set (to `after`) then that means `has_break` is true so we want to jump to
        // `after` and ignore the `vhyp: !cond` in the false case.
        if let Some((ref join, _)) = brk {
          // We don't set `res` because it is ignored in this case
          self.set((fal, fal_ctx, test.2));
          self.join(join, vec![]);
        } else {
          // Set `res` to the `after` block (the false branch of the if),
          // and `vhyp: !cond` is the output
          res = Ok(((fal, fal_ctx, test.2), vhyp.into()));
        }
        // Prepare to generate the `main` label
        self.set((tru, tru_ctx, test.2));
      }
      //   _ := body
      self.block(*body, None)?;
      //   goto base
      self.join(&JoinBlock {tgt: base_bl, gen: base_gen, muts}, vec![]);
      // We've diverged, there is nothing more to do in the loop
      Err(Diverged)
    })().expect_err("it's a loop");

    if let Some((join, _)) = self.labels.pop().expect("underflow").1.brk {
      // If `has_break` is true, then the final location after the while loop is the join point
      // `after`, and the context is `base_ctx` because the while loop doesn't add any bindings
      self.set((join.tgt, base_ctx, join.gen));
      // We return `()` from the loop expression
      Ok(Constant::unit().into())
    } else {
      // If `has_break` is false, then the final location is the false branch inside the loop,
      // which we may or may not have reached before diverging (if for example the loop condition
      // diverges). If we did reach it then we pull out the position and return the value.
      res.map(|(pos, rv)| { self.set(pos); rv })
    }
  }

  fn expr_call(&mut self,
    f: hir::Spanned<'a, AtomId>,
    tys: &'a [ty::Ty<'a>],
    args: Vec<hir::Expr<'a>>,
    variant: Option<Box<hir::Expr<'a>>>,
    dest: Dest,
  ) -> Block<()> {
    drop((f, args, variant));
    todo!()
  }

  fn expr_return<T, I: ExactSizeIterator<Item=T>>(&mut self,
    es: impl FnOnce(usize) -> I,
    mut f: impl FnMut(&mut Self, T) -> Block<Place>,
  ) -> Block<std::convert::Infallible> {
    let (gen, muts, args) = self.returns.as_ref().expect("can't return here").clone();
    let args = es(args.len()).zip(&*args).map(|(e, &v)| {
      Ok((self.tr_gen(v, gen), f(self, e)?.into()))
    }).collect::<Block<Vec<_>>>()?;
    self.cur_block().terminate(Terminator::Return(args));
    Err(Diverged)
  }

  fn build_item(&mut self, it: hir::Item<'a>) {
    match it.k {
      hir::ItemKind::Proc { kind, name, tyargs, args, rets, variant, body } => {

      }
      hir::ItemKind::Global { lhs, rhs } => {
        mem::swap(&mut self.compiler.init.0, &mut self.cfg);

        mem::swap(&mut self.compiler.init.0, &mut self.cfg);
      }
      hir::ItemKind::Const { lhs, rhs } => {}
      hir::ItemKind::Typedef { name, tyargs, args, val } => {}
    }
  }
}