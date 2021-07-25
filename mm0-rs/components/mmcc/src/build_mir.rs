//! Build the mid-level IR from HIR

use std::{rc::Rc, fmt::Debug, mem};
use std::convert::TryInto;
use std::collections::{HashMap, hash_map::Entry};
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;
use types::IntTy;
use crate::Symbol;
use super::types;
use types::{Spanned, VarId as HVarId, hir, ty, mir};
use hir::GenId;
use ty::{TuplePattern, TuplePatternKind, TupleMatchKind};
#[allow(clippy::wildcard_imports)] use mir::*;

#[derive(Debug)]
struct GenMap {
  dominator: GenId,
  value: HashMap<HVarId, VarId>,
  cache: HashMap<HVarId, VarId>,
}

type TrMap<K, V> = HashMap<K, Result<V, HashMap<GenId, V>>>;
#[derive(Debug, Default)]
struct Translator<'a> {
  tys: TrMap<ty::Ty<'a>, Ty>,
  exprs: TrMap<ty::Expr<'a>, Expr>,
  places: TrMap<ty::Place<'a>, EPlace>,
  gen_vars: HashMap<GenId, GenMap>,
  locations: HashMap<HVarId, VarId>,
  // located: HashMap<VarId, Vec<VarId>>,
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
      ty::TyKind::Ref(lft, ty) => TyKind::Ref(lft.tr(tr), ty.tr(tr)),
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

impl<'a> TranslateBase<'a> for ty::PlaceKind<'a> {
  type Output = EPlaceKind;
  fn get_mut<'b>(t: &'b mut Translator<'a>) -> &'b mut TrMap<ty::Place<'a>, EPlace> { &mut t.places }
  fn make(&'a self, tr: &mut Translator<'a>) -> EPlaceKind {
    match *self {
      ty::PlaceKind::Var(v) => EPlaceKind::Var(tr.location(v)),
      ty::PlaceKind::Index(a, ty, i) => EPlaceKind::Index(a.tr(tr), ty.tr(tr), i.tr(tr)),
      ty::PlaceKind::Slice(a, ty, [i, l]) =>
        EPlaceKind::Slice(a.tr(tr), ty.tr(tr), [i.tr(tr), l.tr(tr)]),
      ty::PlaceKind::Proj(a, ty, i) => EPlaceKind::Proj(a.tr(tr), ty.tr(tr), i),
      ty::PlaceKind::Error => unreachable!(),
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
      ty::ExprKind::Slice([a, i, l]) => ExprKind::Slice(a.tr(tr), i.tr(tr), l.tr(tr)),
      ty::ExprKind::Proj(a, i) => ExprKind::Proj(a.tr(tr), i),
      ty::ExprKind::UpdateIndex([a, i, v]) => ExprKind::UpdateIndex(a.tr(tr), i.tr(tr), v.tr(tr)),
      ty::ExprKind::UpdateSlice([a, i, l, v]) =>
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
        Entry::Vacant(e) => {
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

impl<'a> Translate<'a> for ty::Lifetime {
  type Output = Lifetime;
  fn tr(self, tr: &mut Translator<'a>) -> Lifetime {
    match self {
      ty::Lifetime::Extern => Lifetime::Extern,
      ty::Lifetime::Place(v) => Lifetime::Place(v.tr(tr)),
      ty::Lifetime::Infer(_) => unreachable!(),
    }
  }
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
  #[must_use] fn fresh_var(&mut self) -> VarId { self.next_var.fresh() }

  fn tr_var(&mut self, v: HVarId, gen: GenId) -> VarId {
    let gm = self.gen_vars.get(&gen).expect("unknown generation");
    if let Some(&val) = gm.cache.get(&v) { return val }
    let val =
      if let Some(&val) = gm.value.get(&v) { val }
      else if gen == GenId::ROOT { self.next_var.fresh() }
      else { let dom = gm.dominator; self.tr_var(v, dom) };
    self.gen_vars.get_mut(&gen).expect("unknown generation").cache.insert(v, val);
    val
  }

  fn tr_opt_var(&mut self, var: Option<HVarId>) -> VarId {
    if let Some(v) = var { v.tr(self) } else { self.fresh_var() }
  }

  fn location(&mut self, var: HVarId) -> VarId {
    let next = &mut self.next_var;
    *self.locations.entry(var).or_insert_with(|| next.fresh())
  }
  // fn locate(&mut self, var: VarId) -> &mut Vec<VarId> {
  //   self.located.entry(var).or_insert_with(Vec::new)
  // }

  fn add_gen(&mut self, dominator: GenId, gen: GenId, value: HashMap<HVarId, VarId>) {
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
      let attr = ArgAttr::NONDEP | ArgAttr::ghost(ty.ghostly());
      let ty = ty.tr(self);
      Arg {attr, var: self.fresh_var(), ty}
    }).collect())
  }

  fn tr_struct(&mut self, args: &'a [ty::Arg<'a>]) -> TyKind {
    let mut args2 = Vec::with_capacity(args.len());
    for &arg in args {
      match arg.k {
        (attr, ty::ArgKind::Lam(pat)) => {
          let mut attr2 = ArgAttr::empty();
          if attr.contains(ty::ArgAttr::NONDEP) { attr2 |= ArgAttr::NONDEP }
          let ty = pat.k.ty();
          if ty.ghostly() { attr2 |= ArgAttr::GHOST }
          let ty = ty.tr(self);
          if let Some(v) = pat.k.var() {
            args2.push(Arg {attr: attr2, var: v.tr(self), ty})
          } else {
            let v = self.fresh_var();
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
/// * `gen`: The generation on entry to the target
/// * `muts`: The variables that could potentially have been mutated between when this `JoinBlock`
///   was created and the context we are jumping from. These lists are calculated during type
///   inference and are mostly syntax directed.
type JoinPoint = (GenId, Rc<[HVarId]>);

/// A `JoinBlock` represents a potential jump location, together with the information needed to
/// correctly pass all the updated values of mutable variables from the current context.
#[derive(Clone, Debug)]
struct JoinBlock(BlockId, JoinPoint);

/// Data to support the `(jump label[i])` operation.
type LabelData = (BlockId, Rc<[(VarId, bool)]>);

#[derive(Debug)]
struct LabelGroupData {
  /// This is `Some((gen, labs, muts))` if jumping to this label is valid. `gen, muts` are
  /// parameters to the [`JoinBlock`] (which are shared between all labels), and
  /// `labs[i] = (tgt, args)` give the target block and the list of variable names to pass
  jumps: Option<(JoinPoint, Rc<[LabelData]>)>,
  /// The [`JoinBlock`] for breaking to this label, as well as a `BlockDest` which receives the
  /// `break e` expression.
  brk: Option<(JoinBlock, BlockDest)>,
}

/// The global initializer, which contains let bindings for every global variable.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub(crate) struct Initializer {
  cfg: Cfg,
  cur_block: Block<BlockId>,
}

impl Default for Initializer {
  fn default() -> Self {
    let mut cfg = Cfg::default();
    let cur_block = Ok(cfg.new_block(CtxId::ROOT));
    Self {cfg, cur_block}
  }
}

/// The main context struct for the MIR builder.
#[derive(Debug)]
pub(crate) struct BuildMir<'a> {
  /// The main data structure, the MIR control flow graph
  cfg: Cfg,
  /// Contains the current generation and other information relevant to the [`tr`](Self::tr)
  /// function
  tr: Translator<'a>,
  /// The stack of labels in scope
  labels: Vec<(HVarId, LabelGroupData)>,
  /// If this is `Some(args)` then `args` are the names of the return places.
  /// There is no block ID because [`Return`](Terminator::Return) doesn't jump to a block.
  returns: Option<Rc<[(VarId, bool)]>>,
  /// Some variables are replaced by places when referenced; this keeps track of them.
  vars: HashMap<VarId, Place>,
  /// The current block, which is where new statements from functions like [`Self::expr()`] are
  /// inserted.
  cur_block: BlockId,
  /// The current context, which contains typing information about the variables that are in scope.
  cur_ctx: CtxId,
}

/// Indicates that construction diverged. See [`Block`].
#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub(crate) struct Diverged;

/// This is the return type of functions that construct a `T` but may choose instead to perform
/// some kind of non-local exit, in which case [`cur_block`](BuildMir::cur_block) will be
/// terminated.
pub(crate) type Block<T> = Result<T, Diverged>;

impl Default for BuildMir<'_> {
  fn default() -> Self {
    let mut tr = Translator {
      next_var: VarId::default(),
      cur_gen: GenId::ROOT,
      ..Default::default()
    };
    tr.add_gen(GenId::ROOT, GenId::ROOT, Default::default());
    Self {
      cfg: Cfg::default(),
      labels: vec![],
      returns: None,
      tr,
      vars: Default::default(),
      cur_block: BlockId::ENTRY,
      cur_ctx: CtxId::ROOT,
    }
  }
}

impl<'a> BuildMir<'a> {
  fn fresh_var(&mut self) -> VarId { self.tr.fresh_var() }

  #[inline] fn cur(&self) -> (BlockId, CtxId, GenId) {
    (self.cur_block, self.cur_ctx, self.tr.cur_gen)
  }

  #[inline] fn set(&mut self, (block, ctx, gen): (BlockId, CtxId, GenId)) {
    self.cur_block = block; self.cur_ctx = ctx; self.tr.cur_gen = gen;
  }

  fn cur_block(&mut self) -> &mut BasicBlock { &mut self.cfg[self.cur_block] }

  fn new_block(&mut self) -> BlockId { self.cfg.new_block(self.cur_ctx) }

  fn extend_ctx(&mut self, var: VarId, r: bool, ty: ExprTy) {
    self.cur_ctx = self.cfg.ctxs.extend(self.cur_ctx, var, r, ty)
  }

  fn push_stmt(&mut self, stmt: Statement) {
    match stmt {
      Statement::Let(LetKind::Let(v, r, ref e), ref ty, _) =>
        self.extend_ctx(v, r, (e.clone(), ty.clone())),
      Statement::Let(LetKind::Own([(v, vr, ref ty), (h, hr, ref ty2)]), _, _) => {
        self.extend_ctx(v, vr, (None, ty.clone()));
        self.extend_ctx(h, hr, (Some(Rc::new(ExprKind::Unit)), ty2.clone()));
      }
      Statement::Assign(_, _, ref vars) => for v in &**vars {
        self.extend_ctx(v.to, v.rel, v.ety.clone())
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

  fn assert(&mut self, v_cond: Operand, cond: Expr) -> VarId {
    let vh = self.fresh_var();
    self.extend_ctx(vh, false, (None, Rc::new(TyKind::Pure(cond))));
    let tgt = self.new_block();
    self.cur_block().terminate(Terminator::Assert(v_cond, vh, true, tgt));
    self.cur_block = tgt;
    vh
  }

  fn index_projection(&mut self, idx: hir::Expr<'a>,
    hyp_or_n: Result<hir::Expr<'a>, hir::Expr<'a>>
  ) -> Block<Projection> {
    let vi = self.as_temp(idx)?;
    Ok(Projection::Index(vi, match hyp_or_n {
      Ok(hyp) => self.as_temp(hyp)?,
      Err(n) => {
        let vn = self.as_temp(n)?;
        let vb = self.fresh_var();
        let cond = Rc::new(ExprKind::Binop(types::Binop::Lt,
          Rc::new(ExprKind::Var(vi)),
          Rc::new(ExprKind::Var(vn))));
        self.push_stmt(Statement::Let(
          LetKind::Let(vb, true, Some(cond.clone())), Rc::new(TyKind::Bool),
          RValue::Binop(Binop::Lt(IntTy::NAT),
            Operand::Copy(vi.into()), vn.into())));
        self.assert(vb.into(), cond)
      }
    }))
  }

  fn slice_projection(&mut self, idx: hir::Expr<'a>, len: hir::Expr<'a>,
    hyp_or_n: Result<hir::Expr<'a>, hir::Expr<'a>>
  ) -> Block<Projection> {
    let vi = self.as_temp(idx)?;
    let vl = self.as_temp(len)?;
    Ok(Projection::Slice(vi, vl, match hyp_or_n {
      Ok(hyp) => self.as_temp(hyp)?,
      Err(n) => {
        let vn = self.as_temp(n)?;
        let v_add = self.fresh_var();
        let add = Rc::new(ExprKind::Binop(types::Binop::Add,
          Rc::new(ExprKind::Var(vi)),
          Rc::new(ExprKind::Var(vl))));
        self.push_stmt(Statement::Let(
          LetKind::Let(v_add, true, Some(add.clone())),
          Rc::new(TyKind::Int(IntTy::INT)),
          RValue::Binop(Binop::Add(IntTy::NAT),
            Operand::Copy(vi.into()), Operand::Copy(vl.into()))));
        let v_cond = self.fresh_var();
        let cond = Rc::new(ExprKind::Binop(types::Binop::Le,
          add, Rc::new(ExprKind::Var(vn))));
        self.push_stmt(Statement::Let(
          LetKind::Let(v_cond, true, Some(cond.clone())),
          Rc::new(TyKind::Bool),
          RValue::Binop(Binop::Le(IntTy::NAT), v_add.into(), vn.into())));
        self.assert(v_cond.into(), cond)
      }
    }))
  }

  fn place(&mut self, e: hir::Place<'a>) -> Block<Place> {
    Ok(match e.k.0 {
      hir::PlaceKind::Var(v) => {
        let v2 = self.tr.location(v);
        self.vars.get(&v2).cloned().unwrap_or_else(|| v2.into())
      }
      hir::PlaceKind::Index(args) => {
        let (arr, idx, hyp_or_n) = *args;
        self.place(arr)?.proj(self.index_projection(idx, hyp_or_n)?)
      }
      hir::PlaceKind::Slice(args) => {
        let (arr, [idx, len], hyp_or_n) = *args;
        self.place(arr)?.proj(self.slice_projection(idx, len, hyp_or_n)?)
      }
      hir::PlaceKind::Proj(pk, e, i) =>
        self.place(*e)?.proj(Projection::Proj(pk.into(), i)),
      hir::PlaceKind::Deref(e) =>
        Place::local(self.as_temp(*e)?).proj(Projection::Deref),
      hir::PlaceKind::Error => unreachable!()
    })
  }

  fn ignore_place(&mut self, e: hir::Place<'a>) -> Block<()> {
    match e.k.0 {
      hir::PlaceKind::Var(_) => {}
      hir::PlaceKind::Index(args) => {
        let (arr, idx, hyp_or_n) = *args;
        self.ignore_place(arr)?;
        self.expr(idx, None)?;
        if let Ok(hyp) = hyp_or_n { self.expr(hyp, None)?; }
      }
      hir::PlaceKind::Slice(args) => {
        let (arr, [idx, len], hyp_or_n) = *args;
        self.ignore_place(arr)?;
        self.expr(idx, None)?;
        self.expr(len, None)?;
        if let Ok(hyp) = hyp_or_n { self.expr(hyp, None)?; }
      }
      hir::PlaceKind::Proj(_, e, _) => self.ignore_place(*e)?,
      hir::PlaceKind::Deref(e) => self.expr(*e, None)?,
      hir::PlaceKind::Error => unreachable!()
    }
    Ok(())
  }

  fn expr_place(&mut self, e: hir::Expr<'a>) -> Block<Place> {
    Ok(match e.k.0 {
      hir::ExprKind::Var(v, gen) => {
        let v = self.tr_gen(v, gen);
        self.vars.get(&v).cloned().unwrap_or_else(|| v.into())
      }
      hir::ExprKind::Index(args) => {
        let ([arr, idx], hyp_or_n) = *args;
        self.expr_place(arr)?.proj(self.index_projection(idx, hyp_or_n)?)
      }
      hir::ExprKind::Slice(args) => {
        let ([arr, idx, len], hyp_or_n) = *args;
        self.expr_place(arr)?.proj(self.slice_projection(idx, len, hyp_or_n)?)
      }
      hir::ExprKind::Proj(pk, e, i) =>
        self.expr_place(*e)?.proj(Projection::Proj(pk.into(), i)),
      hir::ExprKind::Ref(e) => self.place(*e)?,
      hir::ExprKind::Deref(e) =>
        Place::local(self.as_temp(*e)?).proj(Projection::Deref),
      _ => Place::local(self.as_temp(e)?)
    })
  }

  fn copy_or_move(&mut self, e: hir::Expr<'a>) -> Block<Operand> {
    let copy = e.ty().is_copy();
    let p = self.expr_place(e)?;
    Ok(if copy {Operand::Copy(p)} else {Operand::Move(p)})
  }

  fn copy_or_ref(&mut self, e: hir::Place<'a>) -> Block<Operand> {
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
      hir::ExprKind::ITrue => Constant::itrue().into(),
      hir::ExprKind::Bool(b) => Constant::bool(b).into(),
      hir::ExprKind::Int(n) => let_unchecked!(ty::TyKind::Int(ity) = e.ty().k,
        Constant::int(ity, n.clone()).into()),
      hir::ExprKind::Const(a) => Constant {ety: self.tr(e.k.1), k: ConstKind::Const(a)}.into(),
      hir::ExprKind::Call(ref call)
      if matches!(call.rk, hir::ReturnKind::Unit | hir::ReturnKind::Unreachable) => {
        self.expr(e, None)?;
        Constant::unit().into()
      }
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
      hir::ExprKind::ITrue |
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
      hir::ExprKind::Eq(ty, inv, e1, e2) => {
        let ty = self.tr(ty);
        let v1 = self.as_temp(*e1)?;
        let v2 = self.as_temp(*e2)?;
        RValue::Eq(ty, inv, v1.into(), v2.into())
      }
      hir::ExprKind::Sn(x, h) => {
        let vx = self.as_temp(*x)?;
        let vh = h.map(|h| self.as_temp(*h)).transpose()?.map(|h| h.into());
        RValue::Pun(PunKind::Sn(vh), vx.into())
      }
      hir::ExprKind::List(lk, es) => {
        let vs = es.into_iter().map(|e| self.as_temp(e).map(|v| v.into()))
          .collect::<Block<Box<[_]>>>()?;
        match lk {
          hir::ListKind::List | hir::ListKind::Struct => RValue::List(vs),
          hir::ListKind::Array => RValue::Array(vs),
          hir::ListKind::And => {
            let mut vs = vs.into_vec();
            let_unchecked!(v as Operand::Move(v) = vs.remove(0));
            RValue::Pun(PunKind::And(vs), v)
          }
        }
      }
      hir::ExprKind::Ghost(e) => RValue::Ghost(self.copy_or_move(*e)?),
      hir::ExprKind::Borrow(e) => RValue::Borrow(self.place(*e)?),
      hir::ExprKind::Mm0(types::Mm0Expr {subst, ..}) => RValue::Mm0(
        subst.into_iter().map(|e| self.as_temp(e).map(|v| v.into()))
          .collect::<Block<Box<[_]>>>()?),
      hir::ExprKind::Cast(e, ty, hir::CastKind::Int) =>
        RValue::Cast(CastKind::Int, self.operand(*e)?, self.tr(ty)),
      hir::ExprKind::Cast(e, _, hir::CastKind::Ptr) =>
        RValue::Pun(PunKind::Ptr, self.expr_place(*e)?),
      hir::ExprKind::Cast(e, ty, hir::CastKind::Subtype(h)) => {
        let e = self.operand(*e)?;
        let ty = self.tr(ty);
        RValue::Cast(CastKind::Subtype(self.operand(*h)?), e, ty)
      }
      hir::ExprKind::Cast(e, ty, hir::CastKind::Wand(h)) => {
        let e = self.operand(*e)?;
        let ty = self.tr(ty);
        RValue::Cast(CastKind::Wand(h.map(|h| self.operand(*h)).transpose()?), e, ty)
      }
      hir::ExprKind::Cast(e, ty, hir::CastKind::Mem(h)) => {
        let e = self.operand(*e)?;
        let ty = self.tr(ty);
        RValue::Cast(CastKind::Mem(self.operand(*h)?), e, ty)
      }
      hir::ExprKind::Uninit => Constant::uninit_core(self.tr(e.k.1 .1)).into(),
      hir::ExprKind::Sizeof(ty) => Constant::sizeof(self.tr(ty)).into(),
      hir::ExprKind::Typeof(e) => RValue::Typeof(self.operand(*e)?),
      hir::ExprKind::Assert(e) => if let Some(pe) = e.k.1 .0 {
        let e = self.operand(*e)?;
        let cond = self.tr(pe);
        self.assert(e, cond).into()
      } else {
        let v = self.as_temp(*e)?;
        self.assert(Operand::Move(v.into()), Rc::new(ExprKind::Var(v))).into()
      }
      hir::ExprKind::Assign {..} => {
        self.expr(e, None)?;
        Constant::unit().into()
      }
      hir::ExprKind::Call(ref call)
      if matches!(call.rk, hir::ReturnKind::Struct(_)) => {
        let_unchecked!(call as hir::ExprKind::Call(call) = e.k.0);
        let_unchecked!(n as hir::ReturnKind::Struct(n) = call.rk);
        let dest = (0..n).map(|_| PreVar::Ok(self.fresh_var())).collect::<Vec<_>>();
        self.expr_call(call, e.k.1 .1, &dest)?;
        RValue::List(dest.into_iter().map(|v| {
          let_unchecked!(PreVar::Ok(v) = v, v.into())
        }).collect())
      }
      hir::ExprKind::Call(_) => self.operand(e)?.into(),
      hir::ExprKind::Mm0Proof(p) => Constant::mm0_proof(self.tr(e.k.1 .1), p.clone()).into(),
      hir::ExprKind::While(while_) => self.rvalue_while(*while_, e.k.1)?,
      hir::ExprKind::Unreachable(_) |
      hir::ExprKind::Jump(_, _, _, _) |
      hir::ExprKind::Break(_, _) |
      hir::ExprKind::Return(_) |
      hir::ExprKind::UnpackReturn(_) => {
        self.expr(e, None)?;
        unreachable!()
      }
      hir::ExprKind::If {..} | hir::ExprKind::Block(_) |
      hir::ExprKind::Infer(_) | hir::ExprKind::Error => unreachable!(),
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
      let rel = !ety.1.ghostly();
      let (e, ty) = self.tr(ety);
      self.push_stmt(Statement::Let(LetKind::Let(v, rel, e), ty, rv.into()));
      Ok(r)
    } else { f(self, dest) }
  }

  fn expr_unit(&mut self, dest: Dest) {
    if let Some(v) = dest {
      let rv = Constant::unit();
      let (e, ty) = rv.ety.clone();
      let v = self.tr(v);
      self.push_stmt(Statement::Let(LetKind::Let(v, false, e), ty, rv.into()));
    }
  }

  fn expr(&mut self, e: hir::Expr<'a>, dest: Dest) -> Block<()> {
    self.fulfill_unit_dest(e.k.1, dest, |this, dest| {
      match e.k.0 {
        hir::ExprKind::If {hyp, cond, cases, gen, muts} =>
          return this.expr_if(hyp, *cond, *cases, gen, muts, dest),
        hir::ExprKind::Block(bl) => return this.block(bl, dest),
        hir::ExprKind::Call(ref call) if matches!(call.rk, hir::ReturnKind::One) => {
          let_unchecked!(call as hir::ExprKind::Call(call) = e.k.0);
          return this.expr_call(call, e.k.1 .1, &[dest.unwrap_or(PreVar::Fresh)])
        }
        _ => {}
      }
      match dest {
        None => match e.k.0 {
          hir::ExprKind::Unit |
          hir::ExprKind::ITrue |
          hir::ExprKind::Var(_, _) |
          hir::ExprKind::Const(_) |
          hir::ExprKind::Bool(_) |
          hir::ExprKind::Int(_) |
          hir::ExprKind::Uninit |
          hir::ExprKind::Sizeof(_) => {}
          hir::ExprKind::Unop(_, e) |
          hir::ExprKind::Proj(_, e, _) |
          hir::ExprKind::Rval(e) |
          hir::ExprKind::Deref(e) |
          hir::ExprKind::Ghost(e) |
          hir::ExprKind::Cast(e, _, _) |
          hir::ExprKind::Typeof(e) => return this.expr(*e, None),
          hir::ExprKind::Ref(e) |
          hir::ExprKind::Borrow(e) => return this.ignore_place(*e),
          hir::ExprKind::Binop(_, e1, e2) |
          hir::ExprKind::Eq(_, _, e1, e2) => {
            this.expr(*e1, None)?;
            this.expr(*e2, None)?;
          }
          hir::ExprKind::Sn(e1, h) => {
            this.expr(*e1, None)?;
            if let Some(h) = h { this.expr(*h, None)?; }
          }
          hir::ExprKind::Index(args) => {
            let ([arr, idx], hyp_or_n) = *args;
            this.expr(arr, None)?;
            this.expr(idx, None)?;
            if let Ok(hyp) = hyp_or_n { this.expr(hyp, None)?; }
          }
          hir::ExprKind::Slice(args) => {
            let ([arr, idx, len], hyp_or_n) = *args;
            this.expr(arr, None)?;
            this.expr(idx, None)?;
            this.expr(len, None)?;
            if let Ok(hyp) = hyp_or_n { this.expr(hyp, None)?; }
          }
          hir::ExprKind::List(_, es) => for e in es { this.expr(e, None)? }
          hir::ExprKind::Mm0(e) => for e in e.subst { this.expr(e, None)? }
          hir::ExprKind::Assert(_) => {
            this.expr(e, Some(PreVar::Fresh))?;
          }
          hir::ExprKind::Assign {lhs, rhs, map, gen} => {
            let lhs = this.place(*lhs)?;
            let rhs = this.operand(*rhs)?;
            let varmap = map.iter()
              .map(|&(new, old, _)| (old, this.tr(new))).collect::<HashMap<_, _>>();
            this.tr.add_gen(this.tr.cur_gen, gen, varmap);
            let vars = map.into_vec().into_iter().map(|(new, _, ety)| Rename {
              from: this.tr(new),
              to: this.tr_gen(new, gen),
              rel: true,
              ety: this.tr_gen(ety, gen)
            }).collect::<Box<[_]>>();
            this.tr.cur_gen = gen;
            this.push_stmt(Statement::Assign(lhs, rhs, vars))
          }
          hir::ExprKind::Mm0Proof(_) |
          hir::ExprKind::While {..} => { this.rvalue(e)?; }
          hir::ExprKind::Call(call) => match call.rk {
            hir::ReturnKind::Unreachable |
            hir::ReturnKind::Unit => this.expr_call(call, e.k.1 .1, &[])?,
            hir::ReturnKind::One => unreachable!(),
            hir::ReturnKind::Struct(n) =>
              this.expr_call(call, e.k.1 .1, &vec![PreVar::Fresh; n.into()])?,
          }
          hir::ExprKind::Unreachable(h) => {
            let h = this.as_temp(*h)?;
            this.cur_block().terminate(Terminator::Unreachable(h.into()));
            return Err(Diverged)
          }
          hir::ExprKind::Jump(lab, i, es, _variant) => {
            let (jp, jumps) = this.labels.iter()
              .rfind(|p| p.0 == lab).expect("missing label")
              .1.jumps.as_ref().expect("label does not expect jump");
            let (tgt, args) = jumps[usize::from(i)].clone();
            let jb = JoinBlock(tgt, jp.clone());
            let args = args.iter().zip(es).map(|(&(v, r), e)| {
              Ok((v, r, this.operand(e)?))
            }).collect::<Block<Vec<_>>>()?;
            this.join(&jb, args)
          }
          hir::ExprKind::Break(lab, e) => {
            let (jb, dest) = this.labels.iter()
              .rfind(|p| p.0 == lab).expect("missing label")
              .1.brk.as_ref().expect("label does not expect break").clone();
            let args = match dest {
              None => { this.expr(*e, None)?; vec![] }
              Some(v) => vec![(v, !e.k.1 .1.ghostly(), this.operand(*e)?)]
            };
            this.join(&jb, args)
          }
          hir::ExprKind::Return(es) =>
            match this.expr_return(|_| es.into_iter(), Self::expr_place)? {}
          hir::ExprKind::UnpackReturn(e) => {
            let pl = this.expr_place(*e)?;
            match this.expr_return(|n| 0..n.try_into().expect("overflow"), |_, i| Ok({
              let mut pl = pl.clone();
              pl.proj.push(Projection::Proj(ListKind::Struct, i));
              pl
            }))? {}
          }
          hir::ExprKind::If {..} | hir::ExprKind::Block(_) |
          hir::ExprKind::Infer(_) | hir::ExprKind::Error => unreachable!()
        }
        Some(dest) => {
          let ety = e.k.1;
          let rv = this.rvalue(e)?;
          let dest = this.tr(dest);
          let rel = !ety.1.ghostly();
          let (e, ty) = this.tr(ety);
          this.push_stmt(Statement::Let(LetKind::Let(dest, rel, e), ty, rv))
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
      TuplePatternKind::Tuple(pats, mk, _) => {
        let pk = match mk {
          TupleMatchKind::Unit | TupleMatchKind::True => return,
          TupleMatchKind::List | TupleMatchKind::Struct => ListKind::Struct,
          TupleMatchKind::Array => ListKind::Array,
          TupleMatchKind::And => ListKind::And,
          TupleMatchKind::Sn => ListKind::Sn,
          TupleMatchKind::Own => let_unchecked!([vpat, hpat] = *pats, {
            let tgt = self.tr(pat.k.ty());
            let v = self.tr.tr_opt_var(vpat.k.var());
            let h = self.tr.tr_opt_var(hpat.k.var());
            let vty = vpat.k.ty();
            let lk = LetKind::Own([
              (v, !vty.ghostly(), self.tr(vty)), (h, true, self.tr(hpat.k.ty()))]);
            self.push_stmt(Statement::Let(lk, tgt, src.clone().into()));
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

  fn push_args_raw(&mut self,
    args: &[hir::Arg<'a>], mut f: impl FnMut(ty::ArgAttr, VarId, &Ty)
  ) -> Vec<(VarId, bool)> {
    let mut vs = Vec::with_capacity(args.len());
    for arg in args {
      if let hir::ArgKind::Lam(pat) = arg.1 {
        let var = self.tr(pat.k.var().map_or(PreVar::Fresh, PreVar::Pre));
        let ty = pat.k.ty();
        vs.push((var, !ty.ghostly()));
        let ty = self.tr(ty);
        f(arg.0, var, &ty);
        self.extend_ctx(var, !arg.0.contains(ty::ArgAttr::GHOST), (None, ty));
      }
    }
    vs
  }

  fn push_args(&mut self,
    args: Box<[hir::Arg<'a>]>, f: impl FnMut(ty::ArgAttr, VarId, &Ty)
  ) -> (BlockId, Rc<[(VarId, bool)]>) {
    let vs = self.push_args_raw(&args, f);
    let bl = self.new_block();
    self.cur_block = bl;
    let mut pats = vec![];
    (|| -> Block<()> {
      let mut it = vs.iter();
      for arg in args.into_vec() {
        match arg.1 {
          hir::ArgKind::Lam(pat) => {
            let v = unwrap_unchecked!(it.next()).0;
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
    })().expect("pure expressions can't diverge");
    for pat in pats.into_iter().rev() { self.tr.finish_tup_pat(pat) }
    (bl, vs.into())
  }

  fn join_args(&mut self, ctx: CtxId, &(gen, ref muts): &JoinPoint,
    args: &mut Vec<(VarId, bool, Operand)>
  ) {
    args.extend(muts.iter().filter_map(|&v| {
      let from = self.tr(v);
      let to = self.tr_gen(v, gen);
      if from == to {return None}
      let r = self.cfg.ctxs.rev_iter(ctx).find(|&&(u, _, _)| from == u)?.1;
      Some((to, r, from.into()))
    }));
  }

  fn join(&mut self, &JoinBlock(tgt, ref jp): &JoinBlock, mut args: Vec<(VarId, bool, Operand)>) {
    let ctx = self.cfg[tgt].ctx;
    self.join_args(ctx, jp, &mut args);
    self.cur_block().terminate(Terminator::Jump(tgt, args))
  }

  fn let_stmt(&mut self, lhs: ty::TuplePattern<'a>, rhs: hir::Expr<'a>) -> Block<()> {
    if_chain! {
      if let hir::ExprKind::Call(hir::Call {rk: hir::ReturnKind::Struct(n), ..}) = rhs.k.0;
      if let ty::TuplePatternKind::Tuple(pats, _, _) = lhs.k;
      if pats.len() == usize::from(n);
      then {
        let_unchecked!(call as hir::ExprKind::Call(call) = rhs.k.0);
        let dest = pats.iter().map(|&pat| {
          pat.k.var().map_or_else(|| PreVar::Ok(self.fresh_var()), PreVar::Pre)
        }).collect::<Vec<_>>();
        self.expr_call(call, rhs.k.1 .1, &dest)?;
        for (&pat, v) in pats.iter().zip(dest) {
          let v = self.tr(v);
          self.tup_pat(pat, &mut v.into());
        }
      } else {
        let v = lhs.k.var().map_or_else(|| PreVar::Ok(self.fresh_var()), PreVar::Pre);
        self.expr(rhs, Some(v))?;
        let v = self.tr(v);
        self.tup_pat(lhs, &mut v.into());
      }
    }
    Ok(())
  }

  fn stmt(&mut self, stmt: hir::Stmt<'a>, brk: Option<&(JoinBlock, BlockDest)>) -> Block<()> {
    match stmt.k {
      hir::StmtKind::Let { lhs, rhs } => self.let_stmt(lhs, rhs),
      hir::StmtKind::Expr(e) => self.expr(hir::Spanned {span: stmt.span, k: e}, None),
      hir::StmtKind::Label(v, labs) => {
        let base_ctx = self.cur_ctx;
        let base_bl = self.cur_block;
        let base_gen = self.tr.cur_gen;
        let &(ref brk, dest) = brk.expect("we need a join point for the break here");
        let mut bodies = vec![];
        let jumps = labs.into_vec().into_iter().map(|lab| {
          let (bl, args) = self.push_args(lab.args, |_, _, _| {});
          bodies.push(lab.body);
          self.cur_ctx = base_ctx;
          (bl, args)
        }).collect();
        self.labels.push((v, LabelGroupData {
          jumps: Some(((base_gen, brk.1 .1.clone()), Rc::clone(&jumps))),
          brk: Some((brk.clone(), dest))
        }));
        for (&(bl, _), body) in jumps.iter().zip(bodies) {
          self.cur_ctx = self.cfg[bl].ctx;
          self.cur_block = bl;
          self.tr.cur_gen = base_gen;
          if let Ok(()) = self.block(body, dest.map(PreVar::Ok)) {
            self.join(brk, match dest { None => vec![], Some(v) => vec![(v, true, v.into())] })
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
    let jb = if stmts.iter().any(|s| matches!(s.k, hir::StmtKind::Label(..))) {
      let dest2 = dest.map(|v| self.tr_gen(v, gen));
      Some((JoinBlock(self.new_block(), (gen, muts.into())), dest2))
    } else { None };
    let r = (|| {
      for stmt in stmts { self.stmt(stmt, jb.as_ref())? }
      if let Some(e) = expr { self.expr(*e, dest) }
      else { self.expr_unit(dest); Ok(()) }
    })();
    self.labels.truncate(reset);
    if let Some((JoinBlock(tgt, (gen, _)), _)) = jb {
      self.set((tgt, self.cfg[tgt].ctx, gen));
      Ok(())
    } else { r }
  }

  fn expr_if(&mut self,
    hyp: Option<[HVarId; 2]>,
    cond: hir::Expr<'a>,
    [e_tru, e_fal]: [hir::Expr<'a>; 2],
    gen: GenId,
    muts: Vec<HVarId>,
    dest: Dest,
  ) -> Block<()> {
    // In the general case, we generate:
    //   v_cond := cond
    //   if v_cond {h. goto tru(h)} else {h. goto fal(h)}
    // tru(h: cond):
    //   v := e_tru
    //   goto after(v)
    // fal(h: !cond):
    //   v := e_fal
    //   goto after(v)
    // after(dest: T):
    let pe = cond.k.1 .0;
    //   v_cond := cond
    let v_cond = self.as_temp(cond)?;
    let pe = pe.map_or_else(|| Rc::new(ExprKind::Var(v_cond)), |e| self.tr(e));
    let (vh1, vh2) = match hyp {
      None => (self.fresh_var(), self.fresh_var()),
      Some([vh1, vh2]) => (self.tr(vh1), self.tr(vh2)),
    };
    let (_, base_ctx, base_gen) = self.cur();
    // tru_ctx is the current context with `vh: cond`
    let tru_ctx = self.cfg.ctxs.extend(base_ctx, vh1, false,
      (Some(Rc::new(ExprKind::Unit)), Rc::new(TyKind::Pure(pe.clone()))));
    let tru = self.cfg.new_block(tru_ctx);
    // fal_ctx is the current context with `vh: !cond`
    let fal_ctx = self.cfg.ctxs.extend(base_ctx, vh2, false,
      (Some(Rc::new(ExprKind::Unit)), Rc::new(TyKind::Not(Rc::new(TyKind::Pure(pe))))));
    let fal = self.cfg.new_block(fal_ctx);
    //   if v_cond {vh. goto tru(vh)} else {vh. goto fal(vh)}
    self.cur_block().terminate(Terminator::If(v_cond.into(), [(vh1, tru), (vh2, fal)]));

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
    //     v_cond := cond
    //     if v_cond {h. goto tru(h)} else {h. goto fal(h)}
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
        let join = JoinBlock(self.new_block(), (gen, muts.into()));
        self.set(tru);
        self.join(&join, match trans { None => vec![], Some(v) => vec![(v, true, v.into())] });
        self.set(fal);
        self.join(&join, match trans { None => vec![], Some(v) => vec![(v, true, v.into())] });
        // And the after block is the end of the statement
        self.set((join.0, base_ctx, gen));
      }
    }
    Ok(())
  }

  fn rvalue_while(&mut self,
    hir::While { label, hyp, cond, var: _, body, gen, muts, trivial }: hir::While<'a>,
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
      Some((JoinBlock(self.new_block(), (gen, muts.clone())), None))
    } else { None };

    // Set things up so that `(continue label)` jumps to `base`,
    // and `(break label)` jumps to `after`
    self.labels.push((label, LabelGroupData {
      jumps: Some(((base_gen, muts.clone()), Rc::new([(base_bl, Rc::new([]))]))),
      brk: brk.clone()
    }));

    // `exit_point` captures the exit condition produced from inside the loop.
    let mut exit_point = Err(Diverged);
    // This is the body of the loop. We catch divergence here because if the execution of `cond` or
    // `body` diverges we still have to construct `after` and anything after that, provided that
    // `after` itself is reachable (which we signal by `exit_point` having a value).
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
        // We never set `exit_point`, so it remains `Err(Diverged)` because it is unreachable.
        self.expr(*cond, None)?;
        if let (Some(pe), Some(hyp)) = (pe, hyp) {
          let pe = self.tr(pe);
          let vh = self.tr(hyp);
          self.push_stmt(Statement::Let(
            LetKind::Let(vh, false, Some(Rc::new(ExprKind::Unit))),
            Rc::new(TyKind::Pure(pe)),
            Constant::itrue().into()));
        }
      } else {
        // Otherwise, this is a proper while loop.
        //   v_cond := cond
        let v_cond = self.as_temp(*cond)?;
        let pe = pe.map_or_else(|| Rc::new(ExprKind::Var(v_cond)), |e| self.tr(e));
        let vh = self.tr(hyp.map_or(PreVar::Fresh, PreVar::Pre));
        let test = self.cur();
        // tru_ctx is the current context with `vh: cond`
        let tru_ctx = self.cfg.ctxs.extend(test.1, vh, false,
          (Some(Rc::new(ExprKind::Unit)), Rc::new(TyKind::Pure(pe.clone()))));
        let tru = self.cfg.new_block(tru_ctx);
        // fal_ctx is the current context with `vh: !cond`
        let fal_ctx = self.cfg.ctxs.extend(test.1, vh, false,
          (Some(Rc::new(ExprKind::Unit)), Rc::new(TyKind::Not(Rc::new(TyKind::Pure(pe))))));
        let fal = self.cfg.new_block(fal_ctx);
        //   if v_cond {vh. goto main(vh)} else {vh. goto after(vh)}
        self.cur_block().terminate(Terminator::If(v_cond.into(), [(vh, tru), (vh, fal)]));

        // If `brk` is set (to `after`) then that means `has_break` is true so we want to jump to
        // `after` and ignore the `vh: !cond` in the false case.
        if let Some((ref join, _)) = brk {
          // We don't set `exit_point` because it is ignored in this case
          self.set((fal, fal_ctx, test.2));
          self.join(join, vec![]);
        } else {
          // Set `exit_point` to the `after` block (the false branch of the if),
          // and `vh: !cond` is the output
          exit_point = Ok(((fal, fal_ctx, test.2), vh.into()));
        }
        // Prepare to generate the `main` label
        self.set((tru, tru_ctx, test.2));
      }
      //   _ := body
      self.block(*body, None)?;
      //   goto base
      self.join(&JoinBlock(base_bl, (base_gen, muts)), vec![]);
      // We've diverged, there is nothing more to do in the loop
      Err(Diverged)
    })().expect_err("it's a loop");

    if let Some((JoinBlock(tgt, (gen, _)), _)) = self.labels.pop().expect("underflow").1.brk {
      // If `has_break` is true, then the final location after the while loop is the join point
      // `after`, and the context is `base_ctx` because the while loop doesn't add any bindings
      self.set((tgt, base_ctx, gen));
      // We return `()` from the loop expression
      Ok(Constant::unit().into())
    } else {
      // If `has_break` is false, then the final location is the false branch inside the loop,
      // which we may or may not have reached before diverging (if for example the loop condition
      // diverges). If we did reach it then we pull out the position and return the value.
      exit_point.map(|(pos, rv)| { self.set(pos); rv })
    }
  }

  fn expr_call(&mut self,
    hir::Call {f, side_effect: se, tys, args, variant: _, gen, rk}: hir::Call<'a>,
    tgt: ty::Ty<'a>,
    dest: &[PreVar],
  ) -> Block<()> {
    let tys = self.tr(tys);
    let args = args.into_iter().map(|e| Ok((!e.k.1 .1.ghostly(), self.operand(e)?)))
      .collect::<Block<Box<[_]>>>()?;
    self.tr.cur_gen = gen;
    let vars: Box<[_]> = match rk {
      hir::ReturnKind::Unreachable => {
        let v = self.fresh_var();
        self.extend_ctx(v, false, (None, Rc::new(TyKind::False)));
        let bl = self.new_block();
        self.cur_block().terminate(Terminator::Call {
          f: f.k, se, tys, args, reach: false, tgt: bl, rets: Box::new([v])
        });
        let bl = &mut self.cfg[bl];
        bl.reachable = false;
        bl.terminate(Terminator::Unreachable(v.into()));
        return Err(Diverged)
      }
      hir::ReturnKind::Unit => Box::new([]),
      hir::ReturnKind::One => {
        let v = self.tr(dest[0]);
        let vr = !tgt.ghostly();
        let tgt = self.tr(tgt);
        self.extend_ctx(v, vr, (None, tgt));
        Box::new([v])
      }
      hir::ReturnKind::Struct(_) => {
        let tgt = self.tr(tgt);
        let argtys = if let TyKind::Struct(args) = &*tgt { &**args } else { unreachable!() };
        let mut alph = Alpha::default();
        dest.iter().zip(argtys).map(|(&dest, &Arg {attr, var, ref ty})| {
          let v = self.tr(dest);
          let ty = alph.alpha(ty);
          self.extend_ctx(v, !attr.contains(ArgAttr::GHOST), (None, ty));
          if !attr.contains(ArgAttr::NONDEP) { alph.push(var, v) }
          v
        }).collect()
      }
    };
    let bl = self.new_block();
    self.cur_block().terminate(Terminator::Call {
      f: f.k, se, tys, args, reach: true, tgt: bl, rets: vars
    });
    self.cur_block = bl;
    Ok(())
  }

  fn expr_return<T, I: ExactSizeIterator<Item=T>>(&mut self,
    es: impl FnOnce(usize) -> I,
    mut f: impl FnMut(&mut Self, T) -> Block<Place>,
  ) -> Block<std::convert::Infallible> {
    let args = self.returns.as_ref().expect("can't return here").clone();
    let args = es(args.len()).zip(&*args).map(|(e, &(v, r))| {
      Ok((v, r, f(self, e)?.into()))
    }).collect::<Block<Vec<_>>>()?;
    self.cur_block().terminate(Terminator::Return(args));
    Err(Diverged)
  }

  /// Build the MIR for an item (function, procedure, or static variable).
  pub(crate) fn build_item(mut self,
    mir: &mut HashMap<Symbol, Proc>,
    init: &mut Initializer,
    it: hir::Item<'a>
  ) -> Option<Symbol> {
    match it.k {
      hir::ItemKind::Proc { kind, name, tyargs, args, gen, rets, variant: _, body } => {
        fn tr_attr(attr: ty::ArgAttr) -> ArgAttr {
          if attr.contains(ty::ArgAttr::NONDEP) { ArgAttr::NONDEP } else { ArgAttr::empty() }
        }
        if let hir::ProcKind::Intrinsic(_) = kind { return None }
        let mut args2 = Vec::with_capacity(args.len());
        assert_eq!(self.push_args(args, |attr, var, ty| {
          args2.push(Arg {attr: tr_attr(attr), var, ty: ty.clone()})
        }).0, BlockId::ENTRY);
        self.tr.cur_gen = gen;
        let mut rets2 = Vec::with_capacity(rets.len());
        let ret_vs = self.push_args_raw(&rets, |attr, var, ty| {
          rets2.push(Arg {attr: tr_attr(attr), var, ty: ty.clone()})
        });
        self.returns = Some(ret_vs.into());
        self.tr.cur_gen = GenId::ROOT;
        match self.block(body, None) {
          Ok(()) => unreachable!("bodies should end in unconditional return"),
          Err(Diverged) => {}
        }
        self.cfg.max_var = self.tr.next_var;
        mir.insert(name.k, Proc {
          kind,
          name: Spanned {span: name.span.clone(), k: name.k},
          tyargs,
          args: args2,
          rets: rets2,
          body: self.cfg,
        });
        Some(name.k)
      }
      hir::ItemKind::Global { lhs, rhs } => {
        mem::swap(&mut init.cfg, &mut self.cfg);
        self.tr.next_var = self.cfg.max_var;
        init.cur_block = (|| -> Block<BlockId> {
          self.cur_block = init.cur_block?;
          self.let_stmt(lhs, rhs)?;
          Ok(self.cur_block)
        })();
        self.cfg.max_var = self.tr.next_var;
        mem::swap(&mut init.cfg, &mut self.cfg);
        None
      }
    }
  }
}
