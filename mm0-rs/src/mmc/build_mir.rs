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
      ty::TyKind::List(tys) => TyKind::List(tys.tr(tr)),
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

#[derive(Copy, Clone, Debug)]
enum PreVar {
  Ok(VarId),
  Pre(HVarId),
  Fresh,
}

type Dest = Option<PreVar>;

#[derive(Clone)]
struct BlockDest {
  tgt: BlockId,
  gen: GenId,
  muts: Rc<[HVarId]>,
  dest: Dest,
}
struct LabelData {
  jumps: Rc<[BlockId]>,
  brk: BlockDest,
}
struct BuildMir<'a> {
  compiler: &'a mut Compiler,
  alloc: &'a Bump,
  cfg: Cfg,
  tr: Translator<'a>,
  labels: Vec<(HVarId, LabelData)>,
  vars: HashMap<VarId, Place>,
  muts: HashSet<VarId>,
  cur_block: BlockId,
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
      tr,
      vars: Default::default(),
      muts: Default::default(),
      cur_block: BlockId::ENTRY,
      cur_ctx: CtxId::ROOT,
    }
  }

  fn fresh_var(&mut self) -> VarId { self.tr.fresh_var() }

  fn cur_block(&mut self) -> &mut BasicBlock { &mut self.cfg[self.cur_block] }

  fn new_block(&mut self) -> BlockId { self.cfg.new_block(self.cur_ctx) }

  fn push_stmt(&mut self, stmt: Statement) { self.cur_block().stmts.push(stmt) }

  fn tr<T: Translate<'a>>(&mut self, t: T) -> T::Output { t.tr(&mut self.tr) }

  fn tr_gen<T: Translate<'a>>(&mut self, t: T, gen: GenId) -> T::Output {
    self.tr.with_gen(gen, |tr| t.tr(tr))
  }

  fn rvalue(&mut self, e: hir::Expr<'a>) -> Block<RValue> {
    Ok(match e.k.0 {
      hir::ExprKind::Unit => RValue::Use(Operand::Const(Box::new(Constant::unit()))),
      hir::ExprKind::Var(v, gen) => {
        let v = Place::local(self.tr_gen(v, gen));
        RValue::Use(if e.ty().is_copy() {Operand::Copy(v)} else {Operand::Move(v)})
      }
      hir::ExprKind::Const(_) => todo!(),
      hir::ExprKind::Global(_) => todo!(),
      hir::ExprKind::Bool(b) => RValue::Use(Operand::Const(Box::new(Constant::bool(b)))),
      hir::ExprKind::Int(n) => let_unchecked!(ty::TyKind::Int(ity) = e.ty().k,
        RValue::Use(Operand::Const(Box::new(Constant::int(ity, n.clone()))))),
      hir::ExprKind::Unop(_, _) => todo!(),
      hir::ExprKind::Binop(_, _, _) => todo!(),
      hir::ExprKind::Sn(_, _) => todo!(),
      hir::ExprKind::Index(_, _, _) => todo!(),
      hir::ExprKind::Slice(_, _) => todo!(),
      hir::ExprKind::Proj(_, _) => todo!(),
      hir::ExprKind::Rval(_) => todo!(),
      hir::ExprKind::Deref(_) => todo!(),
      hir::ExprKind::List(_) => todo!(),
      hir::ExprKind::Ghost(_) => todo!(),
      hir::ExprKind::Place(_) => todo!(),
      hir::ExprKind::Ref(_) => todo!(),
      hir::ExprKind::Mm0(_, _) => todo!(),
      hir::ExprKind::Cast(_, _, _, _) => todo!(),
      hir::ExprKind::Pun(_, _) => todo!(),
      hir::ExprKind::Uninit(_) => todo!(),
      hir::ExprKind::Sizeof(_) => todo!(),
      hir::ExprKind::Typeof(_) => todo!(),
      hir::ExprKind::Assert(_) => todo!(),
      hir::ExprKind::Assign {..} => {
        self.expr(e, None)?;
        RValue::Use(Operand::Const(Box::new(Constant::unit())))
      }
      hir::ExprKind::Proof(_) => todo!(),
      hir::ExprKind::While {label, hyp, cond, var, body} => todo!(),
      hir::ExprKind::Unreachable(_) => {
        self.expr(e, None)?;
        unreachable!()
      }
      hir::ExprKind::Jump(_, _, _, _) => todo!(),
      hir::ExprKind::Break(_, _) => todo!(),
      hir::ExprKind::Return(_) => todo!(),
      hir::ExprKind::UnpackReturn(_) => todo!(),
      hir::ExprKind::If {..} | hir::ExprKind::Block(_) | hir::ExprKind::Call {..} |
      hir::ExprKind::Infer(_) | hir::ExprKind::Error => unreachable!()
    })
  }

  fn fulfill_unit_dest<R>(&mut self, ety: ty::ExprTy<'a>,
    dest: Dest, f: impl FnOnce(&mut Self, Dest) -> Block<R>
  ) -> Block<R> {
    if let Some(v) = dest {
      let r;
      let rv = match ety.1.k {
        ty::TyKind::Unit => {
          r = f(self, None)?;
          Box::new(Constant::unit())
        }
        ty::TyKind::True |
        ty::TyKind::Pure(&ty::WithMeta {k: ty::ExprKind::Bool(true), ..}) => {
          r = f(self, None)?;
          Box::new(Constant::itrue())
        }
        ty::TyKind::Uninit(ty) => {
          r = f(self, None)?;
          Box::new(Constant::uninit(self.tr(ty)))
        }
        _ => return f(self, dest),
      };
      let v = self.tr(v);
      let ety = self.tr(ety);
      self.push_stmt(Statement::Let(v, ety, RValue::Use(Operand::Const(rv))));
      Ok(r)
    } else { f(self, dest) }
  }

  fn expr_unit(&mut self, dest: Dest) {
    if let Some(v) = dest {
      let rv = Box::new(Constant::unit());
      let v = self.tr(v);
      self.push_stmt(Statement::Let(v, rv.ety.clone(),
        RValue::Use(Operand::Const(rv))));
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
          hir::ExprKind::Global(_) |
          hir::ExprKind::Bool(_) |
          hir::ExprKind::Int(_) |
          hir::ExprKind::Uninit(_) |
          hir::ExprKind::Sizeof(_) => {}
          hir::ExprKind::Unop(_, e) |
          hir::ExprKind::Proj(e, _) |
          hir::ExprKind::Rval(e) |
          hir::ExprKind::Deref(e) |
          hir::ExprKind::Ghost(e) |
          hir::ExprKind::Place(e) |
          hir::ExprKind::Ref(e) |
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
          hir::ExprKind::Index(e1, e2, h) => {
            this.expr(*e1, None)?;
            this.expr(*e2, None)?;
            if let Some(h) = h { this.expr(*h, None)?; }
          }
          hir::ExprKind::Slice(es, h) => {
            this.expr(es.0, None)?;
            this.expr(es.1, None)?;
            this.expr(es.2, None)?;
            if let Some(h) = h { this.expr(*h, None)?; }
          }
          hir::ExprKind::List(es) => for e in es { this.expr(e, None)? }
          hir::ExprKind::Mm0(e, _) => for e in e.subst { this.expr(e, None)? }
          hir::ExprKind::Assert(_) => {
            this.expr(e, Some(PreVar::Fresh))?;
          }
          hir::ExprKind::Assign {lhs, rhs, oldmap, gen} => {
            todo!()
          }
          hir::ExprKind::Proof(_) => {}
          hir::ExprKind::While {..} => { this.rvalue(e)?; }
          hir::ExprKind::Unreachable(h) => {
            let h = this.rvalue(*h)?;
            this.cur_block().terminate(Terminator::Unreachable(h));
            return Err(Diverged)
          }
          hir::ExprKind::Jump(_, _, _, _) => {}
          hir::ExprKind::Break(_, _) => {}
          hir::ExprKind::Return(_) => {}
          hir::ExprKind::UnpackReturn(_) => {}
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
          TupleMatchKind::List => ProjectionKind::List,
          TupleMatchKind::Struct => ProjectionKind::Struct,
          TupleMatchKind::Array => ProjectionKind::Array,
          TupleMatchKind::And => ProjectionKind::And,
          TupleMatchKind::Sn => ProjectionKind::Sn,
          TupleMatchKind::Own => let_unchecked!([vpat, hpat] = *pats, {
            let tgt = self.tr(pat.k.ty());
            let v = self.tr.tr_opt_var(vpat.k.var());
            let h = self.tr.tr_opt_var(hpat.k.var());
            let ek = ExElimKind::Own([(v, self.tr(vpat.k.ty())), (h, self.tr(hpat.k.ty()))]);
            self.push_stmt(Statement::ExElim(ek, tgt,
              RValue::Use(Operand::Move(src.clone()))));
            self.tup_pat(vpat, &mut Place::local(v));
            self.tup_pat(hpat, &mut Place::local(h));
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

  fn push_args(&mut self, args: &'a [ty::Arg<'a>]) {
    todo!()
  }

  fn join(&mut self,
    &BlockDest {tgt, gen, dest, ref muts}: &BlockDest,
    mut args: Vec<(VarId, Operand)>
  ) {
    let ctx = self.cfg[tgt].ctx;
    args.extend(muts.iter().filter_map(|&v| {
      let from = self.tr(v);
      let to = self.tr_gen(v, gen);
      if from == to || self.cfg.ctxs.rev_iter(ctx).all(|&(u, _)| from != u) {return None}
      Some((to, Operand::Move(Place::local(from))))
    }));
    self.cur_block().terminate(Terminator::Jump(tgt, args))
  }

  fn stmt(&mut self, stmt: hir::Stmt<'a>, brk: Option<&BlockDest>) -> Block<()> {
    match stmt.k {
      hir::StmtKind::Let { lhs, rhs } => {
        let v = lhs.k.var().map_or(PreVar::Fresh, PreVar::Pre);
        self.expr(rhs, Some(v))?;
        let v = self.tr(v);
        self.tup_pat(lhs, &mut Place::local(v));
        Ok(())
      }
      hir::StmtKind::Expr(e) => self.expr(hir::Spanned {span: stmt.span, k: e}, None),
      hir::StmtKind::Label(v, labs) => {
        let base_ctx = self.cur_ctx;
        let base_bl = self.cur_block;
        let base_gen = self.tr.cur_gen;
        let brk = brk.expect("we need a join point for the break here");
        let &BlockDest {tgt, gen, dest, ref muts} = brk;
        let (trans, dest) = match dest {
          None => (None, None),
          Some(v) => {
            let v = self.tr_gen(v, gen);
            (Some(v), Some(PreVar::Ok(v)))
          }
        };
        let jumps = labs.iter().map(|lab| {
          self.push_args(lab.args);
          let bl = self.new_block();
          self.cur_ctx = base_ctx;
          bl
        }).collect();
        self.labels.push((v, LabelData {jumps: Rc::clone(&jumps), brk: brk.clone()}));
        for (&bl, lab) in jumps.iter().zip(labs.into_vec()) {
          self.cur_ctx = self.cfg[bl].ctx;
          self.cur_block = bl;
          self.tr.cur_gen = base_gen;
          if let Ok(()) = self.block(lab.body, dest) {
            match trans {
              None => self.join(brk, vec![]),
              Some(v) => self.join(brk, vec![(v, Operand::Move(Place::local(v)))]),
            }
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
      Some(BlockDest {tgt: self.new_block(), gen, muts: muts.into(), dest})
    } else { None };
    let r = (|| {
      for stmt in stmts { self.stmt(stmt, jp.as_ref())? }
      if let Some(e) = expr { self.expr(*e, dest) }
      else { self.expr_unit(dest); Ok(()) }
    })();
    self.labels.truncate(reset);
    if let Some(BlockDest {tgt, gen, ..}) = jp {
      self.cur_block = tgt;
      self.cur_ctx = self.cfg[tgt].ctx;
      self.tr.cur_gen = gen;
      Ok(())
    } else { r }
  }

  fn expr_if(&mut self,
    hyp: Option<HVarId>,
    cond: hir::Expr<'a>,
    cases: [hir::Expr<'a>; 2],
    gen: GenId,
    muts: Vec<HVarId>,
    dest: Dest,
  ) -> Block<()> {
    drop((cond, cases, gen, muts, dest));
    todo!()
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