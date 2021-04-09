//! Build the mid-level IR from HIR
#![allow(unused)]
#![allow(clippy::unused_self, clippy::match_same_arms)]

use std::borrow::{Borrow, Cow};
use std::{cell::RefCell, rc::Rc, fmt::Debug, hash::{Hash, Hasher}, mem, ops::Index};
use std::result::Result as StdResult;
use std::convert::{TryFrom, TryInto};
use bumpalo::Bump;
use std::collections::{HashMap, hash_map::Entry};
use hir::{Context, ContextNext};
use itertools::Itertools;
use num::Signed;
use types::IntTy;
use crate::{AtomId, FileSpan, FormatEnv, LispVal, lisp::print::alphanumber, u32_as_usize};
use super::{Compiler, parser::try_get_fspan, types};
use types::{Binop, BinopType, FieldName, Mm0ExprNode, Size, Spanned, Unop, VarId, hir, ty, mir};
use types::entity::{Entity, ConstTc, GlobalTc, ProcTy, ProcTc, TypeTc, TypeTy};
use hir::GenId;
use ty::{TuplePattern, TuplePatternKind, TupleMatchKind};
use super::union_find::{UnifyCtx, UnifyKey, UnificationTable};
#[allow(clippy::wildcard_imports)] use mir::*;

type TrMap<K, V> = HashMap<K, Result<V, HashMap<GenId, V>>>;
#[derive(Default)]
struct Translator<'a> {
  tys: TrMap<ty::Ty<'a>, Ty>,
  exprs: TrMap<ty::Expr<'a>, Expr>,
  next_var: VarId,
  subst: HashMap<VarId, Expr>,
}

trait Translate<'a> {
  type Output;
  fn tr(self, _: &'_ mut Translator<'a>, gen: GenId) -> Self::Output;
}
trait TranslateBase<'a>: Sized {
  type Output;
  fn get_mut<'b>(_: &'b mut Translator<'a>) ->
    &'b mut TrMap<&'a ty::WithMeta<Self>, Rc<Self::Output>>;
  fn make(&'a self, _: &mut Translator<'a>, gen: GenId) -> Self::Output;
}

impl<'a> TranslateBase<'a> for ty::TyKind<'a> {
  type Output = TyKind;
  fn get_mut<'b>(t: &'b mut Translator<'a>) -> &'b mut TrMap<ty::Ty<'a>, Ty> { &mut t.tys }
  fn make(&'a self, tr: &mut Translator<'a>, gen: GenId) -> TyKind {
    macro_rules! tr {($e:expr) => {$e.tr(tr, gen)}}
    match *self {
      ty::TyKind::Unit => TyKind::Unit,
      ty::TyKind::True => TyKind::True,
      ty::TyKind::False => TyKind::False,
      ty::TyKind::Bool => TyKind::Bool,
      ty::TyKind::Var(v) => TyKind::Var(v),
      ty::TyKind::Int(ity) => TyKind::Int(ity),
      ty::TyKind::Array(ty, n) => TyKind::Array(tr!(ty), tr!(n)),
      ty::TyKind::Own(ty) => TyKind::Own(tr!(ty)),
      ty::TyKind::Ref(lft, ty) => TyKind::Ref(lft, tr!(ty)),
      ty::TyKind::RefSn(e) => TyKind::RefSn(tr!(e)),
      ty::TyKind::List(tys) => TyKind::List(tr!(tys)),
      ty::TyKind::Sn(a, ty) => TyKind::Sn(tr!(a), tr!(ty)),
      ty::TyKind::Struct(args) => tr.tr_struct(args, gen),
      ty::TyKind::All(pat, ty) => tr.tr_all(pat, ty, gen),
      ty::TyKind::Imp(p, q) => TyKind::Imp(tr!(p), tr!(q)),
      ty::TyKind::Wand(p, q) => TyKind::Wand(tr!(p), tr!(q)),
      ty::TyKind::Not(p) => TyKind::Not(tr!(p)),
      ty::TyKind::And(ps) => TyKind::And(tr!(ps)),
      ty::TyKind::Or(ps) => TyKind::Or(tr!(ps)),
      ty::TyKind::If(c, t, e) => TyKind::If(tr!(c), tr!(t), tr!(e)),
      ty::TyKind::Ghost(ty) => TyKind::Ghost(tr!(ty)),
      ty::TyKind::Uninit(ty) => TyKind::Uninit(tr!(ty)),
      ty::TyKind::Pure(e) => TyKind::Pure(tr!(e)),
      ty::TyKind::User(f, tys, es) => TyKind::User(f, tr!(tys), tr!(es)),
      ty::TyKind::Heap(e, v, ty) => TyKind::Heap(tr!(e), tr!(v), tr!(ty)),
      ty::TyKind::HasTy(e, ty) => TyKind::HasTy(tr!(e), tr!(ty)),
      ty::TyKind::Input => TyKind::Input,
      ty::TyKind::Output => TyKind::Output,
      ty::TyKind::Moved(ty) => TyKind::Moved(tr!(ty)),
      ty::TyKind::Infer(_) |
      ty::TyKind::Error => unreachable!(),
    }
  }
}
impl<'a> TranslateBase<'a> for ty::ExprKind<'a> {
  type Output = ExprKind;
  fn get_mut<'b>(t: &'b mut Translator<'a>) -> &'b mut TrMap<ty::Expr<'a>, Expr> { &mut t.exprs }
  fn make(&'a self, tr: &mut Translator<'a>, gen: GenId) -> ExprKind {
    macro_rules! tr {($e:expr) => {$e.tr(tr, gen)}}
    match *self {
      ty::ExprKind::Unit => ExprKind::Unit,
      ty::ExprKind::Var(v) => ExprKind::Var(v),
      ty::ExprKind::Const(c) => ExprKind::Const(c),
      ty::ExprKind::Bool(b) => ExprKind::Bool(b),
      ty::ExprKind::Int(n) => ExprKind::Int(n.clone()),
      ty::ExprKind::Unop(op, e) => ExprKind::Unop(op, tr!(e)),
      ty::ExprKind::Binop(op, e1, e2) => ExprKind::Binop(op, tr!(e1), tr!(e2)),
      ty::ExprKind::Index(a, i) => ExprKind::Index(tr!(a), tr!(i)),
      ty::ExprKind::Slice(a, i, l) => ExprKind::Slice(tr!(a), tr!(i), tr!(l)),
      ty::ExprKind::Proj(a, i) => ExprKind::Proj(tr!(a), i),
      ty::ExprKind::UpdateIndex(a, i, v) => ExprKind::UpdateIndex(tr!(a), tr!(i), tr!(v)),
      ty::ExprKind::UpdateSlice(a, i, l, v) => ExprKind::UpdateSlice(tr!(a), tr!(i), tr!(l), tr!(v)),
      ty::ExprKind::UpdateProj(a, i, v) => ExprKind::UpdateProj(tr!(a), i, tr!(v)),
      ty::ExprKind::List(es) => ExprKind::List(tr!(es)),
      ty::ExprKind::Array(es) => ExprKind::Array(tr!(es)),
      ty::ExprKind::Sizeof(ty) => ExprKind::Sizeof(tr!(ty)),
      ty::ExprKind::Ref(e) => ExprKind::Ref(tr!(e)),
      ty::ExprKind::Mm0(ref e) => ExprKind::Mm0(tr!(e)),
      ty::ExprKind::Call {f, tys, args} => ExprKind::Call {f, tys: tr!(tys), args: tr!(args)},
      ty::ExprKind::If {cond, then, els} => ExprKind::If {cond: tr!(cond), then: tr!(then), els: tr!(els)},
      ty::ExprKind::Infer(_) |
      ty::ExprKind::Error => unreachable!(),
    }
  }
}

impl<'a, T: TranslateBase<'a>> Translate<'a> for &'a ty::WithMeta<T> {
  type Output = Rc<T::Output>;
  fn tr(self, tr: &mut Translator<'a>, gen: GenId) -> Rc<T::Output> {
    if tr.subst.is_empty() {
      if let Some(v) = T::get_mut(tr).get(self) {
        match v {
          Ok(r) => return r.clone(),
          Err(m) => if let Some(r) = m.get(&gen) { return r.clone() }
        }
      }
      let r = Rc::new(T::make(&self.k, tr, gen));
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
      Rc::new(T::make(&self.k, tr, gen))
    }
  }
}

impl<'a, T: Translate<'a> + Copy> Translate<'a> for &'a [T] {
  type Output = Box<[T::Output]>;
  fn tr(self, tr: &mut Translator<'a>, gen: GenId) -> Box<[T::Output]> {
    self.iter().map(|&e| e.tr(tr, gen)).collect()
  }
}

impl<'a> Translate<'a> for ty::ExprTy<'a> {
  type Output = ExprTy;
  fn tr(self, tr: &mut Translator<'a>, gen: GenId) -> Self::Output {
    (self.0.ok().map(|e| e.tr(tr, gen)), self.1.tr(tr, gen))
  }
}

impl<'a> Translate<'a> for &'a ty::Mm0Expr<'a> {
  type Output = Mm0Expr;
  fn tr(self, tr: &mut Translator<'a>, gen: GenId) -> Mm0Expr {
    Mm0Expr { subst: self.subst.tr(tr, gen), expr: self.expr.clone() }
  }
}

impl<'a> Translator<'a> {
  fn fresh_var(&mut self) -> VarId {
    let n = self.next_var;
    self.next_var.0 += 1;
    n
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

  fn tr_all(&mut self, pat: ty::TuplePattern<'a>, ty: ty::Ty<'a>, gen: GenId) -> TyKind {
    if let Some(v) = pat.k.var() {
      TyKind::All(v, pat.k.ty().tr(self, gen), ty.tr(self, gen))
    } else {
      let v = self.fresh_var();
      let tgt = pat.k.ty().tr(self, gen);
      self.tr_tup_pat(pat, Rc::new(ExprKind::Var(v)));
      let ty = ty.tr(self, gen);
      self.finish_tup_pat(pat);
      TyKind::All(v, tgt, ty)
    }
  }

  fn tr_struct(&mut self, args: &'a [ty::Arg<'a>], gen: GenId) -> TyKind {
    let mut args2 = Vec::with_capacity(args.len());
    for &arg in args {
      match arg.k {
        (attr, ty::ArgKind::Lam(pat)) => {
          let mut attr2 = ArgAttr::empty();
          if attr.contains(ty::ArgAttr::NONDEP) { attr2 |= ArgAttr::NONDEP }
          if let Some(v) = pat.k.var() {
            args2.push(Arg {attr: attr2, var: v, ty: pat.k.ty().tr(self, gen)})
          } else {
            let v = self.fresh_var();
            let ty = pat.k.ty().tr(self, gen);
            self.tr_tup_pat(pat, Rc::new(ExprKind::Var(v)));
            args2.push(Arg {attr: attr2, var: v, ty})
          }
        }
        (_, ty::ArgKind::Let(pat, e)) => {
          let e = e.tr(self, gen);
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

type Dest<'a> = Option<(VarId, ty::ExprTy<'a>)>;

struct LabelData<'a> {
  jumps: Box<[()]>,
  break_: (BlockId, Dest<'a>),
}
struct BuildMir<'a> {
  compiler: &'a mut Compiler,
  alloc: &'a Bump,
  cfg: Cfg,
  tr: Translator<'a>,
  labels: Vec<(VarId, LabelData<'a>)>,
  vars: HashMap<VarId, Place>,
  cur_block: BlockId,
  cur_ctx: CtxId,
  cur_gen: GenId,
}

struct Diverged;

type Block<T> = Result<T, Diverged>;

impl<'a> BuildMir<'a> {
  fn new(compiler: &'a mut Compiler, alloc: &'a Bump, var_names: &[AtomId]) -> Self {
    Self {
      compiler, alloc,
      cfg: Cfg::default(),
      labels: vec![],
      tr: Translator {
        next_var: VarId(var_names.len().try_into().expect("overflow")),
        ..Default::default()
      },
      vars: Default::default(),
      cur_block: BlockId::ENTRY,
      cur_ctx: CtxId::ROOT,
      cur_gen: GenId::ROOT,
    }
  }

  fn fresh_var(&mut self) -> VarId { self.tr.fresh_var() }

  fn cur_block(&mut self) -> &mut BasicBlock { &mut self.cfg[self.cur_block] }

  fn new_block(&mut self) -> BlockId { self.cfg.new_block(self.cur_ctx) }

  fn push_stmt(&mut self, stmt: Statement) { self.cur_block().stmts.push(stmt) }

  fn tr<T: Translate<'a>>(&mut self, t: T) -> T::Output {
    t.tr(&mut self.tr, self.cur_gen)
  }

  fn rvalue(&mut self, e: hir::ExprKind<'a>) -> Block<RValue> {
    match e {
      hir::ExprKind::Unit => todo!(),
      hir::ExprKind::Var(_, _) => todo!(),
      hir::ExprKind::Const(_) => todo!(),
      hir::ExprKind::Global(_) => todo!(),
      hir::ExprKind::Bool(_) => todo!(),
      hir::ExprKind::Int(_) => todo!(),
      hir::ExprKind::Unop(_, _) => todo!(),
      hir::ExprKind::Binop(_, _, _) => todo!(),
      hir::ExprKind::Sn(_, _) => todo!(),
      hir::ExprKind::Index(_, _, _) => todo!(),
      hir::ExprKind::Slice(_, _) => todo!(),
      hir::ExprKind::Proj(_, _) => todo!(),
      hir::ExprKind::Rval(_) => todo!(),
      hir::ExprKind::Deref(_) => todo!(),
      hir::ExprKind::List(_, _) => todo!(),
      hir::ExprKind::Ghost(_) => todo!(),
      hir::ExprKind::Place(_) => todo!(),
      hir::ExprKind::Ref(_) => todo!(),
      hir::ExprKind::Mm0(_, _) => todo!(),
      hir::ExprKind::Cast(_, _, _, _) => todo!(),
      hir::ExprKind::Pun(_, _) => todo!(),
      hir::ExprKind::Uninit(_) => todo!(),
      hir::ExprKind::Sizeof(_) => todo!(),
      hir::ExprKind::Typeof(_, _) => todo!(),
      hir::ExprKind::Assert(_, _) => todo!(),
      hir::ExprKind::Assign {..} => {
        self.expr(e, None)?;
        Ok(RValue::Use(Operand::Const(Box::new(Constant::unit()))))
      }
      hir::ExprKind::Call { f, tys, args, variant } => todo!(),
      hir::ExprKind::Proof(_) => todo!(),
      hir::ExprKind::Block(_) => todo!(),
      hir::ExprKind::If { hyp, cond, cases, gen } => todo!(),
      hir::ExprKind::While { label, hyp, cond, var, body, has_break } => todo!(),
      hir::ExprKind::Unreachable(_) => todo!(),
      hir::ExprKind::Jump(_, _, _, _) => todo!(),
      hir::ExprKind::Break(_, _) => todo!(),
      hir::ExprKind::Return(_) => todo!(),
      hir::ExprKind::UnpackReturn(_) => todo!(),
      hir::ExprKind::Infer(_) | hir::ExprKind::Error => unreachable!()
    }
  }

  fn expr(&mut self, e: hir::ExprKind<'a>, dest: Dest<'a>) -> Block<()> {
    match dest {
      None => match e {
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
        hir::ExprKind::Typeof(e, _) => return self.expr(e.k, None),
        hir::ExprKind::Binop(_, e1, e2) => {
          self.expr(e1.k, None)?;
          self.expr(e2.k, None)?;
        }
        hir::ExprKind::Sn(e1, h) |
        hir::ExprKind::Pun(e1, h) => {
          self.expr(e1.k, None)?;
          if let Some(h) = h { self.expr(h.k, None)?; }
        }
        hir::ExprKind::Index(e1, e2, h) => {
          self.expr(e1.k, None)?;
          self.expr(e2.k, None)?;
          if let Some(h) = h { self.expr(h.k, None)?; }
        }
        hir::ExprKind::Slice(es, h) => {
          self.expr(es.0.k, None)?;
          self.expr(es.1.k, None)?;
          self.expr(es.2.k, None)?;
          if let Some(h) = h { self.expr(h.k, None)?; }
        }
        hir::ExprKind::List(es, _) => for e in es { self.expr(e.k, None)? }
        hir::ExprKind::Mm0(e, _) => for e in e.subst { self.expr(e.k, None)? }
        hir::ExprKind::Assert(_, ety) => {
          let v = self.fresh_var();
          self.expr(e, Some((v, ety)))?;
        }
        hir::ExprKind::Assign { lhs, rhs, oldmap, gen } => {

        }
        hir::ExprKind::Call { f, tys, args, variant } => {}
        hir::ExprKind::Proof(_) => {}
        hir::ExprKind::Block(_) => {}
        hir::ExprKind::If { hyp, cond, cases, gen } => {}
        hir::ExprKind::While { label, hyp, cond, var, body, has_break } => {}
        hir::ExprKind::Unreachable(_) => {}
        hir::ExprKind::Jump(_, _, _, _) => {}
        hir::ExprKind::Break(_, _) => {}
        hir::ExprKind::Return(_) => {}
        hir::ExprKind::UnpackReturn(_) => {}
        hir::ExprKind::Infer(_) | hir::ExprKind::Error => unreachable!()
      }
      Some((dest, ety)) => {
        let rv = self.rvalue(e)?;
        let ety = self.tr(ety);
        self.push_stmt(Statement::Let(dest, ety, rv))
      }
    }
    Ok(())
  }

  fn tup_pat(&mut self, pat: TuplePattern<'a>, src: &mut Place) {
    match pat.k {
      TuplePatternKind::Name(_, v, _) => {self.vars.insert(v, src.clone());}
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
            let v = vpat.k.var().unwrap_or_else(|| self.fresh_var());
            let h = hpat.k.var().unwrap_or_else(|| self.fresh_var());
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

  fn join(&mut self, tgt: BlockId, args: &[(VarId, Operand)]) {
    todo!()
  }

  fn stmt(&mut self, stmt: hir::StmtKind<'a>, break_: Option<(BlockId, Dest<'a>)>) -> Block<()> {
    match stmt {
      hir::StmtKind::Let { lhs, val, rhs } => {
        let v = lhs.k.var().unwrap_or_else(|| self.fresh_var());
        self.expr(rhs.k, Some((v, (val, lhs.k.ty()))))?;
        self.tup_pat(lhs, &mut Place::local(v));
        Ok(())
      }
      hir::StmtKind::Expr(e) => self.expr(e, None),
      hir::StmtKind::Label(v, labs) => {
        let ctx = self.cur_ctx;
        let break_ = break_.expect("we need a join point here");
        let jumps = labs.into_vec().into_iter().map(|hir::Label {args, variant: _, body}| {
          self.push_args(args);
          if let Ok(()) = self.block(body, break_.1) {
            self.join(break_.0, &[]);
          }
          self.cur_ctx = ctx;
        }).collect();
        self.labels.push((v, LabelData {jumps, break_}));
        todo!()
      }
    }
  }

  fn block(&mut self, hir::Block {stmts, expr}: hir::Block<'a>, dest: Dest<'a>) -> Block<()> {
    let jp = if stmts.iter().any(|s| matches!(s.k, hir::StmtKind::Label(..))) {
      Some((self.new_block(), dest))
    } else { None };
    match (|| -> Block<()> {
      for stmt in stmts { self.stmt(stmt.k, jp)? }
      self.expr(expr.map_or(hir::ExprKind::Unit, |e| e.k), dest)
    })() {
      Ok(()) => todo!(),
      Err(Diverged) => todo!(),
    }
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