//! The storage pass, which computes the stack and register allocations for a function.

use std::collections::HashMap;
use std::convert::{Infallible, TryInto};

use crate::AtomId;
use super::super::union_find::{UnificationTable, UnifyCtx};
use super::types::{entity, mir, global};
use entity::{Entity, ConstTc};
#[allow(clippy::wildcard_imports)] use mir::*;

/// The result of storage analysis.
#[derive(Copy, Clone, Debug)]
pub struct StorageResult;

impl ExprKind {
  fn eval_u64(&self, ns: &HashMap<AtomId, Entity>) -> Option<u64> {
    match self {
        ExprKind::Const(c) => if_chain! {
          if let Some(Entity::Const(tc)) = ns.get(c);
          if let ConstTc::Checked {whnf, ..} = &tc.k;
          if let global::ExprKind::Int(n) = &**whnf;
          then { n.try_into().ok() }
          else { None }
        },
        ExprKind::Int(n) => n.try_into().ok(),
        // ExprKind::Unop(_, _) => None,
        // ExprKind::Binop(_, _, _) => None,
        _ => None,
    }
  }
}

impl TyKind {
  fn sizeof(&self, ns: &HashMap<AtomId, Entity>) -> Option<u64> {
    match self {
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
      TyKind::Ghost(_) => Some(0),
      TyKind::Bool => Some(1),
      TyKind::Own(_) |
      TyKind::RefSn(_) => Some(8),
      TyKind::User(_, _, _) | // TODO
      TyKind::Var(_) => None, // TODO: monomorphize first
      TyKind::Int(ity) => ity.size().bytes().map(Into::into),
      TyKind::Array(ty, n) => ty.sizeof(ns)?.checked_mul(n.eval_u64(ns)?),
      TyKind::Sn(_, ty) |
      TyKind::Uninit(ty) |
      TyKind::Moved(ty) |
      TyKind::All(_, _, ty) => ty.sizeof(ns),
      TyKind::Struct(args) => args.iter().try_fold(0_u64, |x, arg| {
        if arg.attr.contains(ArgAttr::GHOST) { Some(x) } else { x.checked_add(arg.ty.sizeof(ns)?) }
      }),
      TyKind::And(tys) |
      TyKind::Or(tys) => tys.iter().try_fold(0_u64, |x, ty| Some(x.max(ty.sizeof(ns)?))),
      TyKind::If(_, ty1, ty2) => Some(ty1.sizeof(ns)?.max(ty2.sizeof(ns)?))
    }
  }
}

impl Cfg {
  /// Compute the storage requirements of the CFG. This is a partitioning of the `VarId`'s into
  /// groups, as few as possible, such that all variables in a group have the same bit pattern at
  /// a given point in time, and any variable whose storage is overwritten by a later variable in
  /// the same group is dead.
  #[must_use] pub fn storage(&self, names: &HashMap<AtomId, Entity>) -> StorageResult {
    #[derive(Copy, Clone, Default)]
    struct Alloc(u64);
    impl UnifyCtx<Alloc> for () {
      type Error = Infallible;
      fn unify_values(&mut self, a: &Alloc, b: &Alloc) -> Result<Alloc, Self::Error> {
        Ok(Alloc(a.0.max(b.0)))
      }
    }
    type Table = UnificationTable<VarId, Alloc>;
    let mut visitor = CtxVisitor::default();
    let mut uf = Table::from_fn(self.max_var, |_| Alloc(0));
    let sizeof = |ty: &TyKind| ty.sizeof(names).expect("can't get size of type");
    for (_, bl) in self.blocks.enum_iter() {
      if bl.is_dead() { continue }
      let visit = |uf: &mut Table, v, ty: &TyKind| {
        let _ = uf.unify_var_value(&mut (), v, &Alloc(sizeof(ty)));
      };
      visitor.visit(&self.ctxs, bl.ctx, |vs| {
        for &(v, r, (_, ref ty)) in vs { if r { visit(&mut uf, v, ty) } }
      });
      for s in &bl.stmts {
        fn copy(uf: &mut Table, from: VarId, to: VarId) {
          let alloc = *uf.probe_value(from);
          let _ = uf.unify_var_value(&mut (), to, &alloc);
        }
        match s {
          Statement::Assign(_, _, vars) => for r in &**vars {
            if r.rel { copy(&mut uf, r.from, r.to) }
          }
          Statement::Let(lk, ty, rv) => {
            let (v, r, ty) = match *lk {
              LetKind::Let(v, r, _) => (v, r, ty),
              LetKind::Own([_, (v, r, ref ty)]) => (v, r, ty),
            };
            if !r { continue }
            visit(&mut uf, v, ty);
            let mut copy_place = |p: &Place| if p.proj.is_empty() { copy(&mut uf, p.local, v) };
            match rv {
              RValue::Use(o) => if let Ok(p) = o.place() { copy_place(p) }
              RValue::Pun(_, p) => copy_place(p),
              _ => {}
            }
          }
        }
      }
    }

    StorageResult
  }
}