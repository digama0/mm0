//! The storage pass, which computes the stack and register allocations for a function.

use std::collections::{HashMap, hash_map::Entry};
use std::convert::TryInto;

use crate::AtomId;
use super::{VecPatch, Replace, types::{IdxVec, entity, mir, global}};
use entity::{Entity, ConstTc};
#[allow(clippy::wildcard_imports)] use mir::*;

enum StorageEdit {
  ChangeAssignTarget(VarId, VarId)
}

impl Replace<Statement> for StorageEdit {
  fn replace(self, stmt: &mut Statement) {
    match self {
      StorageEdit::ChangeAssignTarget(from, to) => {
        if let Statement::Assign(lhs, _, vars) = stmt {
          if lhs.local == from { lhs.local = to }
          for r in &mut **vars { if r.from == from { r.from = to } }
        }
      }
    }
  }
}

mk_id! {
  /// An ID for allocations, which are equivalence classes of variables with the property that
  /// at any given time, all live variables in the class have the same value, and thus can share
  /// the same physical memory location.
  ///
  /// We also ensure that variables that are assigned always share an allocation with the new value
  /// of the variable, so that it is actually an assignment to a memory location (this is important
  /// for the semantics of pointers to a changing memory location). We may need to insert an
  /// additional copy before the assignment, however, if the user accesses old values of a
  /// reassigned variable.
  AllocId
}

impl AllocId {
  const ZERO: Self = Self(0);
}

#[derive(Default, Debug)]
struct Allocation {
  size: u64,
  vars: Vec<VarId>,
}

impl Allocation {
  fn insert(&mut self, v: VarId, sz: u64) {
    self.size = self.size.max(sz);
    self.vars.push(v);
  }
}

/// The result of storage analysis.
#[derive(Debug)]
pub struct Allocations {
  allocs: IdxVec<AllocId, Allocation>,
  vars: HashMap<VarId, AllocId>,
}

impl Default for Allocations {
  fn default() -> Self {
    Self { allocs: vec![Allocation::default()].into(), vars: HashMap::new() }
  }
}
impl Allocations {
  fn insert(&mut self, a: AllocId, v: VarId, sz: u64) {
    if sz != 0 && a != AllocId::ZERO {
      self.allocs[a].insert(v, sz);
    }
    self.vars.insert(v, a);
  }
  fn push(&mut self, v: VarId, sz: u64) -> AllocId {
    let a = if sz == 0 { AllocId::ZERO } else {
      self.allocs.push(Allocation { size: sz, vars: vec![v] })
    };
    self.vars.insert(v, a);
    a
  }
  fn split(&mut self, v: VarId) -> AllocId {
    let a = self.vars.get_mut(&v).expect("variable not allocated");
    if *a == AllocId::ZERO { return AllocId::ZERO }
    let Allocation { size, ref mut vars } = self.allocs[*a];
    if let Some(i) = vars.iter().position(|x| *x == v) { vars.swap_remove(i); }
    *a = self.allocs.push(Allocation { size, vars: vec![v] });
    *a
  }
}

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
  #[must_use] pub fn storage(&mut self, names: &HashMap<AtomId, Entity>) -> Allocations {
    let sizeof = |ty: &TyKind| ty.sizeof(names).expect("can't get size of type");
    let mut allocs = Allocations::default();

    for (_, bl) in self.blocks.enum_iter_mut() {
      if bl.is_dead() { continue }
      let last_use = bl.liveness();
      let mut patch: VecPatch<Statement, StorageEdit> = Default::default();
      let mut ctx = HashMap::new();
      for &(v, r, (ref e, ref ty)) in self.ctxs.rev_iter(bl.ctx) {
        if r {
          ctx.insert(v, (e.as_ref(), ty));
          allocs.push(v, sizeof(ty));
        }
      }

      for (i, s) in bl.stmts.iter().enumerate() {
        match s {
          Statement::Assign(_, _, vars) => for r in vars.iter().filter(|r| r.rel) {
            if !r.rel { continue }
            if let Some(&(mut a)) = allocs.vars.get(&r.from) {

              // Consider the following code.
              //   let y = x;
              //   let z = y;
              //   .. <- .. [z' <- z];
              //   let w = x;
              // After the first two lines, we have that {x, y, z} are all in the same allocation
              // group, but z is modified to z' and x is live, so in this case we split z from
              // the group so that {x, y} is still available while {z, z'} is overwritten to the
              // value of z'.
              //
              // In general, there are three cases:
              // * All variables in z's allocation group is dead. In this case, z' joins the
              //   allocation group, so we get {x, y, z, z'}.
              // * Some variable other than z is live at the assignment.
              //   Then split = true and copy = false, this is the case we just looked at.
              //   z is removed from the group and forms a new group with z',
              //   resulting in {x, y}, {z, z'}.
              // * z is live. This is weird code, because it means the user is using a value that
              //   was directly overwritten. We could error here, but instead we insert an extra
              //   copy before the assignment. For example, if we let w = z on the last line,
              //   we would be in this case, with copy = true. We edit the code to:
              //     let y = x;
              //     let z = y;
              //     let z2 = z;
              //     .. <- .. [z' <- z2];
              //     let w = z;
              //   where z2 is in the new group and z is in the old group, so we get
              //   {x, y, z}, {z2, z'}, and so z's value is still available to be read.

              let mut split = false;
              let mut copy = false;
              for &x in &allocs.allocs[a].vars {
                if last_use.get(&x).map_or(false, |&j| j > i) {
                  if x == r.from { copy = true } else { split = true }
                }
              }
              if copy {
                let (e, ty) = ctx[&r.from];
                let v = self.max_var.fresh();
                patch.insert(i, Statement::Let(
                  LetKind::Let(v, true, e.cloned()), ty.clone(),
                  Operand::Move(r.from.into()).into()));
                patch.replace(i, StorageEdit::ChangeAssignTarget(r.from, v));
                a = allocs.push(v, sizeof(ty))
              } else if split { a = allocs.split(r.from) } else {}
              allocs.insert(a, r.to, sizeof(&r.ety.1));
            }
          }
          Statement::Let(lk, ty, rv) => {
            let (v, r, ty) = match *lk {
              LetKind::Let(v, r, _) => (v, r, ty),
              LetKind::Own([_, (v, r, ref ty)]) => (v, r, ty),
            };
            if !r { continue }
            let mut copy = None;
            let mut copy_place = |p: &Place| if p.proj.is_empty() { copy = Some(p.local) };
            match rv {
              RValue::Use(o) => if let Ok(p) = o.place() { copy_place(p) }
              RValue::Pun(_, p) => copy_place(p),
              _ => {}
            }
            if let Some(from) = copy {
              if let Some(&a) = allocs.vars.get(&from) {
                allocs.insert(a, v, sizeof(ty));
              }
            } else { allocs.push(v, sizeof(ty)); }
          }
        }
        s.foreach_def(|v, r, e, ty| if r { ctx.insert(v, (e, ty)); })
      }

      patch.apply(&mut bl.stmts);
    }
    allocs
  }
}

impl BasicBlock {
  /// Calculates the liveness information for the variables in a basic block.
  /// In the returned map, if `v` maps to `n` then statement `n` is the last
  /// (computationally relevant) use of `v`; the terminator is considered as statement
  /// `stmts.len()`. If `v` is not in the map then it is never used.
  fn liveness(&self) -> HashMap<VarId, usize> {
    let mut map = HashMap::new();
    let mut use_var = |i: usize, v: VarId| {
      if let Entry::Vacant(e) = map.entry(v) { e.insert(i); }
    };
    self.terminator().foreach_use(&mut |v| use_var(self.stmts.len(), v));
    for (i, s) in self.stmts.iter().enumerate().rev() {
      s.foreach_use(&mut |v| use_var(i, v));
    }
    map
  }
}