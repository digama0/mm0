//! The storage pass, which computes the stack and register allocations for a function.

use std::collections::{HashMap, HashSet, hash_map::Entry};
use if_chain::if_chain;

use crate::{Idx, Symbol};
use super::{VecPatch, Replace, types::{IdxVec, entity, mir, global}};
use entity::{Entity, ConstTc};
#[allow(clippy::wildcard_imports)] use mir::*;

#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;

enum StorageEdit {
  ChangeAssignTarget(VarId, VarId)
}

impl Replace<Statement> for StorageEdit {
  fn replace(self, stmt: &mut Statement) {
    match self {
      StorageEdit::ChangeAssignTarget(from, to) => {
        if let Statement::Assign(lhs, _, _, vars) = stmt {
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
  AllocId(Debug("a"))
}

impl AllocId {
  /// Allocations of zero size get the special allocation ID `ZERO`, which is considered disjoint
  /// from all other allocations, including itself.
  pub const ZERO: Self = Self(0);
}

#[derive(Copy, Clone, Default, Debug)]
pub(crate) struct Meta {
  pub(crate) size: u64,
  pub(crate) on_stack: bool,
}
#[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(Meta);

impl Meta {
  const GHOST: Self = Self { size: 0, on_stack: false };
  fn from_size(size: u64) -> Self {
    Self { size, on_stack: false }
  }
  fn on_stack(mut self) -> Self {
    self.on_stack = true;
    self
  }
  fn merge(&mut self, m: Meta) {
    if self.size == 0 { *self = m; return }
    self.size = self.size.max(m.size);
    self.on_stack |= m.on_stack;
  }
}

#[derive(Default, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub(crate) struct Allocation {
  pub(crate) m: Meta,
  pub(crate) vars: Vec<VarId>,
}

impl Allocation {
  fn insert(&mut self, v: VarId, m: Meta) {
    self.m.merge(m);
    self.vars.push(v);
  }
}

/// The result of storage analysis.
#[derive(Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub(crate) struct Allocations {
  allocs: IdxVec<AllocId, Allocation>,
  vars: HashMap<VarId, AllocId>,
}

impl std::ops::Deref for Allocations {
  type Target = IdxVec<AllocId, Allocation>;
  fn deref(&self) -> &Self::Target { &self.allocs }
}
impl Default for Allocations {
  fn default() -> Self {
    Self { allocs: vec![Allocation::default()].into(), vars: HashMap::new() }
  }
}
impl Allocations {
  pub(crate) fn get(&self, v: VarId) -> AllocId {
    self.vars.get(&v).copied().unwrap_or(AllocId::ZERO)
  }

  fn insert(&mut self, a: AllocId, v: VarId, m: Meta) {
    if m.size != 0 && a != AllocId::ZERO {
      self.allocs[a].insert(v, m);
    }
    self.vars.insert(v, a);
  }
  fn push(&mut self, v: VarId, meta: impl FnOnce() -> Meta) -> AllocId {
    if let Some(&a) = self.vars.get(&v) { return a }
    let m = meta();
    let a = if m.size == 0 { AllocId::ZERO } else {
      self.allocs.push(Allocation { m, vars: vec![v] })
    };
    self.vars.insert(v, a);
    a
  }
  fn split(&mut self, v: VarId) -> (AllocId, AllocId) {
    let a = self.vars.get_mut(&v).expect("variable not allocated");
    let old = *a;
    if old == AllocId::ZERO { return (AllocId::ZERO, AllocId::ZERO) }
    let Allocation { m, ref mut vars } = self.allocs[old];
    if let Some(i) = vars.iter().position(|x| *x == v) { vars.swap_remove(i); }
    *a = self.allocs.push(Allocation { m, vars: vec![v] });
    (old, *a)
  }
}

impl ExprKind {
  fn eval_u64(&self, ns: &HashMap<Symbol, Entity>) -> Option<u64> {
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
  /// Gets the size of this type in bytes, if it is a compile-time constant.
  #[must_use] pub fn sizeof(&self, ns: &HashMap<Symbol, Entity>) -> Option<u64> {
    self.meta(ns).map(|m| m.size)
  }

  /// Gets the ABI information of this type, if it is a compile-time constant.
  #[must_use] pub(crate) fn meta(&self, ns: &HashMap<Symbol, Entity>) -> Option<Meta> {
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
      TyKind::Ghost(_) => Some(Meta::from_size(0)),
      TyKind::Bool => Some(Meta::from_size(1)),
      TyKind::Own(_) |
      TyKind::Shr(_, _) |
      TyKind::RefSn(_) => Some(Meta::from_size(8)),
      TyKind::User(_, _, _) | // TODO
      TyKind::Var(_) => None, // TODO: monomorphize first
      TyKind::Int(ity) => ity.size().bytes().map(|n| Meta::from_size(n.into())),
      TyKind::Array(ty, n) => Some(
        Meta::from_size(ty.sizeof(ns)?.checked_mul(n.eval_u64(ns)?)?).on_stack()),
      TyKind::Sn(_, ty) |
      TyKind::Uninit(ty) |
      TyKind::Moved(ty) |
      TyKind::All(_, _, ty) => ty.meta(ns),
      TyKind::Struct(args) => {
        enum State { Start, One, Large }
        let mut state = State::Start;
        let mut size = 0_u64;
        for arg in &**args {
          if !arg.attr.contains(ArgAttr::GHOST) {
            let m1 = arg.ty.meta(ns)?;
            if m1.size > 0 {
              size = size.checked_add(m1.size)?;
              let large = m1.on_stack || !matches!(state, State::Start);
              state = if large { State::One } else { State::Large };
            }
          }
        }
        Some(Meta { size, on_stack: matches!(state, State::Large) })
      }
      TyKind::And(tys) |
      TyKind::Or(tys) => {
        let mut m = Meta::from_size(0);
        for ty in &**tys { m.merge(ty.meta(ns)?) }
        Some(m)
      }
      TyKind::If(_, ty1, ty2) => {
        let mut m = ty1.meta(ns)?;
        m.merge(ty2.meta(ns)?);
        Some(m)
      }
    }
  }
}

// #[derive(Default)]
// struct Interference(HashSet<(AllocId, AllocId)>);

// impl Interference {
//   fn insert(&mut self, a1: AllocId, a2: AllocId) {
//     let (a1, a2) = match a1.cmp(&a2) {
//       Ordering::Less => (a1, a2),
//       Ordering::Equal => return,
//       Ordering::Greater => (a2, a1),
//     };
//     if a1 != AllocId::ZERO { self.0.insert((a1, a2)); }
//   }

//   fn get(&self, a1: AllocId, a2: AllocId) -> bool {
//     let (a1, a2) = match a1.cmp(&a2) {
//       Ordering::Less => (a1, a2),
//       Ordering::Equal => return false,
//       Ordering::Greater => (a2, a1),
//     };
//     a1 != AllocId::ZERO && self.0.contains(&(a1, a2))
//   }
// }

impl Cfg {
  #[must_use] fn build_allocations(&mut self,
    names: &HashMap<Symbol, Entity>
  ) -> Allocations {
    let meta = |ty: &Ty| ty.meta(names).unwrap_or(Meta::GHOST);

    // let mut interference = Interference::default();

    let mut allocs = Allocations::default();

    let init = self.blocks.0.iter().map(|bl| {
      if bl.is_dead() { return Default::default() }
      bl.ctx_rev_iter(&self.ctxs).filter(|p| p.1).map(|p| p.0.k).collect()
    }).collect();
    for (_, bl) in self.blocks.enum_iter_mut() {
      if bl.is_dead() { continue }
      let last_use = bl.liveness(&init);
      let mut patch: VecPatch<Statement, StorageEdit> = Default::default();
      let mut live = HashMap::new();
      let mut to_ghost = vec![];
      let rel = bl.relevance.as_mut().expect("ghost analysis not done yet");
      for (i, (v, r, (e, ty))) in self.ctxs.rev_iter_with_rel(bl.ctx, rel).enumerate() {
        if !r { continue }
        live.insert(v.k, (e.as_ref(), ty));
        if allocs.push(v.k, || meta(ty)) == AllocId::ZERO { to_ghost.push(rel.len() - 1 - i) }
      }

      for (i, s) in bl.stmts.iter_mut().enumerate() {
        match s {
          Statement::Assign(_, _, _, vars) => for r in vars.iter_mut().filter(|r| r.rel) {
            if !r.rel { continue }
            if let Some(&(mut a)) = allocs.vars.get(&r.from) {
              if a == AllocId::ZERO {
                r.rel = false;
                continue
              }

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
              for &x in &allocs[a].vars {
                if last_use.get(&x).map_or(false, |&j| j > i) {
                  if x == r.from { copy = true } else { split = true }
                }
              }
              let interfere = |(_old, new), _allocs: &Allocations| {
                // interference.insert(old, new);
                // for u in live.keys() {
                //   if last_use.get(u).map_or(false, |&j| j > i) {
                //     interference.insert(new, allocs.vars[u]);
                //   }
                // }
                new
              };
              if copy {
                let (e, ty) = live[&r.from];
                let old = allocs.vars[&r.from];
                let v = self.max_var.fresh();
                patch.insert(i, Statement::Let(
                  LetKind::Let(r.to.clone().map_into(|_| v), e.cloned()), true, ty.clone(),
                  Operand::Move(r.from.into()).into()));
                patch.replace(i, StorageEdit::ChangeAssignTarget(r.from, v));
                let new = allocs.push(v, || meta(ty));
                a = if new == AllocId::ZERO { new } else { interfere((old, new), &allocs) };
              } else if split {
                a = interfere(allocs.split(r.from), &allocs)
              }
              allocs.insert(a, r.to.k, meta(&r.ety.1));
            }
          }
          Statement::Let(ref lk, r, ref ty, rv) => {
            let (v, ty) = match lk {
              LetKind::Let(v, _) => (v.k, ty),
              LetKind::Ptr([_, (v, ty)]) => (v.k, ty),
            };
            if !*r { continue }
            let mut copy = None;
            let mut copy_place = |p: &Place| if p.proj.is_empty() { copy = Some(p.local) };
            match rv {
              RValue::Use(o) => if let Ok(p) = o.place() { copy_place(p) }
              RValue::Pun(_, p) => copy_place(p),
              RValue::Borrow(p) => if let Some(&a) = allocs.vars.get(&p.local) {
                allocs.allocs[a].m.on_stack = true;
              }
              _ => {}
            }
            let mut tgt = AllocId::ZERO;
            if let Some(from) = copy {
              if let Some(&a) = allocs.vars.get(&from) {
                tgt = a;
                allocs.insert(a, v, meta(ty));
              }
            } else {
              tgt = allocs.push(v, || meta(ty));
              live.retain(|u, _| last_use.get(u).map_or(false, |&j| j > i) && {
                // interference.insert(a, allocs.vars[u]);
                true
              });
            }
            if tgt == AllocId::ZERO { *r = false }
          }
          Statement::LabelGroup(..) | Statement::PopLabelGroup | Statement::DominatedBlock(..) => {}
        }
        s.foreach_def(|v, r, e, ty| if r { live.insert(v.k, (e, ty)); })
      }

      for i in to_ghost { rel.set(i, false); }
      patch.apply(&mut bl.stmts);
    }

    // (allocs, interference)
    allocs
  }

  /// Compute the storage requirements of the CFG. This is a partitioning of the `VarId`'s into
  /// groups, as few as possible, such that all variables in a group have the same bit pattern at
  /// a given point in time, and any variable whose storage is overwritten by a later variable in
  /// the same group is dead.
  #[must_use] pub(crate) fn storage(&mut self, names: &HashMap<Symbol, Entity>) -> Allocations {
    self.build_allocations(names)
  }
}

impl BasicBlock {
  /// Calculates the liveness information for the variables in a basic block.
  /// In the returned map, if `v` maps to `n` then statement `n` is the last
  /// (computationally relevant) use of `v`; the terminator is considered as statement
  /// `stmts.len()`. If `v` is not in the map then it is never used.
  fn liveness(&self, init: &BlockVec<HashSet<VarId>>) -> HashMap<VarId, usize> {
    let mut map = HashMap::new();
    let term = self.terminator();
    let mut jump_implicits = |id, args: &[(VarId, _, _)]| {
      let i = self.stmts.len();
      for &v in &init[id] { map.insert(v, i); }
      for (v, _, _) in args { map.remove(v); }
    };
    match *term {
      Terminator::Jump(id, ref args, _) => jump_implicits(id, args),
      Terminator::Jump1(_, id) => jump_implicits(id, &[]),
      _ => {}
    }
    let mut use_var = |i: usize, v: VarId| {
      if let Entry::Vacant(e) = map.entry(v) { e.insert(i); }
    };
    term.foreach_use(&mut |v| use_var(self.stmts.len(), v));
    for (i, s) in self.stmts.iter().enumerate().rev() {
      s.foreach_use(&mut |v| use_var(i, v));
    }
    map
  }
}
