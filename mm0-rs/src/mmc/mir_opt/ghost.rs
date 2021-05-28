//! The ghost propagation pass, which determines which variables are needed for computation.
//!
//! This is a MIR -> MIR pass, but it is required since without it most programs will fail
//! legalization.
#![allow(unused)]

use std::collections::HashMap;

use crate::AtomId;
use super::super::types::{ty, mir, entity, Spanned};
use entity::{Entity, ProcTc};
#[allow(clippy::wildcard_imports)] use super::*;

/// This function computes the reachability for each block in the CFG.
///
/// A block is reachable if it is accessible from the entry block by forward edges, except that
/// a block that ends in `unreachable` is not reachable, as well as a branch all of whose targets
/// are unreachable. A closed loop is unreachable, because we do not support nonterminating
/// programs. A loop with a side exit is unreachable iff the exit block is unreachable.
///
/// The correctness condition here is that an unreachable block is either inaccessible from the
/// entry block, or exists in a context where we can prove false. Ultimately, we will use this
/// proof of false to transform
/// ```text
/// l: if cond {h: cond. goto l1} else {h': !cond. goto l2}
/// ```
/// where `l` is reachable and `l2` is not, into
/// ```text
/// l: let h: cond = contra (h': !cond. pf);
/// ```
/// where `pf` is a proof of false in the context of block `l2`.
fn reachability_analysis(cfg: &mut Cfg) -> BitSet<BlockId> {
  cfg.compute_predecessors();
  let mut reachable = BitSet::with_capacity(cfg.blocks.len());
  let queue = &mut WorkQueue::with_capacity(cfg.blocks.len());
  let mut f = |id, bl: &BasicBlock, queue: &mut WorkQueue<_>| if !reachable.contains(id) {
    let new = match *bl.terminator() {
      Terminator::Return(_) |
      Terminator::Assert(_, _, _) => true,
      Terminator::Unreachable(_) => false,
      Terminator::Jump(tgt, _) => reachable.contains(tgt),
      Terminator::If(_, [(_, tgt1), (_, tgt2)]) =>
        reachable.contains(tgt1) || reachable.contains(tgt2),
      Terminator::Call(_, se, _, _, ref tgt) =>
        se || tgt.as_ref().map_or(false, |&(tgt, _)| reachable.contains(tgt)),
    };
    if new {
      for &x in &cfg.predecessors()[id] { queue.insert(x); }
      reachable.insert(id);
    }
  };
  for (id, bl) in cfg.postorder(BlockId::ENTRY) { f(id, bl, queue) }
  while let Some(id) = queue.pop() { f(id, &cfg[id], queue) }
  reachable
}

fn ghost_analysis(cfg: &mut Cfg,
  names: &HashMap<AtomId, Entity>,
  reachable: &BitSet<BlockId>,
  returns: &[Arg],
) {

  #[derive(Clone, Default)]
  struct GhostDom {
    active: bool,
    vars: im::HashSet<VarId>,
  }

  impl Domain for GhostDom {
    fn join(&mut self, other: &Self) -> bool {
      self.active.join(&other.active) |
      self.vars.join(&other.vars)
    }
  }

  impl GhostDom {
    #[inline] fn apply_local(&mut self, v: VarId) {
      self.vars.insert(v);
    }

    #[inline] fn apply_place(&mut self, p: &Place) {
      self.apply_local(p.local)
    }

    fn apply_operand(&mut self, o: &Operand) {
      if let Operand::Copy(p) | Operand::Move(p) | Operand::Ref(p) = o {
        self.apply_place(p)
      }
    }

    fn apply_rvalue(&mut self, rv: &RValue) {
      match rv {
        RValue::Use(o) => self.apply_operand(o),
        RValue::Unop(_, o) |
        RValue::Cast(_, o, _) => {
          self.active = true;
          self.apply_operand(o)
        }
        RValue::Binop(_, o1, o2) => {
          self.active = true;
          self.apply_operand(o1);
          self.apply_operand(o2)
        }
        RValue::Pun(_, p) |
        RValue::Borrow(p) => self.apply_place(p),
        RValue::List(os) |
        RValue::Array(os) => for o in &**os { self.apply_operand(o) }
        RValue::Ghost(_) |
        RValue::Mm0(_) |
        RValue::Typeof(_) => {}
      }
    }
  }

  struct GhostAnalysis<'a> {
    names: &'a HashMap<AtomId, Entity>,
    reachable: &'a BitSet<BlockId>,
    cache: HashMap<AtomId, BitSet<usize>>,
    returns: &'a [Arg],
  }

  impl GhostAnalysis<'_> {
    fn func_data(&mut self, a: AtomId) -> &BitSet {
      let GhostAnalysis {cache, names, ..} = self;
      cache.entry(a).or_insert_with(|| {
        let_unchecked!(ty as Entity::Proc(Spanned {k: ProcTc::Typed(ty), ..}) = &names[&a]);
        let mut needs_args = BitSet::with_capacity(ty.args.len());
        for (i, arg) in ty.args.iter().enumerate() {
          if !arg.0.contains(ty::ArgAttr::GHOST) { needs_args.insert(i); }
        }
        needs_args
      })
    }
  }

  impl Analysis for GhostAnalysis<'_> {
    type Dom = GhostDom;
    type Dir = Backward;
    type Doms = BlockVec<Self::Dom>;

    fn bottom(&mut self, cfg: &Cfg) -> Self::Doms { Self::do_bottom(cfg) }

    fn apply_statement(&mut self, _: Location, stmt: &Statement, d: &mut Self::Dom) {
      match stmt {
        Statement::Let(lk, _, rv) => {
          let needed = match *lk {
            LetKind::Let(v, vr, _) => vr && d.vars.contains(&v),
            LetKind::Own([(x, xr, _), (y, yr, _)]) =>
              xr && d.vars.contains(&x) || yr && d.vars.contains(&y)
          };
          if needed { d.apply_rvalue(rv) }
        }
        Statement::Assign(_, rhs, vars) => {
          let mut needed = false;
          for &(from, to, _) in &**vars {
            if d.vars.contains(&to) {
              needed = true;
              d.apply_local(from);
            }
          }
          if needed {
            d.active = true;
            d.apply_operand(rhs)
          }
        }
      }
    }

    fn apply_terminator(&mut self, _: BlockId, term: &Terminator, d: &mut Self::Dom) {
      match term {
        Terminator::Jump(_, args) => {
          let tgt = std::mem::take(d);
          for (v, o) in args {
            if tgt.vars.contains(v) {
              d.active = true;
              d.apply_operand(o)
            }
          }
        }
        Terminator::Return(args) => {
          d.active = true;
          for ((_, o), ret) in args.iter().zip(self.returns) {
            if !ret.attr.contains(ArgAttr::GHOST) { d.apply_operand(o) }
          }
        }
        Terminator::Unreachable(_) => unreachable!(),
        Terminator::If(o, _) => if d.active { d.apply_operand(o) }
        Terminator::Assert(o, _, _) => {
          d.active = true;
          d.apply_operand(o)
        }
        &Terminator::Call(f, side_effect, _, ref args, ref tgt) => {
          let needs_args = self.func_data(f);
          let needed = tgt.as_ref().map_or(true, |(_, rets)| {
            side_effect || rets.iter().any(|v| d.vars.contains(v))
          });
          if needed {
            d.active = true;
            for i in needs_args.iter() { d.apply_operand(&args[i]) }
          }
        }
      }
    }

    fn apply_trans_for_block(&mut self, id: BlockId, bl: &BasicBlock, d: &mut Self::Dom) {
      if !self.reachable.contains(id) { *d = Default::default(); return }
      self.do_apply_trans_for_block(id, bl, d)
    }
  }

  let mut analysis = GhostAnalysis {names, reachable, returns, cache: Default::default()};
  let result = analysis.iterate_to_fixpoint(cfg);
  todo!()
}