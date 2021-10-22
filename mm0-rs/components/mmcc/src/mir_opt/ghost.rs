//! The ghost propagation pass, which determines which variables are needed for computation.
//!
//! This is a MIR -> MIR pass, but it is required since without it most programs will fail
//! legalization.

use std::{collections::HashSet, mem};

#[allow(clippy::wildcard_imports)] use super::*;

/// The reachability status of a block.
#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq)]
pub enum Reachability {
  /// A block is dead if it is not accessible from the entry block.
  Dead,
  /// A block is unreachable if it is accessible from the entry block, but necessarily ends
  /// in a call to `unreachable`, meaning that `false` is provable in the current context.
  Unreachable,
  /// A block is reachable if it is accessible from the entry block, and we *may* reach some
  /// effectful terminator like `return`, `assert` or a side-effectful function call.
  Reachable,
}

impl Default for Reachability {
  fn default() -> Self { Self::Dead }
}
impl Reachability {
  /// True if this block is reachable.
  #[inline] #[must_use] pub fn reach(self) -> bool { matches!(self, Self::Reachable) }
  /// True if this block is dead.
  #[inline] #[must_use] pub fn dead(self) -> bool { matches!(self, Self::Dead) }
}

impl Domain for Reachability {
  fn join(&mut self, &other: &Self) -> bool {
    *self < other && { *self = other; true }
  }
}

/// The result of ghost analysis, the list of all computationally relevant variables in each
/// basic block.
#[derive(Debug)]
pub struct GhostAnalysisResult(BlockVec<im::HashSet<VarId>>);

impl Cfg {
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
  #[must_use] pub fn reachability_analysis(&self) -> BlockVec<Reachability> {
    struct ReachabilityAnalysis;
    fn side_effecting(t: &Terminator) -> bool {
      matches!(t,
        Terminator::Return(_) |
        Terminator::Exit(_) |
        Terminator::Assert(_, _, _, _) |
        Terminator::Call {se: true, ..})
    }
    impl Analysis for ReachabilityAnalysis {
      type Dir = Backward;
      type Doms = BlockVec<Reachability>;

      fn bottom(&mut self, cfg: &Cfg) -> Self::Doms { BlockVec::bottom(cfg.blocks.len()) }

      fn apply_trans_for_block(&mut self,
        _: &Self::Doms, _: BlockId, bl: &BasicBlock, d: &mut Reachability
      ) {
        if side_effecting(bl.terminator()) {
          *d = Reachability::Reachable
        }
      }
    }
    let mut queue = WorkQueue::with_capacity(self.blocks.len());
    let mut reachable = ReachabilityAnalysis.bottom(self);
    Backward::preferred_traverse(self, |id, _| {
      reachable[id] = Reachability::Unreachable;
      queue.insert(id);
    });
    ReachabilityAnalysis.iterate_to_fixpoint_from(self, &mut queue, &mut reachable);
    for (i, d) in reachable.enum_iter_mut() {
      if *d != Reachability::Dead && side_effecting(self[i].terminator()) {
        *d = Reachability::Reachable
      }
    }
    reachable
  }

  /// Edit the CFG in place to apply the results of reachability analysis.
  pub fn apply_reachability_analysis(&mut self, reachable: &BlockVec<Reachability>) {
    for id in (0..self.blocks.len()).map(BlockId::from_usize) {
      let mut bl = &mut self.blocks[id];
      match reachable[id] {
        Reachability::Dead => { *bl = BasicBlock::DEAD; continue }
        Reachability::Unreachable => { bl.reachable = false; continue }
        Reachability::Reachable => {}
      }
      match bl.term.as_mut() {
        Some(Terminator::Assert(_, _, reach, tgt) | Terminator::Call {reach, tgt, ..}) =>
          *reach = reachable[*tgt].reach(),
        Some(&mut Terminator::If(_, [(_, tgt1), (_, tgt2)])) => {
          let reach1 = reachable[tgt1].reach();
          if reach1 == reachable[tgt2].reach() { continue }
          let_unchecked!(Some(Terminator::If(_, [mut vtgt1, mut vtgt2])) = bl.term.take(), {
            if reach1 { mem::swap(&mut vtgt1, &mut vtgt2) }
            let (_, ty1) = &self.ctxs.head(self[vtgt1.1].ctx).2;
            let (e2, ty2) = &self.ctxs.head(self[vtgt2.1].ctx).2;
            bl = &mut self.blocks[id];
            bl.stmts.push(Statement::Let(
              LetKind::Let(vtgt2.0, false, e2.clone()), ty2.clone(),
              Constant::contra(ty1.clone(), tgt1, vtgt1.0).into()
            ));
            bl.term = Some(Terminator::Jump1(tgt2));
          });
        }
        _ => {}
      }
    }
  }

  /// This function returns true if the entry block can reach a `Return(_)`, i.e. it can terminate
  /// normally. This can be false either because the entry block is unreachable (because the
  /// function inputs are contradictory), or because every path through the function ends in an
  /// `assert(false)` or a call to a function that does not return.
  #[must_use] pub fn can_return(&self) -> bool {
    struct ReturnAnalysis;
    impl Analysis for ReturnAnalysis {
      type Dir = Backward;
      type Doms = BitSet<BlockId>;

      fn bottom(&mut self, cfg: &Cfg) -> Self::Doms { BitSet::bottom(cfg.blocks.len()) }

      fn apply_trans_for_block(&mut self,
          _: &Self::Doms, _: BlockId, bl: &BasicBlock, d: &mut bool) {
        match *bl.terminator() {
          Terminator::Return(_) |
          Terminator::Exit(_) => *d = true,
          Terminator::Assert(_, _, false, _) |
          Terminator::Call {reach: false, ..} => *d = false,
          Terminator::Assert(..) |
          Terminator::Call {..} |
          Terminator::Unreachable(_) |
          Terminator::Dead |
          Terminator::Jump(..) |
          Terminator::Jump1(..) |
          Terminator::If(..) => {}
        }
      }
    }
    let doms = ReturnAnalysis.iterate_to_fixpoint(self);
    ReturnAnalysis.get_applied(self, &doms, BlockId::ENTRY)
  }

  /// This function performs the "ghost analysis" pass. The result of the analysis is a
  /// determination of the computational relevance of each variable in the program based on
  /// whether its result is needed.
  #[must_use] pub fn ghost_analysis(&self,
    reachable: &BlockVec<Reachability>,
    returns: &[Arg],
  ) -> GhostAnalysisResult {
    #[derive(Default)]
    struct GhostDom {
      active: OptBlockId,
      vars: im::HashSet<VarId>,
    }

    impl GhostDom {
      #[inline] fn apply_local(&mut self, v: VarId) { self.vars.insert(v); }

      #[inline] fn apply_place(&mut self, p: &Place) { self.apply_local(p.local) }

      fn apply_operand(&mut self, o: &Operand) {
        if let Operand::Copy(p) | Operand::Move(p) | Operand::Ref(p) = o { self.apply_place(p) }
      }

      fn apply_rvalue(&mut self, id: BlockId, rv: &RValue) {
        match rv {
          RValue::Use(o) => self.apply_operand(o),
          RValue::Unop(_, o) |
          RValue::Cast(_, o, _) => {
            self.active = OptBlockId::new(id);
            self.apply_operand(o)
          }
          RValue::Binop(_, o1, o2) | RValue::Eq(_, _, o1, o2) => {
            self.active = OptBlockId::new(id);
            self.apply_operand(o1);
            self.apply_operand(o2)
          }
          RValue::Pun(_, p) |
          RValue::Borrow(p) => self.apply_place(p),
          RValue::List(os) |
          RValue::Array(os) => {
            self.active = OptBlockId::new(id);
            for o in &**os { self.apply_operand(o) }
          }
          RValue::Ghost(_) |
          RValue::Mm0(..) |
          RValue::Typeof(_) => {}
        }
      }
    }

    struct GhostAnalysis<'a> {
      reachable: &'a BlockVec<Reachability>,
      returns: &'a [Arg],
    }

    struct GhostDoms {
      active: BlockVec<OptBlockId>,
      vars: BlockVec<im::HashSet<VarId>>,
    }

    impl Domains for GhostDoms {
      type Item = GhostDom;
      fn cloned(&self, id: BlockId) -> Self::Item {
        GhostDom {
          active: self.active[id],
          vars: self.vars.cloned(id),
        }
      }

      fn join(&mut self, id: BlockId, &GhostDom {active, ref vars}: &GhostDom) -> bool {
        let cur = &mut self.active[id];
        let changed = match (cur.get(), active.get()) {
          (None, Some(_)) => { *cur = active; true }
          (Some(a), Some(b)) if a != b && a != id => { *cur = OptBlockId::new(id); true }
          _ => false,
        };
        changed | self.vars.join(id, vars)
      }
    }

    impl<'a> Analysis for GhostAnalysis<'a> {
      type Dir = Backward;
      type Doms = GhostDoms;

      fn bottom(&mut self, cfg: &Cfg) -> Self::Doms {
        GhostDoms {
          active: BlockVec::bottom(cfg.blocks.len()),
          vars: BlockVec::bottom(cfg.blocks.len()),
        }
      }

      fn apply_statement(&mut self, _: &Self::Doms,
          loc: Location, stmt: &Statement, d: &mut GhostDom) {
        match stmt {
          Statement::Let(lk, _, rv) => {
            let needed = match *lk {
              LetKind::Let(v, vr, _) => vr && d.vars.contains(&v),
              LetKind::Own([(x, xr, _), (y, yr, _)]) =>
                xr && d.vars.contains(&x) || yr && d.vars.contains(&y)
            };
            if needed { d.apply_rvalue(loc.block, rv) }
          }
          Statement::Assign(_, _, rhs, vars) => {
            let mut needed = false;
            for v in &**vars {
              if v.rel && d.vars.contains(&v.to) {
                needed = true;
                d.apply_local(v.from);
              }
            }
            if needed {
              d.active = OptBlockId::new(loc.block);
              d.apply_operand(rhs)
            }
          }
        }
      }

      fn apply_terminator(&mut self, _: &Self::Doms,
          id: BlockId, term: &Terminator, d: &mut GhostDom) {
        match term {
          Terminator::Jump(_, args) => {
            let GhostDom {vars, ..} = mem::take(d);
            for &(v, vr, ref o) in args {
              if vr && vars.contains(&v) {
                d.active = OptBlockId::new(id);
                d.apply_operand(o)
              }
            }
          }
          Terminator::Jump1(_) |
          Terminator::Exit(_) => {}
          Terminator::Return(args) => {
            d.active = OptBlockId::new(id);
            for ((_, vr, o), ret) in args.iter().zip(self.returns) {
              if *vr && !ret.attr.contains(ArgAttr::GHOST) { d.apply_operand(o) }
            }
          }
          Terminator::Unreachable(_) | Terminator::Dead => unreachable!(),
          Terminator::If(o, _) => if d.active == OptBlockId::new(id) {
            d.apply_operand(o)
          }
          Terminator::Assert(o, _, _, _) => {
            d.active = OptBlockId::new(id);
            d.apply_operand(o)
          }
          &Terminator::Call {se: side_effect, ref args, reach, ref rets, ..} => {
            let needed = !reach || side_effect || rets.iter().any(|v| d.vars.contains(v));
            if needed {
              d.active = OptBlockId::new(id);
              for &(r, ref o) in &**args { if r { d.apply_operand(o) } }
            }
          }
        }
      }

      fn apply_trans_for_block(&mut self,
          ds: &Self::Doms, id: BlockId, bl: &BasicBlock, d: &mut GhostDom) {
        if !self.reachable[id].reach() { *d = Default::default(); return }
        self.do_apply_trans_for_block(ds, id, bl, d)
      }
    }

    let mut analysis = GhostAnalysis { reachable, returns };
    let result = analysis.iterate_to_fixpoint(self);
    GhostAnalysisResult((0..self.blocks.len()).map(BlockId::from_usize).map(|id| {
      analysis.get_applied(self, &result, id).vars
    }).collect())
  }

  /// Modify the CFG in place to apply the result of ghost analysis.
  pub fn apply_ghost_analysis(&mut self,
    res: &GhostAnalysisResult, returns: &[Arg],
  ) {
    self.ctxs.reset_ghost();
    for (id, res) in res.0.enum_iter() {
      let bl = &mut self.blocks[id];
      if bl.is_dead() { continue }
      bl.relevance = Some(self.ctxs.set_ghost(bl.ctx, |v| res.contains(&v)));
      let get = |v| res.contains(&v);
      for stmt in &mut bl.stmts {
        match stmt {
          Statement::Let(LetKind::Let(v, r, _), _, _) => *r = get(*v),
          Statement::Let(LetKind::Own(vs), _, _) => for (v, r, _) in vs { *r = get(*v) }
          Statement::Assign(_, _, _, vs) => for v in &mut **vs { v.rel = get(v.to) }
        }
      }
    }
    let mut cache = BlockVec::<Option<HashSet<VarId>>>::from_default(self.blocks.len());
    let Cfg {ctxs, blocks, ..} = self;
    for i in 0..blocks.len() {
      let blocks = &mut *blocks.0;
      if let Some(Terminator::Jump(tgt, ref mut args)) = blocks[i].term {
        let tgt_ctx = blocks[tgt.0 as usize].ctx;
        let s = cache[tgt].get_or_insert_with(|| {
          ctxs.rev_iter(tgt_ctx).filter(|p| p.1).map(|p| p.0).collect()
        });
        for (v, r, _) in args { *r = s.contains(v) }
      }
    }
  }

  /// Convenience function for applying the result of [`ghost_analysis`](Self::ghost_analysis).
  pub fn do_ghost_analysis(&mut self,
    reachable: &BlockVec<Reachability>,
    returns: &[Arg],
  ) {
    let ghost = self.ghost_analysis(reachable, returns);
    self.apply_ghost_analysis(&ghost, returns);
  }
}