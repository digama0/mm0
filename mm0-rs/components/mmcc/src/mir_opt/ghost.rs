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
type GhostAnalysisResult = BlockVec<im::HashSet<VarId>>;

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
        Terminator::Return(..) |
        Terminator::Exit(..) |
        Terminator::Fail |
        Terminator::Assert(..) |
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
      if let Some(term) = bl.term.as_mut() {
        match term {
          Terminator::Call {reach, tgt, ..} =>
            *reach = reachable[*tgt].reach(),
          &mut Terminator::Assert(_, _, tgt) if !reachable[tgt].reach() =>
            *term = Terminator::Fail,
          &mut Terminator::If(_, _, [(_, tgt1), (_, tgt2)]) => {
            let reach1 = reachable[tgt1].reach();
            if reach1 == reachable[tgt2].reach() { continue }
            let Some(Terminator::If(ctx, _, [mut v_tgt1, mut v_tgt2])) = bl.term.take()
            else { unreachable!() };
            if reach1 { mem::swap(&mut v_tgt1, &mut v_tgt2) }
            let (_, _, (_, ty1)) = &self.ctxs.head(self[v_tgt1.1].ctx);
            let (v2, _, (e2, ty2)) = &self.ctxs.head(self[v_tgt2.1].ctx);
            bl = &mut self.blocks[id];
            bl.stmts.push(Statement::Let(
              LetKind::Let(v2.clone().map_into(|_| v_tgt2.0), e2.clone()), false, ty2.clone(),
              Constant::contra(ty1.clone(), tgt1, v_tgt1.0).into()
            ));
            bl.term = Some(Terminator::Jump1(ctx, tgt2));
          }
          _ => {}
        }
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
          Terminator::Return(..) |
          Terminator::Exit(_) => *d = true,
          Terminator::Fail |
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
    #[derive(Debug, Default)]
    struct GhostDom {
      active: OptBlockId,
      vars: im::HashSet<VarId>,
    }

    impl GhostDom {
      #[inline] fn apply_local(&mut self, v: VarId) { self.vars.insert(v); }

      #[inline] fn apply_place(&mut self, p: &Place) {
        self.apply_local(p.local);
        for proj in &p.proj {
          match proj.1 {
            Projection::Index(i, _) |
            Projection::Slice(i, _, _) => self.apply_local(i),
            Projection::Proj(_, _) |
            Projection::Deref => {}
          }
        }
      }

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

    impl Analysis for GhostAnalysis<'_> {
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
          Statement::LabelGroup(..) | Statement::PopLabelGroup | Statement::DominatedBlock(..) |
          Statement::Let(_, false, _, _) => {}
          Statement::Let(lk, true, _, rv) => {
            let (LetKind::Let(v, _) | LetKind::Ptr([_, (v, _)])) = lk;
            if d.vars.contains(&v.k) { d.apply_rvalue(loc.block, rv) }
          }
          Statement::Assign(_, _, rhs, vars) => {
            let mut needed = false;
            for v in &**vars {
              if v.rel && d.vars.contains(&v.to.k) {
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
          Terminator::Jump(_, args, _) => {
            let vars = d.vars.clone();
            for (v, _, _) in &**args { d.vars.remove(v); }
            for &(v, vr, ref o) in &**args {
              if vr && vars.contains(&v) {
                d.active = OptBlockId::new(id);
                d.apply_operand(o)
              }
            }
          }
          Terminator::Jump1(_, _) |
          Terminator::Fail |
          Terminator::Exit(_) => {}
          Terminator::Return(_, args) => {
            d.active = OptBlockId::new(id);
            for ((_, vr, o), ret) in args.iter().zip(self.returns) {
              if *vr && !ret.attr.contains(ArgAttr::GHOST) { d.apply_operand(o) }
            }
          }
          Terminator::Unreachable(_) | Terminator::Dead => unreachable!(),
          Terminator::If(_, o, _) => if d.active == OptBlockId::new(id) {
            d.apply_operand(o)
          }
          Terminator::Assert(o, _, _) => {
            d.active = OptBlockId::new(id);
            d.apply_operand(o)
          }
          &Terminator::Call {se: side_effect, ref args, reach, ref rets, ..} => {
            let needed = !reach || side_effect ||
              rets.iter().any(|&(vr, v)| vr && d.vars.contains(&v));
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
    (0..self.blocks.len()).map(BlockId::from_usize).map(|id| {
      analysis.get_applied(self, &result, id).vars
    }).collect()
  }

  /// Modify the CFG in place to apply the result of ghost analysis.
  pub fn apply_ghost_analysis(&mut self, result: &GhostAnalysisResult) {
    self.ctxs.reset_ghost();
    for (id, res) in result.enum_iter() {
      let bl = &mut self.blocks[id];
      if bl.is_dead() { continue }
      bl.relevance = Some(self.ctxs.set_ghost(bl.ctx, |v| res.contains(&v)));
      let get = |v| res.contains(&v);
      for stmt in &mut bl.stmts {
        match stmt {
          Statement::Let(LetKind::Let(v, _) | LetKind::Ptr([_, (v, _)]), r, _, _) => *r = get(v.k),
          Statement::Assign(_, _, _, vs) => for v in &mut **vs { v.rel = get(v.to.k) }
          Statement::LabelGroup(..) | Statement::PopLabelGroup | Statement::DominatedBlock(..) => {}
        }
      }
    }
    let mut cache = BlockVec::<Option<HashSet<VarId>>>::from_default(self.blocks.len());
    let Cfg {ctxs, blocks, ..} = self;
    for i in 0..blocks.len() {
      let blocks = &mut *blocks.0;
      match blocks[i].term {
        Some(Terminator::Jump(tgt, ref mut args, _)) => {
          let BasicBlock {ctx: tgt_ctx, relevance: ref rel, ..} = blocks[tgt.0 as usize];
          let rel = rel.as_ref().expect("impossible");
          let s = cache[tgt].get_or_insert_with(|| {
            ctxs.rev_iter_with_rel(tgt_ctx, rel).filter(|p| p.1).map(|p| p.0.k).collect()
          });
          for (v, r, _) in &mut **args { *r = s.contains(v) }
        }
        Some(Terminator::Call {reach: false, ref mut rets, ..}) =>
          for i in &mut **rets { i.0 = false },
        Some(Terminator::Call {reach: true, tgt, ref mut rets, ..}) => {
          let BasicBlock {ctx: tgt_ctx, relevance: ref rel, ..} = blocks[tgt.0 as usize];
          let rel = rel.as_ref().expect("impossible");
          let s = cache[tgt].get_or_insert_with(|| {
            ctxs.rev_iter_with_rel(tgt_ctx, rel).filter(|p| p.1).map(|p| p.0.k).collect()
          });
          for (r, v) in &mut **rets { *r = s.contains(v) }
        }
        _ => {}
      }
    }
  }

  /// Convenience function for applying the result of [`ghost_analysis`](Self::ghost_analysis).
  pub fn do_ghost_analysis(&mut self,
    reachable: &BlockVec<Reachability>,
    returns: &[Arg],
  ) {
    let ghost = self.ghost_analysis(reachable, returns);
    self.apply_ghost_analysis(&ghost);
  }
}
