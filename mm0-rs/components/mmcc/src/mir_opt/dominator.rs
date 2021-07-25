//! The dominator tree for a CFG.
#[allow(clippy::wildcard_imports)] use super::*;

#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;

/// The computed dominator tree information.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct DominatorTree {
  idom: BlockVec<OptBlockId>,
  postorder: BlockVec<usize>,
}

impl DomainsBottom for DominatorTree {
  fn bottom(n: usize) -> Self {
    Self { idom: BlockVec::bottom(n), postorder: BlockVec::bottom(n) }
  }
}

impl DominatorTree {
  /// Get the immediate dominator of a block.
  /// Returns garbage if the input block is not reachable from the entry block.
  #[must_use] pub fn idom(&self, id: BlockId) -> BlockId { self.idom[id].get_unchecked() }

  /// Get the immediate dominator of a block, or `None` for the entry block.
  /// Returns garbage if the input block is not reachable from the entry block.
  #[must_use] pub fn try_idom(&self, id: BlockId) -> Option<BlockId> {
    if id == BlockId::ENTRY { None } else { Some(self.idom(id)) }
  }

  /// Get the intersection of two dominator sets (represented as a block ID and its parents).
  #[must_use] pub fn intersect(&self, mut a: BlockId, mut b: BlockId) -> BlockId {
    while a != b {
      while self.postorder[a] < self.postorder[b] { a = self.idom(a) }
      while self.postorder[b] < self.postorder[a] { b = self.idom(b) }
    }
    a
  }

  /// Get the intersection of two dominator sets (represented as a block ID and its parents).
  #[must_use] pub fn intersect_opt(&self, a: OptBlockId, b: OptBlockId) -> OptBlockId {
    match (a.get(), b.get()) {
      (_, None) => a,
      (None, _) => b,
      (Some(a), Some(b)) => OptBlockId::new(self.intersect(a, b))
    }
  }

  /// Intersect two dominator sets, and return true if the first one was changed as a result.
  pub fn meet(&self, a: &mut OptBlockId, b: OptBlockId) -> bool {
    let a2 = self.intersect_opt(*a, b);
    *a != a2 && { *a = a2; true }
  }
}

impl std::ops::Index<BlockId> for DominatorTree {
  type Output = BlockId;
  fn index(&self, id: BlockId) -> &Self::Output { &self.idom[id].0 }
}

impl Domains for DominatorTree {
  type Item = OptBlockId;
  fn cloned(&self, id: BlockId) -> Self::Item { self.idom[id] }
  fn join(&mut self, id: BlockId, &other: &Self::Item) -> bool {
    let a = self.idom[id];
    let a2 = self.intersect_opt(a, other);
    a != a2 && { self.idom[id] = a2; true }
  }
}

impl Cfg {
  /// This function computes the [dominator tree] for a CFG. It is represented as a mapping from
  /// each basic block to its immediate dominator, which can be iterated to get the full dominator
  /// set up to the entry block.
  ///
  /// [dominator tree]: https://en.wikipedia.org/wiki/Dominator_(graph_theory)
  #[allow(clippy::needless_collect)]
  #[must_use] pub fn dominator_tree_uncached(&self) -> DominatorTree {
    struct DominatorAnalysis;
    impl Analysis for DominatorAnalysis {
      type Dir = Forward;
      type Doms = DominatorTree;
      fn bottom(&mut self, _: &Cfg) -> Self::Doms { unreachable!() }
      fn apply_trans_for_block(&mut self,
        _: &Self::Doms, _: BlockId, _: &BasicBlock, _: &mut OptBlockId) {}
    }

    let mut queue = WorkQueue::with_capacity(self.blocks.len());
    let mut tree = DominatorTree::bottom(self.blocks.len());
    let postorder = self.postorder(BlockId::ENTRY).map(|(id, _)| id).collect::<Vec<_>>();
    for (i, id) in postorder.into_iter().enumerate().rev() {
      queue.insert(id);
      tree.postorder[id] = i;
    }
    tree.idom[BlockId::ENTRY] = OptBlockId::new(BlockId::ENTRY);
    DominatorAnalysis.iterate_to_fixpoint_from(self, &mut queue, &mut tree);
    tree
  }
}
