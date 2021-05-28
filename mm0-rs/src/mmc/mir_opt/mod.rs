//! MIR optimizations.

use std::{collections::VecDeque, hash::Hash, marker::PhantomData};
use super::types;
use types::{Idx, mir};
#[allow(clippy::wildcard_imports)] use mir::*;

pub mod ghost;

/// A bit set with a custom index type.
#[derive(Default, Debug, PartialEq, Eq)]
pub struct BitSet<T = usize>(bit_set::BitSet, PhantomData<T>);

impl<T> Clone for BitSet<T> {
  fn clone(&self) -> Self { BitSet(self.0.clone(), PhantomData) }
}

impl<T> BitSet<T> {
  /// Creates a new `BitSet` with initially no contents, able to
  /// hold `nbits` elements without resizing.
  #[inline] #[must_use] pub fn with_capacity(nbits: usize) -> Self {
    Self(bit_set::BitSet::with_capacity(nbits), PhantomData)
  }

  /// Returns the number of set bits in this set.
  #[inline] #[must_use] pub fn len(&self) -> usize { self.0.len() }

  /// Returns whether there are no bits set in this set
  #[inline] #[must_use] pub fn is_empty(&self) -> bool { self.0.is_empty() }

  /// Adds a value to the set. Returns `true` if the value was not already
  /// present in the set.
  #[inline] #[must_use] pub fn contains(&self, value: T) -> bool where T: Idx {
    self.0.contains(value.into_usize())
  }

  /// Adds a value to the set. Returns `true` if the value was not already
  /// present in the set.
  #[inline] pub fn insert(&mut self, value: T) -> bool where T: Idx {
    self.0.insert(value.into_usize())
  }

  /// Removes a value from the set. Returns `true` if the value was
  /// present in the set.
  #[inline] pub fn remove(&mut self, value: T) -> bool where T: Idx {
    self.0.remove(value.into_usize())
  }

  /// Unions in-place with the specified other bit vector.
  /// Returns `true` if `self` was changed.
  #[inline] pub fn union_with(&mut self, other: &Self) -> bool {
    if other.0.is_subset(&self.0) {
      false
    } else {
      self.0.union_with(&other.0);
      true
    }
  }

  /// Intersects in-place with the specified other bit vector.
  /// Returns `true` if `self` was changed.
  #[inline] pub fn intersect_with(&mut self, other: &Self) -> bool {
    if self.0.is_subset(&other.0) {
      false
    } else {
      self.0.intersect_with(&other.0);
      true
    }
  }

  /// Iterator over each value stored in the `BitSet`.
  pub fn iter(&self) -> impl Iterator<Item=T> + '_ where T: Idx {
    self.0.iter().map(Idx::from_usize)
  }
}

#[derive(Clone, Default)]
struct WorkQueue<T> {
  deque: VecDeque<T>,
  set: BitSet<T>,
}

impl<T> WorkQueue<T> {
  #[inline] fn with_capacity(len: usize) -> Self {
    Self { deque: VecDeque::with_capacity(len), set: BitSet::with_capacity(len) }
  }

  #[inline] fn insert(&mut self, value: T) -> bool where T: Idx {
    self.set.insert(value) && { self.deque.push_back(value); true }
  }

  #[inline] fn pop(&mut self) -> Option<T> where T: Idx {
    let value = self.deque.pop_front()?;
    self.set.remove(value);
    Some(value)
  }
}

struct Postorder<'a> {
  cfg: &'a Cfg,
  visited: BitSet<BlockId>,
  visit_stack: Vec<(BlockId, Successors<'a>)>,
}

impl Cfg {
  fn postorder(&self, start: BlockId) -> Postorder<'_> {
    let mut po = Postorder {
      cfg: self,
      visited: BitSet::with_capacity(self.blocks.len()),
      visit_stack: vec![(start, self[start].successors())]
    };
    po.visited.insert(start);
    po.traverse_successor();
    po
  }
}

impl<'a> Postorder<'a> {
  /// After this function is called, the top of the visit stack will have an
  /// empty list of successors.
  fn traverse_successor(&mut self) {
    while let Some(bb) = self.visit_stack.last_mut().and_then(|(_, it)| it.next()) {
      if self.visited.insert(bb) {
        self.visit_stack.push((bb, self.cfg[bb].successors()));
      }
    }
  }
}

impl<'a> Iterator for Postorder<'a> {
  type Item = (BlockId, &'a BasicBlock);

  fn next(&mut self) -> Option<Self::Item> {
    let bl = self.visit_stack.pop()?.0;
    self.traverse_successor();
    Some((bl, &self.cfg[bl]))
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.visit_stack.len(), Some(self.cfg.blocks.len() - self.visited.len()))
  }
}

trait Direction {
  const FORWARD: bool;
  const NEEDS_PREDS: bool;

  fn map_block<'a, D>(
    bl: &'a BasicBlock,
    d: &mut D,
    f: impl FnMut(usize, &'a Statement, &mut D),
    g: impl FnOnce(&'a Terminator, &mut D)
  );

  fn preferred_traverse<'a>(cfg: &'a Cfg, f: impl FnMut(BlockId, &'a BasicBlock));

  fn join_state_into_successors<'a, D>(
    cfg: &Cfg,
    id: BlockId,
    exit_state: &'a D,
    propagate: impl FnMut(BlockId, &'a D)
  );
}

struct Backward;

impl Direction for Backward {
  const FORWARD: bool = false;
  const NEEDS_PREDS: bool = true;

  #[inline] fn map_block<'a, D>(
    bl: &'a BasicBlock,
    d: &mut D,
    mut f: impl FnMut(usize, &'a Statement, &mut D),
    g: impl FnOnce(&'a Terminator, &mut D)
  ) {
    g(bl.terminator(), d);
    bl.stmts.iter().enumerate().rev().for_each(|(bl, s)| f(bl, s, d))
  }

  fn preferred_traverse<'a>(cfg: &'a Cfg, mut f: impl FnMut(BlockId, &'a BasicBlock)) {
    cfg.postorder(BlockId::ENTRY).for_each(|(id, bl)| f(id, bl))
  }

  fn join_state_into_successors<'a, D>(
    cfg: &Cfg, id: BlockId, exit_state: &'a D,
    mut propagate: impl FnMut(BlockId, &'a D)
  ) {
    cfg.predecessors()[id].iter().for_each(|&pred| propagate(pred, exit_state))
  }
}

struct Forward;

impl Direction for Forward {
  const FORWARD: bool = true;
  const NEEDS_PREDS: bool = false;

  #[inline] fn map_block<'a, D>(
    bl: &'a BasicBlock,
    d: &mut D,
    mut f: impl FnMut(usize, &'a Statement, &mut D),
    g: impl FnOnce(&'a Terminator, &mut D)
  ) {
    bl.stmts.iter().enumerate().for_each(|(bl, s)| f(bl, s, d));
    g(bl.terminator(), d)
  }

  fn preferred_traverse<'a>(cfg: &'a Cfg, mut f: impl FnMut(BlockId, &'a BasicBlock)) {
    cfg.postorder(BlockId::ENTRY).map(|(id, _)| id).collect::<Vec<_>>()
      .iter().rev().for_each(|&id| f(id, &cfg[id]))
  }

  fn join_state_into_successors<'a, D>(
    cfg: &Cfg, id: BlockId, exit_state: &'a D,
    mut propagate: impl FnMut(BlockId, &'a D)
  ) {
    cfg[id].successors().for_each(|tgt| propagate(tgt, exit_state))
  }
}

struct Location {
  _block: BlockId,
  _stmt: usize,
}

impl BlockId {
  #[inline] #[must_use]
  fn at_stmt(self, stmt: usize) -> Location { Location { _block: self, _stmt: stmt } }
}

trait Domain: Clone {
  /// Compute the least upper bound of `self` and `other`,
  /// storing into `self` and returning `true` if `self` changed as a result.
  fn join(&mut self, other: &Self) -> bool;
}

trait DualDomain: Clone {
  /// Compute the greatest lower bound of `self` and `other`,
  /// storing into `self` and returning `true` if `self` changed as a result.
  fn meet(&mut self, other: &Self) -> bool;
}

/// The dual of a [`Domain`] as a [`DualDomain`] and vice versa.
#[repr(transparent)]
#[derive(Copy, Clone, Debug)]
pub struct Dual<T>(pub T);

impl<T: DualDomain> Domain for Dual<T> {
  fn join(&mut self, other: &Self) -> bool { self.0.meet(&other.0) }
}
impl<T: Domain> DualDomain for Dual<T> {
  fn meet(&mut self, other: &Self) -> bool { self.0.join(&other.0) }
}

impl Domain for () {
  fn join(&mut self, _: &Self) -> bool { false }
}

impl DualDomain for () {
  fn meet(&mut self, _: &Self) -> bool { false }
}

impl Domain for bool {
  fn join(&mut self, other: &Self) -> bool {
    *other && !*self && { *self = true; true }
  }
}
impl DualDomain for bool {
  fn meet(&mut self, other: &Self) -> bool {
    !*other && *self && { *self = false; true }
  }
}

impl<T> Domain for BitSet<T> {
  fn join(&mut self, other: &Self) -> bool { self.union_with(other) }
}
impl<T> DualDomain for BitSet<T> {
  fn meet(&mut self, other: &Self) -> bool { self.intersect_with(other) }
}

impl<K: Clone + Hash + Eq, V: Domain> Domain for im::HashMap<K, V> {
  fn join(&mut self, other: &Self) -> bool {
    let mut changed = false;
    for (k, v2) in other {
      if let Some(v1) = self.get_mut(k) {
        changed |= v1.join(v2)
      } else {
        self.insert(k.clone(), v2.clone());
        changed = true
      }
    }
    changed
  }
}

impl<K: Clone + Hash + Eq> Domain for im::HashSet<K> {
  fn join(&mut self, other: &Self) -> bool {
    let mut changed = false;
    for k in other {
      changed |= self.insert(k.clone()).is_none();
    }
    changed
  }
}

impl<K: Clone + Hash + Eq> DualDomain for im::HashSet<K> {
  fn meet(&mut self, other: &Self) -> bool {
    let old = std::mem::take(self);
    for value in other {
      if old.contains(value) {
        self.insert(value.clone());
      }
    }
    self.len() != old.len()
  }
}

trait Domains {
  type Item;
  fn cloned(&self, id: BlockId) -> Self::Item;
  fn join(&mut self, id: BlockId, other: &Self::Item) -> bool;
}

impl<D: Domains> Domains for &mut D {
  type Item = D::Item;
  fn cloned(&self, id: BlockId) -> D::Item { (**self).cloned(id) }
  fn join(&mut self, id: BlockId, other: &D::Item) -> bool { (**self).join(id, other) }
}

impl<D: Domain> Domains for BlockVec<D> {
  type Item = D;
  fn cloned(&self, id: BlockId) -> D { self[id].clone() }
  fn join(&mut self, id: BlockId, other: &D) -> bool { self[id].join(other) }
}

impl<D: DualDomain> Domains for Dual<BlockVec<D>> {
  type Item = D;
  fn cloned(&self, id: BlockId) -> D { self.0[id].clone() }
  fn join(&mut self, id: BlockId, other: &D) -> bool { self.0[id].meet(other) }
}

impl Domains for BitSet<BlockId> {
  type Item = bool;
  fn cloned(&self, id: BlockId) -> bool { self.contains(id) }
  fn join(&mut self, id: BlockId, other: &bool) -> bool { *other && self.insert(id) }
}

impl Domains for Dual<BitSet<BlockId>> {
  type Item = bool;
  fn cloned(&self, id: BlockId) -> bool { self.0.contains(id) }
  fn join(&mut self, id: BlockId, other: &bool) -> bool { !*other && self.0.remove(id) }
}

trait Analysis {
  type Dir: Direction;
  type Doms: Domains;

  /// Compute the initial value of the blocks (from the top for forward passes,
  /// and from the bottom for backward passes).
  fn bottom(&mut self, cfg: &Cfg) -> Self::Doms;

  fn apply_statement(&mut self,
    _: Location, _: &Statement, _: &mut <Self::Doms as Domains>::Item) {}

  fn apply_terminator(&mut self,
    _: BlockId, _: &Terminator, _: &mut <Self::Doms as Domains>::Item) {}

  fn apply_trans_for_block(&mut self,
    id: BlockId, bl: &BasicBlock, d: &mut <Self::Doms as Domains>::Item
  ) {
    self.do_apply_trans_for_block(id, bl, d)
  }

  /* Default implementations of methods, not intended for overriding: */

  fn do_apply_trans_for_block(&mut self,
    id: BlockId, bl: &BasicBlock, d: &mut <Self::Doms as Domains>::Item
  ) {
    Self::Dir::map_block(bl, &mut (self, d),
      |n, stmt, (this, d)| this.apply_statement(id.at_stmt(n), stmt, d),
      |term, (this, d)| this.apply_terminator(id, term, d))
  }

  fn iterate_to_fixpoint(&mut self, cfg: &mut Cfg) -> Self::Doms {
    if Self::Dir::NEEDS_PREDS { cfg.compute_predecessors(); }
    let mut queue = WorkQueue::with_capacity(cfg.blocks.len());
    Self::Dir::preferred_traverse(cfg, |id, _| { queue.insert(id); });
    let mut entry_sets = self.bottom(cfg);
    self.iterate_to_fixpoint_from(cfg, &mut queue, &mut entry_sets);
    entry_sets
  }

  fn iterate_to_fixpoint_from(&mut self, cfg: &Cfg,
    queue: &mut WorkQueue<BlockId>, entry_sets: &mut Self::Doms
  ) {
    while let Some(id) = queue.pop() {
      let bl = &cfg[id];
      let mut state = entry_sets.cloned(id);
      self.apply_trans_for_block(id, bl, &mut state);
      Self::Dir::join_state_into_successors(cfg, id, &state, |tgt, state| {
        if entry_sets.join(tgt, state) { queue.insert(tgt); }
      })
    }
  }
}

/// Perform MIR analysis and optimize the given procedure.
pub fn optimize(_proc: &mut Proc) {

}