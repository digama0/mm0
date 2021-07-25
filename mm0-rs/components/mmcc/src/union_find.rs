// Warning: This file has been adapted from the ena crate, so it has
// a different license.
//
// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Union-find implementation. The main type is `UnificationTable`.
//!
//! You can define your own type for the *keys* in the table, but you
//! must implement `Idx` for that type. The assumption is that
//! keys will be newtyped integers, hence we require that they
//! implement `Copy`.
//!
//! Keys can have values associated with them. The assumption is that
//! these values are cheaply cloneable (ideally, `Copy`), and some of
//! the interfaces are oriented around that assumption. If you just
//! want the classical "union-find" algorithm where you group things
//! into sets, use the `Value` type of `()`.
//!
//! When you have keys with non-trivial values, you must also define
//! how those values can be merged. As part of doing this, you can
//! define the "error" type to return on error; if errors are not
//! possible, use `NoError` (an uninstantiable struct). Using this
//! type also unlocks various more ergonomic methods (e.g., `union()`
//! in place of `unify_var_var()`).

use std::fmt::Debug;

use super::types::{Idx, IdxVec};

/// Trait implemented for a context that defines how to merge the values from two keys that
/// are unioned together. This merging can be fallible. If you attempt
/// to union two keys whose values cannot be merged, then the error is
/// propagated up and the two keys are not unioned.
///
/// This crate provides implementations of `UnifyValue` for `()`
/// (which is infallible) and `Option<T>` (where `T: UnifyValue`). The
/// option implementation merges two sum-values using the `UnifyValue`
/// implementation of `T`.
///
/// See also `EqUnifyValue`, which is a convenience trait for cases
/// where the "merge" operation succeeds only if the two values are
/// equal.
pub(crate) trait UnifyCtx<V> {
  /// Defines the type to return when merging of two values fails.
  /// If merging is infallible, use the special struct `NoError`
  /// found in this crate, which unlocks various more convenient
  /// methods on the unification table.
  type Error;

  /// Given two values, produce a new value that combines them.
  /// If that is not possible, produce an error.
  fn unify_values(&mut self, value1: &V, value2: &V) -> Result<V, Self::Error>;
}

impl UnifyCtx<()> for () {
  type Error = std::convert::Infallible;
  fn unify_values(&mut self, _: &(), _: &()) -> Result<(), Self::Error> { Ok(()) }
}

/// Value of a unification key. We implement Tarjan's union-find
/// algorithm: when two keys are unified, one of them is converted
/// into a "redirect" pointing at the other. These redirects form a
/// DAG: the roots of the DAG (nodes that are not redirected) are each
/// associated with a value of type `V` and a rank. The rank is used
/// to keep the DAG relatively balanced, which helps keep the running
/// time of the algorithm under control. For more information, see
/// <http://en.wikipedia.org/wiki/Disjoint-set_data_structure>.
#[derive(PartialEq, Clone, Debug)]
struct VarValue<K, V> {
  parent: K,     // if equal to self, this is a root
  value: V, // value assigned (only relevant to root)
  rank: u32,     // max depth (only relevant to root)
}

/// Table of unification keys and their values. You must define a key type K
/// that implements the `Idx` trait.
#[derive(Clone, Debug)]
pub(crate) struct UnificationTable<K, V> {
  values: IdxVec<K, VarValue<K, V>>,
}

impl<K, V> Default for UnificationTable<K, V> {
  fn default() -> Self { Self { values: Default::default() } }
}

impl<K, V> VarValue<K, V> {
  fn new_var(key: K, value: V) -> VarValue<K, V> {
    VarValue {parent: key, value, rank: 0}
  }

  fn redirect(&mut self, to: K) {
    self.parent = to;
  }

  fn root(&mut self, rank: u32, value: V) {
    self.rank = rank;
    self.value = value;
  }
}

impl<K: PartialEq + Copy, V> VarValue<K, V> {
  fn parent(&self, self_key: K) -> Option<K> {
    if self.parent == self_key {
      None
    } else {
      Some(self.parent)
    }
  }
}

impl<K, V> UnificationTable<K, V> {
  /// Returns the number of keys created so far.
  #[must_use] pub(crate) fn len(&self) -> usize {
    self.values.len()
  }
  /// Returns true if there are no keys.
  #[must_use] pub(crate) fn is_empty(&self) -> bool {
    self.values.is_empty()
  }

  /// Reserve memory for `num_new_keys` to be created. Does not
  /// actually create the new keys; you must then invoke `new_key`.
  pub(crate) fn reserve(&mut self, num_new_keys: usize) {
    self.values.0.reserve(num_new_keys);
  }
}

impl<K: Idx, V> UnificationTable<K, V> {
  /// Creates a fresh key with the given value.
  pub(crate) fn new_key(&mut self, value: V) -> K {
    let len = self.values.len();
    let key: K = Idx::from_usize(len);
    self.values.push(VarValue::new_var(key, value));
    key
  }

  /// Initializes a unification table with a function that computes all
  /// the values from all the keys up to some bound.
  pub(crate) fn from_fn(sz: K, mut value: impl FnMut(K) -> V) -> Self {
    let it = (0..sz.into_usize()).map(|i| {
      let key = K::from_usize(i);
      VarValue::new_var(key, value(key))
    });
    Self { values: it.collect::<Vec<_>>().into() }
  }

  /// Clears all unifications that have been performed, resetting to
  /// the initial state. The values of each variable are given by
  /// the closure.
  pub(crate) fn reset_unifications(&mut self, mut value: impl FnMut(K) -> V) {
    for (key, vv) in self.values.enum_iter_mut() {
      let value = value(key);
      *vv = VarValue::new_var(key, value)
    }
  }

  /// Obtains the current value for a particular key.
  /// Not for end-users; they can use `probe_value`.
  fn value(&self, key: K) -> &VarValue<K, V> {
    &self.values[key]
  }

  /// Find the root node for `vid`. This uses the standard
  /// union-find algorithm with path compression:
  /// <http://en.wikipedia.org/wiki/Disjoint-set_data_structure>.
  ///
  /// NB. This is a building-block operation and you would probably
  /// prefer to call `probe` below.
  ///
  /// This is an always-inlined version of this function for the hot
  /// callsites. `uninlined_get_root_key` is the never-inlined version.
  #[inline(always)]
  fn inlined_get_root_key(&mut self, vid: K) -> K {
    let redirect = {
      match self.value(vid).parent(vid) {
        None => return vid,
        Some(redirect) => redirect,
      }
    };

    let root_key: K = self.uninlined_get_root_key(redirect);
    if root_key != redirect {
      // Path compression
      self.update_value(vid, |value| value.parent = root_key);
    }

    root_key
  }

  // This is a never-inlined version of this function for cold callsites.
  // 'inlined_get_root_key` is the always-inlined version.
  #[inline(never)]
  fn uninlined_get_root_key(&mut self, vid: K) -> K {
    self.inlined_get_root_key(vid)
  }

  fn update_value(&mut self, key: K, op: impl FnOnce(&mut VarValue<K, V>)) {
    op(&mut self.values[key])
  }

  /// Either redirects `node_a` to `node_b` or vice versa, depending
  /// on the relative rank. The value associated with the new root
  /// will be `new_value`.
  ///
  /// NB: This is the "union" operation of "union-find". It is
  /// really more of a building block. If the values associated with
  /// your key are non-trivial, you would probably prefer to call
  /// `unify_var_var` below.
  fn unify_roots(&mut self, key_a: K, key_b: K, new_value: V) {
    let rank_a = self.value(key_a).rank;
    let rank_b = self.value(key_b).rank;
    if rank_a > rank_b {
      // a has greater rank, so a should become b's parent,
      // i.e., b should redirect to a.
      self.redirect_root(rank_a, key_b, key_a, new_value);
    } else if rank_a < rank_b {
      // b has greater rank, so a should redirect to b.
      self.redirect_root(rank_b, key_a, key_b, new_value);
    } else {
      // If equal, redirect one to the other and increment the
      // other's rank.
      self.redirect_root(rank_a + 1, key_a, key_b, new_value);
    }
  }

  /// Internal method to redirect `old_root_key` (which is currently
  /// a root) to a child of `new_root_key` (which will remain a
  /// root). The rank and value of `new_root_key` will be updated to
  /// `new_rank` and `new_value` respectively.
  fn redirect_root(
    &mut self,
    new_rank: u32,
    old_root_key: K,
    new_root_key: K,
    new_value: V,
  ) {
    self.update_value(old_root_key, |old_root_value| {
      old_root_value.redirect(new_root_key);
    });
    self.update_value(new_root_key, |new_root_value| {
      new_root_value.root(new_rank, new_value);
    });
  }

  /// Given two keys, indicates whether they have been unioned together.
  pub(crate) fn unioned(&mut self, a_id: impl Into<K>, b_id: impl Into<K>) -> bool {
    self.find(a_id) == self.find(b_id)
  }

  /// Given a key, returns the (current) root key.
  pub(crate) fn find(&mut self, id: impl Into<K>) -> K {
    let id = id.into();
    self.uninlined_get_root_key(id)
  }

  /// Unions together two variables, merging their values. If
  /// merging the values fails, the error is propagated and this
  /// method has no effect.
  pub(crate) fn unify_var_var<S: UnifyCtx<V>>(&mut self,
    ctx: &mut S, a_id: impl Into<K>, b_id: impl Into<K>
  ) -> Result<(), S::Error> {
    let a_id = a_id.into();
    let b_id = b_id.into();

    let root_a = self.uninlined_get_root_key(a_id);
    let root_b = self.uninlined_get_root_key(b_id);

    if root_a == root_b {
      return Ok(());
    }

    let combined = ctx.unify_values(&self.value(root_a).value, &self.value(root_b).value)?;

    self.unify_roots(root_a, root_b, combined);
    Ok(())
  }

  /// Sets the value of the key `a_id` to `b`, attempting to merge
  /// with the previous value.
  pub(crate) fn unify_var_value<S: UnifyCtx<V>>(&mut self,
    ctx: &mut S, a_id: impl Into<K>, b: &V
  ) -> Result<(), S::Error> {
    let a_id = a_id.into();
    let root_a = self.uninlined_get_root_key(a_id);
    let value = ctx.unify_values(&self.value(root_a).value, b)?;
    self.update_value(root_a, |node| node.value = value);
    Ok(())
  }
}

impl<K: Idx, V> UnificationTable<K, V> {
  /// Returns the current value for the given key. If the key has
  /// been union'd, this will give the value from the current root.
  pub(crate) fn probe_value(&mut self, id: impl Into<K>) -> &V {
    self.inlined_probe_value(id)
  }

  /// An always-inlined version of `probe_value`, for hot callsites.
  #[inline(always)]
  pub(crate) fn inlined_probe_value(&mut self, id: impl Into<K>) -> &V {
    let id = id.into();
    let id = self.inlined_get_root_key(id);
    &self.value(id).value
  }
}
