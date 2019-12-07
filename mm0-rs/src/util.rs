use std::hash::{Hash, BuildHasher};
use std::collections::{HashMap, hash_map::{Entry, OccupiedEntry}};

pub trait HashMapExt<K, V> {
  fn try_insert(&mut self, k: K, v: V) -> Option<(V, OccupiedEntry<K, V>)>;
}
impl<K: Hash + Eq, V, S: BuildHasher> HashMapExt<K, V> for HashMap<K, V, S> {
  fn try_insert(&mut self, k: K, v: V) -> Option<(V, OccupiedEntry<K, V>)> {
    match self.entry(k) {
      Entry::Vacant(e) => { e.insert(v); None }
      Entry::Occupied(e) => Some((v, e))
    }
  }
}