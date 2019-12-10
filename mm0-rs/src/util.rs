use std::ops::Deref;
use std::borrow::Borrow;
use std::mem::{self, MaybeUninit};
use std::fmt;
use std::error::Error;
use std::sync::Arc;
use std::hash::{Hash, BuildHasher};
use std::collections::{HashMap, hash_map::{Entry, OccupiedEntry}};

pub type BoxError = Box<dyn Error + Send + Sync>;

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

#[derive(Clone, Hash, PartialEq, Eq)] pub struct ArcString(pub Arc<String>);

impl Borrow<str> for ArcString {
  fn borrow(&self) -> &str { &*self.0 }
}
impl Deref for ArcString {
  type Target = str;
  fn deref(&self) -> &str { &*self.0 }
}
impl ArcString {
  pub fn new(s: String) -> ArcString { ArcString(Arc::new(s)) }
}
impl fmt::Display for ArcString {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
}
impl From<&str> for ArcString {
  fn from(s: &str) -> ArcString { ArcString::new(s.to_owned()) }
}

pub struct VecUninit<T>(Vec<MaybeUninit<T>>);

impl<T> VecUninit<T> {
  pub fn new(size: usize) -> Self {
    let mut res = Vec::with_capacity(size);
    unsafe { res.set_len(size) };
    VecUninit(res)
  }

  pub fn set(&mut self, i: usize, val: T) {
    self.0[i] = MaybeUninit::new(val);
  }

  pub unsafe fn assume_init(self) -> Vec<T> {
    mem::transmute(self.0)
  }
}