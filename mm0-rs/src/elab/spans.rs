use std::mem::MaybeUninit;
use std::collections::BTreeMap;
use super::environment::AtomID;
use super::local_context::LocalContext;
use crate::util::*;

pub struct Spans<T> {
  stmt: MaybeUninit<Span>,
  decl: MaybeUninit<AtomID>,
  pub lc: Option<LocalContext>,
  data: BTreeMap<usize, Vec<(Span, T)>>,
}

use std::fmt;
impl<T: fmt::Debug> fmt::Debug for Spans<T> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{{ stmt: {:?},\n  data: {:?} }}", self.stmt(), self.data)
  }
}

impl<T> Spans<T> {
  pub fn new() -> Spans<T> {
    Spans {
      stmt: MaybeUninit::uninit(),
      decl: MaybeUninit::uninit(),
      lc: None,
      data: BTreeMap::new()
    }
  }
  pub fn set_stmt(&mut self, sp: Span) { self.stmt = MaybeUninit::new(sp) }
  pub fn set_decl(&mut self, a: AtomID) { self.decl = MaybeUninit::new(a) }
  pub fn stmt(&self) -> Span { unsafe { self.stmt.assume_init() } }
  pub fn _decl(&self) -> AtomID { unsafe { self.decl.assume_init() } }
  pub fn insert(&mut self, sp: Span, val: T) -> &mut T {
    let v = self.data.entry(sp.start).or_default();
    for (sp1, k) in &mut *v {
      if sp == *sp1 {return unsafe {&mut *(k as *mut T)}}
    }
    // the unsafe above is needed because NLL support is not all there,
    // and this looks like a double borrow of `*v`
    v.push((sp, val));
    &mut v.last_mut().unwrap().1
  }
  pub fn insert_if(&mut self, sp: Span, val: impl FnOnce() -> T) {
    if sp.start >= self.stmt().start {
      self.insert(sp, val());
    }
  }

  pub fn _get(&self, sp: Span) -> Option<&T> {
    self.data.get(&sp.start).and_then(|v|
      v.iter().find(|x| x.0 == sp).map(|x| &x.1))
  }
  pub fn _get_mut(&mut self, sp: Span) -> Option<&mut T> {
    self.data.get_mut(&sp.start).and_then(|v|
      v.iter_mut().find(|x| x.0 == sp).map(|x| &mut x.1))
  }

  pub fn find_pos(&self, pos: usize) -> Vec<&(Span, T)> {
    if let Some((_, v)) = self.data.range(..=pos).rev().next() {
      v.iter().filter(|x| pos < x.0.end).collect()
    } else {vec![]}
  }
}
