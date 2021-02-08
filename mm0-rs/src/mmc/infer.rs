//! Type inference and elaboration

/*
use std::cell::Cell;
use bumpalo::boxed::Box as BBox;
use super::types::ast::Type;

struct Task<'a> {
  trigger: Option<BBox<'a, dyn FnMut() -> bool>>,
  task: Option<BBox<'a, dyn FnMut()>>
}

impl<'a> Task<'a> {
  fn trigger(&mut self) -> bool {
    self.trigger.as_deref_mut().map_or(true, |f| f())
  }
  fn run(&mut self) {
    if let Some(f) = self.task.as_deref_mut() { f() }
  }
}
struct InferCtx<'a> {
  tasks: Vec<Task<'a>>,
  ty_mvars: Vec<&'a MVar<Type>>,
}

#[derive(Default)]
struct MVar<T>(Cell<Option<T>>);

impl<T> MVar<T> {
  fn set(&self, t: T) { self.0.set(Some(t)) }
}

*/