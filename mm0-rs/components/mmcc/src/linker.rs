//! Handles layout of functions, globals, constants in the overall program.

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use crate::types::entity::{Entity, ProcTc};
use crate::types::mir::{ConstKind, Constant, Place, Proc, RValue, Terminator, Ty, Visitor};
use crate::types::vcode::{ConstId, GlobalId, ProcId};
use crate::types::Spanned;
use crate::{Idx, Symbol};

type GenericCall = (Symbol, Box<[Ty]>);

struct Collector<'a> {
  names: &'a HashMap<Symbol, Entity>,
  mir: &'a HashMap<Symbol, Proc>,
  implications: HashMap<Symbol, Option<HashSet<GenericCall>>>,
  funcs: (HashMap<Symbol, ProcId>, ProcId),
  globals: (HashMap<Symbol, GlobalId>, GlobalId),
  consts: (HashMap<Symbol, ConstId>, ConstId),
}

fn alloc<K: Hash + Eq, T: Idx>((map, next): &mut (HashMap<K, T>, T), k: K) -> T {
  let i = next.fresh();
  map.insert(k, i);
  i
}

impl<'a> Collector<'a> {
  fn new(names: &'a HashMap<Symbol, Entity>, mir: &'a HashMap<Symbol, Proc>) -> Self {
    Self {
      names,
      mir,
      implications: Default::default(),
      funcs: Default::default(),
      globals: Default::default(),
      consts: Default::default(),
    }
  }

  fn collect_generics(&mut self, f: Symbol, args: &[Ty], calls: &HashSet<GenericCall>) {
    for &(g, ref tys) in calls {
      let args: Box<[_]> = tys.iter().map(|ty| ty.subst(args)).collect();
      self.collect_func(g, &args);
    }
  }

  fn collect_func(&mut self, f: Symbol, args: &[Ty]) -> ProcId {
    if !args.is_empty() {
      unimplemented!("functions with type args")
    }
    if let Some(&id) = self.funcs.0.get(&f) { return id }
    let id = alloc(&mut self.funcs, f);
    if let Some(imps) = self.implications.get_mut(&f) {
      let calls = imps.take().expect("cycle in collector?");
      self.collect_generics(f, args, &calls);
      self.implications.insert(f, Some(calls));
    } else if let Some(proc) = self.mir.get(&f) {
      let mut calls = HashSet::new();
      for (_, bl) in proc.body.blocks() {
        struct ConstVisitor<'a, 'b>(&'b mut Collector<'a>);
        impl Visitor for ConstVisitor<'_, '_> {
          fn visit_place(&mut self, _: &Place) {}
          fn visit_constant(&mut self, c: &Constant) {
            if let ConstKind::Const(s) = c.k { self.0.collect_const(s); }
          }
        }
        ConstVisitor(self).visit_basic_block(bl);
        if let Terminator::Call { f, tys, .. } = bl.terminator() {
          if tys.iter().any(|ty| ty.has_tyvar()) {
            calls.insert((*f, tys.clone()));
          } else {
            self.collect_func(*f, tys);
          }
        }
      }
      self.implications.insert(f, None);
      self.collect_generics(f, args, &calls);
      self.implications.insert(f, Some(calls));
    }
    id
  }

  fn collect_const(&mut self, c: Symbol) -> ConstId {
    if let Some(&id) = self.consts.0.get(&c) { return id }
    alloc(&mut self.consts, c)
  }
}
