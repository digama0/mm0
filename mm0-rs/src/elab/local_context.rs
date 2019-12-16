use std::ops::{Deref, DerefMut};
use std::sync::{Arc, Mutex};
use std::collections::{HashMap, hash_map::Entry};
use super::environment::AtomID;
use crate::parser::ast::{Decl, Binder, Type, DepType, LocalKind};
use super::{Elaborator, FileServer, ElabError, Result, math_parser::QExpr};
use super::lisp::{LispVal, LispKind, Uncons};
use crate::util::*;

#[derive(Debug)]
pub enum InferSort {
  KnownBound { dummy: bool, sort: AtomID },
  KnownReg {sort: AtomID, deps: Vec<AtomID> },
  Unknown { must_bound: bool, sorts: HashMap<AtomID, LispVal> },
}

impl Default for InferSort {
  fn default() -> InferSort { InferSort::Unknown { must_bound: false, sorts: HashMap::new() } }
}

#[derive(Default, Debug)]
pub struct LocalContext {
  pub vars: HashMap<AtomID, InferSort>,
  pub var_order: Vec<(Option<AtomID>, Option<InferSort>)>, // InferSort only populated for anonymous vars
  pub mvars: Vec<LispVal>,
  pub goals: Vec<LispVal>,
}

impl LocalContext {
  pub fn new() -> LocalContext { Self::default() }

  pub fn clear(&mut self) {
    self.mvars.clear();
    self.goals.clear();
  }

  pub fn set_goals(&mut self, gs: impl IntoIterator<Item=LispVal>) {
    self.goals.clear();
    for g in gs {
      if g.is_goal() {
        self.goals.push(if g.is_ref() {g} else {
          Arc::new(LispKind::Ref(Mutex::new(g)))
        })
      }
    }
  }

  pub fn new_mvar(&mut self, sort: AtomID, bound: bool) -> LispVal {
    let n = self.mvars.len();
    let e = Arc::new(LispKind::Ref(Mutex::new(Arc::new(LispKind::MVar(n, sort, bound)))));
    self.mvars.push(e.clone());
    e
  }

  fn var(&mut self, x: AtomID) -> &mut InferSort {
    self.vars.entry(x).or_default()
  }
}

enum InferBinder {
  Var(Option<AtomID>, InferSort),
  Hyp(Option<AtomID>, LispVal),
}

impl<'a, F: FileServer + ?Sized> Elaborator<'a, F> {
  fn elab_binder(&mut self, error: &mut bool, x: Option<Span>, lk: LocalKind, ty: Option<&Type>) -> Result<InferBinder> {
    let x = if lk == LocalKind::Anon {None} else {x.map(|x| self.env.get_atom(self.ast.span(x)))};
    Ok(match ty {
      None => InferBinder::Var(x, InferSort::Unknown {must_bound: lk.is_bound(), sorts: HashMap::new()}),
      Some(&Type::DepType(DepType {sort, ref deps})) => InferBinder::Var(x, {
        let sort = self.env.get_atom(self.ast.span(sort));
        if lk.is_bound() {
          if !deps.is_empty() {
            self.report(ElabError::new_e(
              deps[0].start..deps.last().unwrap().end, "dependencies not allowed in curly binders"));
            *error = true;
          }
          InferSort::KnownBound {dummy: lk == LocalKind::Dummy, sort}
        } else {
          InferSort::KnownReg {
            sort,
            deps: deps.iter().map(|&y| {
              let y = self.env.get_atom(self.ast.span(y));
              self.lc.var(y);
              y
            }).collect()
          }
        }
      }),
      Some(&Type::Formula(f)) => {
        let e = self.parse_formula(f)?;
        InferBinder::Hyp(x, self.eval_qexpr(e)?)
      },
    })
  }
}

#[derive(Copy, Clone)]
enum InferTarget {
  Unknown,
  Provable,
  Bound(AtomID),
  Reg(AtomID),
}

impl<'a, F: FileServer + ?Sized> Elaborator<'a, F> {
  fn try_get_span(&self, sp: Span, e: &LispKind) -> Span {
    match e.fspan() {
      Some(fsp) if self.path == fsp.file && fsp.span.start >= sp.start => fsp.span,
      _ => sp,
    }
  }

  fn elaborate_atom(&mut self, a: AtomID, tgt: InferTarget) -> Result<LispVal> {
    unimplemented!()
  }
  fn elaborate_term_uncons(&mut self, sp: Span, mut u: Uncons, tgt: InferTarget) -> Result<LispVal> {
    let t = u.next().unwrap();
    let a = match t.as_atom() {
      Some(a) => a,
      None => return Err(ElabError::new_e(self.try_get_span(sp, &t), "Expected an atom"))
    };
    unimplemented!()
  }
  fn elaborate_term_other(&self, sp: Span, e: &LispVal, tgt: InferTarget) -> Result<LispVal> {
    Err(ElabError::new_e(self.try_get_span(sp, e), "Not a valid expression"))
  }
  fn elaborate_term(&mut self, sp: Span, e: &LispVal, tgt: InferTarget) -> Result<LispVal> {
    match &**e {
      &LispKind::Atom(a) => self.elaborate_atom(a, tgt),
      LispKind::DottedList(es, r) if es.is_empty() => self.elaborate_term(sp, r, tgt),
      LispKind::List(es) if es.len() == 1 => self.elaborate_term(sp, &es[0], tgt),
      LispKind::List(_) | LispKind::DottedList(_, _) if e.at_least(2) =>
        self.elaborate_term_uncons(sp, Uncons::from(e.clone()), tgt),
      _ => self.elaborate_term_other(sp, e, tgt),
    }
  }

  pub fn elab_decl(&mut self, d: &Decl) {
    let mut hyps = Vec::new();
    let mut error = false;
    for (span, xsp, lk, ty) in d.bis.iter()
      .map(|Binder {span, local: (x, lk), ty}| (*span, Some(*x), *lk, ty.as_ref()))
      .chain(d.ty.iter().flat_map(|v| v.0.iter()
        .map(|ty| (ty.span(), None, LocalKind::Anon, Some(ty))))) {
      match self.elab_binder(&mut error, xsp, lk, ty) {
        Err(e) => { self.report(e); error = true }
        Ok(InferBinder::Var(x, is)) => {
          if !hyps.is_empty() {
            self.report(ElabError::new_e(span, "hypothesis binders must come after variable binders"));
            error = true;
          }
          if let Some(x) = x {
            match self.lc.vars.entry(x) {
              Entry::Vacant(e) => {e.insert(is);}
              Entry::Occupied(mut e) => {
                e.insert(is);
                self.report(ElabError::new_e(xsp.unwrap(), "variable occurs twice in binder list"));
                error = true;
              }
            }
            self.lc.var_order.push((Some(x), None));
          } else {
            self.lc.var_order.push((None, Some(is)));
          }
        }
        Ok(InferBinder::Hyp(x, f)) => hyps.push((x, f)),
      }
    }
    match d.k {
      _ => self.report(ElabError::new_e(d.id, "unimplemented"))
    }
  }
}