use std::sync::{Arc, Mutex};
use std::collections::{HashMap, hash_map::Entry};
use super::environment::{AtomID, Type as EType};
use crate::parser::ast::{Decl, Binder, Type, DepType, LocalKind};
use super::*;
use super::lisp::{LispVal, LispKind, Annot, Uncons, InferTarget};
use crate::util::*;

#[derive(Debug)]
pub enum InferSort {
  KnownBound { dummy: bool, sort: SortID },
  KnownReg {sort: SortID, deps: Vec<AtomID> },
  Unknown { must_bound: bool, sorts: HashMap<Option<SortID>, LispVal> },
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

fn new_mvar(mvars: &mut Vec<LispVal>, tgt: InferTarget) -> LispVal {
  let n = mvars.len();
  let e = Arc::new(LispKind::Ref(Mutex::new(Arc::new(LispKind::MVar(n, tgt)))));
  mvars.push(e.clone());
  e
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

  pub fn new_mvar(&mut self, tgt: InferTarget) -> LispVal {
    new_mvar(&mut self.mvars, tgt)
  }

  fn var(&mut self, x: AtomID) -> &mut InferSort {
    self.vars.entry(x).or_default()
  }
}

fn decorate_span(fsp: &Option<FileSpan>, e: LispKind) -> LispVal {
  if let Some(fsp) = fsp {
    Arc::new(LispKind::Annot(Annot::Span(fsp.clone()), Arc::new(e)))
  } else {Arc::new(e)}
}

struct ElabTerm<'a> {
  lc: &'a mut LocalContext,
  env: &'a Environment,
  fsp: FileSpan,
}

impl<'a> ElabTerm<'a> {
  fn try_get_span(&self, e: &LispKind) -> Span {
    match e.fspan() {
      Some(fsp) if self.fsp.file == fsp.file && fsp.span.start >= self.fsp.span.start => fsp.span,
      _ => self.fsp.span,
    }
  }

  fn atom(&mut self, e: &LispVal, a: AtomID, tgt: InferTarget) -> Result<LispVal> {
    match (self.lc.vars.entry(a).or_default(), tgt) {
      (InferSort::KnownReg {..}, InferTarget::Bound(_)) =>
        Err(ElabError::new_e(self.try_get_span(e), "expected a bound variable, got regular variable")),
      (&mut InferSort::KnownBound {sort, ..}, InferTarget::Bound(sa)) => {
        let s = self.env.data[sa].sort.unwrap();
        if s == sort {Ok(decorate_span(&e.fspan(), LispKind::Atom(a)))}
        else {
          Err(ElabError::new_e(self.try_get_span(e),
            format!("type error: expected {}, got {}", self.env.sorts[s].name, self.env.sorts[sort].name)))
        }
      }
      (InferSort::Unknown {must_bound, sorts}, tgt) => {
        let s = match tgt {
          InferTarget::Bound(sa) => {*must_bound = true; Some(self.env.data[sa].sort.unwrap())}
          InferTarget::Reg(sa) => Some(self.env.data[sa].sort.unwrap()),
          _ => None,
        };
        let mvars = &mut self.lc.mvars;
        Ok(sorts.entry(s).or_insert_with(|| new_mvar(mvars, tgt)).clone())
      }
      (&mut InferSort::KnownReg {sort, ..}, tgt) => self.coerce(e, sort, LispKind::Atom(a), tgt),
      (&mut InferSort::KnownBound {sort, ..}, tgt) => self.coerce(e, sort, LispKind::Atom(a), tgt),
    }
  }

  fn list(&mut self, e: &LispVal,
    mut it: impl Iterator<Item=LispVal>, tgt: InferTarget) -> Result<LispVal> {
    let t = it.next().unwrap();
    let a = t.as_atom().ok_or_else(|| ElabError::new_e(self.try_get_span(&t), "expected an atom"))?;
    let tid = self.env.term(a).ok_or_else(||
      ElabError::new_e(self.try_get_span(&t), format!("term '{}' not declared", self.env.data[a].name)))?;
    let tdata = &self.env.terms[tid];
    let mut tys = tdata.args.iter();
    let mut args = vec![decorate_span(&t.fspan(), LispKind::Atom(a))];
    for arg in it {
      let tgt = match tys.next().ok_or_else(||
        ElabError::new_e(self.try_get_span(&e),
          format!("expected {} arguments, got {}", tdata.args.len(), e.len() - 1)))?.1 {
        EType::Bound(s) => InferTarget::Bound(self.env.sorts[s].atom),
        EType::Reg(s, _) => InferTarget::Reg(self.env.sorts[s].atom),
      };
      args.push(self.expr(&arg, tgt)?);
    }
    self.coerce(e, tdata.ret.sort(), LispKind::List(args), tgt)
  }

  fn coerce(&self, src: &LispVal, from: SortID, res: LispKind, tgt: InferTarget) -> Result<LispVal> {
    let fsp = src.fspan();
    let res = decorate_span(&fsp, res);
    let to = match tgt {
      InferTarget::Unknown => return Ok(res),
      InferTarget::Provable if self.env.sorts[from].mods.contains(Modifiers::PROVABLE) => return Ok(res),
      InferTarget::Provable => *self.env.pe.coe_prov.get(&from).ok_or_else(||
        ElabError::new_e(self.try_get_span(&src),
          format!("type error: expected provable sort, got {}", self.env.sorts[from].name)))?,
      InferTarget::Reg(to) => self.env.data[to].sort.unwrap(),
      InferTarget::Bound(_) => return Err(ElabError::new_e(
        self.try_get_span(&src), "expected a variable"))
    };
    if from == to {return Ok(res)}
    if let Some(c) = self.env.pe.coes.get(&from).and_then(|m| m.get(&to)) {
      fn apply(c: &Coe, f: impl FnOnce(TermID, LispVal) -> LispVal + Copy, e: LispVal) -> LispVal {
        match c {
          &Coe::One(_, tid) => f(tid, e),
          Coe::Trans(c1, _, c2) => apply(c2, f.clone(), apply(c1, f, e)),
        }
      }
      Ok(apply(c, |tid, e| decorate_span(&fsp, LispKind::List(
        vec![Arc::new(LispKind::Atom(self.env.terms[tid].atom)), e])), res))
    } else {
      Err(ElabError::new_e(self.try_get_span(&src),
        format!("type error: expected {}, got {}", self.env.sorts[to].name, self.env.sorts[from].name)))
    }
  }

  fn other(&self, e: &LispVal, _: InferTarget) -> Result<LispVal> {
    Err(ElabError::new_e(self.try_get_span(e), "Not a valid expression"))
  }

  fn expr(&mut self, e: &LispVal, tgt: InferTarget) -> Result<LispVal> {
    e.unwrapped(|r| match r {
      &LispKind::Atom(a) if self.env.term(a).is_some() =>
        self.list(e, Some(e.clone()).into_iter(), tgt),
      &LispKind::Atom(a) => self.atom(e, a, tgt),
      LispKind::DottedList(es, r) if es.is_empty() => self.expr(r, tgt),
      LispKind::List(es) if es.len() == 1 => self.expr(&es[0], tgt),
      LispKind::List(_) | LispKind::DottedList(_, _) if e.at_least(2) =>
        self.list(e, Uncons::from(e.clone()), tgt),
      _ => self.other(e, tgt),
    })
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
        let a = self.env.get_atom(self.ast.span(sort));
        let sort = self.data[a].sort.ok_or_else(|| ElabError::new_e(sort, "sort not found"))?;
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
        let e = self.eval_qexpr(e)?;
        let e = self.elaborate_term(f.0, &e, InferTarget::Provable)?;
        InferBinder::Hyp(x, e)
      },
    })
  }

  fn elaborate_term(&mut self, sp: Span, e: &LispVal, tgt: InferTarget) -> Result<LispVal> {
    ElabTerm {
      fsp: self.fspan(sp),
      lc: &mut self.lc,
      env: &self.env,
    }.expr(e, tgt)
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
        Ok(InferBinder::Hyp(x, e)) => hyps.push((x, e)),
      }
    }
    match d.k {
      _ => self.report(ElabError::new_e(d.id, "unimplemented"))
    }
  }
}