use std::ops::Deref;
use std::sync::Arc;
use std::mem;
use std::collections::{HashMap, hash_map::Entry};
use itertools::Itertools;
use super::environment::{AtomID, Type as EType};
use crate::parser::ast::{Decl, Type, DepType, LocalKind};
use super::*;
use super::lisp::{LispVal, LispKind, Uncons, InferTarget};
use super::proof::*;
use crate::util::*;

#[derive(Debug)]
pub enum InferSort {
  Bound { dummy: bool, sort: SortID },
  Reg { sort: SortID, deps: Vec<AtomID> },
  Unknown { src: Span, must_bound: bool, sorts: HashMap<Option<SortID>, LispVal> },
}

impl InferSort {
  fn new(src: Span) -> InferSort { InferSort::Unknown { src, must_bound: false, sorts: HashMap::new() } }
}

#[derive(Default, Debug)]
pub struct LocalContext {
  pub vars: HashMap<AtomID, InferSort>,
  pub var_order: Vec<(Span, Option<AtomID>, Option<InferSort>)>, // InferSort only populated for anonymous vars
  pub mvars: Vec<LispVal>,
  pub goals: Vec<LispVal>,
  pub proofs: HashMap<AtomID, usize>,
  pub proof_order: Vec<(AtomID, LispVal, LispVal)>,
}

fn new_mvar(mvars: &mut Vec<LispVal>, tgt: InferTarget) -> LispVal {
  let n = mvars.len();
  let e = LispKind::new_ref(Arc::new(LispKind::MVar(n, tgt)));
  mvars.push(e.clone());
  e
}

impl LocalContext {
  pub fn new() -> LocalContext { Self::default() }

  pub fn clear(&mut self) {
    self.vars.clear();
    self.var_order.clear();
    self.mvars.clear();
    self.goals.clear();
    self.proofs.clear();
    self.proof_order.clear();
  }

  pub fn set_goals(&mut self, gs: impl IntoIterator<Item=LispVal>) {
    self.goals.clear();
    for g in gs {
      if g.is_goal() {
        self.goals.push(if g.is_ref() {g} else {LispKind::new_ref(g)})
      }
    }
  }

  pub fn new_mvar(&mut self, tgt: InferTarget) -> LispVal {
    new_mvar(&mut self.mvars, tgt)
  }

  fn var(&mut self, x: AtomID, sp: Span) -> &mut InferSort {
    self.vars.entry(x).or_insert_with(|| InferSort::new(sp))
  }

  pub fn clean_mvars(&mut self) {
    let mut i = 0;
    self.mvars.retain(|e| e.as_ref_(|e| {
      LispKind::unwrapped_mut(e, |e| {
        if let LispKind::MVar(n, _) = e {*n = i; i += 1; true}
        else {false}
      }).unwrap_or_else(|| {
        match **e {
          LispKind::MVar(n, ref ty) => {
            if n != i {*e = LispKind::MVar(i, ty.clone()).decorate_span(&e.fspan())}
            i += 1; true
          }
          _ => false,
        }
      })
    }).unwrap())
  }

  pub fn get_proof(&self, a: AtomID) -> Option<&(AtomID, LispVal, LispVal)> {
    self.proofs.get(&a).map(|&i| &self.proof_order[i])
  }

  pub fn add_proof(&mut self, a: AtomID, e: LispVal, p: LispVal) {
    self.proofs.insert(a, self.proof_order.len());
    self.proof_order.push((a, e, p));
  }
}

struct ElabTerm<'a> {
  lc: &'a LocalContext,
  env: &'a Environment,
  fsp: FileSpan,
}

struct ElabTermMut<'a> {
  lc: &'a mut LocalContext,
  env: &'a Environment,
  fsp: FileSpan,
}
impl<'a> Deref for ElabTermMut<'a> {
  type Target = ElabTerm<'a>;
  fn deref(&self) -> &ElabTerm<'a> { unsafe { mem::transmute(self) } }
}

pub fn try_get_span(fsp: &FileSpan, e: &LispKind) -> Span {
  try_get_span_from(fsp, e.fspan().as_ref())
}

pub fn try_get_span_from(fsp: &FileSpan, fsp2: Option<&FileSpan>) -> Span {
  match fsp2 {
    Some(fsp2) if fsp.file == fsp2.file && fsp2.span.start >= fsp.span.start => fsp2.span,
    _ => fsp.span,
  }
}

impl Environment {
  pub fn apply_coe(&self, fsp: &Option<FileSpan>, c: &Coe, res: LispVal) -> LispVal {
    fn apply(c: &Coe, f: impl FnOnce(TermID, LispVal) -> LispVal + Clone, e: LispVal) -> LispVal {
      match c {
        &Coe::One(_, tid) => f(tid, e),
        Coe::Trans(c1, _, c2) => apply(c2, f.clone(), apply(c1, f, e)),
      }
    }
    apply(c, |tid, e| LispKind::List(
      vec![Arc::new(LispKind::Atom(self.terms[tid].atom)), e]).decorate_span(fsp), res)
  }
}

impl<'a> ElabTerm<'a> {
  fn try_get_span(&self, e: &LispKind) -> Span {
    try_get_span(&self.fsp, e)
  }

  fn err(&self, e: &LispKind, msg: impl Into<BoxError>) -> ElabError {
    ElabError::new_e(self.try_get_span(e), msg)
  }

  fn coerce(&self, src: &LispVal, from: SortID, res: LispKind, tgt: InferTarget) -> Result<LispVal> {
    let fsp = src.fspan();
    let res = res.decorate_span(&fsp);
    let to = match tgt {
      InferTarget::Unknown => return Ok(res),
      InferTarget::Provable if self.env.sorts[from].mods.contains(Modifiers::PROVABLE) => return Ok(res),
      InferTarget::Provable => *self.env.pe.coe_prov.get(&from).ok_or_else(||
        self.err(&src, format!("type error: expected provable sort, got {}", self.env.sorts[from].name)))?,
      InferTarget::Reg(to) => self.env.data[to].sort.unwrap(),
      InferTarget::Bound(_) => return Err(self.err(&src, "expected a variable"))
    };
    if from == to {return Ok(res)}
    if let Some(c) = self.env.pe.coes.get(&from).and_then(|m| m.get(&to)) {
      Ok(self.env.apply_coe(&fsp, c, res))
    } else {
      Err(self.err(&src,
        format!("type error: expected {}, got {}", self.env.sorts[to].name, self.env.sorts[from].name)))
    }
  }

  fn other(&self, e: &LispVal, _: InferTarget) -> Result<LispVal> {
    Err(self.err(e, "Not a valid expression"))
  }

  fn infer_sort(&self, e: &LispKind) -> Result<SortID> {
    e.unwrapped(|r| match r {
      &LispKind::Atom(a) => match self.lc.vars.get(&a) {
        None => Err(self.err(e, "variable not found")),
        Some(&InferSort::Bound {sort, ..}) => Ok(sort),
        Some(&InferSort::Reg {sort, ..}) => Ok(sort),
        Some(InferSort::Unknown {..}) => panic!("finalized vars already"),
      },
      LispKind::List(es) if !es.is_empty() => {
        let a = es[0].as_atom().ok_or_else(|| self.err(&es[0], "expected an atom"))?;
        let tid = self.env.term(a).ok_or_else(||
          self.err(&es[0], format!("term '{}' not declared", self.env.data[a].name)))?;
        Ok(self.env.terms[tid].ret.0)
      }
      _ => Err(self.err(e, "invalid expression"))
    })
  }
}

impl<'a> ElabTermMut<'a> {
  fn atom(&mut self, e: &LispVal, a: AtomID, tgt: InferTarget) -> Result<LispVal> {
    let is = self.lc.vars.entry(a).or_insert_with({
      let fsp = &self.fsp;
      move || InferSort::new(try_get_span(fsp, e))
    });
    match (is, tgt) {
      (InferSort::Reg {..}, InferTarget::Bound(_)) =>
        Err(self.err(e, "expected a bound variable, got regular variable")),
      (&mut InferSort::Bound {sort, ..}, InferTarget::Bound(sa)) => {
        let s = self.env.data[sa].sort.unwrap();
        if s == sort {Ok(LispKind::Atom(a).decorate_span(&e.fspan()))}
        else {
          Err(self.err(e,
            format!("type error: expected {}, got {}", self.env.sorts[s].name, self.env.sorts[sort].name)))
        }
      }
      (InferSort::Unknown {must_bound, sorts, ..}, tgt) => {
        let s = match tgt {
          InferTarget::Bound(sa) => {*must_bound = true; Some(self.env.data[sa].sort.unwrap())}
          InferTarget::Reg(sa) => Some(self.env.data[sa].sort.unwrap()),
          _ => None,
        };
        let mvars = &mut self.lc.mvars;
        Ok(sorts.entry(s).or_insert_with(|| new_mvar(mvars, tgt)).clone())
      }
      (&mut InferSort::Reg {sort, ..}, tgt) => self.coerce(e, sort, LispKind::Atom(a), tgt),
      (&mut InferSort::Bound {sort, ..}, tgt) => self.coerce(e, sort, LispKind::Atom(a), tgt),
    }
  }

  fn list(&mut self, e: &LispVal,
    mut it: impl Iterator<Item=LispVal>, tgt: InferTarget) -> Result<LispVal> {
    let t = it.next().unwrap();
    let a = t.as_atom().ok_or_else(|| self.err(&t, "expected an atom"))?;
    let tid = self.env.term(a).ok_or_else(||
      self.err(&t, format!("term '{}' not declared", self.env.data[a].name)))?;
    let tdata = &self.env.terms[tid];
    let mut tys = tdata.args.iter();
    let mut args = vec![LispKind::Atom(a).decorate_span(&t.fspan())];
    for arg in it {
      let tgt = match tys.next().ok_or_else(||
        self.err(&e,
          format!("expected {} arguments, got {}", tdata.args.len(), e.len() - 1)))?.1 {
        EType::Bound(s) => InferTarget::Bound(self.env.sorts[s].atom),
        EType::Reg(s, _) => InferTarget::Reg(self.env.sorts[s].atom),
      };
      args.push(self.expr(&arg, tgt)?);
    }
    self.coerce(e, tdata.ret.0, LispKind::List(args), tgt)
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

#[derive(Default)]
struct BuildArgs {
  map: HashMap<AtomID, u64>,
  size: usize,
}
const MAX_BOUND_VARS: usize = 55;

impl BuildArgs {
  fn push_bound(&mut self, a: Option<AtomID>) -> Option<()> {
    if self.size >= MAX_BOUND_VARS {return None}
    if let Some(a) = a {self.map.insert(a, 1 << self.size);}
    self.size += 1;
    Some(())
  }

  fn deps(&self, v: &Vec<AtomID>) -> u64 {
    let mut ret = 0;
    for &a in v { ret |= self.map[&a] }
    ret
  }

  fn push_var(&mut self, vars: &HashMap<AtomID, InferSort>,
    a: Option<AtomID>, is: &Option<InferSort>) -> Option<Option<EType>> {
    match is.as_ref().unwrap_or_else(|| &vars[&a.unwrap()]) {
      &InferSort::Bound {dummy: false, sort} => {
        self.push_bound(a)?;
        Some(Some(EType::Bound(sort)))
      },
      &InferSort::Bound {dummy: true, ..} => Some(None),
      &InferSort::Reg {sort, ref deps} => {
        let n = self.deps(deps);
        if let Some(a) = a {self.map.insert(a, n);}
        Some(Some(EType::Reg(sort, n)))
      }
      InferSort::Unknown {..} => unreachable!(),
    }
  }

  fn expr_deps(&self, env: &Environment, e: &LispKind) -> u64 {
    e.unwrapped(|r| match r {
      &LispKind::Atom(a) => self.map[&a],
      LispKind::List(es) if !es.is_empty() =>
        if let Some(tid) = es[0].as_atom().and_then(|a| env.term(a)) {
          let ref tdef = env.terms[tid];
          let mut argbv = Vec::new();
          let mut out = 0;
          for ((_, ty), e) in tdef.args.iter().zip(&es[1..]) {
            let mut n = self.expr_deps(env, e);
            match ty {
              EType::Bound(_) => argbv.push(n),
              &EType::Reg(_, deps) => {
                let mut i = 1;
                for &arg in &argbv {
                  if deps & i != 0 { n &= !arg }
                  i *= 2;
                }
                out |= n;
              }
            }
          }
          let deps = tdef.ret.1;
          let mut i = 1;
          for arg in argbv {
            if deps & i != 0 { out |= arg }
            i *= 2;
          }
          out
        } else {unreachable!()},
      _ => unreachable!()
    })
  }
}

enum InferBinder {
  Var(Option<AtomID>, InferSort),
  Hyp(Option<AtomID>, LispVal),
}

impl<'a, F: FileServer + ?Sized> Elaborator<'a, F> {
  fn elab_dep_type(&mut self, error: &mut bool, lk: LocalKind, d: &DepType) -> Result<InferSort> {
    let a = self.env.get_atom(self.ast.span(d.sort));
    let sort = self.data[a].sort.ok_or_else(|| ElabError::new_e(d.sort, "sort not found"))?;
    Ok(if lk.is_bound() {
      if !d.deps.is_empty() {
        self.report(ElabError::new_e(
          d.deps[0].start..d.deps.last().unwrap().end, "dependencies not allowed in curly binders"));
        *error = true;
      }
      InferSort::Bound {dummy: lk == LocalKind::Dummy, sort}
    } else {
      InferSort::Reg {
        sort,
        deps: d.deps.iter().map(|&sp| {
          let y = self.env.get_atom(self.ast.span(sp));
          self.lc.var(y, sp);
          y
        }).collect()
      }
    })
  }

  fn elab_binder(&mut self, error: &mut bool, sp: Option<Span>, lk: LocalKind, ty: Option<&Type>) -> Result<InferBinder> {
    let x = if lk == LocalKind::Anon {None} else {sp.map(|sp| self.env.get_atom(self.ast.span(sp)))};
    Ok(match ty {
      None => InferBinder::Var(x, InferSort::Unknown {
        src: sp.unwrap(),
        must_bound: lk.is_bound(),
        sorts: vec![(None, self.lc.new_mvar(InferTarget::Unknown))].into_iter().collect()
      }),
      Some(Type::DepType(d)) => InferBinder::Var(x, self.elab_dep_type(error, lk, d)?),
      Some(&Type::Formula(f)) => {
        let e = self.parse_formula(f)?;
        let e = self.eval_qexpr(e)?;
        let e = self.elaborate_term(f.0, &e, InferTarget::Provable)?;
        InferBinder::Hyp(x, e)
      },
    })
  }

  fn to_elab_term(&mut self, sp: Span) -> ElabTerm {
    ElabTerm {fsp: self.fspan(sp), env: &self.env, lc: &self.lc}
  }

  fn to_elab_term_mut(&mut self, sp: Span) -> ElabTermMut {
    ElabTermMut {fsp: self.fspan(sp), env: &self.env, lc: &mut self.lc}
  }

  fn elaborate_term(&mut self, sp: Span, e: &LispVal, tgt: InferTarget) -> Result<LispVal> {
    self.to_elab_term_mut(sp).expr(e, tgt)
  }

  fn infer_sort(&mut self, sp: Span, e: &LispKind) -> Result<SortID> {
    self.to_elab_term(sp).infer_sort(e)
  }

  fn finalize_vars(&mut self, dummy: bool) -> Vec<ElabError> {
    let mut errs = Vec::new();
    let mut newvars = Vec::new();
    for (&a, is) in &mut self.lc.vars {
      if let InferSort::Unknown {src, must_bound, ref sorts} = *is {
        match if sorts.len() == 1 {
          sorts.keys().next().unwrap().ok_or_else(|| ElabError::new_e(src, "could not infer type"))
        } else {
          let env = &self.env;
          sorts.keys().find_map(|s| s.filter(|&s| {
            match env.pe.coes.get(&s) {
              None => sorts.keys().all(|s2| s2.map_or(true, |s2| s == s2)),
              Some(m) => sorts.keys().all(|s2| s2.map_or(true, |s2| s == s2 || m.contains_key(&s2))),
            }
          })).ok_or_else(|| {
            ElabError::new_e(src, format!("could not infer consistent type from {{{}}}",
              sorts.keys().filter_map(|&k| k).map(|s| &env.sorts[s].name).format(", ")))
          })
        } {
          Ok(sort) => {
            for (s, e) in sorts {
              let mut val = Arc::new(LispKind::Atom(a));
              if let &Some(s) = s {
                if s != sort {
                  let fsp = Some(FileSpan {file: self.path.clone(), span: src});
                  val = self.env.apply_coe(&fsp, &self.env.pe.coes[&sort][&s], val);
                }
              }
              if let LispKind::Ref(m) = &**e {
                *m.lock().unwrap() = val;
              } else {unreachable!()}
            }
            newvars.push((src, a));
            *is = if dummy || must_bound {
              InferSort::Bound {dummy: true, sort}
            } else {
              InferSort::Reg {sort, deps: vec![]}
            }
          }
          Err(e) => errs.push(e),
        }
      }
    }
    newvars.sort_by_key(|&(_, a)| self.env.data[a].name.deref());
    let mut vec: Vec<_> = newvars.into_iter().map(|(src, a)| (src, Some(a), None)).collect();
    vec.append(&mut self.lc.var_order);
    self.lc.var_order = vec;
    errs
  }

  pub fn elab_decl(&mut self, sp: Span, d: &Decl) -> Result<()> {
    let mut ehyps = Vec::new();
    let mut error = false;
    macro_rules! report {
      ($e:expr) => {{let e = $e; self.report(e); error = true;}};
      ($sp:expr, $e:expr) => {report!(ElabError::new_e($sp, $e))};
    }
    // crate::server::log(format!("elab {}", self.ast.span(d.id)));
    for bi in &d.bis {
      match self.elab_binder(&mut error, bi.local, bi.kind, bi.ty.as_ref()) {
        Err(e) => { self.report(e); error = true }
        Ok(InferBinder::Var(x, is)) => {
          if !ehyps.is_empty() {report!(bi.span, "hypothesis binders must come after variable binders")}
          if let Some(x) = x {
            match self.lc.vars.entry(x) {
              Entry::Vacant(e) => {e.insert(is);}
              Entry::Occupied(mut e) => {
                e.insert(is);
                report!(bi.local.unwrap(), "variable occurs twice in binder list");
              }
            }
            self.lc.var_order.push((bi.local.unwrap_or(bi.span), Some(x), None));
          } else {
            self.lc.var_order.push((bi.local.unwrap_or(bi.span), None, Some(is)));
          }
        }
        Ok(InferBinder::Hyp(x, e)) => ehyps.push((bi, x, e)),
      }
    }
    let atom = self.env.get_atom(self.ast.span(d.id));
    match d.k {
      DeclKind::Term | DeclKind::Def => {
        for (bi, _, _) in ehyps {report!(bi.span, "term/def declarations have no hypotheses")}
        let ret = match &d.ty {
          None => None, // Err(ElabError::new_e(d.id, "type required for term declaration"))?,
          Some(Type::Formula(f)) => Err(ElabError::new_e(f.0, "sort expected"))?,
          Some(Type::DepType(ty)) => match self.elab_dep_type(&mut error, LocalKind::Anon, ty)? {
            InferSort::Reg {sort, deps} => Some((ty.sort, sort, deps)),
            _ => unreachable!(),
          },
        };
        let val = match &d.val {
          None => None,
          Some(f) => {
            let e = self.eval_lisp(f)?;
            Some((f.span, self.elaborate_term(f.span, &e, match ret {
              None => InferTarget::Unknown,
              Some((_, s, _)) => InferTarget::Reg(self.sorts[s].atom),
            })?))
          }
        };
        if d.k == DeclKind::Term {
          if let Some(v) = &d.val {report!(v.span, "term declarations have no definition")}
        } else if d.val.is_none() {
          self.report(ElabError::new_e(sp, "def declaration missing value"));
        }
        for e in self.finalize_vars(true) {report!(e)}
        if error {return Ok(())}
        let mut args = Vec::new();
        let mut ba = BuildArgs::default();
        for &(sp, a, ref is) in &self.lc.var_order {
          match ba.push_var(&self.lc.vars, a, is) {
            None => Err(ElabError::new_e(sp, format!("too many bound variables (max {})", MAX_BOUND_VARS)))?,
            Some(None) => (),
            Some(Some(ty)) => args.push((a, ty)),
          }
        }
        let (ret, val) = match val {
          None => match ret {
            None => Err(ElabError::new_e(sp, "expected type or value"))?,
            Some((_, s, ref deps)) => ((s, ba.deps(deps)), None)
          },
          Some((sp, val)) => {
            let s = self.infer_sort(sp, &val)?;
            let deps = ba.expr_deps(&self.env, &val);
            let val = {
              let mut de = Dedup::new(self.lc.var_order.len());
              let nh = NodeHasher::new(self, sp);
              let i = de.dedup(&nh, &val)?;
              let Builder {mut ids, heap} = self.to_builder(&de)?;
              Expr {heap, head: ids[i].take()}
            };
            match ret {
              None => ((s, deps), Some(val)),
              Some((sp, s2, ref deps2)) => {
                if s != s2 {
                  return Err(ElabError::new_e(sp, format!("type error: expected {}, got {}",
                    self.env.sorts[s].name, self.env.sorts[s2].name)))
                }
                let n = ba.deps(deps2);
                if deps & !n != 0 {
                  return Err(ElabError::new_e(sp, format!("variables {{{}}} missing from dependencies",
                    deps2.iter().filter(|&a| deps & !ba.map[a] != 0)
                      .map(|&a| &self.data[a].name).format(", "))))
                }
                ((s2, n), Some(val))
              }
            }
          }
        };
        let t = Term {
          atom, args, ret, val,
          span: self.fspan(sp),
          vis: d.mods,
          id: d.id,
        };
        self.env.add_term(atom, t.span.clone(), || t).map_err(|e| e.to_elab_error(sp))?;
      }
      DeclKind::Axiom | DeclKind::Thm => {
        let eret = match &d.ty {
          None => Err(ElabError::new_e(sp, "return type required"))?,
          Some(Type::DepType(ty)) => Err(ElabError::new_e(ty.sort, "expression expected"))?,
          &Some(Type::Formula(f)) => {
            let e = self.parse_formula(f)?;
            let e = self.eval_qexpr(e)?;
            self.elaborate_term(f.0, &e, InferTarget::Provable)?
          }
        };
        if d.k == DeclKind::Axiom {
          if let Some(v) = &d.val {report!(v.span, "axiom declarations have no definition")}
        } else if d.val.is_none() {
          self.report(ElabError::new_e(sp, "theorem declaration missing value"));
        }
        for e in self.finalize_vars(false) {report!(e)}
        if error {return Ok(())}
        let mut args = Vec::new();
        let mut ba = BuildArgs::default();
        for &(sp, a, ref is) in &self.lc.var_order {
          match ba.push_var(&self.lc.vars, a, is) {
            None => Err(ElabError::new_e(sp, format!("too many bound variables (max {})", MAX_BOUND_VARS)))?,
            Some(None) => (),
            Some(Some(ty)) => args.push((a, ty)),
          }
        }
        let mut de = Dedup::new(self.lc.var_order.len());
        let nh = NodeHasher::new(self, d.id);
        let mut is = Vec::new();
        for &(_, a, ref e) in &ehyps {is.push((a, de.dedup(&nh, e)?))}
        let ir = de.dedup(&nh, &eret)?;
        let NodeHasher {var_map, fsp, ..} = nh;
        let span = fsp.clone();
        let Builder {mut ids, heap} = self.to_builder(&de)?;
        let hyps = is.iter().map(|&(a, i)| (a, ids[i].take())).collect();
        let ret = ids[ir].take();
        let proof = if self.check_proofs {
          d.val.as_ref().map(|e| {
            (|| -> Result<Option<Proof>> {
              let mut de = de.map_proof();
              let mut is2 = Vec::new();
              for (i, (_, a, e)) in ehyps.into_iter().enumerate() {
                if let Some(a) = a {
                  let p = Arc::new(LispKind::Atom(a));
                  is2.push(de.add(&*p, ProofHash::Hyp(i, is[i].1)));
                  self.lc.add_proof(a, e, p)
                }
              }
              let g = LispKind::new_ref(LispKind::new_goal(self.fspan(e.span), eret));
              self.lc.goals = vec![g.clone()];
              self.elab_lisp(e)?;
              for g in mem::replace(&mut self.lc.goals, vec![]) {
                report!(try_get_span(&fsp, &g),
                  format!("|- {}", self.print(&g.goal_type().unwrap())))
              }
              if error {return Ok(None)}
              let nh = NodeHasher {var_map, fsp, elab: self};
              let ip = de.dedup(&nh, &g)?;
              let Builder {mut ids, heap} = self.to_builder(&de)?;
              let hyps = is2.into_iter().map(|i| ids[i].take()).collect();
              let head = ids[ip].take();
              Ok(Some(Proof { heap, hyps, head }))
            })().unwrap_or_else(|e| {self.report(e); None})
          })
        } else {None};
        let t = Thm {
          atom, span, vis: d.mods, id: d.id,
          args, heap, hyps, ret, proof
        };
        self.env.add_thm(atom, t.span.clone(), || t).map_err(|e| e.to_elab_error(sp))?;
      }
    }
    Ok(self.lc.clear())
  }

  pub fn add_term(&self, fsp: FileSpan, sp: Span, es: &[LispVal]) -> Result<()> {
    let x = es[0].as_atom().ok_or_else(|| ElabError::new_e(sp, "expected an atom"))?;
    if self.data[x].decl.is_some() {
      Err(ElabError::new_e(sp, format!("duplicate term/def declaration '{}'", self.print(&x))))?
    }
    macro_rules! sp {($e:expr) => {$e.fspan().unwrap_or(fsp.clone()).span}}
    let mut args = Vec::new();
    let mut vars = HashMap::new();
    let mut bv = 1;
    for e in Uncons::from(es[1].clone()) {
      let mut u = Uncons::from(e.clone());
      if let (Some(ea), Some(es)) = (u.next(), u.next()) {
        let a = ea.as_atom().ok_or_else(|| ElabError::new_e(sp!(ea), "expected an atom"))?;
        let a = if a == AtomID::UNDER {None} else {Some(a)};
        let s = es.as_atom().ok_or_else(|| ElabError::new_e(sp!(es), "expected an atom"))?;
        let s = self.data[s].sort.ok_or_else(|| ElabError::new_e(sp!(es),
          format!("unknown sort '{}'", self.print(&s))))?;
        args.push((a, match u.next() {
          None => {
            if let Some(a) = a {
              if bv >= 1 << MAX_BOUND_VARS {
                Err(ElabError::new_e(sp,
                  format!("too many bound variables (max {})", MAX_BOUND_VARS)))?
              }
              vars.insert(a, bv);
              bv *= 2;
            }
            EType::Bound(s)
          }
          Some(vs) => {
            let mut n = 0;
            for v in Uncons::from(vs) {
              let a = v.as_atom().ok_or_else(|| ElabError::new_e(sp!(v), "expected an atom"))?;
              n |= vars.get(&a).ok_or_else(|| ElabError::new_e(sp!(v),
                format!("undeclared variable '{}'", self.print(&v))))?;
            }
            EType::Reg(s, n)
          }
        }))
      } else {
        Err(ElabError::new_e(sp!(e),
          format!("binder syntax error: {}", self.print(&e))))?;
      }
    }
    // let t = Term {
    //   atom: x,
    //   span: fsp.clone(),
    //   id: sp!(es[0]),
    //   vis, args, ret, val,
    // };
    // self.env.add_term(x, fsp, || t).map_err(|e| e.to_elab_error(sp))
    Ok(())
  }

  pub fn add_thm(&self, fsp: FileSpan, sp: Span, es: &[LispVal]) -> Result<()> {
    let x = es[0].as_atom().ok_or_else(|| ElabError::new_e(sp, "expected an atom"))?;
    if self.data[x].decl.is_some() {
      Err(ElabError::new_e(sp, format!("duplicate term/def declaration '{}'", self.print(&x))))?
    }
    // let t = Thm {};
    // self.env.add_thm(x, fsp, || t).map_err(|e| e.to_elab_error(sp))
    Ok(())
  }
}