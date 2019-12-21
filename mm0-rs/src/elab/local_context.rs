use std::ops::{Deref, DerefMut};
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::mem;
use std::collections::{HashMap, hash_map::Entry};
use itertools::Itertools;
use super::environment::{AtomID, Type as EType};
use crate::parser::ast::{Decl, Binder, Type, DepType, LocalKind};
use super::*;
use super::lisp::{LispVal, LispKind, Annot, Uncons, InferTarget};
use crate::util::*;

#[derive(Debug)]
pub enum InferSort {
  KnownBound { dummy: bool, sort: SortID },
  KnownReg { sort: SortID, deps: Vec<AtomID> },
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
    self.vars.clear();
    self.var_order.clear();
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

  fn var(&mut self, x: AtomID, sp: Span) -> &mut InferSort {
    self.vars.entry(x).or_insert_with(|| InferSort::new(sp))
  }
}

fn decorate_span(fsp: &Option<FileSpan>, e: LispKind) -> LispVal {
  if let Some(fsp) = fsp {
    Arc::new(LispKind::Annot(Annot::Span(fsp.clone()), Arc::new(e)))
  } else {Arc::new(e)}
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

fn try_get_span(fsp: &FileSpan, e: &LispKind) -> Span {
  match e.fspan() {
    Some(fsp) if fsp.file == fsp.file && fsp.span.start >= fsp.span.start => fsp.span,
    _ => fsp.span,
  }
}

impl Environment {
  fn apply_coe(&self, fsp: &Option<FileSpan>, c: &Coe, res: LispVal) -> LispVal {
    fn apply(c: &Coe, f: impl FnOnce(TermID, LispVal) -> LispVal + Clone, e: LispVal) -> LispVal {
      match c {
        &Coe::One(_, tid) => f(tid, e),
        Coe::Trans(c1, _, c2) => apply(c2, f.clone(), apply(c1, f, e)),
      }
    }
    apply(c, |tid, e| decorate_span(fsp, LispKind::List(
      vec![Arc::new(LispKind::Atom(self.terms[tid].atom)), e])), res)
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
    let res = decorate_span(&fsp, res);
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
        Some(&InferSort::KnownBound {sort, ..}) => Ok(sort),
        Some(&InferSort::KnownReg {sort, ..}) => Ok(sort),
        Some(InferSort::Unknown {sorts, ..}) => Ok({
          if sorts.len() == 1 {
            sorts.keys().next().unwrap().ok_or_else(||
              self.err(e, format!("could not infer type for {}", self.env.data[a].name)))?
          } else {
            sorts.keys().find_map(|s| s.filter(|&s| {
              match self.env.pe.coes.get(&s) {
                None => sorts.len() == 1,
                Some(m) => sorts.keys().all(|s2| s2.map_or(true, |s2| s == s2 || m.contains_key(&s2))),
              }
            })).ok_or_else(|| {
              self.err(e, format!("could not infer consistent type from {{{}}} for {}",
                sorts.keys().filter_map(|&k| k).map(|s| &self.env.sorts[s].name).format(", "),
                self.env.data[a].name))
            })?
          }
        }),
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
      (InferSort::KnownReg {..}, InferTarget::Bound(_)) =>
        Err(self.err(e, "expected a bound variable, got regular variable")),
      (&mut InferSort::KnownBound {sort, ..}, InferTarget::Bound(sa)) => {
        let s = self.env.data[sa].sort.unwrap();
        if s == sort {Ok(decorate_span(&e.fspan(), LispKind::Atom(a)))}
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
      (&mut InferSort::KnownReg {sort, ..}, tgt) => self.coerce(e, sort, LispKind::Atom(a), tgt),
      (&mut InferSort::KnownBound {sort, ..}, tgt) => self.coerce(e, sort, LispKind::Atom(a), tgt),
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
    let mut args = vec![decorate_span(&t.fspan(), LispKind::Atom(a))];
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
      &InferSort::KnownBound {dummy: false, sort} => {
        self.push_bound(a)?;
        Some(Some(EType::Bound(sort)))
      },
      &InferSort::KnownBound {dummy: true, ..} => Some(None),
      &InferSort::KnownReg {sort, ref deps} => {
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

#[derive(PartialEq, Eq, Hash)]
enum ExprHash {
  Atom(AtomID),
  App(AtomID, Vec<usize>),
}

#[derive(Default)]
struct DedupExpr {
  map: HashMap<Rc<ExprHash>, usize>,
  prev: HashMap<*const LispKind, usize>,
  vec: Vec<(Rc<ExprHash>, bool)>,
}

impl DedupExpr {
  fn add(&mut self, p: *const LispKind, v: ExprHash) -> usize {
    match self.map.entry(Rc::new(v)) {
      Entry::Vacant(e) => {
        let n = self.vec.len();
        self.vec.push((e.key().clone(), false));
        e.insert(n);
        self.prev.insert(p, n);
        n
      }
      Entry::Occupied(e) => {
        let &n = e.get();
        self.vec[n].1 = true;
        self.prev.insert(p, n);
        n
      }
    }
  }

  fn dedup_expr(&mut self, e: &LispVal) -> usize {
    e.unwrapped(|r| match self.prev.get(&(r as *const _)) {
      Some(&n) => n,
      None => match r {
        &LispKind::Atom(a) => self.add(r, ExprHash::Atom(a)),
        LispKind::List(es) if !es.is_empty() => {
          let e = ExprHash::App(
            es[0].as_atom().unwrap(),
            es[1..].iter().map(|e| self.dedup_expr(e)).collect());
          self.add(r, e)
        }
        _ => unreachable!()
      },
    })
  }
}

struct BuildExpr<'a, F: FileServer + ?Sized> {
  de: DedupExpr,
  elab: &'a Elaborator<'a, F>,
  sp: Span,
}

impl<'a, F: FileServer + ?Sized> BuildExpr<'a, F> {
  fn err(&self, e: impl Into<BoxError>) -> ElabError { ElabError::new_e(self.sp, e) }
  fn to_expr(self, i: usize) -> Result<Expr> {
    enum Val {Built(ExprNode), Ref(usize), Done}
    fn take(e: &mut Val) -> ExprNode {
      match mem::replace(e, Val::Done) {
        Val::Built(x) => x,
        Val::Ref(n) => {*e = Val::Ref(n); ExprNode::Ref(n)}
        Val::Done => panic!("taking a value twice")
      }
    }
    let mut ids: Vec<Val> = Vec::with_capacity(self.de.vec.len());
    let mut heap = Vec::new();
    let mut hsize = self.elab.lc.var_order.len();
    let var_map = {
      let mut m = HashMap::new();
      for (i, &(_, a, _)) in self.elab.lc.var_order.iter().enumerate() {
        if let Some(a) = a {m.insert(a, i);}
      }
      m
    };
    for &(ref e, b) in &self.de.vec {
      let node = match **e {
        ExprHash::Atom(a) => match var_map.get(&a) {
          Some(&i) => ExprNode::Ref(i),
          None => match self.elab.lc.vars.get(&a) {
            Some(&InferSort::KnownBound {dummy: true, sort}) => ExprNode::Dummy(a, sort),
            _ => Err(self.err(format!("variable '{}' not found", self.elab.data[a].name)))?,
          }
        },
        ExprHash::App(a, ref ns) => ExprNode::App(
          self.elab.term(a).ok_or_else(||
            self.err(format!("term '{}' not found", self.elab.data[a].name)))?,
          ns.iter().map(|&i| take(&mut ids[i])).collect()),
      };
      if b {
        ids.push(Val::Ref(hsize));
        heap.push(node);
        hsize += 1;
      } else {
        ids.push(Val::Built(node))
      }
    }
    Ok(Expr {heap, head: take(&mut ids[i])})
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
    if lk.is_bound() {
      if !d.deps.is_empty() {
        self.report(ElabError::new_e(
          d.deps[0].start..d.deps.last().unwrap().end, "dependencies not allowed in curly binders"));
        *error = true;
      }
      Ok(InferSort::KnownBound {dummy: lk == LocalKind::Dummy, sort})
    } else {
      Ok(InferSort::KnownReg {
        sort,
        deps: d.deps.iter().map(|&sp| {
          let y = self.env.get_atom(self.ast.span(sp));
          self.lc.var(y, sp);
          y
        }).collect()
      })
    }
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
      if let InferSort::Unknown {src, ref sorts, ..} = *is {
        match if sorts.len() == 1 {
          sorts.keys().next().unwrap().ok_or_else(|| ElabError::new_e(src, "could not infer type"))
        } else {
          let env = &self.env;
          sorts.keys().find_map(|s| s.filter(|&s| {
            match env.pe.coes.get(&s) {
              None => sorts.len() == 1,
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
            *is = InferSort::KnownBound {dummy, sort}
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

  fn build_expr(&self, sp: Span, e: &LispVal) -> Result<Expr> {
    let mut be = BuildExpr {
      de: DedupExpr::default(),
      elab: self,
      sp,
    };
    let i = be.de.dedup_expr(e);
    be.to_expr(i)
  }

  pub fn elab_decl(&mut self, sp: Span, d: &Decl) -> Result<()> {
    let mut hyps = Vec::new();
    let mut error = false;
    macro_rules! report {
      ($e:expr) => {{self.report($e); error = true;}};
      ($sp:expr, $e:expr) => {report!(ElabError::new_e($sp, $e))};
    }
    for bi in &d.bis {
      match self.elab_binder(&mut error, bi.local, bi.kind, bi.ty.as_ref()) {
        Err(e) => { self.report(e); error = true }
        Ok(InferBinder::Var(x, is)) => {
          if !hyps.is_empty() {report!(bi.span, "hypothesis binders must come after variable binders")}
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
        Ok(InferBinder::Hyp(x, e)) => hyps.push((bi, x, e)),
      }
    }
    // let ret = match d.ty {
    //   None => None,
    //   Some(ref ty) => Some(self.elab_binder(&mut error, None, LocalKind::Anon, Some(ty))?)
    // };
    let atom = self.env.get_atom(self.ast.span(d.id));
    match d.k {
      DeclKind::Term | DeclKind::Def => {
        for (bi, _, _) in hyps {report!(bi.span, "term/def declarations have no hypotheses")}
        let ret = match &d.ty {
          None => None, // Err(ElabError::new_e(d.id, "type required for term declaration"))?,
          Some(Type::Formula(f)) => Err(ElabError::new_e(f.0, "sort expected"))?,
          Some(Type::DepType(ty)) => match self.elab_dep_type(&mut error, LocalKind::Anon, ty)? {
            InferSort::KnownReg {sort, deps} => Some((ty.sort, sort, deps)),
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
        let (ret, val) = match val {
          None => match ret {
            None => Err(ElabError::new_e(sp, "expected type or value"))?,
            Some((_, s, ref deps)) => ((s, ba.deps(deps)), None)
          },
          Some((sp, val)) => {
            let s = self.infer_sort(sp, &val)?;
            let deps = ba.expr_deps(&self.env, &val);
            let val = self.build_expr(sp, &val)?;
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
        self.add_term(atom, t.span.clone(), || t).map_err(|e| e.to_elab_error(sp))?;
      }
      _ => self.report(ElabError::new_e(d.id, "unimplemented"))
    }
    Ok(())
  }
}