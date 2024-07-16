//! The local context, as well as the implementation of elaboration and
//! type inference for top level terms and declarations.

use std::ops::Deref;
use std::mem;
use std::collections::{HashMap, hash_map::Entry};
use itertools::Itertools;
use if_chain::if_chain;
use debug_derive::EnvDebug;
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;
use crate::elab::verify::{VERIFY_ON_ADD, VerifyError};
use crate::{AtomId, TermKind, ThmKind, Type as EType, Span, FileSpan, BoxError, MAX_BOUND_VARS};
use crate::ast::{Decl, Type, DepType, LocalKind};
use super::{Coe, DeclKind, DerefMut, DocComment, ElabError, Elaborator, Environment,
  Expr, Modifiers, ObjectKind, OneOrMore, Proof, Result, SExprKind, SortId, Term, TermId, Thm};
use super::lisp::{LispVal, LispKind, Uncons, InferTarget, print::FormatEnv};
use super::proof::{NodeHasher, ProofKind, ProofHash, build, Dedup};

/// The contexts in which an unknown var can appear.
#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug, EnvDebug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum VarContext {
  /// An unconstrained context
  Unknown,
  /// A context which requires a provable sort
  Provable,
  /// A context which requires this sort
  Sort(SortId),
}

/// The infer status of a variable in a declaration. For example in
/// `def foo {x} (ph: wff x y): wff = $ all z ph $;`, `x` has no declared type
/// but is known to be bound, `y` is not declared at all but known to be a bound non-dummy,
/// and `z` is not declared and must be a bound dummy of type `var` (assuming
/// that `all` has type `var` for its first argument).
#[derive(Debug, EnvDebug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub enum InferSort {
  /// This is a declared bound variable with the given sort.
  Bound {
    /// The sort of the variable.
    sort: SortId,
    /// True if the variable has been referenced.
    used: bool
  },
  /// This is a declared regular variable with the given sort and dependencies.
  Reg {
    /// The sort of the variable.
    sort: SortId,
    /// The variables this one depends on.
    deps: Box<[AtomId]>,
    /// True if the variable has been referenced.
    used: bool
  },
  /// This is a variable does not have a declared type.
  Unknown {
    /// The span of the first occurrence of the variable
    src: Span,
    /// True if this is known to be a bound variable, because it appears
    /// in a context where only bound variables are allowed.
    must_bound: bool,
    /// True if this is a dummy variable, because it was first identified
    /// in a definition body, rather than in part of a theorem statement.
    dummy: bool,
    /// The list of sorts that this variable should have. The keys of this map
    /// are sorts that this variable must coerce to, with [`None`] corresponding
    /// to an unknown provable sort; the values of the map are metavariables
    /// of the indicated sorts that are awaiting assignment when the dummy's
    /// actual sort is determined.
    sorts: Box<HashMap<VarContext, LispVal>>,
  },
}

impl InferSort {
  fn new(src: Span) -> InferSort {
    InferSort::Unknown { src, must_bound: false, dummy: true, sorts: Default::default() }
  }
  /// The sort of this variable. For an unknown variable, it returns a sort iff
  /// this variable has inferred exactly one sort, not counting `Unknown` or `Provable`.
  #[must_use] pub fn sort(&self) -> Option<SortId> {
    match *self {
      InferSort::Bound { sort, .. } | InferSort::Reg { sort, ..} => Some(sort),
      InferSort::Unknown {ref sorts, ..} => {
        let mut res = None;
        for s in sorts.keys() {
          if let VarContext::Sort(s) = *s {
            if mem::replace(&mut res, Some(s)).is_some() {return None}
          }
        }
        res
      }
    }
  }
}

/// The local context is the collection of proof-local data. This is manipulated
/// by lisp tactics in order to keep track of the proof state and eventually produce a proof.
#[derive(Default, Debug, EnvDebug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct LocalContext {
  /// The collection of local variables. The key is the name of the variable, and the
  /// value is `(dummy, is)` where `dummy` is true if this is a dummy variable
  /// (internal to the definition or proof) and `is` is the inferred sort data of the variable.
  /// When multiple variables have the same name, only the last one will be in this map.
  pub vars: HashMap<AtomId, (bool, InferSort)>,
  /// The list of variables in order of declaration. This also stores the variable span,
  /// and the atom is none if this is an anonymous (`_`) variable.
  /// The [`InferSort`] contains the inferred type of the variable, but only for
  /// variables that are not in the `vars` hashmap because they are shadowed or anonymous.
  pub var_order: Vec<(Span, Option<AtomId>, Option<InferSort>)>,
  /// The list of active metavariables. `refine` will add metavariables to this list when
  /// creating them during elaboration, and it is periodically cleaned to remove assigned
  /// metavariables. The `usize` field of a [`MVar`](LispKind::MVar) will refer to the
  /// variable's position in this list.
  pub mvars: Vec<LispVal>,
  /// The list of goals, or holes in the proof. This is the main user-facing state of a proof.
  /// This can be manipulated by user code, but the builtin tactics will manage this list
  /// automatically. When the set of goals is empty, the proof is complete.
  pub goals: Vec<LispVal>,
  /// The proof name map. The keys are subproof name bindings created by `have` or hypothesis
  /// names from the initial proof state, and the values are indexes into `proof_order`.
  pub proofs: HashMap<AtomId, usize>,
  /// The stored subproof data. The proofs are ordered for determinism but there is no real
  /// meaning associated to the order, except that later names shadow earlier names.
  /// The value is the name of the subproof, the type (theorem statement) of the proof,
  /// and the elaborated proof term.
  pub proof_order: Vec<(AtomId, LispVal, LispVal)>,
  /// The "closer", a user-configurable (using [`set-close-fn`])
  /// callback that gets called at the end of a `focus` block.
  ///
  /// [`set-close-fn`]: super::lisp::BuiltinProc::SetCloseFn
  pub closer: LispVal,
}

fn new_mvar(mvars: &mut Vec<LispVal>, tgt: InferTarget, sp: Option<FileSpan>) -> LispVal {
  let n = mvars.len();
  let e = LispVal::new(LispKind::MVar(n, tgt));
  let e = LispVal::new_ref(if let Some(sp) = sp {e.span(sp)} else {e});
  mvars.push(e.clone());
  e
}

impl LocalContext {
  /// Create a new local context.
  #[must_use] pub fn new() -> LocalContext { Default::default() }

  /// Reset the local context. This is the same as assigning to `new()` except it
  /// is a bit more efficient because it reuses allocations.
  pub fn clear(&mut self) {
    self.vars.clear();
    self.var_order.clear();
    self.mvars.clear();
    self.goals.clear();
    self.proofs.clear();
    self.proof_order.clear();
    self.closer = LispVal::undef();
  }

  /// Set the list of goals to `gs`, after filtering the elements that are not
  /// goals or are already instantiated.
  pub fn set_goals(&mut self, gs: impl IntoIterator<Item=LispVal>) {
    self.goals.clear();
    for g in gs {
      if g.is_goal() {
        self.goals.push(if g.is_ref() {g} else {LispVal::new_ref(g)})
      }
    }
  }

  /// Create a new metavariable, and track it in the local context.
  pub fn new_mvar(&mut self, tgt: InferTarget, sp: Option<FileSpan>) -> LispVal {
    new_mvar(&mut self.mvars, tgt, sp)
  }

  fn var(&mut self, x: AtomId, sp: Span) -> &mut (bool, InferSort) {
    self.vars.entry(x).or_insert_with(|| (true, InferSort::new(sp)))
  }

  /// Add a variable occurrence (from a location other than regular variable
  /// declarations) to the inference context. We pass the span of the variable,
  /// the name (or `_`), and whether it is in a dummy context (i.e. the body of a `def`)
  /// and the expected sort.
  ///
  /// It returns true if the variable was already in the binder list.
  fn push_var(&mut self, sp: Span, a: Option<AtomId>, (dummy, is): (bool, InferSort)) -> bool {
    if let Some(a) = a {
      let res = match self.vars.entry(a) {
        Entry::Vacant(e) => {e.insert((dummy, is)); false}
        Entry::Occupied(mut e) => {e.insert((dummy, is)); true}
      };
      if !dummy {self.var_order.push((sp, Some(a), None))}
      res
    } else {
      if !dummy {self.var_order.push((sp, None, Some(is)))}
      false
    }
  }

  /// Remove all metavariables that are already assigned, and renumber those
  /// that remain, so that the printed names `?a`, `?b` etc. stay simple.
  pub fn clean_mvars(&mut self) {
    let mut i = 0;
    self.mvars.retain(|e| e.as_ref_(|e| {
      e.unwrapped_mut(|e| {
        if let LispKind::MVar(n, _) = e {*n = i; i += 1; true}
        else {false}
      }).unwrap_or_else(|| {
        match **e {
          LispKind::MVar(n, ty) => {
            if n != i {*e = LispKind::MVar(i, ty).decorate_span(&e.fspan())}
            i += 1; true
          }
          _ => false,
        }
      })
    }).expect("mvars must be refs"))
  }

  /// Get a subproof by name.
  #[must_use] pub fn get_proof(&self, a: AtomId) -> Option<&(AtomId, LispVal, LispVal)> {
    self.proofs.get(&a).map(|&i| &self.proof_order[i])
  }

  /// Insert a new subproof.
  pub fn add_proof(&mut self, a: AtomId, e: LispVal, p: LispVal) {
    self.proofs.insert(a, self.proof_order.len());
    self.proof_order.push((a, e, p));
  }
}

struct ElabTerm<'a> {
  lc: &'a LocalContext,
  fe: FormatEnv<'a>,
  fsp: FileSpan,
}

struct ElabTermMut<'a> {
  elab: &'a mut Elaborator,
  fsp: FileSpan,
  check_vis: bool,
}

impl<'a> Deref for ElabTermMut<'a> {
  type Target = Elaborator;
  fn deref(&self) -> &Elaborator { self.elab }
}
impl<'a> DerefMut for ElabTermMut<'a> {
  fn deref_mut(&mut self) -> &mut Elaborator { self.elab }
}

/// Get the span from the lisp value `e`, but only if it lies inside the
/// span `fsp`, otherwise return `fsp`. (This prevents errors in
/// one statement from causing error reports further up the file or
/// even in another file.)
pub fn try_get_span(fsp: &FileSpan, e: &LispKind) -> Span {
  try_get_span_from(fsp, e.fspan().as_ref())
}

/// Get the span from `fsp2`, but only if it lies inside the
/// span `fsp`, otherwise return `fsp`. (This prevents errors in
/// one statement from causing error reports further up the file or
/// even in another file.)
#[must_use] pub fn try_get_span_from(fsp: &FileSpan, fsp2: Option<&FileSpan>) -> Span {
  try_get_span_opt(fsp, fsp2).unwrap_or(fsp.span)
}
/// Get the span from `fsp2`, but only if it lies inside the
/// span `fsp`. (This prevents errors in
/// one statement from causing error reports further up the file or
/// even in another file.)
#[must_use] pub fn try_get_span_opt(fsp: &FileSpan, fsp2: Option<&FileSpan>) -> Option<Span> {
  match fsp2 {
    Some(fsp2) if fsp.file == fsp2.file && fsp2.span.start >= fsp.span.start => Some(fsp2.span),
    _ => None,
  }
}

impl Environment {
  /// Construct the proof term corresponding to a coercion `c`.
  #[must_use] pub fn apply_coe(&self, fsp: &Option<FileSpan>, c: &Coe, res: LispVal) -> LispVal {
    fn apply(c: &Coe, f: &mut impl FnMut(TermId, LispVal) -> LispVal, e: LispVal) -> LispVal {
      match c {
        &Coe::One(_, tid) => f(tid, e),
        Coe::Trans(c1, _, c2) => {let e2 = apply(c1, f, e); apply(c2, f, e2)}
      }
    }
    apply(c, &mut |tid, e| LispKind::List(
      vec![LispVal::atom(self.terms[tid].atom), e].into()).decorate_span(fsp), res)
  }
}

impl<'a> ElabTerm<'a> {
  fn from_fsp(fsp: FileSpan, elab: &'a Elaborator) -> Self {
    ElabTerm {fsp, fe: elab.format_env(), lc: &elab.lc}
  }

  fn new(elab: &'a Elaborator, sp: Span) -> Self {
    Self::from_fsp(elab.fspan(sp), elab)
  }

  fn try_get_span(&self, e: &LispKind) -> Span {
    try_get_span(&self.fsp, e)
  }

  fn err(&self, e: &LispKind, msg: impl Into<BoxError>) -> ElabError {
    ElabError::new_e(self.try_get_span(e), msg)
  }

  fn coerce(&self, src: &LispVal, from: SortId, res: LispVal, tgt: InferTarget) -> Result<LispVal> {
    let fsp = src.fspan();
    let res = match &fsp { None => res, Some(fsp) => res.replace_span(fsp.clone()) };
    let to = match tgt {
      InferTarget::Unknown => return Ok(res),
      InferTarget::Provable if self.fe.sorts[from].mods.contains(Modifiers::PROVABLE) => return Ok(res),
      InferTarget::Provable => *self.fe.pe.coe_prov.get(&from).ok_or_else(||
        self.err(src, format!("type error: expected provable sort, got {}", self.fe.sorts[from].name)))?,
      InferTarget::Reg(to) => self.fe.data[to].sort.expect("expected a sort"),
      InferTarget::Bound(_) => return Err(
        self.err(src, format!("expected a variable, got {}", self.fe.to(src))))
    };
    if from == to {return Ok(res)}
    if let Some(c) = self.fe.pe.coes.get(&from).and_then(|m| m.get(&to)) {
      Ok(self.fe.apply_coe(&fsp, c, res))
    } else {
      Err(self.err(src,
        format!("type error: expected {}, got {}", self.fe.sorts[to].name, self.fe.sorts[from].name)))
    }
  }

  fn infer_sort(&self, e: &LispKind) -> Result<SortId> {
    e.unwrapped(|r| match r {
      &LispKind::Atom(a) => match self.lc.vars.get(&a) {
        None => Err(self.err(e, "variable not found")),
        Some(&(_, InferSort::Bound { sort, .. } | InferSort::Reg { sort, .. })) => Ok(sort),
        Some((_, InferSort::Unknown {..})) => panic!("finalized vars already"),
      },
      LispKind::List(es) if !es.is_empty() => {
        let a = es[0].as_atom().ok_or_else(|| self.err(&es[0], "expected an atom"))?;
        let tid = self.fe.term(a).ok_or_else(||
          self.err(&es[0], format!("term '{}' not declared", self.fe.data[a].name)))?;
        Ok(self.fe.terms[tid].ret.0)
      }
      _ => Err(self.err(e, "invalid expression"))
    })
  }
}

impl<'a> ElabTermMut<'a> {
  fn new(elab: &'a mut Elaborator, sp: Span, check_vis: bool) -> Self {
    ElabTermMut { fsp: elab.fspan(sp), elab, check_vis }
  }

  fn as_ref(&self) -> ElabTerm<'_> {
    ElabTerm::from_fsp(self.fsp.clone(), self.elab)
  }

  fn spans_insert(&mut self, e: &LispKind, k: impl FnOnce() -> ObjectKind) {
    if let Some(fsp) = e.fspan() {
      if self.fsp.file.ptr_eq(&fsp.file) {
        self.elab.spans.insert_if(Some(fsp.span), k)
      }
    }
  }

  fn atom(&mut self, e: &LispVal, a: AtomId, tgt: InferTarget) -> Result<LispVal> {
    let a = if a == AtomId::UNDER {
      let mut n = 1;
      loop {
        let a = self.env.get_atom(format!("_{n}").as_bytes());
        if !self.lc.vars.contains_key(&a) {break a}
        n += 1;
      }
    } else {a};
    let is = &mut self.elab.lc.vars.entry(a).or_insert_with(
      || (true, InferSort::new(try_get_span(&self.fsp, e)))).1;
    let res = match (is, tgt) {
      (InferSort::Reg {..}, InferTarget::Bound(_)) =>
        Err(self.as_ref().err(e, "expected a bound variable, got regular variable")),
      (&mut InferSort::Bound { sort, ref mut used }, InferTarget::Bound(sa)) => {
        *used = true;
        let s = self.env.data[sa].sort.expect("expected a sort");
        if s == sort {Ok(LispKind::Atom(a).decorate_span(&e.fspan()))}
        else {
          Err(self.as_ref().err(e, format!("type error: expected {}, got {}",
            self.env.sorts[s].name, self.env.sorts[sort].name)))
        }
      }
      (InferSort::Unknown {src, must_bound, sorts, ..}, tgt) => {
        let s = match tgt {
          InferTarget::Bound(sa) => {
            *must_bound = true;
            VarContext::Sort(self.elab.env.data[sa].sort.expect("expected a sort"))
          }
          InferTarget::Reg(sa) =>
            VarContext::Sort(self.elab.env.data[sa].sort.expect("expected a sort")),
          InferTarget::Provable => VarContext::Provable,
          InferTarget::Unknown => VarContext::Unknown,
        };
        let sp = FileSpan {file: self.fsp.file.clone(), span: *src};
        let val = &*sorts.entry(s).or_insert_with(||
          new_mvar(&mut self.elab.lc.mvars, tgt, Some(sp)));
        Ok(val.clone())
      }
      (&mut (InferSort::Reg { sort, ref mut used, .. } |
             InferSort::Bound { sort, ref mut used }), tgt) => {
        *used = true;
        self.as_ref().coerce(e, sort, LispVal::atom(a), tgt)
      }
    };
    self.spans_insert(e, || ObjectKind::Var(false, a));
    res
  }

  fn list(&mut self, e: &LispVal,
    mut it: impl Iterator<Item=LispVal>, tgt: InferTarget
  ) -> Result<LispVal> {
    let t = it.next().expect("empty iterator");
    let a = t.as_atom().ok_or_else(|| self.as_ref().err(&t, "expected an atom"))?;
    if self.lc.vars.contains_key(&a) {
      return Err(self.as_ref().err(&t,
        format!("term '{}' is shadowed by a local variable", self.env.data[a].name)))
    }
    let tid = self.env.term(a).ok_or_else(||
      self.as_ref().err(&t, format!("term '{}' not declared", self.env.data[a].name)))?;
    let sp1 = self.as_ref().try_get_span(&t);
    self.spans_insert(&t, || ObjectKind::Term(false, tid));
    let mut tdata = &self.env.terms[tid];
    if self.check_vis && tdata.vis.contains(Modifiers::LOCAL) {
      let msg = format!("{}: using private definition '{}' in a public context",
        self.env.data[self.spans.decl()].name, self.env.data[a].name);
      self.report(ElabError::warn(sp1, msg));
      tdata = &self.env.terms[tid];
    }
    let nargs = tdata.args.len();
    let ret = tdata.ret.0;
    let mut arg_it = 0..nargs;
    macro_rules! next_ty {() => {arg_it.next().map(|i| &self.env.terms[tid].args[i])}}
    let mut args = vec![LispKind::Atom(a).decorate_span(&t.fspan())];
    while let Some(arg) = it.next() {
      let tgt = match next_ty!() {
        None => return Err(ElabError::new_e(sp1,
          format!("expected {nargs} arguments, got {}", args.len() + it.count()))),
        Some(&(_, EType::Bound(s))) => InferTarget::Bound(self.env.sorts[s].atom),
        Some(&(_, EType::Reg(s, _))) => InferTarget::Reg(self.env.sorts[s].atom),
      };
      args.push(self.expr(&arg, tgt)?);
    }
    if next_ty!().is_some() {
      return Err(ElabError::new_e(sp1,
        format!("expected {nargs} arguments, got {}", args.len() - 1)))
    }
    self.as_ref().coerce(e, ret, LispVal::list(args), tgt)
  }

  fn other(&mut self, e: &LispVal, tgt: InferTarget) -> Result<LispVal> {
    let proc = match &self.data[AtomId::TO_EXPR_FALLBACK].lisp {
      Some(e) => e.val.clone(),
      None => return Err(self.as_ref().err(e, format!("Not a valid expression: {}", self.print(e))))
    };
    let args = vec![tgt.sort().map_or_else(LispVal::undef, LispVal::atom), e.clone()];
    let sp = self.as_ref().try_get_span(e);
    let res = self.call_func(sp, &proc, args)?;
    let et = self.as_ref();
    et.coerce(e, et.infer_sort(&res)?, res, tgt)
  }

  // TODO: Unify this with RState::RefineExpr
  fn expr(&mut self, e: &LispVal, tgt: InferTarget) -> Result<LispVal> {
    e.unwrapped(|r| match r {
      &LispKind::Atom(a) if self.lc.vars.contains_key(&a) => self.atom(e, a, tgt),
      &LispKind::Atom(a) if self.env.term(a).is_some() =>
        self.list(e, std::iter::once(e.clone()), tgt),
      &LispKind::Atom(a) => self.atom(e, a, tgt),
      LispKind::List(_) | LispKind::DottedList(_, _) if e.is_list() => match e.len() {
        0 => self.other(e, tgt),
        1 => self.expr(&e.head().expect("nonempty"), tgt),
        _ => self.list(e, Uncons::from(e.clone()), tgt),
      },
      _ => self.other(e, tgt),
    })
  }
}

#[derive(Default)]
struct BuildArgs {
  map: HashMap<AtomId, u64>,
  size: usize,
}

impl BuildArgs {
  fn push_bound(&mut self, a: Option<AtomId>) -> Option<()> {
    if self.size >= MAX_BOUND_VARS {return None}
    if let Some(a) = a {self.map.insert(a, 1 << self.size);}
    self.size += 1;
    Some(())
  }

  fn deps(&self, v: &[AtomId]) -> u64 {
    let mut ret = 0;
    for &a in v { ret |= self.map[&a] }
    ret
  }

  fn push_var(&mut self, vars: &HashMap<AtomId, (bool, InferSort)>,
    a: Option<AtomId>, is: &Option<InferSort>) -> Option<EType> {
    match is.as_ref().unwrap_or_else(||
        &vars[&a.expect("a variable must have a name or an expected type")].1) {
      &InferSort::Bound { sort, .. } => {
        self.push_bound(a)?;
        Some(EType::Bound(sort))
      },
      &InferSort::Reg { sort, ref deps, .. } => {
        let n = self.deps(deps);
        if let Some(a) = a {self.map.insert(a, n);}
        Some(EType::Reg(sort, n))
      }
      InferSort::Unknown {..} => unreachable!(),
    }
  }
  fn push_dummies(&mut self, vars: &HashMap<AtomId, (bool, InferSort)>) -> Option<()> {
    for (&a, is) in vars {
      if let (true, InferSort::Bound {..}) = is {
        self.push_bound(Some(a))?
      }
    }
    Some(())
  }

  fn expr_deps(&self, env: &Environment, e: &LispKind) -> u64 {
    e.unwrapped(|r| match r {
      &LispKind::Atom(a) => self.map[&a],
      LispKind::List(es) if !es.is_empty() =>
        if let Some(tid) = es[0].as_atom().and_then(|a| env.term(a)) {
          let tdef = &env.terms[tid];
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

#[allow(variant_size_differences)]
enum InferBinder {
  Var(Option<AtomId>, (bool, InferSort)),
  Hyp(Option<AtomId>, LispVal),
}

impl Elaborator {
  /// Elaborate a binder's [`DepType`] with a given [`LocalKind`]. Enforces the requirements that (1)
  /// bound and dummy variables do not have dependencies, (2) regular variables do not depend
  /// on dummy variables. The bool in the result's pair indicates whether the variable is a dummy variable.
  fn elab_dep_type(&mut self, error: &mut bool, lk: LocalKind, d: &DepType) -> Result<(bool, InferSort)> {
    let a = self.env.get_atom(self.ast.span(d.sort));
    let sort = self.data[a].sort.ok_or_else(|| ElabError::new_e(d.sort, "sort not found"))?;
    self.spans.insert(d.sort, ObjectKind::Sort(false, sort));
    Ok(if lk.is_bound() {
      if let Some(&Span {end, ..}) = d.deps.last() {
        self.report(ElabError::new_e(d.deps[0].start..end,
          "dependencies not allowed in curly binders or dummy variables"));
        *error = true;
      }
      (lk == LocalKind::Dummy, InferSort::Bound { sort, used: false })
    } else {
      let deps = d.deps.iter().map(|&sp| {
        let y = self.env.get_atom(self.ast.span(sp));
        self.spans.insert(sp, ObjectKind::Var(false, y));
        match self.lc.var(y, sp) {
          (_, InferSort::Unknown {dummy, must_bound, ..}) =>
            {*dummy = false; *must_bound = true}
          (_, InferSort::Reg {..}) => {
            self.report(ElabError::new_e(sp,
              "regular variables cannot depend on other regular variables"));
            *error = true;
          }
          (true, InferSort::Bound {..}) => {
            self.report(ElabError::new_e(sp,
              "regular variables cannot depend on dummy variables"));
            *error = true;
          }
          _ => {}
        }
        y
      }).collect::<Vec<_>>().into();
      (false, InferSort::Reg { sort, deps, used: false })
    })
  }

  fn elab_binder(&mut self,
    error: &mut bool, check_vis: bool, sp: Option<Span>, lk: LocalKind, ty: Option<&Type>
  ) -> Result<InferBinder> {
    let x = if lk == LocalKind::Anon {None} else {
      sp.map(|sp| {
        let a = self.env.get_atom(self.ast.span(sp));
        self.spans.insert(sp, if matches!(ty, Some(Type::Formula(_))) {
          ObjectKind::Hyp(true, a)
        } else {
          ObjectKind::Var(true, a)
        });
        a
      })
    };
    Ok(match ty {
      None => {
        let src = sp.expect("omitted type must come from a span");
        let fsp = self.fspan(src);
        if self.mm0_mode {
          self.report(ElabError::warn(src, "(MM0 mode) variable missing sort"))
        }
        let mv = self.lc.new_mvar(InferTarget::Unknown, Some(fsp));
        let dummy = lk == LocalKind::Dummy;
        InferBinder::Var(x, (dummy, InferSort::Unknown {
          src, must_bound: lk.is_bound(), dummy,
          sorts: Box::new(std::iter::once((VarContext::Unknown, mv)).collect())
        }))
      },
      Some(Type::DepType(d)) => InferBinder::Var(x, self.elab_dep_type(error, lk, d)?),
      Some(&Type::Formula(f)) => {
        let e = self.parse_formula(f)?;
        let e = self.eval_qexpr(e)?;
        let e = self.elaborate_term(f.0, check_vis, &e, InferTarget::Provable)?;
        InferBinder::Hyp(x, e)
      },
    })
  }

  /// Elaborate a term used in a theorem statement.
  pub fn elaborate_term(&mut self,
    sp: Span, check_vis: bool, e: &LispVal, tgt: InferTarget
  ) -> Result<LispVal> {
    ElabTermMut::new(self, sp, check_vis).expr(e, tgt)
  }

  /// Get the sort of an expression, assuming it is well typed.
  pub fn infer_sort(&self, sp: Span, e: &LispKind) -> Result<SortId> {
    ElabTerm::new(self, sp).infer_sort(e)
  }

  fn finalize_vars(&mut self, dummy: bool, unused_vars: bool) -> Vec<ElabError> {
    let mut errs = Vec::new();
    let mut newvars = Vec::new();
    for (&a, (new, is)) in &mut self.lc.vars {
      if let InferSort::Unknown {src, must_bound, dummy: d2, ref mut sorts} = *is {
        let unk = sorts.remove(&VarContext::Unknown);
        let prov = sorts.remove(&VarContext::Provable);
        let as_sort = |s| if let VarContext::Sort(s) = s { s } else { unreachable!() };
        let iter = sorts.keys().map(|&s| as_sort(s));
        let result = match sorts.len() {
          0 if prov.is_none() => if self.env.sorts.len() == 1 { Some(SortId(0)) } else { None },
          0 => if let OneOrMore::One(s) = self.env.provable_sort { Some(s) } else { None },
          1 => {
            let s = iter.clone().next().expect("impossible");
            if prov.is_none() || self.env.coe_prov_refl(s).is_some() { Some(s) } else { None }
          }
          _ => iter.clone().find(|&s| {
            (prov.is_none() || self.env.coe_prov_refl(s).is_some()) &&
            match self.env.pe.coes.get(&s) {
              None => iter.clone().all(|s2| s == s2),
              Some(m) => iter.clone().all(|s2| s == s2 || m.contains_key(&s2)),
            }
          })
        };
        if let Some(sort) = result {
          for (s, e) in sorts.iter().map(|(&s, e)| (as_sort(s), e))
            .chain(prov.iter().map(|e| (self.env.coe_prov_refl(sort).expect("impossible"), e)))
            .chain(unk.iter().map(|e| (sort, e)))
          {
            let mut val = LispVal::atom(a);
            if s != sort {
              let fsp = Some(FileSpan {file: self.path.clone(), span: src});
              val = self.env.apply_coe(&fsp, &self.env.pe.coes[&sort][&s], val);
            }
            if let LispKind::Ref(m) = &**e { m.get_mut(|e| *e = val); } else {unreachable!()}
          }
          let new2 = if (dummy && *new) || must_bound {
            *is = InferSort::Bound { sort, used: true };
            if self.mm0_mode {
              errs.push(ElabError::warn(src,
                format!("(MM0 mode) inferred {{{}: {}}}, type inference is not allowed in MM0 files",
                  self.env.data[a].name, self.env.sorts[sort].name)))
            }
            dummy && d2
          } else {
            *is = InferSort::Reg { sort, deps: Box::new([]), used: true };
            if self.mm0_mode {
              errs.push(ElabError::warn(src,
                format!("(MM0 mode) inferred ({}: {}), type inference is not allowed in MM0 files",
                  self.env.data[a].name, self.env.sorts[sort].name)))
            }
            false
          };
          if !new2 && *new {*new = false; newvars.push((src, a))}
        } else {
          let iter = prov.iter().map(|_| std::borrow::Cow::Borrowed("<provable>"))
            .chain(iter
              .map(|s| &*self.env.sorts[s].name)
              .sorted()
              .map(String::from_utf8_lossy));
          errs.push(ElabError::new_e(src, format!("could not infer consistent type from {{{}}}",
            iter.format(", "))))
        }
      }
    }
    newvars.sort_by_key(|&(_, a)| &*self.env.data[a].name);
    let mut vec: Vec<_> = newvars.into_iter().map(|(src, a)| (src, Some(a), None)).collect();
    vec.append(&mut self.lc.var_order);
    if unused_vars && self.options.unused_vars {
      for (sp, a, is) in &vec {
        if_chain! {
          if let Some(a) = *a;
          if let Some(InferSort::Bound { used: false, .. } | InferSort::Reg { used: false, .. }) =
            is.as_ref().or_else(|| self.lc.vars.get(&a).map(|p| &p.1));
          if !self.data[a].name.starts_with(b"_");
          then { self.report(ElabError::warn(*sp, "Unused variable")) }
        }
      }
    }
    self.lc.var_order = vec;
    errs
  }

  /// Elaborate a declaration (`term`, `axiom`, `def`, `theorem`).
  pub fn elab_decl(&mut self, full: Span, d: &Decl, doc: Option<DocComment>) -> Result<()> {
    let mut e_hyps = Vec::new();
    let mut error = false;
    macro_rules! report {
      ($e:expr) => {{let e = $e; self.report(e); error = true;}};
      ($sp:expr, $e:expr) => {report!(ElabError::new_e($sp, $e))};
    }
    if self.mm0_mode && !d.mods.is_empty() {
      self.report(ElabError::warn(d.id, "(MM0 mode) decl modifiers not allowed"))
    }

    // log!("elab {}", self.ast.span(d.id));
    let check_vis = !self.mm0_mode && match d.k {
      DeclKind::Term | DeclKind::Axiom => true,
      DeclKind::Def => !d.mods.intersects(Modifiers::LOCAL | Modifiers::ABSTRACT),
      DeclKind::Thm => d.mods.contains(Modifiers::PUB),
    };
    self.lc.clear();
    for bi in &d.bis {
      match self.elab_binder(&mut error, check_vis, bi.local, bi.kind, bi.ty.as_ref()) {
        Err(e) => { self.report(e); error = true }
        Ok(InferBinder::Var(x, is)) => {
          if !e_hyps.is_empty() {
            report!(bi.span, "hypothesis binders must come after variable binders")
          }
          if let InferSort::Bound { sort, .. } = is.1 {
            let sp = bi.local.expect(
              "this can't happen unless the variable was written explicitly");
            let mods = self.sorts[sort].mods;
            if mods.contains(Modifiers::STRICT) {
              report!(sp, format!("strict sort '{}' does not admit bound variables",
                self.sorts[sort].name.as_str()))
            } else if is.0 && mods.contains(Modifiers::FREE) {
              report!(sp, format!("free sort '{}' does not admit dummy variables",
                self.sorts[sort].name.as_str()))
            }
          }
          if self.lc.push_var(bi.local.unwrap_or(bi.span), x, is) {
            report!(bi.local.expect("this can't happen unless the variable was written explicitly"),
              "variable occurs twice in binder list");
          }
        }
        Ok(InferBinder::Hyp(x, e)) => e_hyps.push((bi, x, e)),
      }
    }
    let atom = self.env.get_atom(self.ast.span(d.id));
    self.spans.set_decl(atom);
    if self.mm0_mode && atom == AtomId::UNDER {
      self.report(ElabError::warn(d.id, "(MM0 mode) declaration name required"))
    }
    match d.k {
      DeclKind::Term | DeclKind::Def => {
        for (bi, _, _) in e_hyps {report!(bi.span, "term/def declarations have no hypotheses")}
        let ret = match &d.ty {
          None => {
            if self.mm0_mode {
              self.report(ElabError::warn(d.id, "(MM0 mode) return type required"))
            }
            None
          }
          Some(Type::Formula(f)) => return Err(ElabError::new_e(f.0, "sort expected")),
          Some(Type::DepType(ty)) => match self.elab_dep_type(&mut error, LocalKind::Anon, ty)?.1 {
            InferSort::Reg { sort, deps, .. } => {
              if self.sorts[sort].mods.contains(Modifiers::PURE) {
                report!(ty.sort, format!("pure sort '{}' cannot have term constructors",
                  self.sorts[sort].name.as_str()))
              }
              Some((ty.sort, sort, deps))
            }
            _ => unreachable!(),
          },
        };
        if d.k == DeclKind::Term {
          if let Some(v) = &d.val {report!(v.span, "term declarations have no definition")}
        } else if d.val.is_none() && !self.mm0_mode {
          self.report(ElabError::warn(d.id, "def declaration missing value"));
        }
        let val = match &d.val {
          None => None,
          Some(f) => (|| -> Result<Option<(Span, LispVal)>> {
            if self.mm0_mode {
              if let SExprKind::Formula(_) = f.k {} else {
                self.report(ElabError::warn(f.span, "(MM0 mode) expected formula"))
              }
            }
            let e = self.eval_lisp(false, f)?;
            Ok(Some((f.span, self.elaborate_term(f.span, check_vis, &e, match ret {
              None => InferTarget::Unknown,
              Some((_, s, _)) => InferTarget::Reg(self.sorts[s].atom),
            })?)))
          })().unwrap_or_else(|e| {self.report(e); None})
        };
        for e in self.finalize_vars(true, val.is_some()) {report!(e)}
        if error {return Ok(())}
        let mut args = Vec::with_capacity(self.lc.var_order.len());
        let mut ba = BuildArgs::default();
        for &(sp, a, ref is) in &self.lc.var_order {
          let ty = ba.push_var(&self.lc.vars, a, is).ok_or_else(||
            ElabError::new_e(sp, format!("too many bound variables (max {MAX_BOUND_VARS})")))?;
          if let EType::Bound(s) = ty {
            if self.sorts[s].mods.contains(Modifiers::STRICT) {
              return Err(ElabError::new_e(sp,
                format!("strict sort '{}' does not admit bound variables", self.sorts[s].name.as_str())))
            }
          }
          args.push((a, ty));
        }
        let (ret, kind) = match val {
          None => match ret {
            None => return Err(ElabError::new_e(full, "expected type or value")),
            Some((_, s, ref deps)) => ((s, ba.deps(deps)),
              if d.k == DeclKind::Term {TermKind::Term} else {TermKind::Def(None)})
          },
          Some((sp, val)) => {
            let s = self.infer_sort(sp, &val)?;
            if ba.push_dummies(&self.lc.vars).is_none() {
              return Err(ElabError::new_e(sp, format!("too many bound variables (max {MAX_BOUND_VARS})")))
            }
            let deps = ba.expr_deps(&self.env, &val);
            let val = {
              let mut de = Dedup::new(&args);
              let nh = NodeHasher::new(&self.lc, self.format_env(), self.fspan(sp));
              let i = de.dedup(&nh, ProofKind::Expr, &val)?;
              let (mut ids, heap, mut store) = build(&de);
              store.push(ids[i].take());
              Expr {heap, store: store.into()}
            };
            match ret {
              None => {
                let mut dummy_deps = vec![];
                for (&a, &(dummy, _)) in &self.lc.vars {
                  if dummy && deps & ba.map[&a] != 0 {
                    dummy_deps.push(self.data[a].name.as_str())
                  }
                }
                if !dummy_deps.is_empty() {
                  return Err(ElabError::new_e(sp, format!("dummy variables {{{}}} are unbound",
                    dummy_deps.iter().sorted().format(", "))))
                }
                ((s, deps), TermKind::Def(Some(val)))
              }
              Some((sp, s2, ref deps2)) => {
                if s != s2 {
                  return Err(ElabError::new_e(sp, format!("type error: expected {}, got {}",
                    self.env.sorts[s].name, self.env.sorts[s2].name)))
                }
                let n = ba.deps(deps2);
                if deps & !n != 0 {
                  return Err(ElabError::new_e(sp, format!("variables {{{}}} missing from dependencies",
                    ba.map.iter().filter_map(|(&a, &i)| {
                      if let InferSort::Bound {..} = self.lc.vars[&a].1 {
                        if i & deps & !n == 0 {None} else {Some(self.data[a].name.as_str())}
                      } else {None}
                    }).sorted().format(", "))))
                }
                ((s2, n), TermKind::Def(Some(val)))
              }
            }
          }
        };
        let t = Term {
          atom, args: args.into(), ret, kind,
          span: self.fspan(d.id),
          doc,
          vis: d.mods,
          full,
        };
        if atom != AtomId::UNDER {
          let (tid, err) = self.env.add_term(t).map_err(|e| e.into_elab_error(d.id))?;
          if let Some(e) = err { self.report(e.into_elab_error(d.id)) }
          self.spans.insert(d.id, ObjectKind::Term(true, tid));
        } else if VERIFY_ON_ADD {
          match self.env.verify_termdef(&Default::default(), &t) {
            Ok(()) | Err(VerifyError::UsesSorry) => {}
            Err(e) => return Err(ElabError::new_e(d.id, e.render_to_string(self))),
          }
        }
      }
      DeclKind::Axiom | DeclKind::Thm => {
        if d.val.is_none() {
          for bi in &d.bis {
            if bi.kind == LocalKind::Dummy {
              self.report(ElabError::warn(bi.local.unwrap_or(bi.span), "useless dummy variable"))
            }
          }
        }
        let e_ret = match &d.ty {
          None => return Err(ElabError::new_e(full, "return type required")),
          Some(Type::DepType(ty)) => return Err(ElabError::new_e(ty.sort, "expression expected")),
          &Some(Type::Formula(f)) => {
            let e = self.parse_formula(f)?;
            let e = self.eval_qexpr(e)?;
            self.elaborate_term(f.0, check_vis, &e, InferTarget::Provable)?
          }
        };
        if d.k == DeclKind::Axiom {
          if let Some(v) = &d.val {report!(v.span, "axiom declarations have no definition")}
        } else if let Some(v) = &d.val {
          if self.mm0_mode {
            self.report(ElabError::warn(v.span, "(MM0 mode) theorems should not have proofs"))
          }
        } else if self.mm0_mode {
        } else {
          self.report(ElabError::warn(d.id, "theorem declaration missing value"))
        }
        for e in self.finalize_vars(false, true) {report!(e)}
        if error {return Ok(())}
        let mut args = Vec::with_capacity(self.lc.var_order.len());
        let mut ba = BuildArgs::default();
        for &(sp, a, ref is) in &self.lc.var_order {
          let ty = ba.push_var(&self.lc.vars, a, is).ok_or_else(||
            ElabError::new_e(sp, format!("too many bound variables (max {MAX_BOUND_VARS})")))?;
          if let EType::Bound(s) = ty {
            if self.sorts[s].mods.contains(Modifiers::STRICT) {
              return Err(ElabError::new_e(sp,
                format!("strict sort '{}' does not admit bound variables", self.sorts[s].name.as_str())))
            }
          }
          args.push((a, ty));
        }
        let mut de = Dedup::new(&args);
        let span = self.fspan(d.id);
        let nh = NodeHasher::new(&self.lc, self.format_env(), span.clone());
        let mut is = Vec::new();
        for &(bi, a, ref e) in &e_hyps {
          if a.map_or(false, |a| self.lc.vars.contains_key(&a)) {
            return Err(ElabError::new_e(bi.span, "hypothesis shadows local variable"))
          }
          is.push((a, de.dedup(&nh, ProofKind::Expr, e)?))
        }
        let ir = de.dedup(&nh, ProofKind::Expr, &e_ret)?;
        let NodeHasher {var_map, fsp, ..} = nh;
        let (mut ids, heap, store) = build(&de);
        let hyps = is.iter().map(|&(a, i)| (a, ids[i].take())).collect();
        let ret = ids[ir].take();
        let kind = match &d.val {
          None if d.k == DeclKind::Axiom => ThmKind::Axiom,
          None => ThmKind::Thm(None),
          Some(e) => ThmKind::Thm({
            if self.options.check_proofs {
              (|| -> Result<Option<Proof>> {
                let mut de: Dedup<ProofHash> = de.map_proof();
                let mut is2 = Vec::new();
                for (i, (bi, a, e)) in e_hyps.into_iter().enumerate() {
                  if let Some(a) = a {
                    let p = LispVal::atom(a);
                    let hyp = de.add(ProofKind::Proof, p.clone(), ProofHash::Hyp(i, is[i].1));
                    let check = self.options.unused_vars && !self.data[a].name.starts_with(b"_");
                    is2.push((bi.span, check, hyp));
                    self.lc.add_proof(a, e, p)
                  }
                }
                let g = LispVal::new_ref(LispVal::goal(self.fspan(e.span), e_ret));
                self.lc.goals = vec![g.clone()];
                self.elab_lisp(e)?;
                if !self.lc.goals.is_empty() {
                  let stat = self.stat();
                  self.call_goal_listener(&stat);
                }
                for g in mem::take(&mut self.lc.goals) {
                  report!(try_get_span(&span, &g), format!("|- {}",
                    self.format_env().pp(&g.goal_type().expect("expected a goal"), 80)))
                }
                if error {return Ok(None)}
                let nh = NodeHasher {var_map, fsp, fe: self.format_env(), lc: &self.lc};
                let ip = de.dedup(&nh, ProofKind::Proof, &g)?;
                let (mut ids, heap, mut store) = build(&de);
                let hyps = is2.into_iter().map(|(sp, check, i)| {
                  let val = &mut ids[i];
                  if check && val.is_unshared() {
                    self.report(ElabError::warn(sp, "Unused hypothesis"))
                  }
                  val.take()
                }).collect();
                store.push(ids[ip].take());
                Ok(Some(Proof {heap, hyps, store: store.into()}))
              })().unwrap_or_else(|e| {self.report(e); None})
            } else {None}
          })
        };
        let t = Thm {
          atom, span, vis: d.mods, full, doc,
          args: args.into(), heap, store: store.into(), hyps, ret, kind
        };
        if atom != AtomId::UNDER {
          let (tid, err) = self.env.add_thm(t).map_err(|e| e.into_elab_error(d.id))?;
          if let Some(e) = err { self.report(e.into_elab_error(d.id)) }
          self.spans.insert(d.id, ObjectKind::Thm(true, tid));
        } else if VERIFY_ON_ADD {
          match self.verify_thmdef(&Default::default(), &t) {
            Ok(()) | Err(VerifyError::UsesSorry) => {}
            Err(e) => return Err(ElabError::new_e(d.id, e.render_to_string(self))),
          }
        }
      }
    }
    self.spans.lc = Some(mem::take(&mut self.lc));
    Ok(())
  }
}

/// This is a temporary structure returned by [`add_thm`](Elaborator::add_thm)
/// which implements the `(add-thm! x bis hyps ret vis vtask)` user-level function,
/// when `vtask` is a lambda instead of a direct proof. In this case, we have to
/// suspend adding the theorem, store local variables in this structure, and execute the
/// user closure, calling [`finish_add_thm`](Elaborator::finish_add_thm) afterwards.
#[derive(Debug)]
pub struct AwaitingProof {
  thm: Thm,
  de: Dedup<ProofHash>,
  var_map: HashMap<AtomId, usize>,
  lc: Box<LocalContext>,
  is: Vec<usize>,
}

impl AwaitingProof {
  /// The theorem name being added.
  #[must_use] pub fn atom(&self) -> AtomId { self.thm.atom }

  /// Once the user closure completes, we can call this function to consume the suspended
  /// computation and finish adding the theorem.
  pub fn finish(self, elab: &mut Elaborator, fsp: &FileSpan, proof: LispVal) -> Result<()> {
    let AwaitingProof {thm, de, var_map, mut lc, is} = self;
    mem::swap(&mut elab.lc, &mut lc);
    elab.finish_add_thm(fsp, thm, Some(Some(ThmVal {de, var_map, lc: Some(lc), is, proof})))
  }
}

#[derive(Debug)]
struct ThmVal {
  de: Dedup<ProofHash>,
  var_map: HashMap<AtomId, usize>,
  lc: Option<Box<LocalContext>>,
  is: Vec<usize>,
  proof: LispVal
}

fn dummies(fe: FormatEnv<'_>, fsp: &FileSpan, lc: &mut LocalContext, e: &LispVal) -> Result<()> {
  macro_rules! sp {($e:expr) => {$e.fspan().unwrap_or(fsp.clone()).span}}
  let mut dummy = |x: AtomId, es: &LispKind| -> Result<()> {
    let s = es.as_atom().ok_or_else(|| ElabError::new_e(sp!(es), "expected an atom"))?;
    let sort = fe.data[s].sort.ok_or_else(|| ElabError::new_e(sp!(es),
      format!("unknown sort '{}'", fe.to(&s))))?;
    if x != AtomId::UNDER { lc.vars.insert(x, (true, InferSort::Bound { sort, used: true })); }
    Ok(())
  };
  e.unwrapped(|r| {
    if let LispKind::AtomMap(m) = r {
      for (&a, e) in m { dummy(a, e)? }
    } else {
      for e in Uncons::from(e.clone()) {
        let mut u = Uncons::from(e.clone());
        if let (Some(ex), Some(es)) = (u.next(), u.next()) {
          let x = ex.as_atom().ok_or_else(|| ElabError::new_e(sp!(ex), "expected an atom"))?;
          dummy(x, &es)?;
        } else {
          return Err(ElabError::new_e(sp!(e), "invalid dummy arguments"))
        }
      }
    }
    Ok(())
  })
}

type Binder = (Option<AtomId>, EType);

impl Elaborator {
  fn deps(&self,
    fsp: &FileSpan, vars: &HashMap<AtomId, u64>, vs: LispVal
  ) -> Result<(Box<[AtomId]>, u64)> {
    macro_rules! sp {($e:expr) => {$e.fspan().unwrap_or(fsp.clone()).span}}
    let mut n = 0;
    let mut ids = Vec::new();
    for v in Uncons::from(vs) {
      let a = v.as_atom().ok_or_else(|| ElabError::new_e(sp!(v), "expected an atom"))?;
      n |= vars.get(&a).ok_or_else(|| ElabError::new_e(sp!(v),
        format!("undeclared variable '{}'", self.print(&v))))?;
      ids.push(a);
    }
    Ok((ids.into(), n))
  }

  fn binders(&self,
    fsp: &FileSpan, u: Uncons, (varmap, next_bv): &mut (HashMap<AtomId, u64>, u64)
  ) -> Result<(LocalContext, Box<[Binder]>)> {
    macro_rules! sp {($e:expr) => {$e.fspan().unwrap_or(fsp.clone()).span}}
    let mut lc = LocalContext::new();
    let mut args = Vec::new();
    for e in u {
      let mut u = Uncons::from(e.clone());
      if let (Some(ea), Some(es)) = (u.next(), u.next()) {
        let a = ea.as_atom().ok_or_else(|| ElabError::new_e(sp!(ea), "expected an atom"))?;
        let a = if a == AtomId::UNDER {None} else {Some(a)};
        let s = es.as_atom().ok_or_else(|| ElabError::new_e(sp!(es), "expected an atom"))?;
        let sort = self.data[s].sort.ok_or_else(|| ElabError::new_e(sp!(es),
          format!("unknown sort '{}'", self.print(&s))))?;
        let (is, ty) = match u.next() {
          None => {
            if let Some(a) = a {
              if *next_bv >= 1 << MAX_BOUND_VARS {
                return Err(ElabError::new_e(fsp.span,
                  format!("too many bound variables (max {MAX_BOUND_VARS})")))
              }
              varmap.insert(a, *next_bv);
              *next_bv *= 2;
            }
            (InferSort::Bound { sort, used: false }, EType::Bound(sort))
          }
          Some(vs) => {
            let (deps, n) = self.deps(fsp, varmap, vs)?;
            (InferSort::Reg { sort, deps, used: false }, EType::Reg(sort, n))
          }
        };
        lc.push_var(sp!(ea), a, (false, is));
        args.push((a, ty))
      } else {
        return Err(ElabError::new_e(sp!(e),
          format!("binder syntax error: {}", self.print(&e))))
      }
    }
    Ok((lc, args.into()))
  }

  fn visibility(&self, fsp: &FileSpan, e: &LispVal) -> Result<Modifiers> {
    macro_rules! sp {($e:expr) => {$e.fspan().unwrap_or(fsp.clone()).span}}
    match e.as_atom() {
      None if e.exactly(0) => Ok(Modifiers::NONE),
      Some(AtomId::PUB) => Ok(Modifiers::PUB),
      Some(AtomId::ABSTRACT) => Ok(Modifiers::ABSTRACT),
      Some(AtomId::LOCAL) => Ok(Modifiers::LOCAL),
      _ => Err(ElabError::new_e(sp!(e), format!("expected visibility, got {}", self.print(e))))
    }
  }

  /// Parse and add a term/def declaration (this is called by the `(add-term!)` lisp function).
  pub fn add_term(&mut self, fsp: &FileSpan, es: &[LispVal]) -> Result<()> {
    macro_rules! sp {($e:expr) => {$e.fspan().unwrap_or_else(|| fsp.clone()).span}}
    let (x, args, ret, vis, val) = match es {
      [x, args, ret] => (x, args, ret, Modifiers::NONE, None),
      [x, args, ret, vis, ds, val] => {
        let mods = self.visibility(fsp, vis)?;
        if !DeclKind::Def.allowed_visibility(mods) {
          return Err(ElabError::new_e(sp!(vis), "invalid modifiers for this keyword"))
        }
        (x, args, ret, mods, Some((ds, val)))
      }
      _ => return Err(ElabError::new_e(fsp.span, "expected 3 or 6 arguments"))
    };
    let span = x.fspan().unwrap_or_else(|| fsp.clone());
    let x = x.as_atom().ok_or_else(|| ElabError::new_e(span.span, "expected an atom"))?;
    if self.data[x].decl.is_some() {
      return Err(ElabError::new_e(fsp.span,
        format!("duplicate term/def declaration '{}'", self.print(&x))))
    }
    let mut vars = (HashMap::new(), 1);
    let (mut lc, args) = self.binders(fsp, Uncons::from(args.clone()), &mut vars)?;
    let ret = if let Some(s) = ret.as_atom() {
      let s = self.data[s].sort.ok_or_else(|| ElabError::new_e(sp!(ret),
        format!("unknown sort '{}'", self.print(&s))))?;
      (s, 0)
    } else {
      let mut u = Uncons::from(ret.clone());
      if let (Some(e), Some(vs)) = (u.next(), u.next()) {
        let s = e.as_atom().ok_or_else(|| ElabError::new_e(sp!(e), "expected an atom"))?;
        let s = self.data[s].sort.ok_or_else(|| ElabError::new_e(sp!(e),
          format!("unknown sort '{}'", self.print(&s))))?;
        (s, self.deps(fsp, &vars.0, vs)?.1)
      } else {
        return Err(ElabError::new_e(sp!(ret), format!("syntax error: {}", self.print(ret))))
      }
    };
    let kind = if let Some((ds, val)) = val {
      TermKind::Def((|| -> Result<Option<Expr>> {
        dummies(self.format_env(), fsp, &mut lc, ds)?;
        let mut de = Dedup::new(&args);
        let nh = NodeHasher::new(&lc, self.format_env(), fsp.clone());
        let i = de.dedup(&nh, ProofKind::Expr, val)?;
        let (mut ids, heap, mut store) = build(&de);
        store.push(ids[i].take());
        Ok(Some(Expr {heap, store: store.into()}))
      })().unwrap_or_else(|e| {
        self.report(ElabError::new_e(e.pos,
          format!("while adding {}: {}", self.print(&x), e.kind.msg())));
        None
      }))
    } else {TermKind::Term};
    let full = fsp.span;
    self.env.add_term(Term {atom: x, span, full, vis, doc: None, args, ret, kind})
      .map_err(|e| e.into_elab_error(full))?;
    Ok(())
  }

  /// Parse and add an axiom/theorem declaration (this is called by the `(add-thm!)` lisp function).
  ///
  /// This function may either complete successfully, in which case it returns `Ok(Ok(()))`,
  /// or it may yield if the user provided proof term is a closure that requires evaluation,
  /// in which case it returns `Ok(Err((ap, proof_closure)))` where `(proof_closure)` should
  /// evaluate to some value `proof`, which can be passed to [`AwaitingProof::finish`]
  /// to finish adding the theorem to the environment.
  pub fn add_thm(&mut self,
    fsp: FileSpan, es: &[LispVal]
  ) -> Result<Result<(), (Box<AwaitingProof>, LispVal)>> {
    macro_rules! sp {($e:expr) => {$e.fspan().unwrap_or(fsp.clone()).span}}
    let (x, args, hyps, ret, vis, proof) = match es {
      [x, args, hyps, ret] => (x, args, hyps, ret, Modifiers::NONE, None),
      [x, args, hyps, ret, vis, vtask] => {
        let mods = self.visibility(&fsp, vis)?;
        if !DeclKind::Thm.allowed_visibility(mods) {
          return Err(ElabError::new_e(sp!(vis), "invalid modifiers for this keyword"))
        }
        (x, args, hyps, ret, mods, Some(vtask.clone()))
      }
      _ => return Err(ElabError::new_e(fsp.span, "expected 4 or 6 arguments"))
    };
    let span = x.fspan().unwrap_or_else(|| fsp.clone());
    let x = x.as_atom().ok_or_else(|| ElabError::new_e(span.span, "expected an atom"))?;
    if self.data[x].decl.is_some() {
      return Err(ElabError::new_e(fsp.span,
        format!("duplicate axiom/theorem declaration '{}'", self.print(&x))))
    }
    let mut vars = (HashMap::new(), 1);
    let (mut lc, args) = self.binders(&fsp, Uncons::from(args.clone()), &mut vars)?;
    let mut is = Vec::new();
    mem::swap(&mut self.lc, &mut lc);
    let check_vis = proof.is_none() || vis.contains(Modifiers::PUB);
    let e_ret = (|| -> Result<_> {
      for e in Uncons::from(hyps.clone()) {
        let mut u = Uncons::from(e.clone());
        if let (Some(ex), Some(ty)) = (u.next(), u.next()) {
          let x = ex.as_atom().ok_or_else(|| ElabError::new_e(sp!(ex), "expected an atom"))?;
          let a = if x == AtomId::UNDER {None} else {Some(x)};
          let ty = self.elaborate_term(sp!(ty), check_vis, &ty, InferTarget::Provable)?;
          is.push((a, ty));
        } else {
          return Err(ElabError::new_e(sp!(hyps), format!("syntax error: {}", self.print(hyps))))
        }
      }
      self.elaborate_term(sp!(ret), check_vis, ret, InferTarget::Provable)
    })();
    mem::swap(&mut self.lc, &mut lc);
    let e_ret = e_ret?;
    if let Some(e) = self.finalize_vars(true, false).into_iter().next() { return Err(e) }
    // crate::server::log(format!("{}: {:#?}", self.print(&x), lc));
    let mut de = Dedup::new(&args);
    let nh = NodeHasher::new(&lc, self.format_env(), fsp.clone());
    // crate::server::log(format!("{}: {:#?}", self.print(&x), nh.var_map));
    let is = is.into_iter().map(|(a, ty)| {
      Ok((a, de.dedup(&nh, ProofKind::Expr, &ty)?, ty))
    }).collect::<Result<Vec<_>>>()?;
    let ir = de.dedup(&nh, ProofKind::Expr, &e_ret)?;
    let (mut ids, heap, store) = build(&de);
    let hyps = is.iter().map(|&(a, i, _)| {
      (a, ids[i].take())
    }).collect();
    let ret = ids[ir].take();
    let thm = Thm {
      atom: x, span, vis, full: fsp.span, doc: None,
      kind: ThmKind::Axiom,
      args, heap, store: store.into(), hyps, ret
    };
    let out = if let Some(proof) = proof {
      Some(if self.options.check_proofs {
        let mut de = de.map_proof();
        let var_map = nh.var_map;
        let is = is.into_iter().enumerate().filter_map(|(i, (a, j, ty))| {
          let a = a?;
          let p = LispVal::atom(a);
          lc.add_proof(a, ty, p.clone());
          Some(de.add(ProofKind::Proof, p, ProofHash::Hyp(i, j)))
        }).collect();
        if proof.is_proc() {
          lc.set_goals(std::iter::once(LispVal::goal(fsp, e_ret)));
          let lc = Box::new(mem::replace(&mut self.lc, lc));
          return Ok(Err((Box::new(AwaitingProof {thm, de, var_map, lc, is}), proof)))
        }
        Some(ThmVal {de, var_map, lc: Some(Box::new(lc)), is, proof})
      } else {None})
    } else {None};
    self.finish_add_thm(&fsp, thm, out)?;
    Ok(Ok(()))
  }

  #[allow(clippy::option_option)]
  fn finish_add_thm(&mut self, fsp: &FileSpan, mut t: Thm, res: Option<Option<ThmVal>>) -> Result<()> {
    macro_rules! sp {($e:expr) => {$e.fspan().unwrap_or(fsp.clone()).span}}
    t.kind = match res {
      None => ThmKind::Axiom,
      Some(res) => ThmKind::Thm(res.and_then(|ThmVal {mut de, var_map, mut lc, is: is2, proof: e}| {
        (|| -> Result<Option<Proof>> {
          let mut u = Uncons::from(e.clone());
          let (Some(ds), Some(pf), true) = (u.next(), u.next(), u.exactly(0)) else {
            return Err(ElabError::new_e(sp!(e), "bad proof format, expected (ds proof)"))
          };
          let lc = lc.as_deref_mut().unwrap_or(&mut self.lc);
          let fe = FormatEnv {source: &self.ast.source, env: &self.env};
          dummies(fe, fsp, lc, &ds)?;
          let nh = NodeHasher {var_map, lc, fe, fsp: fsp.clone()};
          let ip = de.dedup(&nh, ProofKind::Proof, &pf)?;
          let (mut ids, heap, mut store) = build(&de);
          let hyps = is2.into_iter().map(|i| ids[i].take()).collect();
          store.push(ids[ip].take());
          Ok(Some(Proof {heap, hyps, store: store.into()}))
        })().unwrap_or_else(|e| {
          self.report(ElabError::new_e(e.pos,
            format!("while adding {}: {}", self.print(&t.atom), e.kind.msg())));
          None
        })
      }))
    };
    let sp = fsp.span;
    self.env.add_thm(t).map_err(|e| e.into_elab_error(sp))?;
    Ok(())
  }
}
