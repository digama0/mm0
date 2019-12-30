use std::sync::{Arc, Mutex};
use std::mem;
use crate::util::*;
use super::{FileServer, Elaborator, ElabError, Result};
use super::environment::*;
use super::lisp::{*, print::{FormatEnv, EnvDisplay}, eval::SResult};
use super::local_context::{InferSort, try_get_span};
use super::proof::Subst;

#[derive(Debug)]
pub enum InferMode { Regular, Explicit, BoundOnly }

enum RefineExpr {
  App(Span, InferMode, AtomID, Uncons),
  Typed(LispVal, LispVal),
  Exact(LispVal),
}

#[derive(Debug)]
pub enum RStack {
  Goals {g: LispVal, gs: std::vec::IntoIter<LispVal>, es: std::vec::IntoIter<LispVal>},
  Coerce(LispVal),
  Typed(LispVal),
  RefineApp {tgt: InferTarget, t: TermID, u: Uncons, args: Vec<LispVal>},
  RefineExtraArgs {sp: Span, tgt: LispVal, u: Uncons, head: LispVal, args: Vec<LispVal>},
  RefineBis {sp: Span, tgt: LispVal, im: InferMode, t: ThmID, u: Uncons, args: Vec<LispVal>},
  RefineHyps {sp: Span, tgt: LispVal, t: ThmID, u: Uncons, args: Vec<LispVal>,
    hyps: std::vec::IntoIter<LispVal>, res: RefineHypsResult},
}

#[derive(Debug)]
pub enum RState {
  Goals {gs: std::vec::IntoIter<LispVal>, es: std::vec::IntoIter<LispVal>},
  Finish(LispVal),
  RefineProof {tgt: LispVal, p: LispVal},
  RefineExpr {tgt: InferTarget, e: LispVal},
  RefineApp {tgt: InferTarget, t: TermID, u: Uncons, args: Vec<LispVal>},
  Ret(LispVal),
  RefineArgs {sp: Span, v: LispVal, tgt: LispVal, head: LispVal, u: Uncons},
  RefineExtraArgs {sp: Span, tgt: LispVal, u: Uncons, head: LispVal, args: Vec<LispVal>},
  RefineBis {sp: Span, tgt: LispVal, im: InferMode, t: ThmID, u: Uncons, args: Vec<LispVal>},
  RefineHyps {sp: Span, tgt: LispVal, t: ThmID, u: Uncons, args: Vec<LispVal>,
    hyps: std::vec::IntoIter<LispVal>, res: RefineHypsResult},
  Coerce {tgt: LispVal, p: LispVal},
}

impl EnvDisplay for RState {
  fn fmt(&self, fe: FormatEnv, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      RState::Goals {gs, es} => write!(f,
        "Goals {{gs: {}, es: {}}}", fe.to(gs.as_slice()), fe.to(es.as_slice())),
      RState::Finish(e) => write!(f, "Finish({})", fe.to(e)),
      RState::RefineProof {tgt, p} => write!(f,
        "RefineProof {{\n  tgt: {},\n  p: {}}}", fe.to(tgt), fe.to(p)),
      RState::RefineExpr {tgt, e} => write!(f,
        "RefineExpr {{\n  tgt: {},\n  e: {}}}", fe.to(tgt), fe.to(e)),
      RState::RefineApp {tgt, t, u, args} => write!(f,
        "RefineApp {{\n  tgt: {},\n  {} {} -> {}}}",
        fe.to(tgt), fe.to(t), fe.to(u), fe.to(args)),
      RState::Ret(e) => write!(f, "Ret({})", fe.to(e)),
      RState::RefineArgs {sp:_, v, tgt, head, u} => write!(f,
        "RefineArgs {{\n  v: {},\n  tgt: {},\n  head: {},\n  u: {}}}",
        fe.to(v), fe.to(tgt), fe.to(head), fe.to(u)),
      RState::RefineExtraArgs {sp:_, tgt, u, head, args} => write!(f,
        "RefineExtraArgs {{\n  tgt: {},\n  u: {},\n  head: {},\n  args: {}}}",
        fe.to(tgt), fe.to(u), fe.to(head), fe.to(args)),
      RState::RefineBis {sp:_, tgt, im, t, u, args} => write!(f,
        "RefineBis {{\n  tgt: {},\n  im: {:?},\n  {} {} -> {}}}",
        fe.to(tgt), im, fe.to(t), fe.to(u), fe.to(args)),
      RState::RefineHyps {sp:_, tgt, t, u, args, hyps, res} => write!(f,
        "RefineHyps {{\n  tgt: {},\n  {} {} -> {},\n  hyps: {},\n  res: {}}}",
        fe.to(tgt), fe.to(t), fe.to(u), fe.to(args), fe.to(hyps.as_slice()), fe.to(res)),
      RState::Coerce {tgt, p} => write!(f,
        "Coerce {{\n  tgt: {},\n  p: {}}}", fe.to(tgt), fe.to(p)),
    }
  }
}

#[derive(Debug)]
pub enum RefineHypsResult { Ok(LispVal), Extra }

impl EnvDisplay for RefineHypsResult {
  fn fmt(&self, fe: FormatEnv, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      RefineHypsResult::Ok(e) => write!(f, "Ok({})", fe.to(e)),
      RefineHypsResult::Extra => write!(f, "Extra"),
    }
  }
}

pub enum RefineResult {
  Ret(LispVal),
  RefineExtraArgs(LispVal, Vec<LispVal>),
}

impl LispKind {
  fn conv(tgt: LispVal, u: LispVal, p: LispVal) -> LispVal {
    Arc::new(LispKind::List(vec![Arc::new(LispKind::Atom(AtomID::CONV)), tgt, u, p]))
  }
  fn unfold(t: AtomID, es: Vec<LispVal>, p: LispVal) -> LispVal {
    Arc::new(LispKind::List(vec![
      Arc::new(LispKind::Atom(AtomID::UNFOLD)),
      Arc::new(LispKind::Atom(t)),
      Arc::new(LispKind::List(es)), p]))
  }
  fn sym(p: LispVal) -> LispVal {
    Arc::new(LispKind::List(vec![Arc::new(LispKind::Atom(AtomID::SYM)), p]))
  }
  fn apply_conv(c: LispVal, tgt: LispVal, p: LispVal) -> LispVal {
    if c.is_def() {LispKind::conv(tgt, c, p)} else {p}
  }

  fn as_mvar<T>(e: &LispVal, f: impl FnOnce(&LispVal, &Mutex<LispVal>) -> T) -> Option<T> {
    fn rec<T, F: FnOnce(&LispVal, &Mutex<LispVal>) -> T>(e: &LispVal, f: F) -> std::result::Result<T, Option<F>> {
      match &**e {
        LispKind::Annot(_, e2) => rec(e2, f),
        LispKind::Ref(m) => {
          let g = m.try_lock().unwrap().clone();
          match rec(&g, f) {
            Ok(r) => Ok(r),
            Err(None) => Err(None),
            Err(Some(f)) => Ok(f(e, m))
          }
        }
        LispKind::MVar(_, _) => Err(Some(f)),
        _ => Err(None)
      }
    }
    rec(e, f).ok()
  }
}

impl<'a, F: FileServer + ?Sized> Elaborator<'a, F> {
  fn parse_refine(&mut self, fsp: &FileSpan, e: &LispVal) -> Result<RefineExpr> {
    Ok(match &*LispKind::unwrapped_arc(e) {
      &LispKind::Atom(a) =>
        RefineExpr::App(try_get_span(fsp, e), InferMode::Regular, a, Uncons::from(NIL.clone())),
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone());
        let sp = try_get_span(fsp, e);
        match u.next() {
          None if e.is_list() => RefineExpr::App(sp, InferMode::Regular, AtomID::UNDER, Uncons::from(NIL.clone())),
          None => Err(ElabError::new_e(try_get_span(fsp, &e), "refine: syntax error"))?,
          Some(e) => {
            let a = e.as_atom().ok_or_else(||
              ElabError::new_e(try_get_span(fsp, &e), "refine: expected an atom"))?;
            let (im, t) = match a {
              AtomID::BANG => (InferMode::Explicit,
                u.next().ok_or_else(|| ElabError::new_e(try_get_span(fsp, &e),
                  "!: expected at least one argument"))?),
              AtomID::BANG2 => (InferMode::BoundOnly,
                u.next().ok_or_else(|| ElabError::new_e(try_get_span(fsp, &e),
                  "!!: expected at least one argument"))?),
              AtomID::VERB => if let (Some(e), true) = (u.next(), u.exactly(0)) {
                return Ok(RefineExpr::Exact(e))
              } else {
                Err(ElabError::new_e(try_get_span(fsp, &e), "verb: expected one argument"))?
              },
              AtomID::COLON => if let (Some(e), Some(ty), true) = (u.next(), u.next(), u.exactly(0)) {
                return Ok(RefineExpr::Typed(ty, e))
              } else {
                Err(ElabError::new_e(try_get_span(fsp, &e), "':' expected two arguments"))?
              },
              _ => (InferMode::Regular, e)
            };
            let t = t.as_atom().ok_or_else(||
              ElabError::new_e(try_get_span(fsp, &t), "refine: expected an atom"))?;
            RefineExpr::App(sp, im, t, u)
          }
        }
      }
      _ => Err(ElabError::new_e(try_get_span(fsp, &e), "refine: syntax error"))?,
    })
  }

  fn new_goal_gv(&self, gv: &mut Vec<LispVal>, sp: Span, ty: LispVal) -> LispVal {
    let r = LispKind::new_ref(LispKind::new_goal(self.fspan(sp), ty));
    gv.push(r.clone());
    r
  }

  pub fn infer_type(&mut self, sp: Span, e: &LispVal) -> Result<LispVal> {
    macro_rules! err {
      ($e:expr, $err:expr) => {ElabError::new_e(try_get_span(&self.fspan(sp), &$e), $err)}
    }
    Ok(match &*LispKind::unwrapped_arc(e) {
      &LispKind::Atom(h) => match self.lc.get_proof(h) {
        Some((_, e, _)) => e.clone(),
        None => Err(err!(e, format!("unknown hypothesis '{}'", self.data[h].name)))?
      },
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone());
        let head = u.next().ok_or_else(|| err!(e, "not a proof"))?;
        match head.as_atom().ok_or_else(|| err!(head, "expected an atom"))? {
          AtomID::CONV => u.next().ok_or_else(|| err!(e, "bad :conv"))?,
          a => {
            let t = self.thm(a).ok_or_else(||
              err!(head, format!("unknown theorem '{}'", self.data[a].name)))?;
            let tdata = &self.env.thms[t];
            let n = tdata.args.len();
            let mut args = Vec::with_capacity(n);
            if !u.extend_into(n, &mut args) {return Err(err!(e, "not enough arguments"))}
            Subst::new(&mut self.lc, &self.env, &tdata.heap, args).subst(&tdata.ret)
          }
        }
      }
      LispKind::Goal(e) => e.clone(),
      _ => Err(err!(e, format!("not a proof: {}", self.print(e))))?
    })
  }

  fn coerce_to(&mut self, sp: Span, tgt: LispVal, e: LispVal, p: LispVal) -> Result<LispVal> {
    Ok(LispKind::apply_conv(self.unify(sp, &tgt, &e)?, tgt, p))
  }

  fn occurs(&mut self, mv: &LispVal, e: &LispVal) -> bool {
    match &**e {
      LispKind::Annot(_, e) => self.occurs(mv, e),
      LispKind::Ref(m) => Arc::ptr_eq(mv, e) || self.occurs(mv, &m.try_lock().unwrap()),
      LispKind::List(es) => es.iter().any(|e| self.occurs(mv, e)),
      LispKind::DottedList(es, r) =>
        es.iter().any(|e| self.occurs(mv, e)) && self.occurs(mv, r),
      _ => false,
    }
  }

  fn assign(&mut self, _sym: bool, mv: &LispVal, m: &Mutex<LispVal>, e: &LispVal) -> SResult<LispVal> {
    let e = &LispKind::as_mvar(e, |e2, _| e2.clone()).unwrap_or_else(|| e.clone());
    if Arc::ptr_eq(mv, e) {return Ok(UNDEF.clone())}
    if self.occurs(mv, e) {
      Err("occurs-check failed, can't build infinite assignment".into())
    } else {
      *m.try_lock().unwrap() = e.clone();
      Ok(UNDEF.clone())
    }
  }

  fn unify(&mut self, sp: Span, e1: &LispVal, e2: &LispVal) -> Result<LispVal> {
    self.unify1(e1, e2).map_err(|e| ElabError::new_e(sp, e))
  }

  fn unify1(&mut self,e1: &LispVal, e2: &LispVal) -> SResult<LispVal> {
    self.unify_core(e1, e2).map_err(|e| format!(
      "failed to unify:\n{}\n  =?=\n{}\n{}", self.print(e1), self.print(e2), e))
  }

  fn unify_core(&mut self, e1: &LispVal, e2: &LispVal) -> SResult<LispVal> {
    // crate::server::log(format!("{} =?= {}", self.print(e1), self.print(e2)));
    // (|| {
    if Arc::ptr_eq(e1, e2) {return Ok(UNDEF.clone())}
    if let Some(r) = LispKind::as_mvar(e1, |e1, m|
      self.assign(false, e1, m, e2)) {return r}
    if let Some(r) = LispKind::as_mvar(e2, |e2, m|
      self.assign(true, e2, m, e1)) {return r}
    match (e1.as_atom(), e2.as_atom()) {
      (Some(a1), Some(a2)) if a1 == a2 => Ok(UNDEF.clone()),
      (Some(a1), Some(a2)) => Err(format!(
        "variables do not match: {} != {}", self.data[a1].name, self.data[a2].name)),
      (None, None) => {
        let mut u1 = Uncons::from(e1.clone());
        let mut u2 = Uncons::from(e2.clone());
        let et1 = u1.next().ok_or_else(||
          format!("bad term: {}", self.print(e1)))?;
        let at1 = et1.as_atom().ok_or_else(||
          format!("bad term: {}", self.print(e1)))?;
        let at2 = u2.next().and_then(|a| a.as_atom()).ok_or_else(||
          format!("bad term: {}", self.print(e2)))?;
        if at1 == at2 {
          let mut cs = vec![et1.clone()];
          let u3 = u1.clone();
          while let (Some(x1), Some(x2)) = (u1.next(), u2.next()) {
            cs.push(self.unify_core(&x1, &x2)?);
          }
          if u1.exactly(0) && u2.exactly(0) {
            let mut has_undef = false;
            if cs[1..].iter().all(|c| !c.is_def() && {has_undef = true; true}) {
              Ok(UNDEF.clone())
            } else {
              if has_undef {
                for (c, x) in cs[1..].iter_mut().zip(u3) {
                  if !c.is_def() {*c = x}
                }
              }
              Ok(Arc::new(LispKind::List(cs)))
            }
          } else {
            Err(format!("bad terms: {}, {}", self.print(e1), self.print(e2)))?
          }
        } else {
          let t1 = self.term(at1).ok_or_else(||
            format!("bad term: {}", self.print(e1)))?;
          let tdata1 = &self.terms[t1];
          let t2 = self.term(at2).ok_or_else(||
            format!("bad term: {}", self.print(e2)))?;
          let tdata2 = &self.terms[t2];
          macro_rules! s {() => {format!(
            "terms do not match: {} != {}", self.data[at1].name, self.data[at2].name)
          }}

          match (&tdata1.val, &tdata2.val) {
            (_, Some(_)) if t1 < t2 => self.unfold(true, t2, u2, e1).map_err(|e| format!("{}\n{}", s!(), e)),
            (Some(_), _) => self.unfold(false, t1, u1, e2).map_err(|e| format!("{}\n{}", s!(), e)),
            (_, Some(_)) => self.unfold(true, t2, u2, e1).map_err(|e| format!("{}\n{}", s!(), e)),
            _ => Err(s!())
          }
        }
      }
      _ => Err(format!(
        "variable vs term: {} != {}", self.print(e1), self.print(e2))),
    }
    // })().map(|r| {
    //   crate::server::log(format!("{} =?= {}\n:= {}", self.print(e1), self.print(e2), self.print(&r)));
    //   r
    // })
  }

  fn unfold(&mut self, sym: bool, t: TermID, mut u1: Uncons, e2: &LispVal) -> SResult<LispVal> {
    let tdata = &self.env.terms[t];
    let a = tdata.atom;
    let n = tdata.args.len();
    let val = tdata.val.as_ref().unwrap();
    let mut args = Vec::with_capacity(n);
    if !u1.extend_into(n, &mut args) {return Err(format!("bad term: {}", self.print(&u1)))}
    let e = Subst::new(&mut self.lc, &self.env, &val.heap, args.clone()).subst(&val.head);
    let u = self.unify1(&e, e2)?;
    if u.is_def() {
      let u = LispKind::unfold(a, args, u);
      Ok(if sym {LispKind::sym(u)} else {u})
    } else {Ok(u)}
  }

  fn type_target(&self, ty: &Type) -> InferTarget {
    match ty {
      &Type::Bound(s) => InferTarget::Bound(self.sorts[s].atom),
      &Type::Reg(s, _) => InferTarget::Reg(self.sorts[s].atom),
    }
  }

  pub fn run_refine(&mut self,
    sp: Span,
    stack: &mut Vec<RStack>,
    mut active: RState,
    gv: &mut Vec<LispVal>
  ) -> Result<RefineResult> {
    let fsp = self.fspan(sp);
    loop {
      // crate::server::log(format!("{}", self.print(&active)));
      active = match active {
        RState::Goals {mut gs, mut es} => match es.next() {
          None => {gv.extend(gs); RState::Finish(UNDEF.clone())}
          Some(p) => loop {
            if let Some(g) = gs.next() {
              if let Some(tgt) = g.goal_type() {
                stack.push(RStack::Goals {g, gs, es});
                break RState::RefineProof {tgt, p}
              }
            } else {break RState::Finish(UNDEF.clone())}
          }
        },
        RState::Finish(ret) => {
          if !gv.is_empty() {
            if !self.lc.goals.is_empty() {gv.append(&mut self.lc.goals)}
            mem::swap(&mut self.lc.goals, gv);
          }
          self.lc.clean_mvars();
          return Ok(RefineResult::Ret(ret))
        }
        RState::RefineProof {tgt, p} => match self.parse_refine(&fsp, &p)? {
          RefineExpr::App(sp, _, AtomID::QMARK, _) =>
            RState::Ret(LispKind::new_ref(LispKind::new_goal(self.fspan(sp), tgt))),
          RefineExpr::App(sp, _, AtomID::UNDER, u) => {
            if u.exactly(0) {
              RState::Ret(self.new_goal_gv(gv, sp, tgt))
            } else {
              let mv = self.lc.new_mvar(InferTarget::Unknown);
              let head = self.new_goal_gv(gv, sp, mv);
              RState::RefineExtraArgs {sp, tgt, u, head, args: vec![]}
            }
          }
          RefineExpr::App(sp, im, a, u) => {
            if let Some((_, v, _)) = self.lc.get_proof(a) {
              RState::RefineArgs {
                sp, v: v.clone(), tgt, u,
                head: LispKind::new_span(self.fspan(sp), Arc::new(LispKind::Atom(a)))
              }
            } else if let Some(DeclKey::Thm(t)) = self.data[a].decl {
              RState::RefineBis {sp, tgt, im, t, args: vec![Arc::new(LispKind::Atom(a))], u}
            } else {
              Err(ElabError::new_e(sp, format!(
                "unknown theorem/hypothesis '{}'", self.data[a].name)))?
            }
          }
          RefineExpr::Typed(e, p) => {
            stack.push(RStack::Coerce(tgt));
            stack.push(RStack::Typed(p));
            RState::RefineExpr {tgt: InferTarget::Unknown, e}
          }
          RefineExpr::Exact(p) => RState::Coerce {tgt, p},
        },
        RState::Ret(ret) => match stack.pop() {
          None => RState::Finish(ret),
          Some(RStack::Goals {g, gs, es}) => {
            g.as_ref_(|e| *e = ret).unwrap();
            RState::Goals {gs, es}
          },
          Some(RStack::Coerce(tgt)) => RState::Coerce {tgt, p: ret},
          Some(RStack::Typed(p)) => RState::RefineProof {tgt: ret, p},
          Some(RStack::RefineApp {tgt, t, u, mut args}) => {
            args.push(ret);
            RState::RefineApp {tgt, t, u, args}
          }
          Some(RStack::RefineBis {sp, tgt, im, t, u, mut args}) => {
            args.push(ret);
            RState::RefineBis {sp, tgt, im, t, u, args}
          }
          Some(RStack::RefineHyps {sp, tgt, t, u, mut args, hyps, res}) => {
            args.push(ret);
            RState::RefineHyps {sp, tgt, t, u, args, hyps, res}
          }
          Some(RStack::RefineExtraArgs {sp, tgt, u, head, mut args}) => {
            args.push(ret);
            RState::RefineExtraArgs {sp, tgt, u, head, args}
          }
        },
        RState::Coerce {tgt, p} => {
          let e = self.infer_type(sp, &p)?;
          RState::Ret(self.coerce_to(sp, tgt, e, p)?)
        }
        RState::RefineExpr {tgt, e} => match self.parse_refine(&fsp, &e)? {
          RefineExpr::App(_, _, AtomID::UNDER, _) => RState::Ret(self.lc.new_mvar(tgt)),
          RefineExpr::App(sp, _, a, u) => {
            let empty = u.exactly(0);
            if let Some(is) = if empty {self.lc.vars.get(&a)} else {None} {
              let (sort, bd) = match is.1 {
                InferSort::Bound {sort} => (sort, true),
                InferSort::Reg {sort, ..} => (sort, false),
                InferSort::Unknown {..} => unreachable!(),
              };
              let e = Arc::new(LispKind::Atom(a));
              RState::Ret(match tgt {
                InferTarget::Unknown => e,
                InferTarget::Provable =>
                  if self.sorts[sort].mods.contains(Modifiers::PROVABLE) {e}
                  else {
                    Err(ElabError::new_e(sp, format!(
                      "type error: expected provable, got {}", self.sorts[sort].name)))?
                  },
                InferTarget::Bound(s) => {
                  if !bd {Err(ElabError::new_e(sp, "type error: expected bound var, got regular"))?}
                  let s = self.data[s].sort.ok_or_else(|| ElabError::new_e(sp, "bad sort"))?;
                  if s == sort {e} else {
                    Err(ElabError::new_e(sp, format!(
                      "type error: expected {}, got {}", self.sorts[s].name, self.sorts[sort].name)))?
                  }
                }
                InferTarget::Reg(s) => {
                  let s = self.data[s].sort.ok_or_else(|| ElabError::new_e(sp, "bad sort"))?;
                  if s == sort {e}
                  else if let Some(c) = self.pe.coes.get(&sort).and_then(|m| m.get(&s)) {
                    self.apply_coe(&Some(self.fspan(sp)), c, e)
                  } else {
                    Err(ElabError::new_e(sp, format!(
                      "type error: expected {}, got {}", self.sorts[s].name, self.sorts[sort].name)))?
                  }
                }
              })
            } else if let Some(t) = self.term(a) {
              if tgt.bound() {Err(ElabError::new_e(sp, format!(
                "type error: expected bound var, got {}", self.print(&e))))?}
              RState::RefineApp {tgt, t, u, args: vec![Arc::new(LispKind::Atom(a))]}
            } else if let Some(s) = tgt.sort().filter(|_| empty) {
              let sort = self.data[s].sort.ok_or_else(|| ElabError::new_e(sp, "bad sort"))?;
              self.lc.vars.insert(a, (true, InferSort::Bound {sort}));
              RState::Ret(Arc::new(LispKind::Atom(a)))
            } else {
              Err(ElabError::new_e(sp, format!("unknown term '{}'", self.data[a].name)))?
            }
          }
          RefineExpr::Typed(s, e) => {
            let s = s.as_atom().filter(|&s| self.data[s].sort.is_some())
              .ok_or_else(|| ElabError::new_e(sp, "expected a sort"))?;
            RState::RefineExpr {
              e,
              tgt: if tgt.bound() {InferTarget::Bound(s)} else {InferTarget::Reg(s)}
            }
          }
          RefineExpr::Exact(e) => RState::Ret(e),
        },
        RState::RefineApp {tgt: ret, t, mut u, mut args} => 'l: loop { // labeled block, not a loop
          for (_, ty) in &self.env.terms[t].args[args.len() - 1..] {
            let tgt = self.type_target(ty);
            match u.next() {
              Some(e) => {
                stack.push(RStack::RefineApp {tgt: ret, t, u, args});
                break 'l RState::RefineExpr {tgt, e}
              }
              None => args.push(self.lc.new_mvar(tgt))
            }
          }
          break RState::Ret(Arc::new(LispKind::List(args)))
        },
        RState::RefineArgs {sp, v, tgt, head, u} if u.exactly(0) =>
          RState::Ret(self.coerce_to(sp, tgt, v, head)?),
        RState::RefineArgs {sp, tgt, head, u, ..} =>
          RState::RefineExtraArgs {sp, tgt, u, head, args: vec![]},
        RState::RefineExtraArgs {sp, tgt, mut u, head, args} => match u.next() {
          Some(p) => {
            stack.push(RStack::RefineExtraArgs {sp, tgt, u, head, args});
            let mv = self.lc.new_mvar(InferTarget::Unknown);
            RState::RefineProof {tgt: mv, p}
          }
          None => {
            stack.push(RStack::Coerce(tgt));
            return Ok(RefineResult::RefineExtraArgs(head, args))
          }
        },
        RState::RefineBis {sp, tgt, im, t, mut u, mut args} => 'l2: loop { // labeled block, not a loop
          let tdata = &self.env.thms[t];
          for (_, ty) in &tdata.args[args.len() - 1..] {
            let tgt1 = self.type_target(ty);
            if let Some(e) = if match im {
              InferMode::Regular => false,
              InferMode::Explicit => true,
              InferMode::BoundOnly => ty.bound(),
            } {u.next()} else {None} {
              stack.push(RStack::RefineBis {sp, tgt, im, t, u, args});
              break 'l2 RState::RefineExpr {tgt: tgt1, e}
            } else {
              args.push(self.lc.new_mvar(tgt1))
            }
          }
          let mut subst = Subst::new(&mut self.lc, &self.env, &tdata.heap, Vec::from(&args[1..]));
          let hyps = tdata.hyps.iter().map(|(_, h)| subst.subst(h)).collect::<Vec<_>>();
          let ret = subst.subst(&tdata.ret);
          break RState::RefineHyps {
            res: if u.len() <= hyps.len() {
              RefineHypsResult::Ok(self.unify(sp, &tgt, &ret)?)
            } else {
              RefineHypsResult::Extra
            },
            sp, tgt, t, u, args, hyps: hyps.into_iter()
          }
        },
        RState::RefineHyps {sp, tgt, t, mut u, mut args, mut hyps, res} => 'l3: loop { // labeled block, not a loop
          while let Some(h) = hyps.next() {
            if let Some(p) = u.next() {
              stack.push(RStack::RefineHyps {sp, tgt, t, u, args, hyps, res});
              break 'l3 RState::RefineProof {tgt: h, p}
            } else {
              args.push(self.new_goal_gv(gv, sp, h))
            }
          }
          let head = Arc::new(LispKind::List(args));
          break match res {
            RefineHypsResult::Ok(c) => RState::Ret(LispKind::apply_conv(c, tgt, head)),
            RefineHypsResult::Extra => RState::RefineExtraArgs {sp, tgt, u, head, args: vec![]}
          }
        },
      }
    }
  }
}
