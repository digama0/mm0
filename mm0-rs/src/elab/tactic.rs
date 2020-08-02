use crate::util::*;
use super::{Elaborator, ElabError, Result};
use super::environment::*;
use super::lisp::{*, print::{FormatEnv, EnvDisplay}, eval::SResult};
use super::local_context::{InferSort, try_get_span};
use super::proof::Subst;

#[derive(Debug)]
pub enum InferMode { Regular, Explicit, BoundOnly }

enum RefineExpr {
  App(Span, Span, InferMode, AtomID, Uncons),
  Typed(LispVal, LispVal),
  Exact(LispVal),
  Proc,
}

#[derive(Debug)]
pub enum RStack {
  Goals {g: LispVal, gs: std::vec::IntoIter<LispVal>, es: std::vec::IntoIter<LispVal>},
  DeferGoals(Vec<LispVal>),
  Coerce {tgt: LispVal, u: LispVal},
  CoerceTo(LispVal),
  TypedAt {sp: Span, tgt: LispVal, p: LispVal},
  Typed(LispVal),
  RefineApp {sp2: Span, tgt: InferTarget, t: TermID, u: Uncons, args: Vec<LispVal>},
  RefineBis {sp: Span, sp2: Span, tgt: LispVal, im: InferMode, t: ThmID, u: Uncons, args: Vec<LispVal>},
  RefineHyps {sp: Span, sp2: Span, tgt: LispVal, t: ThmID, u: Uncons, args: Vec<LispVal>,
    hyps: std::vec::IntoIter<LispVal>, res: RefineHypsResult},
}

#[derive(Debug)]
pub enum RState {
  Goals {gs: std::vec::IntoIter<LispVal>, es: std::vec::IntoIter<LispVal>},
  RefineProof {tgt: LispVal, p: LispVal},
  RefineExpr {tgt: InferTarget, e: LispVal},
  RefineApp {sp2: Span, tgt: InferTarget, t: TermID, u: Uncons, args: Vec<LispVal>},
  Ret(LispVal),
  RefineArgs {sp: Span, v: LispVal, tgt: LispVal, head: LispVal, u: Uncons},
  RefineBis {sp: Span, sp2: Span, tgt: LispVal, im: InferMode, t: ThmID, u: Uncons, args: Vec<LispVal>},
  RefineHyps {sp: Span, sp2: Span, tgt: LispVal, t: ThmID, u: Uncons, args: Vec<LispVal>,
    hyps: std::vec::IntoIter<LispVal>, res: RefineHypsResult},
  Proc {tgt: LispVal, p: LispVal},
}

impl EnvDisplay for RState {
  fn fmt(&self, fe: FormatEnv, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      RState::Goals {gs, es} => write!(f,
        "Goals {{gs: {}, es: {}}}", fe.to(gs.as_slice()), fe.to(es.as_slice())),
      RState::RefineProof {tgt, p} => write!(f,
        "RefineProof {{\n  tgt: {},\n  p: {}}}", fe.to(tgt), fe.to(p)),
      RState::RefineExpr {tgt, e} => write!(f,
        "RefineExpr {{\n  tgt: {},\n  e: {}}}", fe.to(tgt), fe.to(e)),
      RState::RefineApp {tgt, t, u, args, ..} => write!(f,
        "RefineApp {{\n  tgt: {},\n  {} {} -> {}}}",
        fe.to(tgt), fe.to(t), fe.to(u), fe.to(args)),
      RState::Ret(e) => write!(f, "Ret({})", fe.to(e)),
      RState::RefineArgs {sp:_, v, tgt, head, u} => write!(f,
        "RefineArgs {{\n  v: {},\n  tgt: {},\n  head: {},\n  u: {}}}",
        fe.to(v), fe.to(tgt), fe.to(head), fe.to(u)),
      RState::RefineBis {tgt, im, t, u, args, ..} => write!(f,
        "RefineBis {{\n  tgt: {},\n  im: {:?},\n  {} {} -> {}}}",
        fe.to(tgt), im, fe.to(t), fe.to(u), fe.to(args)),
      RState::RefineHyps {tgt, t, u, args, hyps, res, ..} => write!(f,
        "RefineHyps {{\n  tgt: {},\n  {} {} -> {},\n  hyps: {},\n  res: {}}}",
        fe.to(tgt), fe.to(t), fe.to(u), fe.to(args), fe.to(hyps.as_slice()), fe.to(res)),
      RState::Proc {tgt, p} => write!(f,
        "Proc {{\n  tgt: {},\n  p: {}}}", fe.to(tgt), fe.to(p)),
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
  RefineExtraArgs(LispVal, LispVal, Uncons),
  Proc(LispVal, LispVal),
}

impl LispVal {
  fn conv(tgt: Self, u: Self, p: Self) -> Self {
    Self::list(vec![Self::atom(AtomID::CONV), tgt, u, p])
  }
  fn unfold(t: AtomID, es: Vec<Self>, p: Self) -> Self {
    Self::list(vec![Self::atom(AtomID::UNFOLD), Self::atom(t), Self::list(es), p])
  }
  fn sym(p: Self) -> Self {
    Self::list(vec![Self::atom(AtomID::SYM), p])
  }
  fn apply_conv(c: Self, tgt: Self, p: Self) -> Self {
    if c.is_def() {Self::conv(tgt, c, p)} else {p}
  }

  fn as_mvar<T>(&self, f: impl FnOnce(&Self, &LispRef) -> T) -> Option<T> {
    fn rec<T, F: FnOnce(&LispVal, &LispRef) -> T>(e: &LispVal, f: F) -> std::result::Result<T, Option<F>> {
      match &**e {
        LispKind::Annot(_, e2) => rec(e2, f),
        LispKind::Ref(m) => {
          let g = m.unref();
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
    rec(self, f).ok()
  }
}

#[derive(Debug)]
enum AssignError { Cyclic, BoundVar }

impl Elaborator {
  fn parse_refine(&mut self, fsp: &FileSpan, e: &LispVal) -> Result<RefineExpr> {
    Ok(match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => {
        let sp = try_get_span(fsp, e);
        RefineExpr::App(sp, sp, InferMode::Regular, a, Uncons::from(LispVal::nil()))
      }
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone());
        let sp = try_get_span(fsp, e);
        match u.next() {
          None if e.is_list() => RefineExpr::App(sp, sp, InferMode::Regular, AtomID::UNDER, Uncons::from(LispVal::nil())),
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
            let sp2 = try_get_span(fsp, &t);
            let t = t.as_atom().ok_or_else(|| ElabError::new_e(sp2, "refine: expected an atom"))?;
            RefineExpr::App(sp, sp2, im, t, u)
          }
        }
      }
      LispKind::Proc(_) => RefineExpr::Proc,
      _ => Err(ElabError::new_e(try_get_span(fsp, &e), "refine: syntax error"))?,
    })
  }

  fn new_goal(&mut self, sp: Span, ty: LispVal) -> LispVal {
    let r = LispVal::new_ref(LispVal::goal(self.fspan(sp), ty));
    self.lc.goals.push(r.clone());
    r
  }

  pub fn infer_type(&self, sp: Span, e: &LispVal) -> Result<LispVal> {
    macro_rules! err {
      ($e:expr, $err:expr) => {ElabError::new_e(try_get_span(&self.fspan(sp), &$e), $err)}
    }
    Ok(match &*e.unwrapped_arc() {
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
            Subst::new(&self.env, &tdata.heap, args).subst(&tdata.ret)
          }
        }
      }
      LispKind::Goal(e) => e.clone(),
      _ => Err(err!(e, format!("not a proof: {}", self.print(e))))?
    })
  }

  fn coerce_term(&mut self, sp: Span, tgt: InferTarget, s: SortID, bd: bool, e: LispVal) -> Result<LispVal> {
    let tgt = match tgt {
      InferTarget::Unknown => return Ok(e),
      InferTarget::Provable if self.sorts[s].mods.contains(Modifiers::PROVABLE) => return Ok(e),
      InferTarget::Provable => *self.pe.coe_prov.get(&s).ok_or_else(||
        ElabError::new_e(sp, format!("type error: expected provable, got {}", self.print(&s))))?,
      InferTarget::Bound(_) if !bd => Err(ElabError::new_e(sp, "type error: expected bound var, got regular"))?,
      InferTarget::Bound(tgt) => self.data[tgt].sort.ok_or_else(|| ElabError::new_e(sp, "bad sort"))?,
      InferTarget::Reg(tgt) => self.data[tgt].sort.ok_or_else(|| ElabError::new_e(sp, "bad sort"))?,
    };
    if s == tgt {return Ok(e)}
    let c = self.pe.coes.get(&s).and_then(|m| m.get(&tgt)).ok_or_else(||
      ElabError::new_e(sp, format!("type error: expected {}, got {}", self.print(&tgt), self.print(&s))))?;
    Ok(self.apply_coe(&Some(self.fspan(sp)), c, e))
  }

  fn coerce_to(&mut self, sp: Span, tgt: LispVal, e: LispVal, p: LispVal) -> Result<LispVal> {
    Ok(LispVal::apply_conv(self.unify(sp, &tgt, &e)?, tgt, p))
  }

  fn occurs(&mut self, mv: &LispVal, e: &LispVal) -> bool {
    match &**e {
      LispKind::Annot(_, e) => self.occurs(mv, e),
      LispKind::Ref(m) => mv.ptr_eq(e) || self.occurs(mv, &m.get()),
      LispKind::List(es) => es.iter().any(|e| self.occurs(mv, e)),
      LispKind::DottedList(es, r) =>
        es.iter().any(|e| self.occurs(mv, e)) && self.occurs(mv, r),
      _ => false,
    }
  }

  fn assign(&mut self, _sym: bool, mv: &LispVal, m: &LispRef, e: &LispVal) -> std::result::Result<(), AssignError> {
    let e = &e.as_mvar(|e2, _| e2.clone()).unwrap_or_else(|| e.clone());
    if mv.ptr_eq(e) {return Ok(())}
    if self.occurs(mv, e) {
      Err(AssignError::Cyclic)
    } else {
      if let Some(InferTarget::Bound(_)) = mv.mvar_target() {
        if !e.unwrapped(|r| match r {
          LispKind::Atom(a) => match self.lc.vars.get(&a) {
            Some((_, InferSort::Bound {..})) => true,
            _ => false
          },
          LispKind::MVar(_, is) => is.bound(),
          _ => false,
        }) {return Err(AssignError::BoundVar)}
      }
      let mut e = e.clone();
      if e.fspan().is_none() {
        if let Some(sp) = m.get().fspan() {e = e.span(sp)}
      }
      *m.get_mut() = e;
      Ok(())
    }
  }

  fn unify(&mut self, sp: Span, e1: &LispVal, e2: &LispVal) -> Result<LispVal> {
    self.unify1(e1, e2).map_err(|e| ElabError::new_e(sp, e))
  }

  fn unify1(&mut self, e1: &LispVal, e2: &LispVal) -> SResult<LispVal> {
    self.unify_core(e1, e2).map_err(|e| self.format_env().pretty(|p|
      format!("{}\n{}", p.unify_err(e1, e2).pretty(80).to_string(), e)))
  }

  fn unify_core(&mut self, e1: &LispVal, e2: &LispVal) -> SResult<LispVal> {
    // println!("{} =?= {}", self.format_env().pp(e1, 80), self.format_env().pp(e2, 80));
    // (|| {
    if e1.ptr_eq(e2) {return Ok(LispVal::undef())}
    match e1.as_mvar(|e1, m| self.assign(false, e1, m, e2)) {
      Some(Ok(())) => return Ok(LispVal::undef()),
      Some(Err(AssignError::Cyclic)) =>
        return Err("occurs-check failed, can't build infinite assignment".into()),
      r1 => match (r1, e2.as_mvar(|e2, m| self.assign(true, e2, m, e1))) {
        (_, Some(Ok(()))) => return Ok(LispVal::undef()),
        (_, Some(Err(AssignError::Cyclic))) =>
          return Err("occurs-check failed, can't build infinite assignment".into()),
        (Some(Err(AssignError::BoundVar)), None) =>
          return Err(format!("type error: expected bound var, got {}", self.print(e2))),
        (None, Some(Err(AssignError::BoundVar))) =>
          return Err(format!("type error: expected bound var, got {}", self.print(e1))),
        (None, None) => {},
        _ => unreachable!()
      }
    }
    match (e1.as_atom(), e2.as_atom()) {
      (Some(a1), Some(a2)) if a1 == a2 => Ok(LispVal::undef()),
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
            if cs[1..].iter().any(|c| c.is_def()) {
              for (c, x) in cs[1..].iter_mut().zip(u3) {
                if !c.is_def() {*c = x}
              }
              Ok(LispVal::list(cs))
            } else {
              Ok(LispVal::undef())
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
    //   let fe = self.format_env();
    //   println!("{} =?= {}\n:= {}", fe.pp(e1, 80), fe.pp(e2, 80), fe.pp(&r, 80));
    //   r
    // })
  }

  fn unfold(&mut self, sym: bool, t: TermID, u1: Uncons, e2: &LispVal) -> SResult<LispVal> {
    let tdata = &self.env.terms[t];
    let a = tdata.atom;
    let n = tdata.args.len();
    if let Some(Some(val)) = &tdata.val {
      let mut args = Vec::with_capacity(n);
      if !u1.extend_into(n, &mut args) {return Err(format!("bad term: {}", self.print(&u1)))}
      let e = Subst::new(&self.env, &val.heap, args.clone()).subst_mut(&mut self.lc, &val.head);
      let u = self.unify1(&e, e2)?;
      let u = LispVal::unfold(a, args, if u.is_def() {u} else {e});
      Ok(if sym {LispVal::sym(u)} else {u})
    } else {return Err(format!("not a definition: {}", self.print(&a)))}
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
    mut active: RState
  ) -> Result<RefineResult> {
    let fsp = self.fspan(sp);
    loop {
      // if self.check_proofs {
      //   println!("{}", self.print(&active));
      // }
      active = match active {
        RState::Goals {mut gs, mut es} => match es.next() {
          None => {self.lc.goals.extend(gs); RState::Ret(LispVal::undef())}
          Some(p) => loop {
            if let Some(g) = gs.next() {
              if let Some(tgt) = g.goal_type() {
                stack.push(RStack::Goals {g, gs, es});
                break RState::RefineProof {tgt, p}
              }
            } else {break RState::Ret(LispVal::undef())}
          }
        },
        RState::RefineProof {tgt, p} => match self.parse_refine(&fsp, &p)? {
          RefineExpr::App(sp, sp2, _, AtomID::QMARK, _) => {
            let head = LispVal::new_ref(LispVal::goal(self.fspan(sp), tgt));
            self.spans.insert_if(sp2, || ObjectKind::Proof(head.clone()));
            RState::Ret(head)
          }
          RefineExpr::App(sp, sp2, _, AtomID::UNDER, u) => {
            if u.exactly(0) {
              let head = self.new_goal(sp, tgt);
              self.spans.insert_if(sp2, || ObjectKind::Proof(head.clone()));
              RState::Ret(head)
            } else {
              let mv = self.lc.new_mvar(InferTarget::Unknown, Some(self.fspan(sp2)));
              let head = self.new_goal(sp, mv);
              self.spans.insert_if(sp2, || ObjectKind::Proof(head.clone()));
              return Ok(RefineResult::RefineExtraArgs(tgt, head, u))
            }
          }
          RefineExpr::App(sp, sp2, im, a, u) => {
            let head = LispVal::atom(a).span(self.fspan(sp2));
            if let Some((_, v, _)) = self.lc.get_proof(a) {
              self.spans.insert_if(sp2, || ObjectKind::Proof(head.clone()));
              RState::RefineArgs {sp, v: v.clone(), tgt, u, head}
            } else if let Some(DeclKey::Thm(t)) = self.data[a].decl {
              RState::RefineBis {sp, sp2, tgt, im, t, args: vec![head], u}
            } else {
              Err(ElabError::new_e(sp2, format!(
                "unknown theorem/hypothesis '{}'", self.data[a].name)))?
            }
          }
          RefineExpr::Typed(e, q) => {
            stack.push(RStack::TypedAt {sp: try_get_span(&fsp, &p), tgt, p: q});
            RState::RefineExpr {tgt: InferTarget::Unknown, e}
          }
          RefineExpr::Exact(p) => {
            let e = self.infer_type(sp, &p)?;
            RState::Ret(self.coerce_to(sp, tgt, e, p)?)
          }
          RefineExpr::Proc => RState::Proc {tgt, p},
        },
        RState::Ret(ret) => match stack.pop() {
          None => return Ok(RefineResult::Ret(ret)),
          Some(RStack::DeferGoals(mut gs)) => {
            self.lc.goals.append(&mut gs);
            RState::Ret(ret)
          }
          Some(RStack::Goals {g, gs, es}) => {
            g.as_ref_(|e| *e = ret).unwrap();
            RState::Goals {gs, es}
          }
          Some(RStack::Coerce {tgt, u}) => RState::Ret(LispVal::apply_conv(u, tgt, ret)),
          Some(RStack::CoerceTo(tgt)) => {
            let sp = try_get_span(&fsp, &ret);
            let e = self.infer_type(sp, &ret)?;
            RState::Ret(self.coerce_to(sp, tgt, e, ret)?)
          }
          Some(RStack::TypedAt {sp, tgt, p}) => {
            stack.push(RStack::Coerce {u: self.unify(sp, &tgt, &ret)?, tgt});
            RState::RefineProof {tgt: ret, p}
          }
          Some(RStack::Typed(p)) => RState::RefineProof {tgt: ret, p},
          Some(RStack::RefineApp {sp2, tgt, t, u, mut args}) => {
            args.push(ret);
            RState::RefineApp {sp2, tgt, t, u, args}
          }
          Some(RStack::RefineBis {sp, sp2, tgt, im, t, u, mut args}) => {
            args.push(ret);
            RState::RefineBis {sp, sp2, tgt, im, t, u, args}
          }
          Some(RStack::RefineHyps {sp, sp2, tgt, t, u, mut args, hyps, res}) => {
            args.push(ret);
            RState::RefineHyps {sp, sp2, tgt, t, u, args, hyps, res}
          }
        },
        RState::RefineExpr {tgt, e} => match self.parse_refine(&fsp, &e)? {
          RefineExpr::App(_, sp2, _, AtomID::UNDER, _) => {
            let head = self.lc.new_mvar(tgt, Some(self.fspan(sp2)));
            self.spans.insert_if(sp2, || ObjectKind::Expr(head.clone()));
            RState::Ret(head)
          }
          RefineExpr::App(sp, sp2, _, a, u) => {
            let empty = u.exactly(0);
            let head = LispVal::atom(a);
            self.spans.insert_if(sp2, || ObjectKind::Expr(head.clone()));
            if let Some(is) = if empty {self.lc.vars.get(&a)} else {None} {
              let (sort, bd) = match is.1 {
                InferSort::Bound {sort} => (sort, true),
                InferSort::Reg {sort, ..} => (sort, false),
                InferSort::Unknown {..} => unreachable!(),
              };
              RState::Ret(self.coerce_term(sp, tgt, sort, bd, head)?)
            } else if let Some(t) = if tgt.bound() {None} else {self.term(a)} {
              RState::RefineApp {sp2, tgt, t, u, args: vec![head]}
            } else if let Some(s) = tgt.sort().filter(|_| empty) {
              let sort = self.data[s].sort.ok_or_else(|| ElabError::new_e(sp, "bad sort"))?;
              self.lc.vars.insert(a, (true, InferSort::Bound {sort}));
              RState::Ret(head)
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
          RefineExpr::Proc => RState::Ret(e),
        },
        RState::RefineApp {sp2, tgt: ret, t, mut u, mut args} => 'l: loop { // labeled block, not a loop
          let tdata = &self.env.terms[t];
          for (_, ty) in &tdata.args[args.len() - 1..] {
            let tgt = self.type_target(ty);
            match u.next() {
              Some(e) => {
                stack.push(RStack::RefineApp {sp2, tgt: ret, t, u, args});
                break 'l RState::RefineExpr {tgt, e}
              }
              None => args.push(self.lc.new_mvar(tgt, Some(self.fspan(sp2))))
            }
          }
          let s = tdata.ret.0;
          break RState::Ret(self.coerce_term(sp, ret, s, false, LispVal::list(args))?)
        },
        RState::RefineArgs {sp, v, tgt, head, u} if u.exactly(0) =>
          RState::Ret(self.coerce_to(sp, tgt, v, head)?),
        RState::RefineArgs {tgt, head, u, ..} =>
          return Ok(RefineResult::RefineExtraArgs(tgt, head, u)),
        RState::RefineBis {sp, sp2, tgt, im, t, mut u, mut args} => 'l2: loop { // labeled block, not a loop
          let tdata = &self.env.thms[t];
          for (_, ty) in &tdata.args[args.len() - 1..] {
            let tgt1 = self.type_target(ty);
            let explicit = match im {
              InferMode::Regular => false,
              InferMode::Explicit => true,
              InferMode::BoundOnly => ty.bound(),
            };
            if let Some(e) = if explicit {u.next()} else {None} {
              stack.push(RStack::RefineBis {sp, sp2, tgt, im, t, u, args});
              break 'l2 RState::RefineExpr {tgt: tgt1, e}
            } else {
              args.push(self.lc.new_mvar(tgt1, Some(self.fspan(sp2))))
            }
          }
          let mut subst = Subst::new(&self.env, &tdata.heap, Vec::from(&args[1..]));
          let hyps = tdata.hyps.iter().map(|(_, h)| subst.subst(h)).collect::<Vec<_>>();
          let ret = subst.subst(&tdata.ret);
          break RState::RefineHyps {
            res: if u.len() <= hyps.len() {
              RefineHypsResult::Ok(self.unify(sp, &tgt, &ret)?)
            } else {
              RefineHypsResult::Extra
            },
            sp, sp2, tgt, t, u, args, hyps: hyps.into_iter()
          }
        },
        RState::RefineHyps {sp, sp2, tgt, t, mut u, mut args, mut hyps, res} => 'l3: loop { // labeled block, not a loop
          while let Some(h) = hyps.next() {
            if let Some(p) = u.next() {
              stack.push(RStack::RefineHyps {sp, sp2, tgt, t, u, args, hyps, res});
              break 'l3 RState::RefineProof {tgt: h, p}
            } else {
              args.push(self.new_goal(sp, h))
            }
          }
          let head = LispVal::list(args);
          self.spans.insert_if(sp2, || ObjectKind::Proof(head.clone()));
          break match res {
            RefineHypsResult::Ok(c) => RState::Ret(LispVal::apply_conv(c, tgt, head)),
            RefineHypsResult::Extra =>
              return Ok(RefineResult::RefineExtraArgs(tgt, head, u)),
          }
        },
        RState::Proc {tgt, p} => return Ok(RefineResult::Proc(tgt, p)),
      }
    }
  }
}
