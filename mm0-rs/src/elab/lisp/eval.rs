use std::ops::{Deref, DerefMut};
use std::mem;
use std::time::{Instant, Duration};
use std::sync::atomic::Ordering;
use std::collections::HashMap;
use num::{BigInt, ToPrimitive};
use crate::util::*;
use crate::parser::ast::SExpr;
use super::super::{Result, Elaborator,
  AtomID, Environment, AtomData, DeclKey,
  ElabError, ElabErrorKind, ErrorLevel, BoxError,
  tactic::{RStack, RState, RefineResult}};
use super::*;
use super::parser::{IR, Branch, Pattern};
use super::super::local_context::{InferSort, AwaitingProof, try_get_span};
use super::print::{FormatEnv, EnvDisplay};

#[derive(Debug)]
enum Stack<'a> {
  List(Span, Vec<LispVal>, std::slice::Iter<'a, IR>),
  DottedList(Vec<LispVal>, std::slice::Iter<'a, IR>, &'a IR),
  DottedList2(Vec<LispVal>),
  App(Span, Span, &'a [IR]),
  App2(Span, Span, LispVal, Vec<LispVal>, std::slice::Iter<'a, IR>),
  AppHead(Span, Span, LispVal),
  If(&'a IR, &'a IR),
  Def(Option<&'a Option<(Span, AtomID)>>),
  Eval(std::slice::Iter<'a, IR>),
  Match(Span, std::slice::Iter<'a, Branch>),
  TestPattern(Span, LispVal, std::slice::Iter<'a, Branch>,
    &'a Branch, Vec<PatternStack<'a>>, Box<[LispVal]>),
  Drop(usize),
  Ret(FileSpan, ProcPos, Vec<LispVal>, Arc<IR>),
  MatchCont(Span, LispVal, std::slice::Iter<'a, Branch>, Arc<AtomicBool>),
  MapProc(Span, Span, LispVal, Box<[Uncons]>, Vec<LispVal>),
  AddThmProc(FileSpan, Span, AwaitingProof),
  Refines(Span, Option<Span>, std::slice::Iter<'a, IR>),
  Refine {sp: Span, stack: Vec<RStack>, gv: Arc<Mutex<Vec<LispVal>>>},
  Focus(Vec<LispVal>),
  Have(Span, AtomID),
}

impl<'a> EnvDisplay for Stack<'a> {
  fn fmt(&self, fe: FormatEnv, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      Stack::List(_, es, irs) => write!(f, "(list {}\n  _ {})",
        fe.to(es), fe.to(irs.as_slice())),
      &Stack::DottedList(ref es, ref irs, ir) => write!(f, "(cons {}\n  _ {} {})",
        fe.to(es), fe.to(irs.as_slice()), fe.to(ir)),
      Stack::DottedList2(es) => write!(f, "(cons {}\n  _)", fe.to(es)),
      &Stack::App(_, _, irs) => write!(f, "(_ {})", fe.to(irs)),
      Stack::App2(_, _, e, es, irs) => write!(f, "({} {}\n  _ {})",
        fe.to(e), fe.to(es), fe.to(irs.as_slice())),
      Stack::AppHead(_, _, e) => write!(f, "(_ {})", fe.to(e)),
      &Stack::If(e1, e2) => write!(f, "(if _ {} {})", fe.to(e1), fe.to(e2)),
      &Stack::Def(Some(&Some((_, a)))) => write!(f, "(def {} _)", fe.to(&a)),
      Stack::Def(_) => write!(f, "(def _ _)"),
      Stack::Eval(es) => write!(f, "(begin\n  _ {})", fe.to(es.as_slice())),
      Stack::Match(_, bs) => write!(f, "(match _\n  {})", fe.to(bs.as_slice())),
      &Stack::TestPattern(_, ref e, ref bs, br, _, _) => write!(f,
        "(match {}\n  {}\n  {})\n  ->(? _)",
        fe.to(e), fe.to(br), fe.to(bs.as_slice())),
      &Stack::Drop(n) => write!(f, "drop {}", n),
      Stack::Ret(_, pos, _, _) => match pos {
        &ProcPos::Named(_, a) => write!(f, "ret {}", fe.to(&a)),
        ProcPos::Unnamed(_) => write!(f, "ret"),
      },
      Stack::MatchCont(_, e, bs, _) => write!(f, "(=> match {}\n  {})",
        fe.to(e), fe.to(bs.as_slice())),
      Stack::MapProc(_, _, e, us, es) => write!(f, "(map {}\n  {})\n  ->{} _",
        fe.to(e), fe.to(&**us), fe.to(es)),
      Stack::AddThmProc(_, _, ap) => write!(f, "(add-thm {} _)", fe.to(&ap.t.atom)),
      Stack::Refines(_, _, irs) => write!(f, "(refine _ {})", fe.to(irs.as_slice())),
      Stack::Refine {..} => write!(f, "(refine _)"),
      Stack::Focus(es) => write!(f, "(focus _)\n  ->{}", fe.to(es)),
      &Stack::Have(_, a) => write!(f, "(have {} _)", fe.to(&a)),
    }
  }
}

#[derive(Debug)]
enum State<'a> {
  Eval(&'a IR),
  Refines(Span, std::slice::Iter<'a, IR>),
  Ret(LispVal),
  List(Span, Vec<LispVal>, std::slice::Iter<'a, IR>),
  DottedList(Vec<LispVal>, std::slice::Iter<'a, IR>, &'a IR),
  App(Span, Span, LispVal, Vec<LispVal>, std::slice::Iter<'a, IR>),
  Match(Span, LispVal, std::slice::Iter<'a, Branch>),
  Pattern(Span, LispVal, std::slice::Iter<'a, Branch>,
    &'a Branch, Vec<PatternStack<'a>>, Box<[LispVal]>, PatternState<'a>),
  MapProc(Span, Span, LispVal, Box<[Uncons]>, Vec<LispVal>),
  Refine {sp: Span, stack: Vec<RStack>, state: RState, gv: Arc<Mutex<Vec<LispVal>>>},
}

impl<'a> EnvDisplay for State<'a> {
  fn fmt(&self, fe: FormatEnv, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      &State::Eval(ir) => write!(f, "-> {}", fe.to(ir)),
      State::Refines(_, irs) => write!(f, "(refine {})", fe.to(irs.as_slice())),
      State::Ret(e) => write!(f, "<- {}", fe.to(e)),
      State::List(_, es, irs) => write!(f, "(list {}\n  {})",
        fe.to(es), fe.to(irs.as_slice())),
      &State::DottedList(ref es, ref irs, ir) => write!(f, "(cons {}\n  {} {})",
        fe.to(es), fe.to(irs.as_slice()), fe.to(ir)),
      State::App(_, _, e, es, irs) => write!(f, "({} {}\n  {})",
        fe.to(e), fe.to(es), fe.to(irs.as_slice())),
      State::Match(_, e, bs) => write!(f, "(match {}\n  {})",
        fe.to(e), fe.to(bs.as_slice())),
      &State::Pattern(_, ref e, ref bs, br, _, _, ref st) => write!(f,
        "(match {}\n  {}\n  {})\n  ->{}",
        fe.to(e), fe.to(br), fe.to(bs.as_slice()), fe.to(st)),
      State::MapProc(_, _, e, us, es) => write!(f, "(map {}\n  {})\n  ->{}",
        fe.to(e), fe.to(&**us), fe.to(es)),
      State::Refine {state, ..} => state.fmt(fe, f),
    }
  }
}

impl LispKind {
  fn as_ref_mut<T>(&self, f: impl FnOnce(&mut LispVal) -> T) -> Option<T> {
    match self {
      LispKind::Ref(m) => Some(f(&mut m.get_mut())),
      LispKind::Annot(_, e) => e.as_ref_mut(f),
      _ => None
    }
  }

  fn make_map_mut<T>(&self, f: impl FnOnce(&mut HashMap<AtomID, LispVal>) -> T) -> (Option<T>, Option<LispVal>) {
    match self {
      LispKind::AtomMap(m) => {
        let mut m = m.clone();
        (Some(f(&mut m)), Some(LispVal::new(LispKind::AtomMap(m))))
      }
      LispKind::Annot(sp, e) => match e.make_map_mut(f) {
        (r, None) => (r, None),
        (r, Some(e)) => (r, Some(LispVal::new(LispKind::Annot(sp.clone(), e)))),
      },
      LispKind::Ref(m) => (m.get_mut().as_map_mut(f), None),
      _ => (None, None)
    }
  }
}
impl LispVal {
  fn as_map_mut<T>(&mut self, f: impl FnOnce(&mut HashMap<AtomID, LispVal>) -> T) -> Option<T> {
    match self.get_mut() {
      None => {
        let (r, new) = self.make_map_mut(f);
        if let Some(e) = new {*self = e}
        r
      }
      Some(LispKind::AtomMap(m)) => Some(f(m)),
      Some(LispKind::Annot(_, e)) => Self::as_map_mut(e, f),
      Some(LispKind::Ref(m)) => Self::as_map_mut(&mut m.get_mut(), f),
      _ => None
    }
  }
}

#[derive(Debug)]
enum Dot<'a> { List(Option<usize>), DottedList(&'a Pattern) }
#[derive(Debug)]
enum PatternStack<'a> {
  Bool(&'a Pattern, bool),
  List(Uncons, std::slice::Iter<'a, Pattern>, Dot<'a>),
  Binary(bool, bool, LispVal, std::slice::Iter<'a, Pattern>),
}

#[derive(Debug)]
enum PatternState<'a> {
  Eval(&'a Pattern, LispVal),
  Ret(bool),
  List(Uncons, std::slice::Iter<'a, Pattern>, Dot<'a>),
  Binary(bool, bool, LispVal, std::slice::Iter<'a, Pattern>),
}

impl<'a> EnvDisplay for PatternState<'a> {
  fn fmt(&self, fe: FormatEnv, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      &PatternState::Eval(p, ref e) => write!(f, "{} := {}", fe.to(p), fe.to(e)),
      &PatternState::Ret(e) => write!(f, "<- {}", e),
      PatternState::List(u, ps, Dot::List(None)) => write!(f, "({}) := {}",
        fe.to(ps.as_slice()), fe.to(u)),
      PatternState::List(u, ps, Dot::List(Some(0))) => write!(f, "({} ...) := {}",
        fe.to(ps.as_slice()), fe.to(u)),
      PatternState::List(u, ps, Dot::List(Some(n))) => write!(f, "({} __ {}) := {}",
        fe.to(ps.as_slice()), n, fe.to(u)),
      &PatternState::List(ref u, ref ps, Dot::DottedList(r)) => write!(f, "({} . {}) := {}",
        fe.to(ps.as_slice()), fe.to(r), fe.to(u)),
      PatternState::Binary(false, false, e, ps) => write!(f, "(and {}) := {}", fe.to(ps.as_slice()), fe.to(e)),
      PatternState::Binary(true, true, e, ps) => write!(f, "(or {}) := {}", fe.to(ps.as_slice()), fe.to(e)),
      PatternState::Binary(true, false, e, ps) => write!(f, "(not {}) := {}", fe.to(ps.as_slice()), fe.to(e)),
      PatternState::Binary(false, true, e, ps) => write!(f, "(nor {}) := {}", fe.to(ps.as_slice()), fe.to(e)),
    }
  }
}

struct TestPending<'a>(Span, LispVal, &'a IR);

pub type SResult<T> = std::result::Result<T, String>;

impl Elaborator {
  fn pattern_match<'b>(&mut self, stack: &mut Vec<PatternStack<'b>>, ctx: &mut [LispVal],
      mut active: PatternState<'b>) -> std::result::Result<bool, TestPending<'b>> {
    loop {
      // crate::server::log(format!("{}\n", self.print(&active)));
      active = match active {
        PatternState::Eval(p, e) => match p {
          Pattern::Skip => PatternState::Ret(true),
          &Pattern::Atom(i) => {ctx[i] = e; PatternState::Ret(true)}
          &Pattern::QuoteAtom(a) => PatternState::Ret(e.unwrapped(|e|
            match e {&LispKind::Atom(a2) => a == a2, _ => false})),
          Pattern::String(s) => PatternState::Ret(e.unwrapped(|e|
            match e {LispKind::String(s2) => s == s2, _ => false})),
          &Pattern::Bool(b) => PatternState::Ret(e.unwrapped(|e|
            match e {&LispKind::Bool(b2) => b == b2, _ => false})),
          Pattern::Number(i) => PatternState::Ret(e.unwrapped(|e|
            match e {LispKind::Number(i2) => i == i2, _ => false})),
          Pattern::MVar(p) => e.unwrapped(|e| match e {
            LispKind::MVar(_, is) => match (p, is) {
              (None, InferTarget::Unknown) => PatternState::Ret(true),
              (None, InferTarget::Provable) => PatternState::Ret(true),
              (None, _) => PatternState::Ret(false),
              (Some(_), InferTarget::Unknown) => PatternState::Ret(false),
              (Some(_), InferTarget::Provable) => PatternState::Ret(false),
              (Some(p), &InferTarget::Bound(s)) => {
                stack.push(PatternStack::Bool(&p.1, true));
                PatternState::Eval(&p.0, LispVal::atom(s))
              }
              (Some(p), &InferTarget::Reg(s)) => {
                stack.push(PatternStack::Bool(&p.1, false));
                PatternState::Eval(&p.0, LispVal::atom(s))
              }
            }
            _ => PatternState::Ret(false),
          }),
          Pattern::Goal(p) => e.unwrapped(|e| match e {
            LispKind::Goal(e) => PatternState::Eval(p, e.clone()),
             _ => PatternState::Ret(false)
          }),
          &Pattern::QExprAtom(a) => PatternState::Ret(e.unwrapped(|e| match e {
            &LispKind::Atom(a2) => a == a2,
            LispKind::List(es) if es.len() == 1 => es[0].unwrapped(|e|
              match e {&LispKind::Atom(a2) => a == a2, _ => false}),
            _ => false
          })),
          Pattern::DottedList(ps, r) => PatternState::List(Uncons::from(e), ps.iter(), Dot::DottedList(r)),
          &Pattern::List(ref ps, n) => PatternState::List(Uncons::from(e), ps.iter(), Dot::List(n)),
          Pattern::And(ps) => PatternState::Binary(false, false, e, ps.iter()),
          Pattern::Or(ps) => PatternState::Binary(true, true, e, ps.iter()),
          Pattern::Not(ps) => PatternState::Binary(true, false, e, ps.iter()),
          &Pattern::Test(sp, ref ir, ref ps) => {
            stack.push(PatternStack::Binary(false, false, e.clone(), ps.iter()));
            return Err(TestPending(sp, e, ir))
          },
        },
        PatternState::Ret(b) => match stack.pop() {
          None => return Ok(b),
          Some(PatternStack::Bool(_, _)) if !b => PatternState::Ret(b),
          Some(PatternStack::Bool(p, e)) =>
            PatternState::Eval(p, LispVal::bool(e)),
          Some(PatternStack::List(u, it, r)) =>
            if b {PatternState::List(u, it, r)}
            else {PatternState::Ret(false)},
          Some(PatternStack::Binary(or, out, u, it)) =>
            if b^or {PatternState::Binary(or, out, u, it)}
            else {PatternState::Ret(out)},
        }
        PatternState::List(mut u, mut it, dot) => match it.next() {
          None => match dot {
            Dot::List(None) => PatternState::Ret(u.exactly(0)),
            Dot::List(Some(n)) => PatternState::Ret(u.at_least(n)),
            Dot::DottedList(p) => PatternState::Eval(p, u.as_lisp()),
          }
          Some(p) => match u.next() {
            None => PatternState::Ret(false),
            Some(l) => {
              stack.push(PatternStack::List(u, it, dot));
              PatternState::Eval(p, l)
            }
          }
        },
        PatternState::Binary(or, out, e, mut it) => match it.next() {
          None => PatternState::Ret(!out),
          Some(p) => {
            stack.push(PatternStack::Binary(or, out, e.clone(), it));
            PatternState::Eval(p, e)
          }
        }
      }
    }
  }
}

impl Elaborator {
  pub fn print_lisp(&mut self, sp: Span, e: &LispVal) {
    self.report(ElabError::info(sp, format!("{}", self.print(e))))
  }

  pub fn eval_lisp<'b>(&'b mut self, e: &SExpr) -> Result<LispVal> {
    let sp = e.span;
    let ir = self.parse_lisp(e)?;
    self.evaluate(sp, &ir)
  }

  pub fn eval_qexpr<'b>(&'b mut self, e: QExpr) -> Result<LispVal> {
    let sp = e.span;
    let ir = self.parse_qexpr(e)?;
    self.evaluate(sp, &ir)
  }

  pub fn elab_lisp<'b>(&'b mut self, e: &SExpr) -> Result<LispVal> {
    let sp = e.span;
    let ir = self.parse_lisp(e)?;
    Evaluator::new(self, sp).run(State::Refines(sp, [ir].iter()))
  }

  pub fn evaluate<'b>(&'b mut self, sp: Span, ir: &'b IR) -> Result<LispVal> {
    Evaluator::new(self, sp).run(State::Eval(ir))
  }

  pub fn call_func(&mut self, sp: Span, f: LispVal, es: Vec<LispVal>) -> Result<LispVal> {
    Evaluator::new(self, sp).run(State::App(sp, sp, f, es, [].iter()))
  }

  pub fn _call_overridable(&mut self, sp: Span, p: BuiltinProc, es: Vec<LispVal>) -> Result<LispVal> {
    let a = self.get_atom(p.to_str());
    let val = match &self.data[a].lisp {
      Some((_, e)) => e.clone(),
      None => LispVal::proc(Proc::Builtin(p))
    };
    self.call_func(sp, val, es)
  }

  fn as_string(&self, e: &LispVal) -> SResult<ArcString> {
    e.unwrapped(|e| if let LispKind::String(s) = e {Ok(s.clone())} else {
      Err(format!("expected a string, got {}", self.print(e)))
    })
  }

  fn as_atom_string(&self, e: &LispVal) -> SResult<ArcString> {
    e.unwrapped(|e| match e {
      LispKind::String(s) => Ok(s.clone()),
      &LispKind::Atom(a) => Ok(self.data[a].name.clone()),
      _ => Err(format!("expected an atom, got {}", self.print(e)))
    })
  }

  fn as_string_atom(&mut self, e: &LispVal) -> SResult<AtomID> {
    e.unwrapped(|e| match e {
      LispKind::String(s) => Ok(self.get_atom(s)),
      &LispKind::Atom(a) => Ok(a),
      _ => Err(format!("expected an atom, got {}", self.print(e)))
    })
  }

  fn as_int(&self, e: &LispVal) -> SResult<BigInt> {
    e.unwrapped(|e| if let LispKind::Number(n) = e {Ok(n.clone())} else {
      Err(format!("expected a integer, got {}", self.print(e)))
    })
  }

  fn as_ref<T>(&self, e: &LispKind, f: impl FnOnce(&mut LispVal) -> SResult<T>) -> SResult<T> {
    e.as_ref_(f).unwrap_or_else(|| Err(format!("not a ref-cell: {}", self.print(e))))
  }

  fn as_map<T>(&self, e: &LispKind, f: impl FnOnce(&HashMap<AtomID, LispVal>) -> SResult<T>) -> SResult<T> {
    e.unwrapped(|e| match e {
      LispKind::AtomMap(m) => f(m),
      _ => Err(format!("not an atom map: {}", self.print(e)))
    })
  }

  fn to_string(&self, e: &LispKind) -> ArcString {
    match e {
      LispKind::Ref(m) => self.to_string(&m.get()),
      LispKind::Annot(_, e) => self.to_string(e),
      LispKind::String(s) => s.clone(),
      &LispKind::Atom(a) => self.data[a].name.clone(),
      LispKind::Number(n) => ArcString::new(n.to_string()),
      _ => ArcString::new(format!("{}", self.print(e)))
    }
  }

  fn int_bool_binop(&self, mut f: impl FnMut(&BigInt, &BigInt) -> bool, args: &[LispVal]) -> SResult<bool> {
    let mut it = args.iter();
    let mut last = self.as_int(it.next().unwrap())?;
    while let Some(v) = it.next() {
      let new = self.as_int(v)?;
      if !f(&last, &new) {return Ok(false)}
      last = new;
    }
    Ok(true)
  }

  fn head(&self, e: &LispKind) -> SResult<LispVal> {
    e.unwrapped(|e| match e {
      LispKind::List(es) if es.is_empty() => Err("evaluating 'hd ()'".into()),
      LispKind::List(es) => Ok(es[0].clone()),
      LispKind::DottedList(es, r) if es.is_empty() => self.head(r),
      LispKind::DottedList(es, _) => Ok(es[0].clone()),
      _ => Err(format!("expected a list, got {}", self.print(e)))
    })
  }

  fn tail(&self, e: &LispKind) -> SResult<LispVal> {
    fn exponential_backoff(es: &[LispVal], i: usize, r: impl FnOnce(Vec<LispVal>) -> LispVal) -> LispVal {
      let j = 2 * i;
      if j >= es.len() { r(es[i..].into()) }
      else { LispVal::dotted_list(es[i..j].into(), exponential_backoff(es, j, r)) }
    }
    e.unwrapped(|e| match e {
      LispKind::List(es) if es.is_empty() => Err("evaluating 'tl ()'".into()),
      LispKind::List(es) =>
        Ok(exponential_backoff(es, 1, LispVal::list)),
      LispKind::DottedList(es, r) if es.is_empty() => self.tail(r),
      LispKind::DottedList(es, r) =>
        Ok(exponential_backoff(es, 1, |v| LispVal::dotted_list(v, r.clone()))),
      _ => Err(format!("expected a list, got {}", self.print(e)))
    })
  }

  fn get_decl(&self, fsp: FileSpan, x: AtomID) -> LispVal {
    use super::super::environment::{Type, ExprNode, ProofNode};
    fn deps(bvs: &[LispVal], mut v: Vec<LispVal>, xs: u64) -> Vec<LispVal> {
      v.push(if xs == 0 {LispVal::nil()} else {
        let mut i = 1;
        LispVal::list(bvs.iter().filter(|_| (xs & i != 0, i *= 2).0).cloned().collect())
      });
      v
    }
    fn binders(env: &Environment, bis: &[(Option<AtomID>, Type)],
        heap: &mut Vec<LispVal>, bvs: &mut Vec<LispVal>) -> LispVal {
      LispVal::list(bis.iter().map(|(a, t)| LispVal::list({
        let a = LispVal::atom(a.unwrap_or(AtomID::UNDER));
        heap.push(a.clone());
        match t {
          &Type::Bound(s) => {bvs.push(a.clone()); vec![a, LispVal::atom(env.sorts[s].atom)]}
          &Type::Reg(s, xs) => deps(&bvs, vec![a, LispVal::atom(env.sorts[s].atom)], xs)
        }
      })).collect())
    }
    fn vis(mods: Modifiers) -> LispVal {
      match mods {
        Modifiers::PUB => LispVal::atom(AtomID::PUB),
        Modifiers::ABSTRACT => LispVal::atom(AtomID::ABSTRACT),
        Modifiers::LOCAL => LispVal::atom(AtomID::LOCAL),
        Modifiers::NONE => LispVal::nil(),
        _ => unreachable!()
      }
    }
    fn expr_node(env: &Environment, heap: &Vec<LispVal>,
        ds: &mut Option<&mut Vec<LispVal>>, e: &ExprNode) -> LispVal {
      match e {
        &ExprNode::Ref(n) => heap[n].clone(),
        &ExprNode::Dummy(a, s) => {
          let a = LispVal::atom(a);
          ds.as_mut().unwrap().push(
            LispVal::list(vec![a.clone(), LispVal::atom(env.sorts[s].atom)]));
          a
        }
        &ExprNode::App(t, ref es) => {
          let mut args = vec![LispVal::atom(env.terms[t].atom)];
          args.extend(es.iter().map(|e| expr_node(env, heap, ds, e)));
          LispVal::list(args)
        }
      }
    }
    fn proof_node(env: &Environment, hyps: &[(Option<AtomID>, ExprNode)],
        heap: &Vec<LispVal>, ds: &mut Vec<LispVal>, p: &ProofNode) -> LispVal {
      match p {
        &ProofNode::Ref(n) => heap[n].clone(),
        &ProofNode::Dummy(a, s) => {
          let a = LispVal::atom(a);
          ds.push(LispVal::list(vec![a.clone(), LispVal::atom(env.sorts[s].atom)]));
          a
        }
        &ProofNode::Term {term, args: ref es} => {
          let mut args = vec![LispVal::atom(env.terms[term].atom)];
          args.extend(es.iter().map(|e| proof_node(env, hyps, heap, ds, e)));
          LispVal::list(args)
        }
        &ProofNode::Hyp(h, _) => LispVal::atom(hyps[h].0.unwrap_or(AtomID::UNDER)),
        &ProofNode::Thm {thm, args: ref es} => {
          let mut args = vec![LispVal::atom(env.thms[thm].atom)];
          args.extend(es.iter().map(|e| proof_node(env, hyps, heap, ds, e)));
          LispVal::list(args)
        }
        ProofNode::Conv(es) => {
          let (t, c, p) = &**es;
          LispVal::list(vec![LispVal::atom(AtomID::CONV),
            proof_node(env, hyps, heap, ds, t),
            proof_node(env, hyps, heap, ds, c),
            proof_node(env, hyps, heap, ds, p),
          ])
        }
        ProofNode::Sym(p) =>
          LispVal::list(vec![LispVal::atom(AtomID::SYM), proof_node(env, hyps, heap, ds, &**p)]),
        &ProofNode::Unfold {term, ref args, ref res} =>
          LispVal::list(vec![LispVal::atom(AtomID::UNFOLD),
            LispVal::atom(env.terms[term].atom),
            LispVal::list(args.iter().map(|e| proof_node(env, hyps, heap, ds, e)).collect()),
            proof_node(env, hyps, heap, ds, &**res)]),
      }
    }

    match self.data[x].decl {
      None => LispVal::undef(),
      Some(DeclKey::Term(t)) => {
        let tdata = &self.env.terms[t];
        let mut bvs = Vec::new();
        let mut heap = Vec::new();
        let mut args = vec![
          LispVal::atom(if tdata.val.is_some() {AtomID::TERM} else {AtomID::DEF}),
          LispVal::atom(x),
          binders(self, &tdata.args, &mut heap, &mut bvs),
          LispVal::list(deps(&bvs,
            vec![LispVal::atom(self.sorts[tdata.ret.0].atom)], tdata.ret.1))
        ];
        if let Some(Some(v)) = &tdata.val {
          args.push(vis(tdata.vis));
          let mut ds = Vec::new();
          for e in &v.heap[heap.len()..] {
            let e = expr_node(self, &heap, &mut Some(&mut ds), e);
            heap.push(e)
          }
          let ret = expr_node(self, &heap, &mut Some(&mut ds), &v.head);
          args.push(LispVal::list(ds));
          args.push(ret);
        }
        LispVal::list(args)
      }
      Some(DeclKey::Thm(t)) => {
        let tdata = &self.thms[t];
        let mut bvs = Vec::new();
        let mut heap = Vec::new();
        let mut args = vec![
          LispVal::atom(if tdata.proof.is_some() {AtomID::THM} else {AtomID::AXIOM}),
          LispVal::atom(x),
          binders(self, &tdata.args, &mut heap, &mut bvs),
          {
            for e in &tdata.heap[heap.len()..] {
              let e = expr_node(self, &heap, &mut None, e);
              heap.push(e)
            }
            LispVal::list(tdata.hyps.iter().map(|(a, e)| LispVal::list(vec![
              LispVal::atom(a.unwrap_or(AtomID::UNDER)),
              expr_node(self, &heap, &mut None, e)
            ])).collect())
          },
          expr_node(self, &heap, &mut None, &tdata.ret)
        ];
        if let Some(v) = &tdata.proof {
          args.push(vis(tdata.vis));
          let val = match v {
            None => LispVal::atom(AtomID::SORRY),
            Some(pr) => {
              let mut ds = Vec::new();
              for e in &pr.heap[heap.len()..] {
                let e = proof_node(self, &tdata.hyps, &heap, &mut ds, e);
                heap.push(e)
              }
              let ret = proof_node(self, &tdata.hyps, &heap, &mut ds, &pr.head);
              LispVal::list(vec![LispVal::list(ds), ret])
            }
          };
          args.push(LispVal::proc(Proc::Lambda {
            pos: ProcPos::Unnamed(fsp),
            env: vec![],
            spec: ProcSpec::AtLeast(0),
            code: Arc::new(IR::Const(val))
          }));
        }
        LispVal::list(args)
      }
    }
  }
}

struct Evaluator<'a> {
  elab: &'a mut Elaborator,
  ctx: Vec<LispVal>,
  file: FileRef,
  orig_span: Span,
  stack: Vec<Stack<'a>>,
}
impl<'a> Deref for Evaluator<'a> {
  type Target = Elaborator;
  fn deref(&self) -> &Elaborator { self.elab }
}
impl<'a> DerefMut for Evaluator<'a> {
  fn deref_mut(&mut self) -> &mut Elaborator { self.elab }
}

impl<'a> Evaluator<'a> {
  fn new(elab: &'a mut Elaborator, orig_span: Span) -> Evaluator<'a> {
    let file = elab.path.clone();
    Evaluator {elab, ctx: vec![], file, orig_span, stack: vec![]}
  }

  fn fspan_base(&mut self, sp: Span) -> FileSpan {
    for s in &self.stack {
      if let Stack::Ret(fsp, _, _, _) = s {return fsp.clone()}
    }
    self.fspan(sp)
  }

  fn make_stack_err(&mut self, sp: Option<Span>, level: ErrorLevel,
      base: BoxError, err: impl Into<BoxError>) -> ElabError {
    let mut old = sp.map(|sp| (self.fspan(sp), base));
    let mut info = vec![];
    for s in self.stack.iter().rev() {
      if let Stack::Ret(fsp, pos, _, _) = s {
        let x = match pos {
          ProcPos::Named(_, a) => format!("({})", self.data[*a].name).into(),
          ProcPos::Unnamed(_) => "[fn]".into(),
        };
        if let Some((sp, base)) = old.take() {
          info.push((sp, base));
        }
        old = Some((fsp.clone(), x))
      }
    }
    ElabError {
      pos: old.map_or(self.orig_span, |(sp, _)| sp.span),
      level,
      kind: ElabErrorKind::Boxed(err.into(), Some(info))
    }
  }

  fn info(&mut self, sp: Span, base: &str, msg: impl Into<BoxError>) {
    let msg = self.make_stack_err(Some(sp), ErrorLevel::Info, base.into(), msg);
    self.report(msg)
  }

  fn err(&mut self, sp: Option<Span>, err: impl Into<BoxError>) -> ElabError {
    self.make_stack_err(sp, ErrorLevel::Error, "error occurred here".into(), err)
  }

  fn add_thm(&mut self, fsp: FileSpan, sp1: Span, args: &[LispVal]) -> Result<State<'a>> {
    Ok(if let Some((ap, proc)) = self.elab.add_thm(fsp.clone(), sp1, args)? {
      self.stack.push(Stack::AddThmProc(fsp, sp1, ap));
      let sp = try_get_span(&self.fspan(sp1), &proc);
      State::App(sp, sp, proc, vec![], [].iter())
    } else {State::Ret(LispVal::undef())})
  }
}

macro_rules! make_builtins {
  ($self:ident, $sp1:ident, $sp2:ident, $args:ident,
      $($e:ident: $ty:ident($n:expr) => $res:expr,)*) => {
    impl BuiltinProc {
      pub fn spec(self) -> ProcSpec {
        match self {
          $(BuiltinProc::$e => ProcSpec::$ty($n)),*
        }
      }
    }

    impl<'a> Evaluator<'a> {
      fn evaluate_builtin(&mut $self, $sp1: Span, $sp2: Span, f: BuiltinProc, mut $args: Vec<LispVal>) -> Result<State<'a>> {
        macro_rules! print {($sp:expr, $x:expr) => {{
          let msg = $x; $self.info($sp, f.to_str(), msg)
        }}}
        macro_rules! try1 {($x:expr) => {{
          match $x {
            Ok(e) => e,
            Err(s) => return Err($self.make_stack_err(
              Some($sp1), ErrorLevel::Error, format!("({})", f).into(), s))
          }
        }}}

        Ok(State::Ret(match f { $(BuiltinProc::$e => $res),* }))
      }
    }
  }
}

make_builtins! { self, sp1, sp2, args,
  Display: Exact(1) => {print!(sp1, &*try1!(self.as_string(&args[0]))); LispVal::undef()},
  Error: Exact(1) => try1!(Err(&*try1!(self.as_string(&args[0])))),
  Print: Exact(1) => {print!(sp1, format!("{}", self.print(&args[0]))); LispVal::undef()},
  Begin: AtLeast(0) => args.last().cloned().unwrap_or_else(LispVal::undef),
  Apply: AtLeast(2) => {
    let proc = args.remove(0);
    let sp = proc.fspan().map_or(sp2, |fsp| fsp.span);
    fn gather(args: &mut Vec<LispVal>, e: &LispKind) -> bool {
      e.unwrapped(|e| match e {
        LispKind::List(es) => {args.extend_from_slice(&es); true}
        LispKind::DottedList(es, r) => {args.extend_from_slice(&es); gather(args, r)}
        _ => false
      })
    }
    let tail = args.pop().unwrap();
    if !gather(&mut args, &tail) {
      try1!(Err(format!("apply: last argument is not a list: {}", self.print(&tail))))
    }
    return Ok(State::App(sp1, sp, proc, args, [].iter()))
  },
  Add: AtLeast(0) => {
    let mut n: BigInt = 0.into();
    for e in args { n += try1!(self.as_int(&e)) }
    LispVal::number(n)
  },
  Mul: AtLeast(0) => {
    let mut n: BigInt = 1.into();
    for e in args { n *= try1!(self.as_int(&e)) }
    LispVal::number(n)
  },
  Max: AtLeast(1) => {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap())).clone();
    for e in it { n = n.max(try1!(self.as_int(&e)).clone()) }
    LispVal::number(n)
  },
  Min: AtLeast(1) => {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap())).clone();
    for e in it { n = n.min(try1!(self.as_int(&e)).clone()) }
    LispVal::number(n)
  },
  Sub: AtLeast(1) => if args.len() == 1 {
    LispVal::number(-try1!(self.as_int(&args[0])).clone())
  } else {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap())).clone();
    for e in it { n -= try1!(self.as_int(&e)) }
    LispVal::number(n)
  },
  Div: AtLeast(1) => {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap())).clone();
    for e in it { n /= try1!(self.as_int(&e)) }
    LispVal::number(n)
  },
  Mod: AtLeast(1) => {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap())).clone();
    for e in it { n %= try1!(self.as_int(&e)) }
    LispVal::number(n)
  },
  Lt: AtLeast(1) => LispVal::bool(try1!(self.int_bool_binop(|a, b| a < b, &args))),
  Le: AtLeast(1) => LispVal::bool(try1!(self.int_bool_binop(|a, b| a <= b, &args))),
  Gt: AtLeast(1) => LispVal::bool(try1!(self.int_bool_binop(|a, b| a > b, &args))),
  Ge: AtLeast(1) => LispVal::bool(try1!(self.int_bool_binop(|a, b| a >= b, &args))),
  Eq: AtLeast(1) => LispVal::bool(try1!(self.int_bool_binop(|a, b| a == b, &args))),
  ToString: Exact(1) => LispVal::string(self.to_string(&args[0])),
  StringToAtom: Exact(1) => {
    let s = try1!(self.as_string(&args[0]));
    LispVal::atom(self.get_atom(&s))
  },
  StringAppend: AtLeast(0) => {
    let mut out = String::new();
    for e in args { out.push_str(&try1!(self.as_string(&e))) }
    LispVal::string(ArcString::new(out))
  },
  Not: AtLeast(0) => LispVal::bool(!args.iter().any(|e| e.truthy())),
  And: AtLeast(0) => LispVal::bool(args.iter().all(|e| e.truthy())),
  Or: AtLeast(0) => LispVal::bool(args.iter().any(|e| e.truthy())),
  List: AtLeast(0) => LispVal::list(args),
  Cons: AtLeast(0) => match args.len() {
    0 => LispVal::nil(),
    1 => args[0].clone(),
    _ => {
      let r = args.pop().unwrap();
      if r.exactly(0) {LispVal::list(args)}
      else {LispVal::new(LispKind::DottedList(args, r))}
    }
  },
  Head: Exact(1) => try1!(self.head(&args[0])),
  Tail: Exact(1) => try1!(self.tail(&args[0])),
  Map: AtLeast(1) => {
    let mut it = args.into_iter();
    let proc = it.next().unwrap();
    let sp = proc.fspan().map_or(sp2, |fsp| fsp.span);
    if it.as_slice().is_empty() {
      return Ok(State::App(sp1, sp, proc, vec![], [].iter()))
    }
    return Ok(State::MapProc(sp1, sp, proc,
      it.map(Uncons::from).collect(), vec![]))
  },
  IsBool: Exact(1) => LispVal::bool(args[0].is_bool()),
  IsAtom: Exact(1) => LispVal::bool(args[0].is_atom()),
  IsPair: Exact(1) => LispVal::bool(args[0].at_least(1)),
  IsNull: Exact(1) => LispVal::bool(args[0].exactly(0)),
  IsNumber: Exact(1) => LispVal::bool(args[0].is_int()),
  IsString: Exact(1) => LispVal::bool(args[0].is_string()),
  IsProc: Exact(1) => LispVal::bool(args[0].is_proc()),
  IsDef: Exact(1) => LispVal::bool(args[0].is_def()),
  IsRef: Exact(1) => LispVal::bool(args[0].is_ref()),
  NewRef: AtLeast(0) => LispVal::new_ref(args.get(0).cloned().unwrap_or_else(LispVal::undef)),
  GetRef: Exact(1) => try1!(self.as_ref(&args[0], |e| Ok(e.clone()))),
  SetRef: Exact(2) => {
    try1!(self.as_ref(&args[0], |e| Ok(*e = args[1].clone())));
    LispVal::undef()
  },
  Async: AtLeast(1) => {
    let proc = args.remove(0);
    let sp = proc.fspan().map_or(sp2, |fsp| fsp.span);
    // TODO: actually async this
    return Ok(State::App(sp1, sp, proc, args, [].iter()))
  },
  IsAtomMap: Exact(1) => LispVal::bool(args[0].is_map()),
  NewAtomMap: AtLeast(0) => {
    let mut m = HashMap::new();
    for e in args {
      let mut u = Uncons::from(e);
      let e = try1!(u.next().ok_or("invalid arguments"));
      let a = try1!(self.as_string_atom(&e));
      let ret = u.next();
      if !u.exactly(0) {try1!(Err("invalid arguments"))}
      if let Some(v) = ret {m.insert(a, v);} else {m.remove(&a);}
    }
    LispVal::new_ref(LispVal::new(LispKind::AtomMap(m)))
  },
  Lookup: AtLeast(2) => {
    let k = self.as_string_atom(&args[1]);
    let e = try1!(self.as_map(&args[0], |m| Ok(m.get(&k?).cloned())));
    if let Some(e) = e {e} else {
      let v = args.get(2).cloned().unwrap_or_else(LispVal::undef);
      if v.is_proc() {
        let sp = v.fspan().map_or(sp2, |fsp| fsp.span);
        return Ok(State::App(sp1, sp, v, vec![], [].iter()))
      } else {v}
    }
  },
  Insert: AtLeast(2) => {
    try1!(try1!(args[0].as_ref_mut(|r| {
      r.as_map_mut(|m| -> SResult<_> {
        let k = self.as_string_atom(&args[1])?;
        Ok(match args.get(2) {
          Some(v) => {m.insert(k, v.clone());}
          None => {m.remove(&k);}
        })
      })
    }).unwrap_or(None).ok_or("expected a mutable map")));
    LispVal::undef()
  },
  InsertNew: AtLeast(2) => {
    let mut it = args.into_iter();
    let mut m = it.next().unwrap();
    let k = self.as_string_atom(&it.next().unwrap());
    try1!(try1!(m.as_map_mut(|m| -> SResult<_> {
      Ok(match it.next() {
        Some(v) => {m.insert(k?, v.clone());}
        None => {m.remove(&k?);}
      })
    }).ok_or("expected a map")));
    LispVal::undef()
  },
  SetTimeout: Exact(1) => {
    match try1!(args[0].as_int(|n| n.to_u64()).ok_or("expected a number")) {
      None | Some(0) => {self.timeout = None; self.cur_timeout = None},
      Some(n) => {
        let d = Duration::from_millis(n);
        self.timeout = Some(d);
        self.cur_timeout = Instant::now().checked_add(d)
      }
    }
    LispVal::undef()
  },
  IsMVar: Exact(1) => LispVal::bool(args[0].is_mvar()),
  IsGoal: Exact(1) => LispVal::bool(args[0].is_goal()),
  NewMVar: AtLeast(0) => self.lc.new_mvar(
    if args.is_empty() { InferTarget::Unknown }
    else if args.len() == 2 {
      let sort = try1!(args[0].as_atom().ok_or("expected an atom"));
      if try1!(args[1].as_bool().ok_or("expected a bool")) {
        InferTarget::Bound(sort)
      } else {
        InferTarget::Reg(sort)
      }
    } else {try1!(Err("invalid arguments"))}
  ),
  PrettyPrint: Exact(1) => /* TODO: pretty */
    LispVal::string(ArcString::new(format!("{}", self.print(&args[0])))),
  NewGoal: Exact(1) => LispVal::goal(self.fspan(sp1), args.pop().unwrap()),
  GoalType: Exact(1) => try1!(args[0].goal_type().ok_or("expected a goal")),
  InferType: Exact(1) => self.infer_type(sp1, &args[0])?,
  GetMVars: AtLeast(0) => LispVal::list(self.lc.mvars.clone()),
  GetGoals: AtLeast(0) => LispVal::list(self.lc.goals.clone()),
  SetGoals: AtLeast(0) => {self.lc.set_goals(args); LispVal::undef()},
  ToExpr: Exact(1) => return Ok(State::Refine {
    sp: sp1, stack: vec![], gv: Arc::new(Mutex::new(vec![])),
    state: RState::RefineExpr {tgt: InferTarget::Unknown, e: args.swap_remove(0)}
  }),
  Refine: AtLeast(0) => return Ok(State::Refine {
    sp: sp1, stack: vec![], gv: Arc::new(Mutex::new(vec![])),
    state: RState::Goals {
      gs: mem::replace(&mut self.lc.goals, vec![]).into_iter(),
      es: args.into_iter()
    }
  }),
  Have: AtLeast(2) => {
    let x = try1!(args[0].as_atom().ok_or("expected an atom"));
    if args.len() > 3 {try1!(Err("invalid arguments"))}
    let p = args.pop().unwrap();
    self.stack.push(Stack::Have(sp1, x));
    let mut stack = vec![];
    let state = match args.pop().filter(|_| args.len() > 0) {
      None => RState::RefineProof {tgt: self.lc.new_mvar(InferTarget::Unknown), p},
      Some(e) => {
        stack.push(RStack::Typed(p));
        RState::RefineExpr {tgt: InferTarget::Unknown, e}
      }
    };
    return Ok(State::Refine {sp: sp1, stack, state, gv: Arc::new(Mutex::new(vec![]))})
  },
  Stat: Exact(0) => {
    use std::fmt::Write;
    let mut s = String::new();
    for (a, e, _) in &self.lc.proof_order {
      write!(s, "{}: {}\n", self.print(a), self.print(e)).unwrap()
    }
    for e in &self.lc.goals {
      e.unwrapped(|r| if let LispKind::Goal(e) = r {
        write!(s, "|- {}\n", self.print(e)).unwrap()
      })
    }
    print!(sp1, s);
    LispVal::undef()
  },
  GetDecl: Exact(1) => {
    let x = try1!(args[0].as_atom().ok_or("expected an atom"));
    self.get_decl(self.fspan(sp1), x)
  },
  AddDecl: AtLeast(4) => {
    let fsp = self.fspan_base(sp1);
    match try1!(args[0].as_atom().ok_or("expected an atom")) {
      AtomID::TERM | AtomID::DEF => self.add_term(fsp, sp1, &args[1..])?,
      AtomID::AXIOM | AtomID::THM => return self.add_thm(fsp, sp1, &args[1..]),
      e => try1!(Err(format!("invalid declaration type '{}'", self.print(&e))))
    }
    LispVal::undef()
  },
  AddTerm: AtLeast(3) => {
    let fsp = self.fspan_base(sp1);
    self.add_term(fsp, sp1, &args)?;
    LispVal::undef()
  },
  AddThm: AtLeast(4) => {
    let fsp = self.fspan_base(sp1);
    return self.add_thm(fsp, sp1, &args)
  },
  NewDummy: AtLeast(1) => {
    if args.len() > 2 {try1!(Err("expected 1 or 2 armuments"))}
    let (x, s) = match args.get(1) {
      None => {
        let mut i = 1;
        let x = loop {
          let a = self.get_atom(&format!("_{}", i));
          if !self.lc.vars.contains_key(&a) {break a}
          i += 1;
        };
        (x, &args[0])
      }
      Some(s) => (try1!(args[0].as_atom().ok_or("expected an atom")), s)
    };
    let sort = try1!(s.as_atom().and_then(|s| self.data[s].sort).ok_or("expected a sort"));
    self.lc.vars.insert(x, (true, InferSort::Bound {sort}));
    LispVal::atom(x)
  },
  SetReporting: AtLeast(1) => {
    if args.len() == 1 {
      if let Some(b) = args[0].as_bool() {
        self.reporting.error = b;
        self.reporting.warn = b;
        self.reporting.info = b;
      } else {try1!(Err("invalid arguments"))}
    } else {
      if let Some(b) = args[1].as_bool() {
        match try1!(self.as_atom_string(&args[0])).deref() {
          "error" => self.reporting.error = b,
          "warn" => self.reporting.warn = b,
          "info" => self.reporting.info = b,
          s => try1!(Err(format!("unknown error level '{}'", s)))
        }
      } else {try1!(Err("invalid arguments"))}
    }
    LispVal::undef()
  },
  CheckProofs: Exact(1) => {
    if let Some(b) = args[0].as_bool() {
      self.check_proofs = b;
    } else {try1!(Err("invalid arguments"))}
    LispVal::undef()
  },
  RefineExtraArgs: AtLeast(2) => {
    if args.len() > 2 {try1!(Err("too many arguments"))}
    args.into_iter().nth(1).unwrap()
  },
}

impl<'a> Evaluator<'a> {
  fn fspan(&self, span: Span) -> FileSpan {
    FileSpan {file: self.file.clone(), span}
  }

  fn proc_pos(&self, sp: Span) -> ProcPos {
    if let Some(Stack::Def(Some(&Some((sp, x))))) = self.stack.last() {
      ProcPos::Named(self.fspan(sp), x)
    } else {
      ProcPos::Unnamed(self.fspan(sp))
    }
  }

  fn run(&mut self, mut active: State<'a>) -> Result<LispVal> {
    macro_rules! throw {($sp:expr, $e:expr) => {{
      let err = $e;
      return Err(self.err(Some($sp), err))
    }}}
    macro_rules! push {($($e:expr),*; $ret:expr) => {{
      $(self.stack.push({ #[allow(unused_imports)] use Stack::*; $e });)*
      { #[allow(unused_imports)] use State::*; $ret }
    }}}

    let mut iters: u8 = 0;
    // let mut stacklen = 0;
    loop {
      iters = iters.wrapping_add(1);
      if iters == 0 {
        if self.cur_timeout.map_or(false, |t| t < Instant::now()) {
          return Err(self.err(None, "timeout"))
        }
        if self.cancel.load(Ordering::Relaxed) {
          return Err(self.err(None, "cancelled"))
        }
      }
      if self.stack.len() >= 1024 {
        return Err(self.err(None, format!("stack overflow: {:#?}", self.ctx)))
      }
      // if self.check_proofs {
      //   if self.stack.len() < stacklen {
      //     log!("stack -= {}", stacklen - self.stack.len());
      //     stacklen = self.stack.len()
      //   }
      //   if self.stack.len() > stacklen {
      //     for e in &self.stack[stacklen..] {
      //       log!("stack += {}", self.print(e));
      //     }
      //     stacklen = self.stack.len()
      //   } else if let Some(e) = self.stack.last() {
      //     log!("stack top = {}", self.print(e));
      //   }
      //   log!("[{}] {}\n", self.ctx.len(), self.print(&active));
      // }
      active = match active {
        State::Eval(ir) => match ir {
          &IR::Local(i) => State::Ret(self.ctx[i].clone()),
          &IR::Global(sp, a) => State::Ret(match &self.data[a] {
            AtomData {name, lisp: None, ..} => match BuiltinProc::from_str(name) {
              None => throw!(sp, format!("Reference to unbound variable '{}'", name)),
              Some(p) => {
                let s = name.clone();
                let a = self.get_atom(&s);
                let ret = LispVal::proc(Proc::Builtin(p));
                self.data[a].lisp = Some((None, ret.clone()));
                ret
              }
            },
            AtomData {lisp: Some((_, x)), ..} => x.clone(),
          }),
          IR::Const(val) => State::Ret(val.clone()),
          IR::List(sp, ls) => State::List(*sp, vec![], ls.iter()),
          IR::DottedList(ls, e) => State::DottedList(vec![], ls.iter(), e),
          IR::App(sp1, sp2, f, es) => push!(App(*sp1, *sp2, es); Eval(f)),
          IR::If(e) => push!(If(&e.1, &e.2); Eval(&e.0)),
          &IR::Focus(sp, ref irs) => {
            if self.lc.goals.is_empty() {throw!(sp, "no goals")}
            let gs = self.lc.goals.drain(1..).collect();
            push!(Focus(gs); Refines(sp, irs.iter()))
          }
          &IR::Def(n, ref x, ref val) => {
            assert!(self.ctx.len() == n);
            push!(Def(Some(x)); Eval(val))
          }
          IR::Eval(keep, es) => {
            if !keep {self.stack.push(Stack::Def(None))}
            let mut it = es.iter();
            match it.next() {
              None => State::Ret(LispVal::undef()),
              Some(e) => push!(Eval(it); Eval(e)),
            }
          }
          &IR::Lambda(sp, n, spec, ref e) => {
            assert!(self.ctx.len() == n);
            State::Ret(LispVal::proc(Proc::Lambda {
              pos: self.proc_pos(sp),
              env: self.ctx.clone(),
              spec,
              code: e.clone()
            }))
          }
          &IR::Match(sp, ref e, ref brs) => push!(Match(sp, brs.iter()); State::Eval(e)),
        },
        State::Ret(ret) => match self.stack.pop() {
          None => return Ok(ret),
          Some(Stack::List(sp, mut vec, it)) => { vec.push(ret); State::List(sp, vec, it) }
          Some(Stack::DottedList(mut vec, it, e)) => { vec.push(ret); State::DottedList(vec, it, e) }
          Some(Stack::DottedList2(vec)) if vec.is_empty() => State::Ret(ret),
          Some(Stack::DottedList2(mut vec)) => State::Ret(match ret.try_unwrap() {
            Ok(LispKind::List(es)) => { vec.extend(es); LispVal::list(vec) }
            Ok(LispKind::DottedList(es, e)) => { vec.extend(es); LispVal::dotted_list(vec, e) }
            Ok(e) => LispVal::dotted_list(vec, LispVal::new(e)),
            Err(ret) => LispVal::dotted_list(vec, ret),
          }),
          Some(Stack::App(sp1, sp2, es)) => State::App(sp1, sp2, ret, vec![], es.iter()),
          Some(Stack::App2(sp1, sp2, f, mut vec, it)) => { vec.push(ret); State::App(sp1, sp2, f, vec, it) }
          Some(Stack::AppHead(sp1, sp2, e)) => State::App(sp1, sp2, ret, vec![e], [].iter()),
          Some(Stack::If(e1, e2)) => State::Eval(if ret.truthy() {e1} else {e2}),
          Some(Stack::Def(x)) => if let Some(s) = self.stack.pop() {
            macro_rules! push_ret {($e:expr) => {{
              if x.is_some() {
                self.stack.push(Stack::Drop(self.ctx.len()));
                self.ctx.push(ret);
              }
              $e
            }}}
            match s {
              Stack::App(sp1, sp2, es) => match es.split_first() {
                None => State::App(sp1, sp2, LispVal::undef(), vec![], [].iter()),
                Some((f, es)) => push_ret!(push!(App(sp1, sp2, es); Eval(f))),
              },
              Stack::App2(sp1, sp2, f, vec, it) => push_ret!(State::App(sp1, sp2, f, vec, it)),
              Stack::Eval(mut it) => push_ret!(match it.next() {
                None => State::Ret(LispVal::undef()),
                Some(e) => push!(Eval(it); Eval(e))
              }),
              Stack::Refines(sp, _, it) => push_ret!(State::Refines(sp, it)),
              _ => {self.stack.push(s); State::Ret(LispVal::undef())}
            }
          } else {
            if let Some(&Some((sp, a))) = x {
              self.data[a].lisp = Some((Some(self.fspan(sp)), ret));
            }
            State::Ret(LispVal::undef())
          },
          Some(Stack::Eval(mut it)) => match it.next() {
            None => State::Ret(ret),
            Some(e) => push!(Eval(it); Eval(e)),
          },
          Some(Stack::Match(sp, it)) => State::Match(sp, ret, it),
          Some(Stack::TestPattern(sp, e, it, br, pstack, vars)) =>
            State::Pattern(sp, e, it, br, pstack, vars, PatternState::Ret(ret.truthy())),
          Some(Stack::Drop(n)) => {self.ctx.truncate(n); State::Ret(ret)}
          Some(Stack::Ret(fsp, _, old, _)) => {self.file = fsp.file; self.ctx = old; State::Ret(ret)}
          Some(Stack::MatchCont(_, _, _, valid)) => {
            if let Err(valid) = Arc::try_unwrap(valid) {valid.store(false, Ordering::Relaxed)}
            State::Ret(ret)
          }
          Some(Stack::MapProc(sp1, sp2, f, us, mut vec)) => {
            vec.push(ret);
            State::MapProc(sp1, sp2, f, us, vec)
          }
          Some(Stack::AddThmProc(fsp, sp1, AwaitingProof {t, de, var_map, lc, is})) => {
            self.finish_add_thm(fsp, sp1, t, Some(Some((de, var_map, Some(lc), is, ret))))?;
            State::Ret(LispVal::undef())
          }
          Some(Stack::Refines(sp, Some(_), it)) if !ret.is_def() => State::Refines(sp, it),
          Some(Stack::Refines(sp, Some(esp), it)) => {
            self.stack.push(Stack::Refines(sp, None, it));
            self.evaluate_builtin(esp, esp, BuiltinProc::Refine, vec![ret])?
          }
          Some(Stack::Refines(sp, None, it)) => State::Refines(sp, it),
          Some(Stack::Focus(gs)) => {
            let mut gs1 = mem::replace(&mut self.lc.goals, vec![]);
            gs1.extend_from_slice(&gs);
            self.lc.set_goals(gs1);
            State::Ret(LispVal::undef())
          }
          Some(Stack::Refine {sp, stack, gv}) => State::Refine {sp, stack, state: RState::Ret(ret), gv},
          Some(Stack::Have(sp, x)) => {
            let e = self.infer_type(sp, &ret)?;
            self.lc.add_proof(x, e, ret);
            State::Ret(LispVal::undef())
          },
        },
        State::List(sp, vec, mut it) => match it.next() {
          None => State::Ret(LispVal::list(vec).span(self.fspan(sp))),
          Some(e) => push!(List(sp, vec, it); Eval(e)),
        },
        State::DottedList(vec, mut it, r) => match it.next() {
          None => push!(DottedList2(vec); Eval(r)),
          Some(e) => push!(DottedList(vec, it, r); Eval(e)),
        },
        State::App(sp1, sp2, f, mut args, mut it) => match it.next() {
          Some(e) => push!(App2(sp1, sp2, f, args, it); Eval(e)),
          None => f.unwrapped(|f| {
            let f = match f {
              LispKind::Proc(f) => f,
              _ => throw!(sp1, "not a function, cannot apply")
            };
            let spec = f.spec();
            if !spec.valid(args.len()) {
              match spec {
                ProcSpec::Exact(n) => throw!(sp1, format!("expected {} argument(s)", n)),
                ProcSpec::AtLeast(n) => throw!(sp1, format!("expected at least {} argument(s)", n)),
              }
            }
            Ok(match f {
              &Proc::Builtin(f) => self.evaluate_builtin(sp1, sp2, f, args)?,
              Proc::Lambda {pos, env, code, ..} => {
                if let Some(Stack::Ret(_, _, _, _)) = self.stack.last() { // tail call
                  if let Some(Stack::Ret(fsp, _, old, _)) = self.stack.pop() {
                    self.ctx = env.clone();
                    self.stack.push(Stack::Ret(fsp, pos.clone(), old, code.clone()));
                  } else {unsafe {std::hint::unreachable_unchecked()}}
                } else {
                  self.stack.push(Stack::Ret(self.fspan(sp1), pos.clone(),
                    mem::replace(&mut self.ctx, env.clone()), code.clone()));
                }
                self.file = pos.fspan().file.clone();
                self.stack.push(Stack::Drop(self.ctx.len()));
                match spec {
                  ProcSpec::Exact(_) => self.ctx.extend(args),
                  ProcSpec::AtLeast(nargs) => {
                    self.ctx.extend(args.drain(..nargs));
                    self.ctx.push(LispVal::list(args));
                  }
                }
                // Unfortunately we're fighting the borrow checker here. The problem is that
                // ir is borrowed in the Stack type, with most IR being owned outside the
                // function, but when you apply a lambda, the Proc::LambdaExact constructor
                // stores an Arc to the code to execute, hence it comes under our control,
                // which means that when the temporaries in this block go away, so does
                // ir (which is borrowed from f). We solve the problem by storing an Arc of
                // the IR inside the Ret instruction above, so that it won't get deallocated
                // while in use. Rust doesn't reason about other owners of an Arc though, so...
                State::Eval(unsafe {&*(&**code as *const IR)})
              },
              Proc::MatchCont(valid) => {
                if !valid.load(Ordering::Relaxed) {throw!(sp2, "continuation has expired")}
                loop {
                  match self.stack.pop() {
                    Some(Stack::MatchCont(span, expr, it, a)) => {
                      a.store(false, Ordering::Relaxed);
                      if Arc::ptr_eq(&a, &valid) {
                        break State::Match(span, expr, it)
                      }
                    }
                    Some(Stack::Drop(n)) => {self.ctx.truncate(n);}
                    Some(Stack::Ret(fsp, _, old, _)) => {self.file = fsp.file; self.ctx = old},
                    Some(_) => {}
                    None => throw!(sp2, "continuation has expired")
                  }
                }
              }
              Proc::RefineCallback(gv) => match gv.upgrade() {
                None => throw!(sp2, "callback has expired"),
                Some(gv) => {
                  let p = args.pop().unwrap();
                  match args.pop() {
                    None => State::Refine {
                      sp: sp1, stack: vec![], gv,
                      state: RState::RefineProof {tgt: self.lc.new_mvar(InferTarget::Unknown), p}
                    },
                    Some(tgt) if args.is_empty() => State::Refine {
                      sp: sp1, stack: vec![], gv, state: RState::RefineProof {tgt, p}
                    },
                    _ => throw!(sp1, "expected two arguments")
                  }
                }
              }
            })
          })?,
        }
        State::Match(sp, e, mut it) => match it.next() {
          None => throw!(sp, format!("match failed: {}", self.print(&e))),
          Some(br) =>
            State::Pattern(sp, e.clone(), it, br, vec![], vec![LispVal::undef(); br.vars].into(),
              PatternState::Eval(&br.pat, e))
        },
        State::Pattern(sp, e, it, br, mut pstack, mut vars, st) => {
          match self.pattern_match(&mut pstack, &mut vars, st) {
            Err(TestPending(sp2, e2, ir)) => push!(
              TestPattern(sp, e, it, br, pstack, vars),
              AppHead(sp2, sp2, e2),
              Drop(self.ctx.len());
              Eval(ir)),
            Ok(false) => State::Match(sp, e, it),
            Ok(true) => {
              let start = self.ctx.len();
              self.ctx.extend_from_slice(&vars);
              if br.cont {
                let valid = Arc::new(AtomicBool::new(true));
                self.ctx.push(LispVal::proc(Proc::MatchCont(valid.clone())));
                self.stack.push(Stack::MatchCont(sp, e.clone(), it, valid));
              }
              self.stack.push(Stack::Drop(start));
              State::Eval(&br.eval)
            },
          }
        }
        State::MapProc(sp1, sp2, f, mut us, vec) => {
          let mut it = us.iter_mut();
          let u0 = it.next().unwrap();
          match u0.next() {
            None => {
              if !(u0.exactly(0) && it.all(|u| u.exactly(0))) {
                throw!(sp1, "mismatched input length")
              }
              State::Ret(LispVal::list(vec))
            }
            Some(e0) => {
              let mut args = vec![e0];
              for u in it {
                if let Some(e) = u.next() {args.push(e)}
                else {throw!(sp1, "mismatched input length")}
              }
              push!(MapProc(sp1, sp2, f.clone(), us, vec); App(sp1, sp2, f, args, [].iter()))
            }
          }
        }
        State::Refines(sp, mut it) => match it.next() {
          None => State::Ret(LispVal::undef()),
          Some(e) => push!(Refines(sp, Some(e.span().unwrap_or(sp)), it); Eval(e))
        },
        State::Refine {sp, mut stack, state, gv} => {
          let res = self.run_refine(sp, &mut stack, state, &mut gv.lock().unwrap())
            .map_err(|e| self.err(Some(e.pos), e.kind.msg()))?;
          match res {
            RefineResult::Ret(e) => State::Ret(e),
            RefineResult::RefineExtraArgs(e, mut es) => {
              let mut args = vec![
                LispVal::proc(Proc::RefineCallback(Arc::downgrade(&gv))),
                e];
              args.append(&mut es);
              self.stack.push(Stack::Refine {sp, stack, gv});
              match &self.data[AtomID::REFINE_EXTRA_ARGS].lisp {
                None => self.evaluate_builtin(sp, sp, BuiltinProc::RefineExtraArgs, args)?,
                Some((_, v)) => State::App(sp, sp, v.clone(), args, [].iter()),
              }
            }
          }
        }
      }
    }
  }
}