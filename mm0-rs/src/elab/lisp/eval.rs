//! The lisp evaluator, where most functions are implemented.
//!
//! We use an explicit call stack for evaluating lisp [`Ir`], so that we can give useful
//! stack traces, as well as having a uniform location to be able to check for interrupts
//! and timeout.

use std::collections::{hash_map::Entry, HashMap};
use std::mem;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};
use num::{BigInt, Signed, ToPrimitive, Zero};
use crate::{ast::SExpr, ArcString, AtomData, AtomId, BoxError, DeclKey, DocComment, ElabError,
  Elaborator, Environment, ErrorLevel, FileRef, FileSpan, LispData,
  MergeStrategy, MergeStrategyInner, ObjectKind, SliceExt, Span, StmtTrace,
  ExprNode, ProofNode, TermKind, ThmKind, ThmId};
use crate::elab::local_context::{try_get_span, try_get_span_from, AwaitingProof, InferSort};
use crate::elab::{
  refine::{RStack, RState, RefineResult},
  ElabErrorKind, ReportMode, Result};
use super::parser::{Branch, DefTarget, Ir, MVarPattern, Pattern};
use super::print::{EnvDisplay, FormatEnv};
use super::{Arc, BuiltinProc, Cell, InferTarget, LispKind, LispRef, LispVal, Modifiers, Proc,
  ProcPos, ProcSpec, QExpr, Rc, RefCell, Uncons};

#[derive(Debug)]
enum Stack<'a> {
  List(Span, Vec<LispVal>, std::slice::Iter<'a, Ir>),
  DottedList(Vec<LispVal>, std::slice::Iter<'a, Ir>, &'a Ir),
  DottedList2(Vec<LispVal>),
  App(Span, Span, &'a [Ir]),
  App2(Span, Span, LispVal, Vec<LispVal>, std::slice::Iter<'a, Ir>),
  AppHead(Span, Span, LispVal),
  If(&'a Ir, &'a Ir),
  NoTailRec,
  Def(Option<&'a DefTarget>),
  DefMerge((FileSpan, Span), AtomId, Option<DocComment>),
  Eval(&'a Ir, std::slice::Iter<'a, Ir>),
  Match(Span, std::slice::Iter<'a, Branch>),
  TestPattern(Span, LispVal, std::slice::Iter<'a, Branch>,
    &'a Branch, Vec<PatternStack<'a>>, Box<[LispVal]>),
  Drop(usize),
  Ret(FileSpan, ProcPos, Vec<LispVal>, Arc<Ir>),
  MatchCont(Span, LispVal, std::slice::Iter<'a, Branch>, Rc<Cell<bool>>),
  SetMergeStrategy(Span, AtomId),
  MapProc(Span, Span, LispVal, Box<[Uncons]>, Vec<LispVal>),
  MergeMap(Span, LispVal, MergeStrategy, std::vec::IntoIter<(AtomId, LispVal, LispVal)>, HashMap<AtomId, LispVal>, AtomId),
  AddThmProc(FileSpan, Box<AwaitingProof>),
  Refines(Span, Option<Span>, std::slice::Iter<'a, Ir>),
  Refine {sp: Span, stack: Vec<RStack>},
  Focus(Span, bool, Vec<LispVal>),
  Have(Span, LispVal, AtomId),
}

impl<'a> EnvDisplay for Stack<'a> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
      Stack::NoTailRec => write!(f, "(no-tail-rec)"),
      &Stack::Def(Some(&Some((_, _, _, a)))) => write!(f, "(def {} _)", fe.to(&a)),
      Stack::Def(_) => write!(f, "(def _ _)"),
      Stack::DefMerge(..) => write!(f, "(def-merge _ _)"),
      &Stack::Eval(ir, ref es) => write!(f, "(begin\n  _ {} {})", fe.to(ir), fe.to(es.as_slice())),
      Stack::Match(_, bs) => write!(f, "(match _\n  {})", fe.to(bs.as_slice())),
      &Stack::TestPattern(_, ref e, ref bs, br, _, _) => write!(f,
        "(match {}\n  {}\n  {})\n  ->(? _)",
        fe.to(e), fe.to(br), fe.to(bs.as_slice())),
      &Stack::Drop(n) => write!(f, "drop {}", n),
      Stack::Ret(_, pos, _, _) => match pos {
        &ProcPos::Named(_, _, a) => write!(f, "ret {}", fe.to(&a)),
        ProcPos::Unnamed(_) => write!(f, "ret"),
      },
      Stack::MatchCont(_, e, bs, _) => write!(f, "(=> match {}\n  {})",
        fe.to(e), fe.to(bs.as_slice())),
      Stack::SetMergeStrategy(_, a) => write!(f, "(set-merge-strategy {}\n  _)", fe.to(a)),
      Stack::MapProc(_, _, e, us, es) => write!(f, "(map {}\n  {})\n  ->{} _",
        fe.to(e), fe.to(&**us), fe.to(es)),
      Stack::MergeMap(..) => write!(f, "(merge-map)"),
      Stack::AddThmProc(_, ap) => write!(f, "(add-thm {} _)", fe.to(&ap.atom())),
      Stack::Refines(_, _, irs) => write!(f, "(refine _ {})", fe.to(irs.as_slice())),
      Stack::Refine {..} => write!(f, "(refine _)"),
      &Stack::Focus(_, cl, ref es) => write!(f, "(focus {} _)\n  ->{}", cl, fe.to(es)),
      Stack::Have(_, _, a) => write!(f, "(have {} _)", fe.to(a)),
    }
  }
}

#[derive(Debug)]
enum State<'a> {
  Eval(&'a Ir),
  Evals(&'a Ir, std::slice::Iter<'a, Ir>),
  Refines(Span, std::slice::Iter<'a, Ir>),
  Ret(LispVal),
  List(Span, Vec<LispVal>, std::slice::Iter<'a, Ir>),
  DottedList(Vec<LispVal>, std::slice::Iter<'a, Ir>, &'a Ir),
  App(Span, Span, LispVal, Vec<LispVal>, std::slice::Iter<'a, Ir>),
  Match(Span, LispVal, std::slice::Iter<'a, Branch>),
  Pattern(Span, LispVal, std::slice::Iter<'a, Branch>,
    &'a Branch, Vec<PatternStack<'a>>, Box<[LispVal]>, PatternState<'a>),
  MapProc(Span, Span, LispVal, Box<[Uncons]>, Vec<LispVal>),
  MergeMap(Span, LispVal, MergeStrategy, std::vec::IntoIter<(AtomId, LispVal, LispVal)>, HashMap<AtomId, LispVal>),
  Refine {sp: Span, stack: Vec<RStack>, state: RState},
}

impl<'a> EnvDisplay for State<'a> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      &State::Eval(ir) => write!(f, "-> {}", fe.to(ir)),
      &State::Evals(ir, ref irs) => write!(f, "-> {}, {}", fe.to(ir), fe.to(irs.as_slice())),
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
      State::MergeMap(..) => write!(f, "(merge-map)"),
      State::Refine {state, ..} => state.fmt(fe, f),
    }
  }
}

impl LispKind {
  fn as_ref_mut<T>(&self, f: impl FnOnce(&mut LispVal) -> T) -> Option<T> {
    match self {
      LispKind::Ref(m) => Some(m.get_mut(f)),
      LispKind::Annot(_, e) => e.as_ref_mut(f),
      _ => None
    }
  }

  fn make_map_mut<T>(&self, f: impl FnOnce(&mut HashMap<AtomId, LispVal>) -> T) -> (Option<T>, Option<LispVal>) {
    match self {
      LispKind::AtomMap(m) => {
        let mut m = m.clone();
        (Some(f(&mut m)), Some(LispVal::new(LispKind::AtomMap(m))))
      }
      LispKind::Annot(sp, e) => match e.make_map_mut(f) {
        (r, None) => (r, None),
        (r, Some(e)) => (r, Some(LispVal::new(LispKind::Annot(sp.clone(), e)))),
      },
      LispKind::Ref(m) => (m.get_mut(|e| e.as_map_mut(f)), None),
      _ => (None, None)
    }
  }
}
impl LispVal {
  fn as_map_mut<T>(&mut self, f: impl FnOnce(&mut HashMap<AtomId, LispVal>) -> T) -> Option<T> {
    match self.get_mut() {
      None => {
        let (r, new) = self.make_map_mut(f);
        if let Some(e) = new {*self = e}
        r
      }
      Some(LispKind::AtomMap(m)) => Some(f(m)),
      Some(LispKind::Annot(_, e)) => Self::as_map_mut(e, f),
      Some(LispKind::Ref(m)) => m.get_mut(|e| Self::as_map_mut(e, f)),
      Some(_) => None
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
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

struct TestPending<'a>(Span, LispVal, &'a Ir);

/// A [`Result`](std::result::Result) type alias for string errors, used by functions that
/// work without an elaboration context.
pub type SResult<T> = std::result::Result<T, String>;

fn pattern_match<'b>(stack: &mut Vec<PatternStack<'b>>, ctx: &mut [LispVal],
    mut active: PatternState<'b>) -> std::result::Result<bool, TestPending<'b>> {
  loop {
    // println!("{}\n", self.print(&active));
    active = match active {
      PatternState::Eval(p, e) => match p {
        Pattern::Skip => PatternState::Ret(true),
        &Pattern::Atom(i) => {ctx[i] = e; PatternState::Ret(true)}
        &Pattern::QuoteAtom(a) => PatternState::Ret(e.unwrapped(|e|
          if let LispKind::Atom(a2) = *e {a == a2} else {false})),
        Pattern::String(s) => PatternState::Ret(e.unwrapped(|e|
          if let LispKind::String(s2) = e {s == s2} else {false})),
        &Pattern::Bool(b) => PatternState::Ret(e.unwrapped(|e|
          if let LispKind::Bool(b2) = *e {b == b2} else {false})),
        Pattern::Undef => PatternState::Ret(e.unwrapped(|e| *e == LispKind::Undef)),
        Pattern::Number(i) => PatternState::Ret(e.unwrapped(|e|
          if let LispKind::Number(i2) = e {i == i2} else {false})),
        Pattern::MVar(p) => e.unwrapped(|e| match e {
          LispKind::MVar(_, is) => match (p, is) {
            (MVarPattern::Any, _) |
            (MVarPattern::Unknown, InferTarget::Unknown | InferTarget::Provable) =>
              PatternState::Ret(true),
            (MVarPattern::Unknown, _) |
            (MVarPattern::Simple(_), InferTarget::Unknown | InferTarget::Provable) =>
              PatternState::Ret(false),
            (MVarPattern::Simple(p), &InferTarget::Bound(s)) => {
              stack.push(PatternStack::Bool(&p.1, true));
              PatternState::Eval(&p.0, LispVal::atom(s))
            }
            (MVarPattern::Simple(p), &InferTarget::Reg(s)) => {
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
          LispKind::List(es) if es.len() == 1 =>
            es[0].unwrapped(|e| if let LispKind::Atom(a2) = *e {a == a2} else {false}),
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
        Some(PatternStack::Bool(_, _)) if !b => PatternState::Ret(false),
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
          Dot::List(Some(n)) => PatternState::Ret(u.list_at_least(n)),
          Dot::DottedList(p) => PatternState::Eval(p, u.into()),
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

impl Elaborator {
  /// Render a lisp expression using the basic printer, and print it to the front end.
  pub fn print_lisp(&mut self, sp: Span, e: &LispVal) {
    self.report(ElabError::info(sp, format!("{}", self.print(e))))
  }

  /// Parse and evaluate a lisp expression. This is the main entry point.
  pub fn eval_lisp(&mut self, e: &SExpr) -> Result<LispVal> {
    self.eval_lisp_doc(e, String::new())
  }

  /// Parse and evaluate a lisp expression, with the given doc comment.
  pub fn eval_lisp_doc(&mut self, e: &SExpr, doc: String) -> Result<LispVal> {
    let sp = e.span;
    let ir = self.parse_lisp_doc(e, doc)?;
    // println!("{}", self.print(&ir));
    self.evaluate(sp, &ir)
  }

  /// Parse and evaluate a math formula.
  pub fn eval_qexpr(&mut self, e: QExpr) -> Result<LispVal> {
    let sp = e.span;
    let ir = self.parse_qexpr(e)?;
    self.evaluate(sp, &ir)
  }

  /// Parse and evaluate a lisp expression being used as a proof. Essentially the same
  /// as evaluating `(refine e)` where `e` is the input expression.
  pub fn elab_lisp(&mut self, e: &SExpr) -> Result<LispVal> {
    let sp = e.span;
    let ir = self.parse_lisp(e)?;
    Evaluator::new(self, sp).run(State::Refines(sp, [ir].iter()))
  }

  /// Evaluate a compiled lisp expression.
  pub fn evaluate<'b>(&'b mut self, sp: Span, ir: &'b Ir) -> Result<LispVal> {
    Evaluator::new(self, sp).run(State::Eval(ir))
  }

  /// Shorthand to call a lisp function from the top level.
  pub fn call_func(&mut self, sp: Span, f: LispVal, es: Vec<LispVal>) -> Result<LispVal> {
    Evaluator::new(self, sp).run(State::App(sp, sp, f, es, [].iter()))
  }

  /// Call an overridable lisp function. This uses the name of a builtin procedure `foo`
  /// and calls `(foo)` using the usual name resolution, meaning that if the user redefines
  /// `foo` then that function will be called instead of the builtin.
  pub fn call_overridable(&mut self, sp: Span, p: BuiltinProc, es: Vec<LispVal>) -> Result<LispVal> {
    let a = self.get_atom(p.to_byte_str());
    let val = match &self.data[a].lisp {
      Some(e) => (**e).clone(),
      None => LispVal::proc(Proc::Builtin(p))
    };
    self.call_func(sp, val, es)
  }

  /// Run a merge operation from the top level. This is used during `import` in order to handle
  /// merge operations that occur due to diamond dependencies.
  pub fn apply_merge(&mut self, sp: Span, strat: Option<&MergeStrategyInner>, old: LispVal, new: LispVal) -> Result<LispVal> {
    let mut eval = Evaluator::new(self, sp);
    let st = eval.apply_merge(sp, strat, old, new)?;
    eval.run(st)
  }

  fn as_string(&self, e: &LispVal) -> SResult<ArcString> {
    e.unwrapped(|e| if let LispKind::String(s) = e {Ok(s.clone())} else {
      Err(format!("expected a string, got {}", self.print(e)))
    })
  }

  fn as_string_atom(&mut self, e: &LispVal) -> Option<AtomId> {
    e.unwrapped(|e| match e {
      LispKind::String(s) => Some(self.get_atom(s)),
      &LispKind::Atom(a) => Some(a),
      _ => None
    })
  }

  fn with_int<T>(&self, e: &LispVal, f: impl FnOnce(&BigInt) -> SResult<T>) -> SResult<T> {
    e.unwrapped(|e| if let LispKind::Number(n) = e {f(n)} else {
      Err(format!("expected a integer, got {}", self.print(e)))
    })
  }

  fn as_int(&self, e: &LispVal) -> SResult<BigInt> {
    self.with_int(e, |n| Ok(n.clone()))
  }

  fn as_lref<T>(&self, e: &LispKind, f: impl FnOnce(&LispRef) -> SResult<T>) -> SResult<T> {
    e.as_lref(f).unwrap_or_else(|| Err(format!("not a ref-cell: {}", self.print(e))))
  }

  fn as_ref<T>(&self, e: &LispKind, f: impl FnOnce(&mut LispVal) -> SResult<T>) -> SResult<T> {
    self.as_lref(e, |m| m.get_mut(f))
  }

  fn as_map<T>(&self, e: &LispKind, f: impl FnOnce(&HashMap<AtomId, LispVal>) -> SResult<T>) -> SResult<T> {
    e.unwrapped(|e| match e {
      LispKind::AtomMap(m) => f(m),
      _ => Err(format!("not an atom map: {}", self.print(e)))
    })
  }

  fn to_string(&self, e: &LispKind) -> ArcString {
    match e {
      LispKind::Ref(m) => m.get(|e| self.to_string(e)),
      LispKind::Annot(_, e) => self.to_string(e),
      LispKind::String(s) => s.clone(),
      &LispKind::Atom(a) => self.data[a].name.clone(),
      LispKind::Number(n) => n.to_string().into(),
      _ => format!("{}", self.print(e)).into()
    }
  }

  fn int_bool_binop(&self, mut f: impl FnMut(&BigInt, &BigInt) -> bool, args: &[LispVal]) -> SResult<bool> {
    let mut it = args.iter();
    let mut last = self.as_int(it.next().expect("int_bool_binop([])"))?;
    for v in it {
      let new = self.as_int(v)?;
      if !f(&last, &new) {return Ok(false)}
      last = new;
    }
    Ok(true)
  }

  /// Returns a string representation of the current proof context.
  pub fn stat(&self) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    for (a, e, _) in &self.lc.proof_order {
      writeln!(s, "{}: {}", self.print(a), self.format_env().pp(e, 80)).unwrap()
    }
    for e in &self.lc.goals {
      e.unwrapped(|r| if let LispKind::Goal(e) = r {
        writeln!(s, "|- {}", self.format_env().pp(e, 80)).unwrap()
      })
    }
    s
  }

  fn head_err(&self, e: &LispKind) -> SResult<LispVal> {
    e.unwrapped(|e| match e {
      LispKind::List(es) if es.is_empty() => Err("evaluating 'hd ()'".into()),
      LispKind::List(es) => Ok(es[0].clone()),
      LispKind::DottedList(es, r) if es.is_empty() => self.head_err(r),
      LispKind::DottedList(es, _) => Ok(es[0].clone()),
      _ => Err(format!("expected a list, got {}", self.print(e)))
    })
  }

  fn tail(&self, e: &LispKind) -> SResult<LispVal> {
    fn exponential_backoff(es: &[LispVal], i: usize, r: impl FnOnce(Vec<LispVal>) -> LispVal) -> LispVal {
      let j = 2 * i;
      if j >= es.len() { r(es[i..].into()) }
      else { LispVal::dotted_list(es[i..j].cloned_box(), exponential_backoff(es, j, r)) }
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

  fn nth(&self, e: &LispKind, i: usize) -> SResult<LispVal> {
    e.unwrapped(|e| match e {
      LispKind::List(es) => Ok(es.get(i).cloned().unwrap_or_else(LispVal::undef)),
      LispKind::DottedList(es, r) => match es.get(i) {
        Some(e) => Ok(e.clone()),
        None => self.nth(r, i - es.len()),
      },
      _ => Err(format!("expected a list, got {}", self.print(e)))
    })
  }

  fn proof_node(&self, hyps: &[(Option<AtomId>, ExprNode)],
    heap: &[LispVal], ds: &mut Vec<LispVal>, p: &ProofNode) -> LispVal {
    match *p {
      ProofNode::Ref(n) => heap[n].clone(),
      ProofNode::Dummy(a, s) => {
        let a = LispVal::atom(a);
        ds.push(LispVal::list(vec![a.clone(), LispVal::atom(self.env.sorts[s].atom)]));
        a
      }
      ProofNode::Term {term, args: ref es} |
      ProofNode::Cong {term, args: ref es, ..} => {
        let mut args = vec![LispVal::atom(self.terms[term].atom)];
        args.extend(es.iter().map(|e| self.proof_node(hyps, heap, ds, e)));
        LispVal::list(args)
      }
      ProofNode::Hyp(h, _) => LispVal::atom(hyps[h].0.unwrap_or(AtomId::UNDER)),
      ProofNode::Thm {thm, args: ref es, ..} => {
        let mut args = vec![LispVal::atom(self.thms[thm].atom)];
        args.extend(es.iter().map(|e| self.proof_node(hyps, heap, ds, e)));
        LispVal::list(args)
      }
      ProofNode::Conv(ref es) => {
        let (t, c, p) = &**es;
        LispVal::list(vec![LispVal::atom(AtomId::CONV),
          self.proof_node(hyps, heap, ds, t),
          self.proof_node(hyps, heap, ds, c),
          self.proof_node(hyps, heap, ds, p),
        ])
      }
      ProofNode::Refl(ref p) => self.proof_node(hyps, heap, ds, p),
      ProofNode::Sym(ref p) =>
        LispVal::list(vec![LispVal::atom(AtomId::SYM), self.proof_node(hyps, heap, ds, p)]),
      ProofNode::Unfold {term, ref args, ref res} =>
        LispVal::list(vec![LispVal::atom(AtomId::UNFOLD),
          LispVal::atom(self.terms[term].atom),
          LispVal::list(args.iter().map(|e| self.proof_node(hyps, heap, ds, e)).collect::<Vec<_>>()),
          self.proof_node(hyps, heap, ds, &res.1)]),
    }
  }

  fn get_proof(&self, t: ThmId, mut heap: Vec<LispVal>) -> LispVal {
    let tdata = &self.thms[t];
    match &tdata.kind {
      ThmKind::Thm(Some(pr)) => {
        let mut ds = Vec::new();
        for e in &pr.heap[heap.len()..] {
          let e = self.proof_node(&tdata.hyps, &heap, &mut ds, e);
          heap.push(e)
        }
        let ret = self.proof_node(&tdata.hyps, &heap, &mut ds, &pr.head);
        LispVal::list(vec![LispVal::list(ds), ret])
      }
      _ => LispVal::atom(AtomId::SORRY),
    }
  }

  fn get_decl(&mut self, fsp: Option<FileSpan>, x: AtomId) -> LispVal {
    fn vis(mods: Modifiers) -> LispVal {
      match mods {
        Modifiers::PUB => LispVal::atom(AtomId::PUB),
        Modifiers::ABSTRACT => LispVal::atom(AtomId::ABSTRACT),
        Modifiers::LOCAL => LispVal::atom(AtomId::LOCAL),
        Modifiers::NONE => LispVal::nil(),
        _ => unreachable!()
      }
    }

    match self.data[x].decl {
      None => LispVal::undef(),
      Some(DeclKey::Term(t)) => {
        if let Some(fsp) = fsp {
          self.spans.insert_if(fsp.span, || ObjectKind::Term(t, fsp.span));
        }
        let tdata = &self.env.terms[t];
        let mut bvs = Vec::new();
        let mut heap = Vec::new();
        let mut args = vec![
          LispVal::atom(match tdata.kind {
            TermKind::Term => AtomId::TERM,
            TermKind::Def(_) => AtomId::DEF
          }),
          LispVal::atom(x),
          self.binders(&tdata.args, &mut heap, &mut bvs),
          LispVal::list(vec![
            LispVal::atom(self.sorts[tdata.ret.0].atom),
            Environment::deps(&bvs, tdata.ret.1)])];
        if let TermKind::Def(Some(v)) = &tdata.kind {
          args.push(vis(tdata.vis));
          let mut ds = Vec::new();
          for e in &v.heap[heap.len()..] {
            let e = self.expr_node(&heap, &mut Some(&mut ds), e);
            heap.push(e)
          }
          let ret = self.expr_node(&heap, &mut Some(&mut ds), &v.head);
          args.push(LispVal::list(ds));
          args.push(ret);
        }
        LispVal::list(args)
      }
      Some(DeclKey::Thm(t)) => {
        if let Some(fsp) = fsp {
          self.spans.insert_if(fsp.span, || ObjectKind::Thm(t));
        }
        let tdata = &self.thms[t];
        let mut bvs = Vec::new();
        let mut heap = Vec::new();
        let mut args = vec![
          LispVal::atom(match tdata.kind {
            ThmKind::Axiom => AtomId::AXIOM,
            ThmKind::Thm(_) => AtomId::THM
          }),
          LispVal::atom(x),
          self.binders(&tdata.args, &mut heap, &mut bvs),
          {
            for e in &tdata.heap[heap.len()..] {
              let e = self.expr_node(&heap, &mut None, e);
              heap.push(e)
            }
            LispVal::list(tdata.hyps.iter().map(|(a, e)| LispVal::list(vec![
              LispVal::atom(a.unwrap_or(AtomId::UNDER)),
              self.expr_node(&heap, &mut None, e)
            ])).collect::<Vec<_>>())
          },
          self.expr_node(&heap, &mut None, &tdata.ret)
        ];
        if let ThmKind::Thm(_) = tdata.kind {
          args.push(vis(tdata.vis));
          heap.truncate(tdata.args.len());
          args.push(LispVal::proc(Proc::ProofThunk(x, RefCell::new(Err(heap.into())))));
        }
        LispVal::list(args)
      }
    }
  }
}

fn set_report_mode(fe: FormatEnv<'_>, mode: &mut ReportMode, args: &[LispVal]) -> SResult<()> {
  if args.len() == 1 {
    if let Some(b) = args[0].as_bool() {
      mode.error = b;
      mode.warn = b;
      mode.info = b;
      Ok(())
    } else {Err("invalid arguments".into())}
  } else if let Some(b) = args[1].as_bool() {
    match args[0].as_atom().ok_or("expected an atom")? {
      AtomId::ERROR => mode.error = b,
      AtomId::WARN => mode.warn = b,
      AtomId::INFO => mode.info = b,
      s => return Err(format!("unknown error level '{}'", fe.to(&s)))
    }
    Ok(())
  } else {Err("invalid arguments".into())}
}

/// The lisp evaluation context, representing a lisp evaluation in progress.
/// This is an explicitly unfolled state machine (rather than using recursive functions)
/// so that we can explicitly manipulate the program stack for error reporting purposes.
#[derive(Debug)]
pub struct Evaluator<'a> {
  /// The elaborator, which is used to mediate all access to the elaboration context.
  elab: &'a mut Elaborator,
  /// The values assigned to local variables in the current context.
  ctx: Vec<LispVal>,
  /// The file that contains the location we are currently evaluating.
  /// This can change when we call a function.
  file: FileRef,
  /// The span of the statement we were originally asked to evaluate. This does
  /// not change during elaboration, and we use it to avoid reporting spans in random
  /// locations if an error is thrown in "library code".
  orig_span: Span,
  /// The evaluation stack. This is a structured object containing a stack of continuations
  /// each of which represent a context which awaiting a value from a sub-computation.
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

  fn make_stack_err(&mut self, sp: Option<(Span, bool)>, level: ErrorLevel,
      base: BoxError, err: impl Into<BoxError>) -> ElabError {
    let mut old = sp.map(|(sp, good)| (self.fspan(sp), good, base));
    let mut info = vec![];
    for s in self.stack.iter().rev() {
      if let Stack::Ret(fsp, pos, _, _) = s {
        let x = match pos {
          ProcPos::Named(_, _, a) => format!("({})", self.data[*a].name).into(),
          ProcPos::Unnamed(_) => "[fn]".into(),
        };
        if let Some((sp, good, base)) = old.take() {
          let (sp, osp) = if good {(sp, fsp.clone())} else {(fsp.clone(), sp)};
          info.push((osp, base));
          old = Some((sp, good, x));
        } else {
          old = Some((fsp.clone(), false, x));
        }
      }
    }
    ElabError {
      pos: old.map_or(self.orig_span, |(sp, _, _)| sp.span),
      level,
      kind: ElabErrorKind::Boxed(err.into(),
        if self.backtrace.active(level) {Some(info)} else {None})
    }
  }

  fn stack_span(&self, mut n: usize) -> Option<FileSpan> {
    for s in self.stack.iter().rev() {
      if let Stack::Ret(fsp, _, _, _) = s {
        match n.checked_sub(1) {
          None => return Some(fsp.clone()),
          Some(i) => n = i
        }
      }
    }
    None
  }

  fn info(&mut self, sp: Span, good: bool, base: &str, msg: impl Into<BoxError>) {
    let msg = self.make_stack_err(Some((sp, good)), ErrorLevel::Info, base.into(), msg);
    self.report(msg)
  }

  fn err(&mut self, sp: Option<(Span, bool)>, err: impl Into<BoxError>) -> ElabError {
    self.make_stack_err(sp, ErrorLevel::Error, "error occurred here".into(), err)
  }

  fn add_thm(&mut self, fsp: FileSpan, args: &[LispVal]) -> Result<State<'a>> {
    Ok(match self.elab.add_thm(fsp.clone(), args)? {
      Ok(()) => State::Ret(LispVal::undef()),
      Err((ap, proc)) => {
        let sp = try_get_span(&fsp, &proc);
        self.stack.push(Stack::AddThmProc(fsp, Box::new(ap)));
        State::App(sp, sp, proc, vec![], [].iter())
      }
    })
  }

  fn merge_map(&mut self, sp: Span, strat: MergeStrategy, mut old: LispVal, new: &LispKind) -> Result<State<'a>> {
    new.unwrapped(|e| match e {
      LispKind::Undef => Ok(State::Ret(old)),
      LispKind::AtomMap(newmap) => {
        if newmap.is_empty() {return Ok(State::Ret(old))}
        let mut opt = Some(old.as_map_mut(mem::take).ok_or_else(||
          self.err(Some((sp, false)), "merge-map: not an atom-map"))?);
        let oldmap = opt.as_mut().expect("impossible");
        let mut todo = vec![];
        if strat.is_none() {
          for (&k, v) in newmap { oldmap.insert(k, v.clone()); }
        } else {
          for (&k, v) in newmap {
            match oldmap.entry(k) {
              Entry::Vacant(e) => { e.insert(v.clone()); }
              Entry::Occupied(e) => { todo.push((k, v.clone(), e.get().clone())); }
            }
          }
        }
        if todo.is_empty() {
          Ok(State::Ret({
            if old.is_ref() && old.as_map_mut(|m| *m = opt.take().expect("impossible")).is_some() { old }
            else { LispVal::new(LispKind::AtomMap(opt.take().expect("impossible"))) }
          }))
        } else {
          Ok(State::MergeMap(sp, old, strat, todo.into_iter(), opt.expect("impossible")))
        }
    },
      _ => Err(self.err(Some((sp, false)), "merge-map: not an atom map"))
    })
  }

  fn apply_merge(&mut self, sp: Span, strat: Option<&MergeStrategyInner>, old: LispVal, new: LispVal) -> Result<State<'a>> {
    match strat {
      None => Ok(State::Ret(new)),
      Some(MergeStrategyInner::AtomMap(strat)) =>
        self.merge_map(sp, strat.clone(), old, &new),
      Some(MergeStrategyInner::Custom(f)) =>
        Ok(State::App(sp, sp, f.clone(), vec![old, new], [].iter()))
    }
  }
}

macro_rules! make_builtins {
  ($self:ident, $sp1:ident, $sp2:ident, $args:ident,
      $($(#[$attr:meta])* $e:ident: $ty:ident($n:expr) => $res:expr,)*) => {
    impl BuiltinProc {
      /// Get the argument specification for a builtin.
      #[must_use] pub fn spec(self) -> ProcSpec {
        match self {
          $($(#[$attr])* BuiltinProc::$e => ProcSpec::$ty($n)),*
        }
      }
    }

    impl<'a> Evaluator<'a> {
      #[allow(clippy::unwrap_used)]
      fn evaluate_builtin(&mut $self, $sp1: Span, $sp2: Span, f: BuiltinProc, mut $args: Vec<LispVal>) -> Result<State<'a>> {
        macro_rules! print {($sp:expr, $x:expr) => {{
          let msg = $x; $self.info($sp, false, f.to_str(), msg)
        }}}
        macro_rules! try1 {($x:expr) => {{
          match $x {
            Ok(e) => e,
            Err(s) => return Err($self.make_stack_err(
              Some(($sp1, false)), ErrorLevel::Error, format!("({})", f).into(), s))
          }
        }}}

        Ok(State::Ret(match f { $($(#[$attr])* BuiltinProc::$e => $res),* }))
      }
    }
  }
}

make_builtins! { self, sp1, sp2, args,
  Display: Exact(1) => {
    let s = try1!(self.as_string(&args[0]));
    print!(sp1, String::from_utf8_lossy(&s));
    LispVal::undef()
  },
  Error: Exact(1) => {
    let s = try1!(self.as_string(&args[0]));
    try1!(Err(String::from_utf8_lossy(&s)))
  },
  Print: Exact(1) => {print!(sp1, format!("{}", self.print(&args[0]))); LispVal::undef()},
  ReportAt: Exact(3) => {
    let level = match args[0].as_atom() {
      Some(AtomId::ERROR) => ErrorLevel::Error,
      Some(AtomId::WARN) => ErrorLevel::Warning,
      Some(AtomId::INFO) =>  ErrorLevel::Info,
      _ => try1!(Err("expected 'error, 'warn, or 'info"))
    };
    let FileSpan {file, span} = try1!(args[1].fspan().ok_or("expected a span"));
    if file == self.file {
      let s = try1!(self.as_string(&args[2]));
      let s = String::from_utf8_lossy(&s).into();
      let msg = if args[1].as_bool() == Some(true) {
        self.make_stack_err(Some((span, true)), level, "(report-at)".into(), s)
      } else {
        ElabError { pos: span, level, kind: ElabErrorKind::Boxed(s, None) }
      };
      self.report(msg);
    }
    LispVal::undef()
  },
  Begin: AtLeast(0) => args.last().cloned().unwrap_or_else(LispVal::undef),
  Apply: AtLeast(2) => {
    fn gather(args: &mut Vec<LispVal>, e: &LispKind) -> bool {
      e.unwrapped(|e| match e {
        LispKind::List(es) => {args.extend_from_slice(es); true}
        LispKind::DottedList(es, r) => {args.extend_from_slice(es); gather(args, r)}
        _ => false
      })
    }
    let proc = args.remove(0);
    let sp = proc.fspan().map_or(sp2, |fsp| fsp.span);
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
  Pow: AtLeast(0) => {
    let mut it = args.into_iter().rev();
    match it.next() {
      None => LispVal::number(1.into()),
      Some(b) => {
        let mut n = try1!(self.as_int(&b));
        for e in it {
          let exp: u32 = try1!(n.try_into().map_err(|_| "exponent out of range"));
          let base = try1!(self.as_int(&e));
          n = if base == 2.into() { BigInt::from(1) << exp } else { BigInt::pow(&base, exp) };
        }
        LispVal::number(n)
      }
    }
  },
  Max: AtLeast(1) => {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap()));
    for e in it { n = n.max(try1!(self.as_int(&e)).clone()) }
    LispVal::number(n)
  },
  Min: AtLeast(1) => {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap()));
    for e in it { n = n.min(try1!(self.as_int(&e)).clone()) }
    LispVal::number(n)
  },
  Sub: AtLeast(1) => if args.len() == 1 {
    LispVal::number(-try1!(self.as_int(&args[0])))
  } else {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap()));
    for e in it { n -= try1!(self.as_int(&e)) }
    LispVal::number(n)
  },
  Div: AtLeast(1) => {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap()));
    for e in it {
      let a = try1!(self.as_int(&e));
      if a.is_zero() {n.set_zero()} else {n /= a}
    }
    LispVal::number(n)
  },
  Mod: AtLeast(1) => {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap()));
    for e in it {
      let a = try1!(self.as_int(&e));
      if !a.is_zero() {n %= a}
    }
    LispVal::number(n)
  },
  Lt: AtLeast(1) => LispVal::bool(try1!(self.int_bool_binop(|a, b| a < b, &args))),
  Le: AtLeast(1) => LispVal::bool(try1!(self.int_bool_binop(|a, b| a <= b, &args))),
  Gt: AtLeast(1) => LispVal::bool(try1!(self.int_bool_binop(|a, b| a > b, &args))),
  Ge: AtLeast(1) => LispVal::bool(try1!(self.int_bool_binop(|a, b| a >= b, &args))),
  Eq: AtLeast(1) => LispVal::bool(try1!(self.int_bool_binop(|a, b| a == b, &args))),
  Shl: AtLeast(1) => {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap()));
    for e in it {
      try1!(self.with_int(&e, |e| {
        if e.is_negative() {
          let i: u64 = e.magnitude().try_into().map_err(|_| "shift out of range")?;
          n >>= &i
        } else {
          let i: u64 = e.try_into().map_err(|_| "shift out of range")?;
          n <<= &i
        }
        Ok(())
      }))
    }
    LispVal::number(n)
  },
  Shr: AtLeast(1) => {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap()));
    for e in it {
      try1!(self.with_int(&e, |e| {
        if e.is_negative() {
          let i: u64 = e.magnitude().try_into().map_err(|_| "shift out of range")?;
          n <<= &i
        } else {
          let i: u64 = e.try_into().map_err(|_| "shift out of range")?;
          n >>= &i
        }
        Ok(())
      }))
    }
    LispVal::number(n)
  },
  BAnd: AtLeast(0) => {
    let mut n: BigInt = (-1).into();
    for e in args { n &= try1!(self.as_int(&e)) }
    LispVal::number(n)
  },
  BOr: AtLeast(0) => {
    let mut n: BigInt = 0.into();
    for e in args { n |= try1!(self.as_int(&e)) }
    LispVal::number(n)
  },
  BXor: AtLeast(0) => {
    let mut n: BigInt = 0.into();
    for e in args { n ^= try1!(self.as_int(&e)) }
    LispVal::number(n)
  },
  BNot: AtLeast(0) => {
    let n = if let [e] = &*args {
      try1!(self.as_int(e))
    } else {
      let mut n: BigInt = (-1).into();
      for e in args { n &= try1!(self.as_int(&e)) }
      n
    };
    LispVal::number(!n)
  },
  Equal: AtLeast(1) => {
    let (e1, args) = args.split_first().unwrap();
    LispVal::bool(args.iter().all(|e2| e1 == e2))
  },
  ToString: Exact(1) => LispVal::string(self.to_string(&args[0])),
  StringToAtom: Exact(1) => {
    let s = try1!(self.as_string(&args[0]));
    LispVal::atom(self.get_atom(&s))
  },
  StringAppend: AtLeast(0) => {
    let mut out = Vec::new();
    for e in args { out.extend_from_slice(&self.to_string(&e)) }
    LispVal::string(out.into())
  },
  StringLen: Exact(1) => LispVal::number(try1!(self.as_string(&args[0])).len().into()),
  StringNth: Exact(2) => {
    let i: usize = try1!(self.with_int(&args[0],
      |n| n.try_into().map_err(|_| format!("index out of range: {}", n))));
    let s = try1!(self.as_string(&args[1]));
    let c = *try1!(s.get(i).ok_or_else(||
      format!("index out of range: index {}, length {}", i, s.len())));
    LispVal::number(c.into())
  },
  Substr: Exact(3) => {
    let start: usize = try1!(self.with_int(&args[0],
      |n| n.try_into().map_err(|_| format!("index out of range: start {}", n))));
    let end: usize = try1!(self.with_int(&args[1],
      |n| n.try_into().map_err(|_| format!("index out of range: end {}", n))));
    if start > end { try1!(Err(format!("start {} > end {}", start, end))) }
    let s = try1!(self.as_string(&args[2]));
    if end > s.len() { try1!(Err(format!("index out of range: end {}, length {}", end, s.len()))) }
    LispVal::string(ArcString::new(s[start..end].into()))
  },
  StringToList: Exact(1) => {
    let s = try1!(self.as_string(&args[0]));
    LispVal::list(s.iter()
      .map(|&c| LispVal::number(c.into()))
      .collect::<Vec<_>>())
  },
  ListToString: Exact(1) => {
    let mut u = Uncons::New(args[0].clone());
    let mut out: Vec<u8> = Vec::with_capacity(u.len());
    for e in &mut u {
      out.push(try1!(self.with_int(&e,
        |n| n.try_into().map_err(|_| format!("character out of range: {}", n)))));
    }
    if !u.is_empty() {
      try1!(Err(format!("list->string: not a list: {}", self.print(&args[0]))))
    }
    LispVal::string(out.into())
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
      else {LispVal::dotted_list(args, r)}
    }
  },
  Head: Exact(1) => try1!(self.head_err(&args[0])),
  Tail: Exact(1) => try1!(self.tail(&args[0])),
  Nth: Exact(2) => try1!(self.nth(&args[1],
    try1!(args[0].as_int(|n| n.to_usize().unwrap_or(usize::MAX)).ok_or("expected a number")))),
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
    try1!(self.as_ref(&args[0], |e| {*e = args[1].clone(); Ok(())}));
    LispVal::undef()
  },
  SetWeak: Exact(2) => {
    try1!(self.as_lref(&args[0], |e| {e.set_weak(&args[1]); Ok(())}));
    LispVal::undef()
  },
  CopySpan: Exact(2) => {
    let mut it = args.drain(..);
    match (it.next().unwrap().fspan(), it.next().unwrap()) {
      (Some(sp), e) => e.replace_span(sp),
      (None, e) => e
    }
  },
  StackSpan: Exact(1) => {
    let n = try1!(args[0].as_int(|n| n.to_usize().unwrap_or(usize::MAX)).ok_or("expected a number"));
    match self.stack_span(n) {
      Some(sp) => LispVal::undef().span(sp),
      None => LispVal::undef()
    }
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
      let a = try1!(self.as_string_atom(&e)
        .ok_or_else(|| format!("expected an atom, got {}", self.print(&e))));
      let ret = u.next();
      if !u.exactly(0) {try1!(Err("invalid arguments"))}
      if let Some(v) = ret {m.insert(a, v);} else {m.remove(&a);}
    }
    LispVal::new_ref(LispVal::new(LispKind::AtomMap(m)))
  },
  Lookup: AtLeast(2) => {
    match self.as_string_atom(&args[1]) {
      None => LispVal::undef(),
      Some(k) => {
        let e = try1!(self.as_map(&args[0], |m| Ok(m.get(&k).cloned())));
        if let Some(e) = e {e} else {
          let v = args.get(2).cloned().unwrap_or_else(LispVal::undef);
          if v.is_proc() {
            let sp = v.fspan().map_or(sp2, |fsp| fsp.span);
            return Ok(State::App(sp1, sp, v, vec![], [].iter()))
          }
          v
        }
      }
    }
  },
  Insert: AtLeast(2) => {
    try1!(try1!(args[0].as_ref_mut(|r| {
      r.as_map_mut(|m| -> SResult<_> {
        let k = self.as_string_atom(&args[1])
          .ok_or_else(|| format!("expected an atom, got {}", self.print(&args[1])))?;
        match args.get(2) {
          Some(v) => {m.insert(k, v.clone());}
          None => {m.remove(&k);}
        }
        Ok(())
      })
    }).unwrap_or(None).ok_or("expected a mutable map")));
    LispVal::undef()
  },
  InsertNew: AtLeast(2) => {
    let mut it = args.into_iter();
    let mut m = it.next().unwrap();
    let k = it.next().unwrap();
    let k = self.as_string_atom(&k)
      .ok_or_else(|| format!("expected an atom, got {}", self.print(&k)));
    try1!(try1!(m.as_map_mut(|m| -> SResult<_> {
      match it.next() {
        Some(v) => {m.insert(k?, v);}
        None => {m.remove(&k?);}
      }
      Ok(())
    }).ok_or("expected a map")));
    LispVal::undef()
  },
  MergeMap: AtLeast(0) => {
    let mut it = args.drain(..);
    if let Some(arg1) = it.next() {
      if let Some(arg2) = it.next() {
        if let Some(arg3) = it.next() {
          if it.next().is_some() {
            try1!(Err("merge-map: expected 0 to 3 arguments"))
          } else {return self.merge_map(sp1, arg1.into_merge_strategy(), arg2, &arg3)}
        } else {return self.merge_map(sp1, None, arg1, &arg2)}
      } else {LispVal::proc(Proc::MergeMap(arg1.into_merge_strategy()))}
    } else {LispVal::proc(Proc::MergeMap(None))}
  },
  SetTimeout: Exact(1) => {
    match try1!(args[0].as_int(BigInt::to_u64).ok_or("expected a number")) {
      None | Some(0) => {self.timeout = None; self.cur_timeout = None},
      Some(n) => {
        let d = Duration::from_millis(n);
        self.timeout = Some(d);
        self.cur_timeout = Instant::now().checked_add(d)
      }
    }
    LispVal::undef()
  },
  SetStackLimit: Exact(1) => {
    self.stack_limit =
      try1!(args[0].as_int(BigInt::to_usize).ok_or("expected a number"))
        .unwrap_or(usize::MAX);
    LispVal::undef()
  },
  IsMVar: Exact(1) => LispVal::bool(args[0].is_mvar()),
  IsGoal: Exact(1) => LispVal::bool(args[0].is_goal()),
  NewMVar: AtLeast(0) => {
    let fsp = self.fspan(sp1);
    self.lc.new_mvar(
      if args.is_empty() { InferTarget::Unknown }
      else if args.len() == 2 {
        let sort = try1!(args[0].as_atom().ok_or("expected an atom"));
        if try1!(args[1].as_bool().ok_or("expected a bool")) {
          InferTarget::Bound(sort)
        } else {
          InferTarget::Reg(sort)
        }
      } else {try1!(Err("invalid arguments"))},
      Some(fsp))
  },
  PrettyPrint: Exact(1) =>
    LispVal::string(format!("{}", self.format_env().pp(&args[0], 80)).into()),
  NewGoal: Exact(1) => LispVal::goal(self.fspan(sp1), args.pop().unwrap()),
  GoalType: Exact(1) => try1!(args[0].goal_type().ok_or("expected a goal")),
  InferType: Exact(1) => try1!(self.infer_type(sp1, &args[0]).map_err(|e| e.kind.msg())),
  InferSort: Exact(1) => match try1!(self.infer_target(sp1, &args[0]).map_err(|e| e.kind.msg())) {
    InferTarget::Bound(s) | InferTarget::Reg(s) => LispVal::atom(s),
    InferTarget::Unknown | InferTarget::Provable => LispVal::undef(),
  },
  GetMVars: AtLeast(0) => LispVal::list(self.lc.mvars.clone()),
  GetGoals: AtLeast(0) => LispVal::list(self.lc.goals.clone()),
  SetGoals: AtLeast(0) => {self.lc.set_goals(args); LispVal::undef()},
  SetCloseFn: AtLeast(0) => {
    let e = args.drain(..).next().unwrap_or_default();
    if e.is_def() && !e.is_proc() {try1!(Err("expected a procedure"))}
    self.lc.closer = e;
    LispVal::undef()
  },
  LocalCtx: Exact(0) =>
    LispVal::list(self.lc.proof_order.iter().map(|a| LispVal::atom(a.0)).collect::<Vec<_>>()),
  ToExpr: Exact(1) => return Ok(State::Refine {
    sp: sp1, stack: vec![RStack::DeferGoals(mem::take(&mut self.lc.goals))],
    state: RState::RefineExpr {tgt: InferTarget::Unknown, e: args.swap_remove(0)}
  }),
  Refine: AtLeast(0) => return Ok(State::Refine {
    sp: sp1, stack: vec![],
    state: RState::Goals {
      gs: mem::take(&mut self.lc.goals).into_iter(),
      es: args.into_iter()
    }
  }),
  Have: AtLeast(2) => {
    if args.len() > 3 {try1!(Err("invalid arguments"))}
    let mut args = args.drain(..);
    let xarg = args.next().unwrap();
    let a = try1!(xarg.as_atom().ok_or("expected an atom"));
    let x_sp = try_get_span(&self.fspan(sp1), &xarg);
    self.stack.push(Stack::Have(sp1, xarg, a));
    let mut stack = vec![RStack::DeferGoals(mem::take(&mut self.lc.goals))];
    let state = match (args.next().unwrap(), args.next()) {
      (p, None) => {
        let fsp = self.fspan(x_sp);
        RState::RefineProof {tgt: self.lc.new_mvar(InferTarget::Unknown, Some(fsp)), p}
      }
      (e, Some(p)) => {
        stack.push(RStack::Typed(p));
        RState::RefineExpr {tgt: InferTarget::Unknown, e}
      }
    };
    return Ok(State::Refine {sp: sp1, stack, state})
  },
  Stat: Exact(0) => {print!(sp1, self.stat()); LispVal::undef()},
  GetDecl: Exact(1) => {
    let x = try1!(args[0].as_atom().ok_or("expected an atom"));
    self.get_decl(args[0].fspan(), x)
  },
  AddDecl: AtLeast(4) => {
    let fsp = self.fspan_base(sp1);
    match try1!(args[0].as_atom().ok_or("expected an atom")) {
      AtomId::TERM | AtomId::DEF => self.add_term(&fsp, &args[1..])?,
      AtomId::AXIOM | AtomId::THM => return self.add_thm(fsp, &args[1..]),
      e => try1!(Err(format!("invalid declaration type '{}'", self.print(&e))))
    }
    LispVal::undef()
  },
  AddTerm: AtLeast(3) => {
    let fsp = self.fspan_base(sp1);
    self.add_term(&fsp, &args)?;
    LispVal::undef()
  },
  AddThm: AtLeast(4) => {
    let fsp = self.fspan_base(sp1);
    return self.add_thm(fsp, &args)
  },
  NewDummy: AtLeast(1) => {
    if args.len() > 2 {try1!(Err("expected 1 or 2 armuments"))}
    let (x, s) = match args.get(1) {
      None => {
        let mut i = 1;
        let x = loop {
          let a = self.get_atom(format!("_{}", i).as_bytes());
          if !self.lc.vars.contains_key(&a) {break a}
          i += 1;
        };
        (x, &args[0])
      }
      Some(s) => (try1!(args[0].as_atom().ok_or("expected an atom")), s)
    };
    let sort = try1!(s.as_atom().and_then(|s| self.data[s].sort).ok_or("expected a sort"));
    self.lc.vars.insert(x, (true, InferSort::Bound(sort)));
    LispVal::atom(x)
  },
  SetReporting: AtLeast(1) => {
    let fe = FormatEnv {source: &self.elab.ast.source, env: &self.elab.env};
    try1!(set_report_mode(fe, &mut self.elab.reporting, &args));
    LispVal::undef()
  },
  SetBacktrace: AtLeast(1) => {
    let fe = FormatEnv {source: &self.elab.ast.source, env: &self.elab.env};
    try1!(set_report_mode(fe, &mut self.elab.backtrace, &args));
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
  EvalString: AtLeast(0) => {
    let fsp = self.fspan(sp1);
    let bytes = self.eval_string(&fsp, &args)?;
    LispVal::string(bytes.into())
  },
  #[cfg(feature = "mmc")]
  MmcInit: Exact(0) => LispVal::proc(Proc::MmcCompiler(
    RefCell::new(Box::new(crate::mmc::Compiler::new(self)))
  )),
}

impl<'a> Evaluator<'a> {
  fn fspan(&self, span: Span) -> FileSpan {
    FileSpan {file: self.file.clone(), span}
  }

  fn try_get_span(&self, fsp: Option<&FileSpan>) -> Span {
    let orig = FileSpan {file: self.path.clone(), span: self.orig_span};
    try_get_span_from(&orig, fsp)
  }

  #[allow(unused)]
  fn respan(&self, sp: Span) -> Span { self.try_get_span(Some(&self.fspan(sp))) }

  fn proc_pos(&self, sp: Span) -> ProcPos {
    if let Some(Stack::Def(Some(&Some((sp1, sp2, _, x))))) = self.stack.last() {
      ProcPos::Named(self.fspan(sp2), sp1, x)
    } else {
      ProcPos::Unnamed(self.fspan(sp))
    }
  }

  #[allow(clippy::never_loop)]
  fn run(&mut self, mut active: State<'a>) -> Result<LispVal> {
    macro_rules! throw {($sp:expr, $e:expr) => {{
      let err = $e;
      return Err(self.err(Some(($sp, false)), err))
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
      if self.stack.len() >= self.stack_limit {
        return Err(self.err(None, "stack overflow"))
      }
      // if self.check_proofs {
      //   if self.stack.len() < stacklen {
      //     println!("stack -= {}", stacklen - self.stack.len());
      //     stacklen = self.stack.len()
      //   }
      //   if self.stack.len() > stacklen {
      //     for e in &self.stack[stacklen..] {
      //       println!("stack += {}", self.print(e));
      //     }
      //     stacklen = self.stack.len()
      //   } else if let Some(e) = self.stack.last() {
      //     println!("stack top = {}", self.print(e));
      //   }
      //   println!("[{}] {}\n", self.ctx.len(), self.print(&active));
      // }
      active = match active {
        State::Eval(ir) => match ir {
          &Ir::Local(i) => State::Ret(self.ctx[i].clone()),
          &Ir::Global(sp, a) => State::Ret(match &self.data[a] {
            AtomData {name, lisp: None, ..} => match BuiltinProc::from_bytes(name) {
              None => throw!(sp, format!("Reference to unbound variable '{}'", name)),
              Some(p) => {
                let s = name.clone();
                let a = self.get_atom(&s);
                let ret = LispVal::proc(Proc::Builtin(p));
                self.data[a].lisp = Some(LispData {src: None, doc: None, val: ret.clone(), merge: None});
                ret
              }
            },
            AtomData {lisp: Some(x), ..} => x.val.clone(),
          }),
          Ir::Const(val) => State::Ret(val.clone()),
          Ir::List(sp, ls) => State::List(*sp, vec![], ls.iter()),
          Ir::DottedList(ls, e) => State::DottedList(vec![], ls.iter(), e),
          Ir::App(sp1, sp2, f, es) => push!(App(*sp1, *sp2, es); Eval(f)),
          Ir::If(e) => push!(If(&e.1, &e.2); Eval(&e.0)),
          Ir::NoTailRec => match self.stack.pop() {
            None => State::Ret(LispVal::undef()),
            Some(Stack::Eval(e, it)) => push!(NoTailRec; Evals(e, it)),
            Some(s) => push!(s; State::Ret(LispVal::undef())),
          }
          &Ir::Focus(sp, ref irs) => {
            if self.lc.goals.is_empty() {throw!(sp, "no goals")}
            let gs = self.lc.goals.drain(1..).collect();
            push!(Focus(sp, true, gs); Refines(sp, irs.iter()))
          }
          &Ir::SetMergeStrategy(sp, a, ref ir) => push!(SetMergeStrategy(sp, a); Eval(ir)),
          &Ir::Def(n, ref x, ref val) => {
            assert!(self.ctx.len() == n);
            push!(Def(Some(x)); Eval(val))
          }
          Ir::Eval(keep, es) => {
            if !keep {self.stack.push(Stack::Def(None))}
            let mut it = es.iter();
            match it.next() {
              None => State::Ret(LispVal::undef()),
              Some(e1) => match it.next() {
                None => State::Eval(e1),
                Some(e2) => push!(Eval(e2, it); Eval(e1)),
              }
            }
          }
          &Ir::Lambda(sp, n, spec, ref e) => {
            assert!(self.ctx.len() == n);
            State::Ret(LispVal::proc(Proc::Lambda {
              pos: self.proc_pos(sp),
              env: self.ctx.clone().into(),
              spec,
              code: e.clone()
            }))
          }
          &Ir::Match(sp, ref e, ref brs) => push!(Match(sp, brs.iter()); Eval(e)),
        },
        State::Ret(ret) => match self.stack.pop() {
          None => return Ok(ret),
          Some(Stack::List(sp, mut vec, it)) => { vec.push(ret); State::List(sp, vec, it) }
          Some(Stack::DottedList(mut vec, it, e)) => { vec.push(ret); State::DottedList(vec, it, e) }
          Some(Stack::DottedList2(vec)) if vec.is_empty() => State::Ret(ret),
          Some(Stack::DottedList2(mut vec)) => State::Ret(match ret.try_unwrap() {
            Ok(LispKind::List(es)) => { vec.extend::<Vec<_>>(es.into()); LispVal::list(vec) }
            Ok(LispKind::DottedList(es, e)) => { vec.extend::<Vec<_>>(es.into()); LispVal::dotted_list(vec, e) }
            Ok(e) => LispVal::dotted_list(vec, LispVal::new(e)),
            Err(ret) => LispVal::dotted_list(vec, ret),
          }),
          Some(Stack::App(sp1, sp2, es)) => State::App(sp1, sp2, ret, vec![], es.iter()),
          Some(Stack::App2(sp1, sp2, f, mut vec, it)) => { vec.push(ret); State::App(sp1, sp2, f, vec, it) }
          Some(Stack::AppHead(sp1, sp2, e)) => State::App(sp1, sp2, ret, vec![e], [].iter()),
          Some(Stack::If(e1, e2)) => State::Eval(if ret.truthy() {e1} else {e2}),
          Some(Stack::NoTailRec) => State::Ret(ret),
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
              Stack::Eval(e, it) => push_ret!(State::Evals(e, it)),
              Stack::Refines(sp, _, it) => push_ret!(State::Refines(sp, it)),
              _ => {self.stack.push(s); State::Ret(LispVal::undef())}
            }
          } else if let Some(&Some((sp1, sp2, ref doc, a))) = x {
            let loc = (self.fspan(sp2), sp1);
            let lisp = &mut self.data[a].lisp;
            if let Some(LispData {merge: strat @ Some(_), val, ..}) = lisp {
              let (strat, old) = (strat.clone(), val.clone());
              self.stack.push(Stack::DefMerge(loc, a, doc.clone()));
              self.apply_merge(sp1, strat.as_deref(), old, ret)?
            } else {
              if ret.is_def_strict() {
                let e = mem::replace(&mut self.data[a].lisp,
                  Some(LispData {src: Some(loc), doc: doc.clone(), val: ret, merge: None}));
                if e.is_none() {
                  self.stmts.push(StmtTrace::Global(a))
                }
              } else if mem::take(&mut self.data[a].lisp).is_some() {
                self.data[a].graveyard = Some(Box::new(loc));
              } else {}
              State::Ret(LispVal::undef())
            }
          } else { State::Ret(LispVal::undef()) },
          Some(Stack::DefMerge(loc1, a, doc)) => {
            match (&mut self.data[a].lisp, ret.is_def_strict()) {
              (l @ None, true) =>
                *l = Some(LispData {src: Some(loc1), doc, val: ret, merge: None}),
              (Some(LispData {val, ..}), true) => *val = ret,
              (l, false) => if l.is_some() {
                self.data[a].graveyard = Some(Box::new(loc1));
              }
            }
            State::Ret(LispVal::undef())
          }
          Some(Stack::Eval(e, it)) => State::Evals(e, it),
          Some(Stack::Match(sp, it)) => State::Match(sp, ret, it),
          Some(Stack::TestPattern(sp, e, it, br, pstack, vars)) =>
            State::Pattern(sp, e, it, br, pstack, vars, PatternState::Ret(ret.truthy())),
          Some(Stack::Drop(n)) => {self.ctx.truncate(n); State::Ret(ret)}
          Some(Stack::Ret(fsp, _, old, _)) => {self.file = fsp.file; self.ctx = old; State::Ret(ret)}
          Some(Stack::MatchCont(_, _, _, valid)) => {
            if let Err(valid) = Rc::try_unwrap(valid) {valid.set(false)}
            State::Ret(ret)
          }
          Some(Stack::SetMergeStrategy(sp1, a)) => {
            if let Some(ref mut data) = self.data[a].lisp {
              data.merge = ret.into_merge_strategy()
            } else {
              throw!(sp1, format!("unknown definition '{}', cannot set merge strategy", self.print(&a)))
            }
            State::Ret(LispVal::undef())
          }
          Some(Stack::MapProc(sp1, sp2, f, us, mut vec)) => {
            vec.push(ret);
            State::MapProc(sp1, sp2, f, us, vec)
          }
          Some(Stack::MergeMap(sp, old, strat, it, mut map, k)) => {
            map.insert(k, ret);
            State::MergeMap(sp, old, strat, it, map)
          }
          Some(Stack::AddThmProc(fsp, ap)) => {
            ap.finish(self, &fsp, ret)?;
            State::Ret(LispVal::undef())
          }
          Some(Stack::Refines(sp, Some(_), it)) if !ret.is_def() => State::Refines(sp, it),
          Some(Stack::Refines(sp, Some(esp), it)) => {
            self.stack.push(Stack::Refines(sp, None, it));
            self.evaluate_builtin(esp, esp, BuiltinProc::Refine, vec![ret])?
          }
          Some(Stack::Refines(sp, None, it)) => State::Refines(sp, it),
          Some(Stack::Focus(sp, close, gs)) => loop { // labeled block, not a loop. See rust#48594
            if close {
              if self.lc.closer.is_def() {
                break push!(Focus(sp, false, gs); App(sp, sp, self.lc.closer.clone(), vec![], [].iter()))
              } else if self.lc.goals.is_empty() {
              } else {
                let stat = self.stat();
                self.call_goal_listener(&stat);
                let span = self.fspan(sp);
                for g in mem::take(&mut self.lc.goals) {
                  let err = ElabError::new_e(try_get_span(&span, &g),
                    format!("|- {}", self.format_env().pp(&g.goal_type().expect("expected a goal"), 80)));
                  self.report(err)
                }
                throw!(sp, format!("focused goal has not been solved\n\n{}", stat))
              }
            }
            self.lc.set_goals(gs);
            break State::Ret(LispVal::undef())
          },
          Some(Stack::Refine {sp, stack}) =>
            State::Refine {sp, stack, state: RState::Ret(ret)},
          Some(Stack::Have(sp, x, a)) => {
            let e = self.infer_type(sp, &ret)?;
            let span = try_get_span(&self.fspan(sp), &x);
            self.lc.add_proof(a, e, ret.clone());
            if span != sp {
              self.spans.insert_if(span, || ObjectKind::proof(x));
            }
            State::Ret(LispVal::undef())
          },
        },
        State::Evals(e, mut it) => match it.next() {
          None => State::Eval(e),
          Some(e2) => push!(Eval(e2, it); Eval(e)),
        },
        State::List(sp, vec, mut it) => match it.next() {
          None => State::Ret(LispVal::list(vec).span(self.fspan(sp))),
          Some(e) => push!(List(sp, vec, it); Eval(e)),
        },
        State::DottedList(vec, mut it, r) => match it.next() {
          None => push!(DottedList2(vec); Eval(r)),
          Some(e) => push!(DottedList(vec, it, r); Eval(e)),
        },
        State::App(sp1, sp2, func, mut args, mut it) => match it.next() {
          Some(e) => push!(App2(sp1, sp2, func, args, it); Eval(e)),
          None => func.unwrapped(|func| {
            let func = if let LispKind::Proc(f) = func { f }
            else { throw!(sp1, "not a function, cannot apply") };
            let spec = func.spec();
            if !spec.valid(args.len()) {
              match spec {
                ProcSpec::Exact(n) => throw!(sp1, format!("expected {} argument(s)", n)),
                ProcSpec::AtLeast(n) => throw!(sp1, format!("expected at least {} argument(s)", n)),
              }
            }
            Ok(match func {
              &Proc::Builtin(func) => self.evaluate_builtin(sp1, sp2, func, args)?,
              Proc::Lambda {pos, env, code, ..} => {
                let tail_call = (|| {
                  for (i, s) in self.stack.iter().enumerate().rev() {
                    match s {
                      Stack::Ret(..) => return Some(i),
                      Stack::Drop(_) => {}
                      _ => break
                    }
                  }
                  None
                })();
                if let Some(i) = tail_call { // tail call
                  let s = self.stack.drain(i..).next();
                  let_unchecked!((fsp, old) as Some(Stack::Ret(fsp, _, old, _)) = s);
                  self.ctx = (**env).into();
                  self.stack.push(Stack::Ret(fsp, pos.clone(), old, code.clone()));
                } else {
                  self.stack.push(Stack::Ret(self.fspan(sp1), pos.clone(),
                    mem::replace(&mut self.ctx, (**env).into()), code.clone()));
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
                let code: *const Ir = &**code;
                State::Eval(unsafe { &*code })
              },
              Proc::MatchCont(valid) => {
                if !valid.get() {throw!(sp2, "continuation has expired")}
                loop {
                  match self.stack.pop() {
                    Some(Stack::MatchCont(span, expr, it, a)) => {
                      a.set(false);
                      if Rc::ptr_eq(&a, valid) {
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
              Proc::MergeMap(strat) => {
                let new = args.pop().expect("impossible");
                let old = args.pop().expect("impossible");
                self.merge_map(sp1, strat.clone(), old, &new)?
              }
              Proc::RefineCallback => State::Refine {
                sp: sp1, stack: vec![],
                state: {
                  let p = args.pop().expect("impossible");
                  match args.pop() {
                    None => RState::RefineProof {
                      tgt: {
                        let fsp = p.fspan().unwrap_or_else(|| self.fspan(sp1));
                        self.lc.new_mvar(InferTarget::Unknown, Some(fsp))
                      },
                      p
                    },
                    Some(tgt) if args.is_empty() => RState::RefineProof {tgt, p},
                    Some(_) => throw!(sp1, "expected two arguments")
                  }
                }
              },
              &Proc::ProofThunk(x, ref m) => {
                let mut g = m.borrow_mut();
                match &*g {
                  Ok(e) => State::Ret(e.clone()),
                  Err(_) => if let Some(DeclKey::Thm(t)) = self.data[x].decl {
                    let_unchecked!(heap as Err(heap) = mem::replace(&mut *g, Ok(LispVal::undef())));
                    let e = self.get_proof(t, heap.into());
                    *g = Ok(e.clone());
                    State::Ret(e)
                  } else {unreachable!()}
                }
              }
              #[cfg(feature = "mmc")]
              Proc::MmcCompiler(c) => {
                let sp = self.respan(sp1);
                State::Ret(c.borrow_mut().call(self, sp, args)?)
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
          match pattern_match(&mut pstack, &mut vars, st) {
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
                let valid = Rc::new(Cell::new(true));
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
          let u0 = it.next().expect("impossible");
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
        State::MergeMap(sp, mut old, strat, mut it, map) => match it.next() {
          None => {
            let mut opt = Some(map);
            State::Ret({
              if old.is_ref() && old.as_map_mut(|m| *m = opt.take().expect("impossible")).is_some() { old }
              else { LispVal::new(LispKind::AtomMap(opt.take().expect("impossible"))) }
            })
          }
          Some((k, oldv, newv)) => {
            let st = self.apply_merge(sp, strat.as_deref(), oldv, newv)?;
            push!(MergeMap(sp, old, strat, it, map, k); st)
          }
        },
        State::Refines(sp, mut it) => match it.next() {
          None => State::Ret(LispVal::undef()),
          Some(e) => push!(Refines(sp, Some(e.span().unwrap_or(sp)), it); Eval(e))
        },
        State::Refine {sp, mut stack, state} => {
          let res = self.elab.run_refine(self.orig_span, &mut stack, state)
            .map_err(|e| self.err(Some((e.pos, true)), e.kind.msg()))?;
          match res {
            RefineResult::Ret(e) => {self.lc.clean_mvars(); State::Ret(e)}
            RefineResult::RefineExtraArgs(tgt, e, u) => {
              let mut args = vec![LispVal::proc(Proc::RefineCallback), tgt.clone(), e];
              for e in u {args.push(e)}
              stack.push(RStack::CoerceTo(tgt));
              self.stack.push(Stack::Refine {sp, stack});
              match &self.data[AtomId::REFINE_EXTRA_ARGS].lisp {
                None => self.evaluate_builtin(sp, sp, BuiltinProc::RefineExtraArgs, args)?,
                Some(v) => State::App(sp, sp, v.val.clone(), args, [].iter()),
              }
            }
            RefineResult::Proc(tgt, proc) => {
              let args = vec![LispVal::proc(Proc::RefineCallback), tgt];
              push!(Refine {sp, stack}; App(sp, sp, proc, args, [].iter()))
            }
          }
        }
      }
    }
  }
}