//! The lisp evaluator, where most functions are implemented.
//!
//! We use an explicit call stack for evaluating lisp [`Ir`], so that we can give useful
//! stack traces, as well as having a uniform location to be able to check for interrupts
//! and timeout.

use std::collections::{hash_map::Entry, HashMap};
use std::mem;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::Ordering;
use std::time::Duration;
use instant::Instant;
use num::{BigInt, Signed, ToPrimitive, Zero};
use crate::{ast::SExpr, ArcString, AtomData, AtomId, BoxError, DeclKey, ElabError,
  Elaborator, Environment, ErrorLevel, FileRef, FileSpan, LispData,
  MergeStrategy, MergeStrategyInner, ObjectKind, SliceExt, Span, StmtTrace,
  TermKind, ThmKind, ThmId};
use crate::elab::local_context::{try_get_span, try_get_span_from, AwaitingProof, InferSort};
use crate::elab::{
  refine::{RStack, RState, RefineResult},
  ElabErrorKind, ReportMode, Result};
use super::parser::{Ir, MVarPattern};
use super::print::FormatEnv;
use super::{Arc, BuiltinProc, Cell, InferTarget, LispKind, LispRef, LispVal, Modifiers, Proc,
  ProcPos, ProcSpec, QExpr, Rc, RefCell, Uncons};

#[derive(Debug)]
struct MergeMapData {
  old: LispVal,
  strat: MergeStrategy,
  it: std::vec::IntoIter<(AtomId, LispVal, LispVal)>,
  map: HashMap<AtomId, LispVal>,
  k: Option<AtomId>,
}

#[derive(Debug)]
enum Stack {
  Undef,
  Bool(bool),
  Val(LispVal),
  DefMerge,
  Branch(usize, LispVal, Option<usize>),
  PatternPause(Box<[LispVal]>),
  PatternTry(usize, usize),
  Ret,
  MatchCont(usize, usize, LispVal, Rc<Cell<bool>>),
  MapProc1(Span, Box<[Uncons]>),
  MapProc2(Vec<LispVal>),
  MergeMap(Box<MergeMapData>),
  AddThmProc(Box<AwaitingProof>),
  Refine(Span, Vec<RStack>),
  Focus(Span, Vec<LispVal>),
}

impl From<bool> for Stack {
  fn from(v: bool) -> Self { Self::Bool(v) }
}

impl From<LispVal> for Stack {
  fn from(v: LispVal) -> Self { Self::Val(v) }
}

impl Stack {
  fn try_to_lisp(&self) -> Option<LispVal> {
    match *self {
      Self::Undef => Some(LispVal::undef()),
      Self::Bool(b) => Some(LispVal::bool(b)),
      Self::Val(ref e) => Some(e.clone()),
      _ => None,
    }
  }

  fn into_lisp(self) -> LispVal {
    match self {
      Self::Undef => LispVal::undef(),
      Self::Bool(b) => LispVal::bool(b),
      Self::Val(e) => e,
      _ => panic!("stack type error"),
    }
  }

  fn cloned_lisp(&self) -> LispVal {
    match *self {
      Self::Undef => LispVal::undef(),
      Self::Bool(b) => LispVal::bool(b),
      Self::Val(ref e) => e.clone(),
      _ => panic!("stack type error"),
    }
  }

  /// Essentially the same as `clone`,
  /// but `Stack` doesn't implement `Clone` in some of its variants.
  /// Luckily we only need it for lisp values, which are `Clone`.
  fn dup(&self) -> Self {
    match *self {
      Stack::Undef => Stack::Undef,
      Stack::Bool(b) => Stack::Bool(b),
      Stack::Val(ref e) => Stack::Val(e.clone()),
      _ => panic!("stack type error"),
    }
  }
}

impl crate::EnvDisplay for Stack {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Stack::Undef => write!(f, "[#undef]"),
      &Stack::Bool(b) => write!(f, "[{b}]"),
      Stack::Val(e) => e.fmt(fe, f),
      Stack::DefMerge => write!(f, "def-merge"),
      Stack::Branch(n, e, None) => write!(f, "(branch {n} {})", fe.to(e)),
      Stack::Branch(n, e, Some(_)) => write!(f, "(branch-cont {n} {})", fe.to(e)),
      Stack::PatternPause(_) => write!(f, "pattern-pause"),
      &Stack::PatternTry(ok, err) => write!(f, "(pattern-try {ok} {err})"),
      Stack::Ret => write!(f, "ret"),
      Stack::MatchCont(start, n, e, _) => write!(f, "(match-cont {start} {n} {})", fe.to(e)),
      Stack::MapProc1(_, us) => write!(f, "(map-proc-1 {})", fe.to(&**us)),
      Stack::MapProc2(es) => write!(f, "(map-proc-2 {})", fe.to(es)),
      Stack::MergeMap(_) => write!(f, "(merge-map)"),
      Stack::AddThmProc(ap) => write!(f, "(add-thm {})", fe.to(&ap.atom())),
      Stack::Refine(_, rs) => write!(f, "(refine {})", fe.to(rs)),
      Stack::Focus(_, es) => write!(f, "(focus {})", fe.to(es)),
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
      LispKind::Ref(m) => {
        let mut f = Some(f);
        match m.try_get_mut(|e| e.as_map_mut(f.take().expect("impossible"))) {
          Some(r) => (r, None),
          None => m.get(|e| e.make_map_mut(f.take().expect("impossible")))
        }
      }
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

#[derive(Clone, Copy, Debug)]
enum Dot { List(Option<usize>), DottedList }

/// A [`Result`](std::result::Result) type alias for string errors, used by functions that
/// work without an elaboration context.
pub type SResult<T> = std::result::Result<T, String>;

impl Elaborator {
  /// Render a lisp expression using the basic printer, and print it to the front end.
  pub fn print_lisp(&mut self, sp: Span, e: &LispVal) {
    self.report(ElabError::info(sp, format!("{}", self.print(e))))
  }

  /// Parse and evaluate a lisp expression. This is the main entry point.
  pub fn eval_lisp(&mut self, global: bool, e: &SExpr) -> Result<LispVal> {
    self.eval_lisp_doc(global, e, String::new())
  }

  /// Parse and evaluate a lisp expression, with the given doc comment.
  pub fn eval_lisp_doc(&mut self, global: bool, e: &SExpr, doc: String) -> Result<LispVal> {
    let sp = e.span;
    let ir = self.parse_lisp_doc(global, e, doc)?;
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
    let ir = self.parse_refine_lisp(e)?;
    self.evaluate(e.span, &ir)
  }

  /// Evaluate a compiled lisp expression.
  pub fn evaluate<'b>(&'b mut self, sp: Span, ir: &'b [Ir]) -> Result<LispVal> {
    // an easy and common special case
    if let [Ir::Const(e)] = ir { return Ok(e.clone()) }
    Evaluator::new(self, sp, ir).run()
  }

  /// Shorthand to call a lisp function from the top level.
  pub fn call_func(&mut self, sp: Span, f: &LispVal, es: Vec<LispVal>) -> Result<LispVal> {
    let mut eval = Evaluator::new(self, sp, &[]);
    eval.app(false, &(sp, sp), f, es)?;
    eval.run()
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
    self.call_func(sp, &val, es)
  }

  /// Run a merge operation from the top level. This is used during `import` in order to handle
  /// merge operations that occur due to diamond dependencies.
  pub fn apply_merge(&mut self,
    sp: Span, strat: Option<&MergeStrategyInner>, old: LispVal, new: LispVal
  ) -> Result<LispVal> {
    let mut eval = Evaluator::new(self, sp, &[]);
    eval.run_apply_merge(sp, strat, old, new)
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
      LispKind::DottedList(es, r) if es.is_empty() => self.head_err(r),
      LispKind::List(es) |
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

  fn get_proof(&self, t: ThmId, mut heap: Vec<LispVal>) -> LispVal {
    let tdata = &self.thms[t];
    match &tdata.kind {
      ThmKind::Thm(Some(pr)) => {
        let mut ds = Vec::new();
        for e in &pr.heap[heap.len()..] {
          let e = self.proof_node(&[], &heap, &mut Some(&mut ds), &pr.store, e);
          heap.push(e)
        }
        let ret = self.proof_node(&[], &heap, &mut Some(&mut ds), &pr.store, pr.head());
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
          self.spans.insert_if(Some(fsp.span), || ObjectKind::Term(false, t));
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
            let e = self.expr_node(&heap, &mut Some(&mut ds), &v.store, e);
            heap.push(e)
          }
          let ret = self.expr_node(&heap, &mut Some(&mut ds), &v.store, v.head());
          args.push(LispVal::list(ds));
          args.push(ret);
        }
        LispVal::list(args)
      }
      Some(DeclKey::Thm(t)) => {
        if let Some(fsp) = fsp {
          self.spans.insert_if(Some(fsp.span), || ObjectKind::Thm(true, t));
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
              let e = self.expr_node(&heap, &mut None, &tdata.store, e);
              heap.push(e)
            }
            LispVal::list(tdata.hyps.iter().map(|(a, e)| LispVal::list(vec![
              LispVal::atom(a.unwrap_or(AtomId::UNDER)),
              self.expr_node(&heap, &mut None, &tdata.store, e)
            ])).collect::<Vec<_>>())
          },
          self.expr_node(&heap, &mut None, &tdata.store, &tdata.ret)
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

#[derive(Debug)]
struct CallStack<'a> {
  parent_code: &'a [Ir],
  parent_ctx: Vec<LispVal>,
  parent_ip: usize,
  arc: Option<Arc<[Ir]>>,
  span: FileSpan,
  pos: ProcPos,
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
  /// The function currently being evaluated.
  code: &'a [Ir],
  /// The instruction pointer.
  ip: usize,
  /// The file that contains the location we are currently evaluating.
  /// This can change when we call a function.
  file: FileRef,
  /// The span of the statement we were originally asked to evaluate. This does
  /// not change during elaboration, and we use it to avoid reporting spans in random
  /// locations if an error is thrown in "library code".
  orig: FileSpan,
  /// The evaluation stack. This is a structured object containing a stack of continuations
  /// each of which represent a context which awaiting a value from a sub-computation.
  stack: Vec<Stack>,
  call_stack: Vec<CallStack<'a>>,
}
impl<'a> Deref for Evaluator<'a> {
  type Target = Elaborator;
  fn deref(&self) -> &Elaborator { self.elab }
}
impl<'a> DerefMut for Evaluator<'a> {
  fn deref_mut(&mut self) -> &mut Elaborator { self.elab }
}

macro_rules! stack_match {
  (let $pat:pat = $e:expr) => {
    let $pat = $e else { panic!("stack type error") };
  };
  ($x:ident => $e:expr) => {
    if let Stack::$x(x) = $e { x } else { panic!("stack type error") }
  };
}

impl<'a> Evaluator<'a> {
  fn new(elab: &'a mut Elaborator, orig_span: Span, code: &'a [Ir]) -> Evaluator<'a> {
    // println!("new:\n{}", elab.print(&IrList(1, code)));
    let file = elab.path.clone();
    Evaluator {
      elab,
      ctx: vec![],
      file: file.clone(),
      orig: FileSpan { file, span: orig_span },
      code,
      ip: 0,
      stack: vec![],
      call_stack: vec![],
    }
  }

  fn fspan_base(&mut self, sp: Span) -> FileSpan {
    if let Some(frame) = self.call_stack.first() {
      frame.span.clone()
    } else {
      self.fspan(sp)
    }
  }

  fn make_stack_err(&mut self, sp: Option<(Span, bool)>, level: ErrorLevel,
      base: BoxError, err: impl Into<BoxError>) -> ElabError {
    let mut old = sp.map(|(sp, good)| (self.fspan(sp), good, base));
    let mut info = vec![];
    for frame in self.call_stack.iter().rev() {
      let x = match frame.pos {
        ProcPos::Named(_, _, a) => format!("({})", self.data[a].name).into(),
        ProcPos::Unnamed(_) => "[fn]".into(),
        ProcPos::Builtin(p) => format!("({p})").into()
      };
      if let Some((sp, good, base)) = old.take() {
        let (sp, osp) = if good {(sp, frame.span.clone())} else {(frame.span.clone(), sp)};
        info.push((osp, base));
        old = Some((sp, good, x));
      } else {
        old = Some((frame.span.clone(), false, x));
      }
    }
    ElabError {
      pos: try_get_span_from(&self.orig, old.as_ref().map(|(sp, _, _)| sp)),
      level,
      kind: ElabErrorKind::Boxed(err.into(),
        if self.backtrace.active(level) {Some(info)} else {None})
    }
    // if e.level == ErrorLevel::Error { panic!("{}", e.kind.msg()); }
  }

  fn stack_span(&self, mut n: usize) -> Option<FileSpan> {
    for frame in self.call_stack.iter().rev() {
      match n.checked_sub(1) {
        None => return Some(frame.span.clone()),
        Some(i) => n = i
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

  fn add_thm(&mut self, tail: bool, fsp: FileSpan, args: &[LispVal]) -> Result<()> {
    match self.elab.add_thm(fsp.clone(), args)? {
      Ok(()) => { self.stack.push(Stack::Undef); Ok(()) }
      Err((ap, proc)) => {
        let sp = try_get_span(&fsp, &proc);
        self.call(tail, &[Ir::AddThm], None, fsp, ProcPos::Builtin(BuiltinProc::AddThm), vec![]);
        self.stack.push(Stack::AddThmProc(ap));
        self.app(false, &(sp, sp), &proc, vec![])
      }
    }
  }

  fn add_thm_resume(&mut self) -> Result<()> {
    let ret = self.pop_lisp();
    stack_match!(let Some(Stack::AddThmProc(ap)) = self.stack.pop());
    let fsp = &self.call_stack.last().expect("impossible").span;
    ap.finish(self.elab, fsp, ret)?;
    self.stack.push(Stack::Undef);
    Ok(())
  }

  fn merge_map(&mut self,
    sp: Span, strat: MergeStrategy, mut old: LispVal, new: &LispKind
  ) -> Result<Option<LispVal>> {
    new.unwrapped(|e| match e {
      LispKind::Undef => Ok(Some(old)),
      LispKind::AtomMap(newmap) => {
        if newmap.is_empty() { return Ok(Some(old)) }
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
          Ok(Some({
            if old.is_ref() && old.as_map_mut(|m| *m = opt.take().expect("impossible")).is_some() { old }
            else { LispVal::new(LispKind::AtomMap(opt.take().expect("impossible"))) }
          }))
        } else {
          let fsp = self.fspan(sp);
          self.call(false, &[Ir::MergeMap], None, fsp, ProcPos::Builtin(BuiltinProc::MergeMap), vec![]);
          self.stack.push(Stack::MergeMap(Box::new(MergeMapData {
            old, strat, it: todo.into_iter(), map: opt.expect("impossible"), k: None
          })));
          Ok(None)

        }
      }
      _ => Err(self.err(Some((sp, false)), "merge-map: not an atom map"))
    })
  }

  fn merge_map_resume(&mut self) -> Result<()> {
    let ret = self.try_pop_lisp();
    stack_match!(let Some(Stack::MergeMap(data)) = self.stack.last_mut());
    if let (Some(ret), Some(k)) = (ret, data.k.take()) {
      data.map.insert(k, ret);
    }
    let sp = self.call_stack.last().expect("impossible").span.span;
    if let Some((k, oldv, newv)) = data.it.next() {
      data.k = Some(k);
      self.ip -= 1;
      let strat = data.strat.clone();
      self.push_apply_merge(sp, strat.as_deref(), oldv, newv)
    } else {
      let Some(Stack::MergeMap(data)) = self.stack.pop() else { unreachable!() };
      let MergeMapData { mut old, map, .. } = *data;
      let mut opt = Some(map);
      if !old.is_ref() || old.as_map_mut(|m| *m = opt.take().expect("impossible")).is_none() {
        old = LispVal::new(LispKind::AtomMap(opt.take().expect("impossible")))
      }
      self.stack.push(old.into());
      Ok(())
    }
  }

  fn push_merge_map(&mut self,
    sp: Span, strat: MergeStrategy, old: LispVal, new: &LispKind
  ) -> Result<()> {
    if let Some(val) = self.merge_map(sp, strat, old, new)? {
      self.stack.push(val.into())
    }
    Ok(())
  }

  fn apply_merge(&mut self,
    sp: Span, strat: Option<&MergeStrategyInner>, old: LispVal, new: LispVal
  ) -> Result<Option<LispVal>> {
    match strat {
      None => Ok(Some(new)),
      Some(MergeStrategyInner::AtomMap(strat)) =>
        self.merge_map(sp, strat.clone(), old, &new),
      Some(MergeStrategyInner::Custom(f)) => {
        self.app(false, &(sp, sp), f, vec![old, new])?;
        Ok(None)
      }
    }
  }

  fn push_apply_merge(&mut self,
    sp: Span, strat: Option<&MergeStrategyInner>, old: LispVal, new: LispVal
  ) -> Result<()> {
    if let Some(val) = self.apply_merge(sp, strat, old, new)? {
      self.stack.push(val.into())
    }
    Ok(())
  }

  fn run_apply_merge(&mut self,
    sp: Span, strat: Option<&MergeStrategyInner>, old: LispVal, new: LispVal
  ) -> Result<LispVal> {
    if let Some(val) = self.apply_merge(sp, strat, old, new)? {
      Ok(val)
    } else {
      self.run()
    }
  }
}

macro_rules! make_builtins {
  ($self:ident, $tail:ident, $sp1:ident, $sp2:ident, $args:ident,
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
      fn evaluate_builtin(&mut $self, $tail: bool, sp: &(Span, Span), f: BuiltinProc, mut $args: Vec<LispVal>) -> Result<()> {
        macro_rules! print {($sp:expr, $x:expr) => {{
          let msg = $x; $self.info($sp, false, f.to_str(), msg)
        }}}
        let ($sp1, $sp2) = *sp;
        macro_rules! try1 {($x:expr) => {{
          match $x {
            Ok(e) => e,
            Err(s) => return Err($self.make_stack_err(
              Some(($sp1, false)), ErrorLevel::Error, format!("({})", f).into(), s))
          }
        }}}
        let ret = match f { $($(#[$attr])* BuiltinProc::$e => $res),* };
        Ok($self.stack.push(ret))
      }
    }
  }
}

make_builtins! { self, tail, sp1, sp2, args,
  Display: Exact(1) => {
    let s = try1!(self.as_string(&args[0]));
    print!(sp1, String::from_utf8_lossy(&s));
    Stack::Undef
  },
  Error: Exact(1) => {
    let s = try1!(self.as_string(&args[0]));
    try1!(Err(String::from_utf8_lossy(&s)))
  },
  Print: Exact(1) => { print!(sp1, format!("{}", self.print(&args[0]))); Stack::Undef },
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
    Stack::Undef
  },
  Begin: AtLeast(0) => args.last().cloned().map_or(Stack::Undef, Stack::Val),
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
    let last = args.pop().unwrap();
    if !gather(&mut args, &last) {
      try1!(Err(format!("apply: last argument is not a list: {}", self.print(&last))))
    }
    return self.app(tail, &(sp1, sp), &proc, args)
  },
  Add: AtLeast(0) => {
    let mut n: BigInt = 0.into();
    for e in args { n += try1!(self.as_int(&e)) }
    LispVal::number(n).into()
  },
  Mul: AtLeast(0) => {
    let mut n: BigInt = 1.into();
    for e in args { n *= try1!(self.as_int(&e)) }
    LispVal::number(n).into()
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
    }.into()
  },
  Max: AtLeast(1) => {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap()));
    for e in it { n = n.max(try1!(self.as_int(&e)).clone()) }
    LispVal::number(n).into()
  },
  Min: AtLeast(1) => {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap()));
    for e in it { n = n.min(try1!(self.as_int(&e)).clone()) }
    LispVal::number(n).into()
  },
  Sub: AtLeast(1) => if args.len() == 1 {
    LispVal::number(-try1!(self.as_int(&args[0]))).into()
  } else {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap()));
    for e in it { n -= try1!(self.as_int(&e)) }
    LispVal::number(n).into()
  },
  Div: AtLeast(1) => {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap()));
    for e in it {
      let a = try1!(self.as_int(&e));
      if a.is_zero() {n.set_zero()} else {n /= a}
    }
    LispVal::number(n).into()
  },
  Mod: AtLeast(1) => {
    let mut it = args.into_iter();
    let mut n: BigInt = try1!(self.as_int(&it.next().unwrap()));
    for e in it {
      let a = try1!(self.as_int(&e));
      if !a.is_zero() {n %= a}
    }
    LispVal::number(n).into()
  },
  Lt: AtLeast(1) => try1!(self.int_bool_binop(|a, b| a < b, &args)).into(),
  Le: AtLeast(1) => try1!(self.int_bool_binop(|a, b| a <= b, &args)).into(),
  Gt: AtLeast(1) => try1!(self.int_bool_binop(|a, b| a > b, &args)).into(),
  Ge: AtLeast(1) => try1!(self.int_bool_binop(|a, b| a >= b, &args)).into(),
  Eq: AtLeast(1) => try1!(self.int_bool_binop(|a, b| a == b, &args)).into(),
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
    LispVal::number(n).into()
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
    LispVal::number(n).into()
  },
  BAnd: AtLeast(0) => {
    let mut n: BigInt = (-1).into();
    for e in args { n &= try1!(self.as_int(&e)) }
    LispVal::number(n).into()
  },
  BOr: AtLeast(0) => {
    let mut n: BigInt = 0.into();
    for e in args { n |= try1!(self.as_int(&e)) }
    LispVal::number(n).into()
  },
  BXor: AtLeast(0) => {
    let mut n: BigInt = 0.into();
    for e in args { n ^= try1!(self.as_int(&e)) }
    LispVal::number(n).into()
  },
  BNot: AtLeast(0) => {
    let n = if let [e] = &*args {
      try1!(self.as_int(e))
    } else {
      let mut n: BigInt = (-1).into();
      for e in args { n &= try1!(self.as_int(&e)) }
      n
    };
    LispVal::number(!n).into()
  },
  Equal: AtLeast(1) => {
    let (e1, args) = args.split_first().unwrap();
    args.iter().all(|e2| e1 == e2).into()
  },
  ToString: Exact(1) => LispVal::string(self.to_string(&args[0])).into(),
  StringToAtom: Exact(1) => {
    let s = try1!(self.as_string(&args[0]));
    LispVal::atom(self.get_atom(&s)).into()
  },
  StringAppend: AtLeast(0) => {
    let mut out = Vec::new();
    for e in args { out.extend_from_slice(&self.to_string(&e)) }
    LispVal::string(out.into()).into()
  },
  StringLen: Exact(1) => LispVal::number(try1!(self.as_string(&args[0])).len().into()).into(),
  StringNth: Exact(2) => {
    let i: usize = try1!(self.with_int(&args[0],
      |n| n.try_into().map_err(|_| format!("index out of range: {n}"))));
    let s = try1!(self.as_string(&args[1]));
    let c = *try1!(s.get(i).ok_or_else(||
      format!("index out of range: index {i}, length {}", s.len())));
    LispVal::number(c.into()).into()
  },
  Substr: Exact(3) => {
    let start: usize = try1!(self.with_int(&args[0],
      |n| n.try_into().map_err(|_| format!("index out of range: start {n}"))));
    let end: usize = try1!(self.with_int(&args[1],
      |n| n.try_into().map_err(|_| format!("index out of range: end {n}"))));
    if start > end { try1!(Err(format!("start {start} > end {end}"))) }
    let s = try1!(self.as_string(&args[2]));
    if end > s.len() { try1!(Err(format!("index out of range: end {end}, length {}", s.len()))) }
    LispVal::string(ArcString::new(s[start..end].into())).into()
  },
  StringToList: Exact(1) => {
    let s = try1!(self.as_string(&args[0]));
    LispVal::list(s.iter()
      .map(|&c| LispVal::number(c.into()))
      .collect::<Vec<_>>()).into()
  },
  ListToString: Exact(1) => {
    let mut u = Uncons::new(args[0].clone());
    let mut out: Vec<u8> = Vec::with_capacity(u.len());
    for e in &mut u {
      out.push(try1!(self.with_int(&e,
        |n| n.try_into().map_err(|_| format!("character out of range: {n}")))));
    }
    if !u.is_empty() {
      try1!(Err(format!("list->string: not a list: {}", self.print(&args[0]))))
    }
    LispVal::string(out.into()).into()
  },
  Not: AtLeast(0) => (!args.iter().any(|e| e.truthy())).into(),
  And: AtLeast(0) => args.iter().all(|e| e.truthy()).into(),
  Or: AtLeast(0) => args.iter().any(|e| e.truthy()).into(),
  List: AtLeast(0) => LispVal::list(args).into(),
  Cons: AtLeast(0) => match args.len() {
    0 => LispVal::nil(),
    1 => args[0].clone(),
    _ => {
      let r = args.pop().unwrap();
      if r.exactly(0) {LispVal::list(args)}
      else {LispVal::dotted_list(args, r)}
    }
  }.into(),
  Head: Exact(1) => try1!(self.head_err(&args[0])).into(),
  Tail: Exact(1) => try1!(self.tail(&args[0])).into(),
  Nth: Exact(2) => {
    let n = try1!(args[0].as_int(|n| n.to_usize().unwrap_or(usize::MAX))
      .ok_or("expected a number"));
    try1!(self.nth(&args[1], n)).into()
  },
  Map: AtLeast(1) => {
    let mut it = args.into_iter();
    let proc = it.next().unwrap();
    let sp = proc.fspan().map_or(sp2, |fsp| fsp.span);
    if it.as_slice().is_empty() {
      return self.app(tail, &(sp1, sp), &proc, vec![])
    }
    let fsp = self.fspan(sp1);
    self.call(tail, &[Ir::Map], None, fsp, ProcPos::Builtin(BuiltinProc::Map), vec![]);
    self.stack.push(proc.into());
    self.stack.push(Stack::MapProc2(vec![]));
    self.stack.push(Stack::MapProc1(sp1, it.map(Uncons::from).collect()));
    return Ok(())
  },
  IsBool: Exact(1) => args[0].is_bool().into(),
  IsAtom: Exact(1) => args[0].is_atom().into(),
  IsPair: Exact(1) => args[0].at_least(1).into(),
  IsNull: Exact(1) => args[0].exactly(0).into(),
  IsNumber: Exact(1) => args[0].is_int().into(),
  IsString: Exact(1) => args[0].is_string().into(),
  IsProc: Exact(1) => args[0].is_proc().into(),
  IsDef: Exact(1) => args[0].is_def().into(),
  IsRef: Exact(1) => args[0].is_ref().into(),
  NewRef: AtLeast(0) =>
    LispVal::new_ref(args.get(0).cloned().unwrap_or_else(LispVal::undef)).into(),
  GetRef: Exact(1) => try1!(self.as_ref(&args[0], |e| Ok(e.clone()))).into(),
  SetRef: Exact(2) => {
    try1!(self.as_ref(&args[0], |e| {*e = args[1].clone(); Ok(())}));
    Stack::Undef
  },
  SetWeak: Exact(2) => {
    try1!(self.as_lref(&args[0], |e| {e.set_weak(&args[1]); Ok(())}));
    args[1].clone().into()
  },
  CopySpan: Exact(2) => {
    let mut it = args.into_iter();
    match (it.next().unwrap().fspan(), it.next().unwrap()) {
      (Some(sp), e) => e.replace_span(sp),
      (None, e) => e
    }.into()
  },
  StackSpan: Exact(1) => {
    let n = try1!(args[0].as_int(|n| n.to_usize().unwrap_or(usize::MAX)).ok_or("expected a number"));
    match self.stack_span(n) {
      Some(sp) => LispVal::undef().span(sp),
      None => LispVal::undef()
    }.into()
  },
  Async: AtLeast(1) => {
    let proc = args.remove(0);
    let sp = proc.fspan().map_or(sp2, |fsp| fsp.span);
    // TODO: actually async this
    return self.app(tail, &(sp1, sp), &proc, args)
  },
  IsAtomMap: Exact(1) => args[0].is_map().into(),
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
    LispVal::new_ref(LispVal::new(LispKind::AtomMap(m))).into()
  },
  Lookup: AtLeast(2) => {
    match self.as_string_atom(&args[1]) {
      None => Stack::Undef,
      Some(k) => {
        let e = try1!(self.as_map(&args[0], |m| Ok(m.get(&k).cloned())));
        if let Some(e) = e {e} else {
          let v = args.get(2).cloned().unwrap_or_else(LispVal::undef);
          if v.is_proc() {
            let sp = v.fspan().map_or(sp2, |fsp| fsp.span);
            return self.app(tail, &(sp1, sp), &v, vec![])
          }
          v
        }.into()
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
    Stack::Undef
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
    Stack::Undef
  },
  MergeMap: AtLeast(0) => {
    let mut it = args.into_iter();
    if let Some(arg1) = it.next() {
      if let Some(arg2) = it.next() {
        if let Some(arg3) = it.next() {
          if it.next().is_some() {
            try1!(Err("merge-map: expected 0 to 3 arguments"))
          } else { return self.push_merge_map(sp1, arg1.into_merge_strategy(), arg2, &arg3) }
        } else { return self.push_merge_map(sp1, None, arg1, &arg2) }
      } else { LispVal::proc(Proc::MergeMap(arg1.into_merge_strategy())) }
    } else { LispVal::proc(Proc::MergeMap(None)) }.into()
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
    Stack::Undef
  },
  SetStackLimit: Exact(1) => {
    self.stack_limit =
      try1!(args[0].as_int(BigInt::to_usize).ok_or("expected a number"))
        .unwrap_or(usize::MAX);
    Stack::Undef
  },
  IsMVar: Exact(1) => args[0].is_mvar().into(),
  IsGoal: Exact(1) => args[0].is_goal().into(),
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
      Some(fsp)).into()
  },
  PrettyPrint: Exact(1) =>
    LispVal::string(format!("{}", self.format_env().pp(&args[0], 80)).into()).into(),
  NewGoal: Exact(1) => LispVal::goal(self.fspan(sp1), args.pop().unwrap()).into(),
  GoalType: Exact(1) => try1!(args[0].goal_type().ok_or("expected a goal")).into(),
  InferType: Exact(1) => try1!(self.infer_type(sp1, &args[0]).map_err(|e| e.kind.msg())).into(),
  InferSort: Exact(1) => match try1!(self.infer_target(sp1, &args[0]).map_err(|e| e.kind.msg())) {
    InferTarget::Bound(s) | InferTarget::Reg(s) => LispVal::atom(s).into(),
    InferTarget::Unknown | InferTarget::Provable => Stack::Undef,
  },
  GetMVars: AtLeast(0) => LispVal::list(self.lc.mvars.clone()).into(),
  GetGoals: AtLeast(0) => LispVal::list(self.lc.goals.clone()).into(),
  SetGoals: AtLeast(0) => { self.lc.set_goals(args); Stack::Undef },
  SetCloseFn: AtLeast(0) => {
    let e = args.into_iter().next().unwrap_or_default();
    if e.is_def() && !e.is_proc() { try1!(Err("expected a procedure")) }
    self.lc.closer = e;
    Stack::Undef
  },
  LocalCtx: Exact(0) => {
    let args = self.lc.proof_order.iter().map(|a| LispVal::atom(a.0)).collect::<Box<[_]>>();
    LispVal::list(args).into()
  },
  ToExpr: Exact(1) => {
    let rstack = vec![RStack::DeferGoals(mem::take(&mut self.lc.goals))];
    self.stack.push(Stack::Refine(sp1, rstack));
    return self.call_refine(tail,
      RState::RefineExpr {tgt: InferTarget::Unknown, e: args.swap_remove(0)})
  },
  Refine: AtLeast(0) => {
    self.stack.push(Stack::Refine(sp1, vec![]));
    let gs = mem::take(&mut self.lc.goals).into_iter();
    return self.call_refine(tail, RState::Goals { gs, es: args.into_iter(), ret_val: true })
  },
  Have: AtLeast(2) => {
    if args.len() > 3 { try1!(Err("invalid arguments")) }
    let mut args = args.into_iter();
    let xarg = args.next().unwrap();
    try1!(xarg.as_atom().ok_or("expected an atom"));
    let fsp = self.fspan(sp1);
    let x_sp = try_get_span(&fsp, &xarg);
    self.call(tail, &[Ir::Have], None, fsp, ProcPos::Builtin(BuiltinProc::Have), vec![]);
    let mut rstack = vec![RStack::DeferGoals(mem::take(&mut self.lc.goals))];
    let state = match (args.next().unwrap(), args.next()) {
      (p, None) => {
        let fsp = self.fspan(x_sp);
        RState::RefineProof {tgt: self.lc.new_mvar(InferTarget::Unknown, Some(fsp)), p}
      }
      (e, Some(p)) => {
        rstack.push(RStack::Typed(p));
        RState::RefineExpr {tgt: InferTarget::Unknown, e}
      }
    };
    self.stack.push(xarg.into());
    self.stack.push(Stack::Refine(sp1, rstack));
    return self.call_refine(false, state)
  },
  Stat: Exact(0) => { print!(sp1, self.stat()); Stack::Undef },
  GetDecl: Exact(1) => {
    let x = try1!(args[0].as_atom().ok_or("expected an atom"));
    self.get_decl(args[0].fspan(), x).into()
  },
  AddDecl: AtLeast(4) => {
    let fsp = self.fspan_base(sp1);
    match try1!(args[0].as_atom().ok_or("expected an atom")) {
      AtomId::TERM | AtomId::DEF => self.add_term(&fsp, &args[1..])?,
      AtomId::AXIOM | AtomId::THM => return self.add_thm(tail, fsp, &args[1..]),
      e => try1!(Err(format!("invalid declaration type '{}'", self.print(&e))))
    }
    Stack::Undef
  },
  AddTerm: AtLeast(3) => {
    let fsp = self.fspan_base(sp1);
    self.add_term(&fsp, &args)?;
    Stack::Undef
  },
  AddThm: AtLeast(4) => {
    let fsp = self.fspan_base(sp1);
    return self.add_thm(tail, fsp, &args)
  },
  GetDoc: AtLeast(1) => {
    let (k, a) = match args.len() {
      1 => (AtomId::UNDER, &args[0]),
      2 => (try1!(args[0].as_atom().ok_or("expected an atom")), &args[1]),
      _ => try1!(Err("invalid arguments")),
    };
    let a = try1!(a.as_atom().ok_or("expected an atom"));
    let doc = match k {
      AtomId::SORT => self.data[a].sort.and_then(|s| self.sorts[s].doc.as_ref()),
      AtomId::TERM | AtomId::DEF | AtomId::AXIOM | AtomId::THM => {
        self.data[a].decl.and_then(|dk| match dk {
          DeclKey::Term(tid) => self.terms[tid].doc.as_ref(),
          DeclKey::Thm(tid) => self.thms[tid].doc.as_ref(),
        })
      },
      AtomId::LISP => self.data[a].lisp.as_ref().and_then(|data| data.doc.as_ref()),
      AtomId::UNDER => self.data[a].lisp.as_ref().and_then(|data| data.doc.as_ref())
        .or_else(|| self.data[a].decl.and_then(|dk| match dk {
          DeclKey::Term(tid) => self.terms[tid].doc.as_ref(),
          DeclKey::Thm(tid) => self.thms[tid].doc.as_ref(),
        }))
        .or_else(|| self.data[a].sort.and_then(|s| self.sorts[s].doc.as_ref())),
      _ => try1!(Err("invalid arguments")),
    };
    match doc {
      Some(doc) => Stack::Val(LispVal::string(doc.as_bytes().into())),
      None => Stack::Undef
    }
  },
  SetDoc: AtLeast(2) => {
    let (k, args) = match args.len() {
      2 => (AtomId::UNDER, &*args),
      3 => (try1!(args[0].as_atom().ok_or("expected an atom")), &args[1..]),
      _ => try1!(Err("invalid arguments")),
    };
    let a = try1!(args[0].as_atom().ok_or("expected an atom"));
    let val = if args[1].is_def() { Some(try1!(self.as_string(&args[1]))) } else { None };
    let doc = match k {
      AtomId::SORT => self.data[a].sort.map(|s| &mut self.sorts[s].doc),
      AtomId::TERM | AtomId::DEF | AtomId::AXIOM | AtomId::THM => {
        self.data[a].decl.map(|dk| match dk {
          DeclKey::Term(tid) => &mut self.terms[tid].doc,
          DeclKey::Thm(tid) => &mut self.thms[tid].doc,
        })
      },
      AtomId::LISP => self.data[a].lisp.as_mut().map(|data| &mut data.doc),
      AtomId::UNDER => {
        #[allow(clippy::never_loop)] loop {
          let o = self.data[a].lisp.as_mut().map(|data| &mut data.doc);
          if o.is_some() { break o }
          let o = self.data[a].decl.map(|dk| match dk {
            DeclKey::Term(tid) => &mut self.terms[tid].doc,
            DeclKey::Thm(tid) => &mut self.thms[tid].doc,
          });
          if o.is_some() { break o }
          break self.data[a].sort.map(|s| &mut self.sorts[s].doc)
        }
      },
      _ => try1!(Err("invalid arguments")),
    };
    if let Some(doc) = doc {
      *doc = val.map(|val| String::from_utf8_lossy(&val.0).into())
    } else {
      try1!(Err(format!("could not find declaration named {} in namespace {}",
        self.data[a].name, self.data[k].name)))
    }
    Stack::Undef
  },
  NewDummy: AtLeast(1) => {
    if args.len() > 2 { try1!(Err("expected 1 or 2 arguments")) }
    let (x, s) = match args.get(1) {
      None => {
        let mut i = 1;
        let x = loop {
          let a = self.get_atom(format!("_{i}").as_bytes());
          if !self.lc.vars.contains_key(&a) {break a}
          i += 1;
        };
        (x, &args[0])
      }
      Some(s) => (try1!(args[0].as_atom().ok_or("expected an atom")), s)
    };
    let sort = try1!(s.as_atom().and_then(|s| self.data[s].sort).ok_or("expected a sort"));
    self.lc.vars.insert(x, (true, InferSort::Bound { sort, used: false }));
    LispVal::atom(x).into()
  },
  SetReporting: AtLeast(1) => {
    let fe = FormatEnv {source: &self.elab.ast.source, env: &self.elab.env};
    try1!(set_report_mode(fe, &mut self.elab.reporting, &args));
    Stack::Undef
  },
  SetBacktrace: AtLeast(1) => {
    let fe = FormatEnv {source: &self.elab.ast.source, env: &self.elab.env};
    try1!(set_report_mode(fe, &mut self.elab.backtrace, &args));
    Stack::Undef
  },
  CheckProofs: Exact(1) => {
    if let Some(b) = args[0].as_bool() {
      self.options.check_proofs = b;
    } else {try1!(Err("invalid arguments"))}
    Stack::Undef
  },
  WarnUnnecessaryParens: Exact(1) => {
    if let Some(b) = args[0].as_bool() {
      self.options.check_parens = b;
    } else {try1!(Err("invalid arguments"))}
    Stack::Undef
  },
  WarnUnusedVars: Exact(1) => {
    if let Some(b) = args[0].as_bool() {
      self.options.unused_vars = b;
    } else {try1!(Err("invalid arguments"))}
    Stack::Undef
  },
  RefineExtraArgs: AtLeast(2) => {
    if args.len() > 2 {try1!(Err("too many arguments"))}
    args.into_iter().nth(1).unwrap().into()
  },
  EvalString: AtLeast(0) => {
    let fsp = self.fspan(sp1);
    let bytes = self.eval_string(&fsp, &args)?;
    LispVal::string(bytes.into()).into()
  },
  #[cfg(feature = "mmc")]
  MmcInit: Exact(0) => LispVal::proc(Proc::Dyn(
    RefCell::new(Box::new(crate::mmc::Compiler::new(self)))
  )).into(),
}

impl<'a> Evaluator<'a> {
  fn fspan(&self, span: Span) -> FileSpan {
    FileSpan {file: self.file.clone(), span}
  }

  fn try_get_span(&self, fsp: Option<&FileSpan>) -> Span {
    try_get_span_from(&self.orig, fsp)
  }

  #[allow(unused)]
  fn respan(&self, sp: Span) -> Span { self.try_get_span(Some(&self.fspan(sp))) }

  fn pop_lisp(&mut self) -> LispVal {
    self.stack.pop().expect("underflow").into_lisp()
  }

  fn try_pop_lisp(&mut self) -> Option<LispVal> {
    let e = self.stack.pop()?;
    #[allow(clippy::needless_match)] // rust-clippy#8549
    if let Some(e) = e.try_to_lisp() {
      Some(e)
    } else {
      self.stack.push(e);
      None
    }
  }

  fn popn(&mut self, n: usize) -> impl Iterator<Item=Stack> + '_ {
    self.stack.drain(self.stack.len() - n..)
  }

  fn call(&mut self,
    tail: bool,
    code: &'a [Ir],
    arc: Option<Arc<[Ir]>>,
    span: FileSpan,
    pos: ProcPos,
    ctx: Vec<LispVal>,
  ) {
    // if self.check_proofs {
    //   println!("calling (tail = {}):\n{}with:", tail, self.print(&IrList(1, code)));
    //   for (i, e) in ctx.iter().enumerate() {
    //     println!("  x{} = {}", i, self.print(e));
    //   }
    //   println!();
    // }
    if let Some(fsp) = pos.fspan() { self.file = fsp.file.clone() }
    if tail {
      if let Some(frame) = self.call_stack.last_mut() {
        self.code = code;
        self.ctx = ctx;
        self.ip = 0;
        frame.arc = arc;
        frame.span = span;
        frame.pos = pos;
        return
      }
    }
    self.stack.push(Stack::Ret);
    self.call_stack.push(CallStack {
      arc, span, pos,
      parent_code: mem::replace(&mut self.code, code),
      parent_ip: mem::take(&mut self.ip),
      parent_ctx: mem::replace(&mut self.ctx, ctx),
    })
  }

  fn ret(&mut self) {
    let frame = self.call_stack.pop().expect("underflow");
    self.file = frame.span.file;
    self.code = frame.parent_code;
    self.ctx = frame.parent_ctx;
    self.ip = frame.parent_ip;
    // println!("returning to:\n  ip = {}\n{}", self.ip, self.print(&IrList(1, self.code)));
  }

  fn app(&mut self,
    tail: bool, sp: &(Span, Span), func: &LispVal, mut args: Vec<LispVal>
  ) -> Result<()> {
    macro_rules! throw {($sp:expr, $e:expr) => {{
      let err = $e;
      return Err(self.err(Some(($sp, false)), err))
    }}}
    self.heartbeat()?;
    func.unwrapped(|func| {
      let LispKind::Proc(func) = func else { throw!(sp.0, "not a function, cannot apply") };
      let spec = func.spec();
      if !spec.valid(args.len()) { throw!(sp.0, spec.arity_error()) }
      match func {
        &Proc::Builtin(func) => self.evaluate_builtin(tail, sp, func, args)?,
        Proc::Lambda {pos, env, code, ..} => {
          #[allow(clippy::useless_transmute)]
          // Safety: Unfortunately we're fighting the borrow checker here. The problem is that
          // ir is borrowed in the Stack type, with most IR being owned outside the
          // function, but when you apply a lambda, the Proc::LambdaExact constructor
          // stores an Arc to the code to execute, hence it comes under our control,
          // which means that when the temporaries in this block go away, so does
          // ir (which is borrowed from f). We solve the problem by storing an Arc of
          // the IR inside the Ret instruction above, so that it won't get deallocated
          // while in use. Rust doesn't reason about other owners of an Arc though, so...
          let code2 = unsafe { std::mem::transmute::<&[Ir], &[Ir]>(&**code) };
          let fsp = self.fspan(sp.0);
          self.call(tail, code2, Some(code.clone()), fsp, pos.clone(), (**env).into());
          match spec {
            ProcSpec::Exact(_) => self.ctx.extend(args),
            ProcSpec::AtLeast(nargs) => {
              self.ctx.extend(args.drain(..nargs));
              self.ctx.push(LispVal::list(args));
            }
          }
        },
        Proc::MatchCont(valid) => {
          if !valid.get() { throw!(sp.1, "continuation has expired") }
          loop {
            match self.stack.pop() {
              Some(Stack::MatchCont(n, tgt, e, a)) => {
                a.set(false);
                if Rc::ptr_eq(&a, valid) {
                  self.ctx.truncate(n);
                  self.ip = tgt;
                  self.stack.push(e.into());
                  break
                }
              }
              Some(Stack::Ret) => self.ret(),
              Some(_) => {}
              None => throw!(sp.1, "continuation has expired")
            }
          }
        }
        Proc::MergeMap(strat) => {
          let new = args.pop().expect("impossible");
          let old = args.pop().expect("impossible");
          self.push_merge_map(sp.0, strat.clone(), old, &new)?
        }
        Proc::RefineCallback => {
          self.stack.push(Stack::Refine(sp.0, vec![]));
          let p = args.pop().expect("impossible");
          let tgt = match args.pop() {
            None => {
              let fsp = p.fspan().unwrap_or_else(|| self.fspan(sp.0));
              self.lc.new_mvar(InferTarget::Unknown, Some(fsp))
            }
            Some(tgt) if args.is_empty() => tgt,
            Some(_) => throw!(sp.0, "expected two arguments")
          };
          self.call_refine(tail, RState::RefineProof { tgt, p })?
        }
        &Proc::ProofThunk(x, ref m) => {
          let mut g = m.borrow_mut();
          match &*g {
            Ok(e) => self.stack.push(e.clone().into()),
            Err(_) => if let Some(DeclKey::Thm(t)) = self.data[x].decl {
              let Err(heap) = mem::replace(&mut *g, Ok(LispVal::undef())) else { unreachable!() };
              let e = self.get_proof(t, heap.into());
              *g = Ok(e.clone());
              self.stack.push(e.into())
            } else { unreachable!() }
          }
        }
        Proc::Dyn(c) => {
          let sp = self.respan(sp.0);
          let ret = c.borrow_mut().call(self, sp, args)?;
          self.stack.push(ret.into())
        }
      }
      Ok(())
    })
  }

  fn insert_call_refine(&mut self, tail: bool, sp: Span) {
    let fsp = self.fspan(sp);
    self.call(tail, &[Ir::RefineResume], None, fsp,
      ProcPos::Builtin(BuiltinProc::Refine), vec![]);
    if !tail {
      let len = self.stack.len();
      self.stack.swap(len - 1, len - 2);
    }
  }

  fn call_refine(&mut self, tail: bool, state: RState) -> Result<()> {
    let val = self.stack.last_mut().expect("underflow");
    stack_match!(let Stack::Refine(sp, ref mut stack) = *val);
    match self.elab.run_refine(self.orig.span, stack, state) {
      Err(e) => return Err(self.err(Some((e.pos, true)), e.kind.msg())),
      Ok(RefineResult::Ret(e)) => {
        self.elab.lc.clean_mvars();
        *val = Stack::Val(e)
      }
      Ok(RefineResult::RetNone) => {
        self.elab.lc.clean_mvars();
        self.stack.pop();
      }
      Ok(RefineResult::RefineExtraArgs(tgt, e, u)) => {
        let mut args = vec![LispVal::proc(Proc::RefineCallback), tgt.clone(), e];
        for e in u { args.push(e) }
        stack.push(RStack::CoerceTo(tgt));
        self.insert_call_refine(tail, sp);
        match &self.data[AtomId::REFINE_EXTRA_ARGS].lisp {
          None => self.evaluate_builtin(false, &(sp, sp), BuiltinProc::RefineExtraArgs, args)?,
          Some(v) => { let v = v.val.clone(); self.app(false, &(sp, sp), &v, args)? }
        }
      }
      Ok(RefineResult::Proc(tgt, proc)) => {
        self.insert_call_refine(tail, sp);
        self.app(false, &(sp, sp), &proc, vec![LispVal::proc(Proc::RefineCallback), tgt])?
      }
    }
    Ok(())
  }

  fn pattern_match_list(&mut self, e: LispVal, n: usize, dot: Dot) -> Option<()> {
    let mut u = Uncons::from(e);
    let start = self.stack.len();
    for _ in 0..n { self.stack.push(u.next()?.into()) }
    match dot {
      Dot::DottedList => self.stack.push(Stack::Val(u.into())),
      Dot::List(None) if u.exactly(0) => {}
      Dot::List(Some(n)) if u.list_at_least(n) => {}
      Dot::List(_) => return None
    }
    self.stack[start..].reverse();
    Some(())
  }

  fn pattern_match(&mut self, mut vars: Box<[LispVal]>, mut ok: bool) -> Result<()> {
    // let mut stacklen = self.stack.len();
    loop {
      if !ok {
        loop {
          match self.stack.pop().expect("stack type error") {
            Stack::PatternTry(_, tgt) => { self.ip = tgt; ok = true; break }
            Stack::Branch(tgt, e, _) => {
              self.ip = tgt; self.stack.push(e.into());
              return Ok(())
            }
            _ => {}
          }
        }
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
      //   println!();
      //   // let mut calls = self.call_stack.iter().rev();
      //   for e in &self.stack {
      //     println!("stack: {}", self.print(e));
      //     // if let Stack::Ret = e {
      //     //   let call = calls.next().expect("missing");
      //     //   print!("  ip = {}\n{}", call.parent_ip, self.print(&IrList(1, call.parent_code)))
      //     // }
      //   }

      //   print!("> [{}, {}] {}: ", self.stack.len(), self.ctx.len(), self.ip);
      //   match self.code.get(self.ip) {
      //     Some(ir) => println!("{}\n", self.print(ir)),
      //     None => println!("ret\n"),
      //   }
      // }
      let e = match self.stack.pop() {
        Some(Stack::Undef) => LispVal::undef(),
        Some(Stack::Bool(b)) => LispVal::bool(b),
        Some(Stack::Val(e)) => e,
        Some(Stack::PatternTry(tgt, _)) => { self.ip = tgt; continue }
        Some(Stack::Branch(tgt, e, cont)) => {
          if ok {
            self.ctx.extend(vars.into_vec());
            if let Some(n) = cont {
              assert!(self.ctx.len() == n);
              let valid = Rc::new(Cell::new(true));
              self.ctx.push(LispVal::proc(Proc::MatchCont(valid.clone())));
              self.stack.push(Stack::MatchCont(n, tgt, e, valid));
            }
          } else {
            self.ip = tgt; self.stack.push(e.into())
          }
          return Ok(())
        }
        _ => panic!("stack type error"),
      };
      ok = match *self.code.get(self.ip).expect("returning in pattern mode") {
        Ir::Dup => { self.stack.push(e.clone().into()); self.stack.push(e.into()); true }
        Ir::PatternResult(b) => b,
        Ir::PatternAtom(i) => { vars[i] = e; true },
        Ir::PatternQuoteAtom(a) => e.unwrapped(|e|
          if let LispKind::Atom(a2) = *e {a == a2} else {false}),
        Ir::PatternString(ref s) => e.unwrapped(|e|
          if let LispKind::String(s2) = e {s == s2} else {false}),
        Ir::PatternBool(b) => e.unwrapped(|e|
          if let LispKind::Bool(b2) = *e {b == b2} else {false}),
        Ir::PatternUndef => e.unwrapped(|e| *e == LispKind::Undef),
        Ir::PatternNumber(ref i) => e.unwrapped(|e|
          if let LispKind::Number(i2) = e {i == i2} else {false}),
        Ir::PatternMVar(p) => e.unwrapped(|e| match e {
          LispKind::MVar(_, is) => match (p, is) {
            (MVarPattern::Any, _) |
            (MVarPattern::Unknown, InferTarget::Unknown | InferTarget::Provable) => true,
            (MVarPattern::Unknown, _) |
            (MVarPattern::Simple, InferTarget::Unknown | InferTarget::Provable) => false,
            (MVarPattern::Simple, &(InferTarget::Bound(s) | InferTarget::Reg(s))) => {
              self.stack.push(is.bound().into());
              self.stack.push(LispVal::atom(s).into());
              true
            }
          }
          _ => false,
        }),
        Ir::PatternGoal => e.unwrapped(|e| match e {
          LispKind::Goal(e) => { self.stack.push(e.clone().into()); true }
          _ => false
        }),
        Ir::PatternDottedList(n) => self.pattern_match_list(e, n, Dot::DottedList).is_some(),
        Ir::PatternList(n, dot) => self.pattern_match_list(e, n, Dot::List(dot)).is_some(),
        Ir::PatternTry(tgt1, tgt2) => {
          self.stack.push(Stack::PatternTry(tgt1, tgt2));
          self.stack.push(e.into());
          true
        }
        Ir::PatternTestPause => {
          self.ip += 1;
          self.stack.push(e.clone().into());
          self.stack.push(Stack::PatternPause(vars));
          self.stack.push(e.into());
          return Ok(())
        }
        Ir::PatternQExprAtom(a) => e.unwrapped(|e| match e {
          &LispKind::Atom(a2) => a == a2,
          LispKind::List(es) if es.len() == 1 =>
            es[0].unwrapped(|e| if let LispKind::Atom(a2) = *e {a == a2} else {false}),
          _ => false
        }),

        // Listing the instructions explicitly so that we get missing match arm errors
        Ir::Drop(_) | Ir::DropAbove(_) | Ir::Undef | Ir::AssertScope(_) | Ir::EndScope(_) |
        Ir::Local(_) | Ir::Global(..) | Ir::Const(_) | Ir::List(..) | Ir::DottedList(_) |
        Ir::App(..) | Ir::BuiltinApp(..) | Ir::AppHead(_) | Ir::JumpUnless(_) | Ir::Jump(_) |
        Ir::ArityError(..) | Ir::FocusStart(_) | Ir::RefineGoal(_) | Ir::FocusFinish |
        Ir::SetMergeStrategy(..) | Ir::LocalDef(_) | Ir::GlobalDef(..) | Ir::SetDoc(..) |
        Ir::Lambda(..) | Ir::Branch(..) | Ir::TestPatternResume | Ir::BranchFail(_) |
        Ir::Map | Ir::Have | Ir::RefineResume | Ir::AddThm | Ir::MergeMap
        => panic!("unexpected in pattern mode"),
      };
      self.ip += 1;
    }
  }

  fn heartbeat(&mut self) -> Result<()> {
    // self.iters = self.iters.wrapping_add(1);
    if self.cur_timeout.map_or(false, |t| t < Instant::now()) {
      return Err(self.err(None, "timeout"))
    }
    if self.cancel.load(Ordering::Relaxed) {
      return Err(self.err(None, "cancelled"))
    }
    if self.stack.len() >= self.stack_limit {
      return Err(self.err(None, "stack overflow"))
    }
    Ok(())
  }

  fn dotted_list(&mut self, n: usize) {
    let dot = self.pop_lisp();
    let args = self.popn(n).map(Stack::into_lisp);
    let ret = match dot.try_unwrap() {
      Ok(LispKind::List(es)) =>
        LispVal::list(args.chain(es.into_vec()).collect::<Box<[_]>>()),
      Ok(LispKind::DottedList(es, e)) =>
        LispVal::dotted_list(args.chain(es.into_vec()).collect::<Box<[_]>>(), e),
      Ok(e) => LispVal::dotted_list(args.collect::<Box<[_]>>(), LispVal::new(e)),
      Err(ret) => LispVal::dotted_list(args.collect::<Box<[_]>>(), ret),
    };
    self.stack.push(ret.into())
  }

  fn focus_finish(&mut self) -> Result<()> {
    macro_rules! throw {($sp:expr, $e:expr) => {{
      let err = $e;
      return Err(self.err(Some(($sp, false)), err))
    }}}
    let mut ir = self.stack.pop().expect("underflow");
    let mut close = true;
    loop {
      if let Stack::Focus(sp, gs) = ir {
        if close {
          if self.lc.closer.is_def() {
            self.ip -= 1;
            self.stack.push(Stack::Focus(sp, gs));
            self.app(false, &(sp, sp), &self.lc.closer.clone(), vec![])?;
            break
          } else if !self.lc.goals.is_empty() {
            let stat = self.stat();
            self.call_goal_listener(&stat);
            let span = self.fspan(sp);
            for g in mem::take(&mut self.lc.goals) {
              let err = ElabError::new_e(try_get_span(&span, &g), format!("|- {}",
                self.format_env().pp(&g.goal_type().expect("expected a goal"), 80)));
              self.report(err)
            }
            throw!(sp, format!("focused goal has not been solved\n\n{stat}"))
          }
        }
        self.lc.set_goals(gs);
        self.stack.push(Stack::Undef);
        break
      }
      ir = self.stack.pop().expect("underflow");
      close = false;
    }
    Ok(())
  }

  fn global_def(&mut self, sp1: Span, sp2: Span, a: AtomId) -> Result<()> {
    let ret = self.pop_lisp();
    if matches!(self.stack.last(), Some(Stack::DefMerge)) {
      self.stack.pop();
    } else if let Some(LispData {merge: strat @ Some(_), val, ..}) =
      &mut self.data[a].lisp
    {
      let (strat, old) = (strat.clone(), val.clone());
      self.ip -= 1;
      self.stack.push(Stack::DefMerge);
      self.push_apply_merge(sp1, strat.as_deref(), old, ret)?;
      return Ok(())
    }
    let loc = (self.fspan(sp2), sp1);
    let env = &mut self.env;
    match (&mut env.data[a].lisp, ret.is_def_strict()) {
      (l @ None, true) => {
        env.stmts.push(StmtTrace::Global(a));
        *l = Some(LispData {src: Some(loc), doc: None, val: ret, merge: None})
      }
      (Some(LispData {val, ..}), true) => *val = ret,
      (l, false) => if l.is_some() {
        env.data[a].graveyard = Some(Box::new(loc));
      }
    }
    Ok(())
  }

  fn lambda(&mut self, name: u8, &(sp, spec, ref code): &(Span, ProcSpec, Arc<[Ir]>)) {
    let pos = if name == u8::MAX {
      ProcPos::Unnamed(self.fspan(sp))
    } else {
      let Ir::GlobalDef(span, full, x) = self.code[self.ip + usize::from(name)]
      else { unreachable!() };
      ProcPos::Named(self.fspan(full), span, x)
    };
    self.stack.push(LispVal::proc(Proc::Lambda {
      pos,
      env: self.ctx.clone().into(),
      spec,
      code: code.clone(),
    }).into())
  }

  fn map(&mut self) -> Result<()> {
    if let Some(e) = self.try_pop_lisp() {
      let len = self.stack.len();
      stack_match!(MapProc2 => &mut self.stack[len - 2]).push(e)
    }
    let len = self.stack.len();
    let func = self.stack[len - 3].cloned_lisp();
    stack_match!(let Some(&mut Stack::MapProc1(sp, ref mut us)) = self.stack.last_mut());
    let mut it = us.iter_mut();
    let u0 = it.next().expect("impossible");
    if let Some(e0) = u0.next() {
      let mut args = vec![e0];
      for u in it {
        if let Some(e) = u.next() { args.push(e) }
        else { return Err(self.err(Some((sp, false)), "mismatched input length")) }
      }
      self.ip -= 1;
      self.app(false, &(sp, sp), &func, args)?
    } else {
      if !(u0.exactly(0) && it.all(|u| u.exactly(0))) {
        return Err(self.err(Some((sp, false)), "mismatched input length"))
      }
      self.stack.pop();
      stack_match!(let Some(Stack::MapProc2(args)) = self.stack.pop());
      *self.stack.last_mut().expect("underflow") = LispVal::list(args).into()
    }
    Ok(())
  }

  fn have(&mut self) -> Result<()> {
    let ret = self.pop_lisp();
    let x = self.pop_lisp();
    let a = x.as_atom().expect("checked");
    let fsp = &self.call_stack.last().expect("impossible").span;
    let e = self.elab.infer_type(fsp.span, &ret)?;
    let span = try_get_span(fsp, &x);
    self.elab.lc.add_proof(a, e, ret);
    if span != fsp.span {
      self.spans.insert_if(Some(span), || ObjectKind::Hyp(true, a));
    }
    self.stack.push(Stack::Undef);
    Ok(())
  }

  fn refine_goal(&mut self, ret_val: bool) -> Result<()> {
    match self.stack.pop().expect("underflow") {
      Stack::Undef => if ret_val { self.stack.push(Stack::Undef) }
      Stack::Val(e) if !e.is_def() => if ret_val { self.stack.push(Stack::Undef) }
      e => {
        let e = e.into_lisp();
        let esp = self.try_get_span(e.fspan().as_ref());
        self.stack.push(Stack::Refine(esp, vec![]));
        let gs = mem::take(&mut self.lc.goals).into_iter();
        let es = vec![e].into_iter();
        self.call_refine(false, RState::Goals { gs, es, ret_val })?
      }
    }
    Ok(())
  }

  #[inline] fn global_var(&mut self, sp: Span, a: AtomId) -> Result<()> {
    match &self.data[a] {
      AtomData {name, lisp: None, ..} => match BuiltinProc::from_bytes(name) {
        None => {
          let err = format!("Reference to unbound variable '{name}'");
          return Err(self.err(Some((sp, false)), err))
        },
        Some(p) => {
          let s = name.clone();
          let a = self.get_atom(&s);
          let ret = LispVal::proc(Proc::Builtin(p));
          self.data[a].lisp =
            Some(LispData {src: None, doc: None, val: ret.clone(), merge: None});
          self.stack.push(ret.into())
        }
      },
      AtomData {lisp: Some(x), ..} => {
        let ret = x.val.clone();
        self.stack.push(ret.into())
      }
    }
    Ok(())
  }

  #[allow(clippy::never_loop, clippy::many_single_char_names)]
  fn run(&mut self) -> Result<LispVal> {
    macro_rules! throw {($sp:expr, $e:expr) => {{
      let err = $e;
      return Err(self.err(Some(($sp, false)), err))
    }}}

    // let mut stacklen = 0;
    loop {
      // if self.options.check_proofs {
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
      //   println!();
      //   // // let mut calls = self.call_stack.iter().rev();
      //   // for e in &self.stack {
      //   //   println!("stack: {}", self.print(e));
      //   //   // if let Stack::Ret = e {
      //   //   //   let call = calls.next().expect("missing");
      //   //   //   print!("  ip = {}\n{}", call.parent_ip, self.print(&IrList(1, call.parent_code)))
      //   //   // }
      //   // }

      //   print!("[{}, {}] {}: ", self.stack.len(), self.ctx.len(), self.ip);
      //   match self.code.get(self.ip) {
      //     Some(ir) => println!("{}\n", self.print(ir)),
      //     None => println!("ret\n"),
      //   }
      // }
      if let Some(ir) = self.code.get(self.ip) {
        self.ip += 1;
        match *ir {
          Ir::Drop(n) => self.stack.truncate(self.stack.len() - n),
          Ir::DropAbove(n) => {
            let s = self.stack.pop().expect("underflow");
            self.stack.truncate(self.stack.len() - n);
            self.stack.push(s);
          }
          Ir::Undef => self.stack.push(Stack::Undef),
          Ir::Dup => self.stack.push(self.stack.last().expect("underflow").dup()),
          Ir::AssertScope(n) => assert!(self.ctx.len() == n),
          Ir::EndScope(n) => self.ctx.truncate(n),
          Ir::Local(i) => self.stack.push(self.ctx[i].clone().into()),
          Ir::Global(sp, a) => self.global_var(sp, a)?,
          Ir::Const(ref val) => self.stack.push(val.clone().into()),
          Ir::List(sp, n) => {
            let args = self.popn(n).map(Stack::into_lisp).collect::<Box<[_]>>();
            self.stack.push(LispVal::list(args).span(self.fspan(sp)).into())
          }
          Ir::DottedList(n) => self.dotted_list(n),
          Ir::App(tail, ref sp, n) => {
            let args = self.popn(n).map(Stack::into_lisp).collect();
            let func = self.pop_lisp();
            self.app(tail, sp, &func, args)?
          }
          Ir::BuiltinApp(tail, func, ref sp, n) => {
            debug_assert!(func.spec().valid(n));
            let args = self.popn(n).map(Stack::into_lisp).collect();
            self.heartbeat()?;
            self.evaluate_builtin(tail, sp, func, args)?
          }
          Ir::ArityError(sp, spec) => throw!(sp, spec.arity_error()),
          Ir::AppHead(sp) => {
            let func = self.pop_lisp();
            let e = self.pop_lisp();
            self.app(false, &(sp, sp), &func, vec![e])?
          }
          Ir::JumpUnless(tgt) => match self.stack.pop().expect("underflow") {
            Stack::Bool(true) => {}
            Stack::Val(e) if e.truthy() => {}
            _ => self.ip = tgt
          }
          Ir::Jump(tgt) => self.ip = tgt,
          Ir::FocusStart(sp) => {
            if self.lc.goals.is_empty() { throw!(sp, "no goals") }
            let gs = self.lc.goals.drain(1..).collect();
            self.stack.push(Stack::Focus(sp, gs));
          }
          Ir::FocusFinish => self.focus_finish()?,
          Ir::SetMergeStrategy(sp, a) => if let Some(ref mut data) = self.elab.data[a].lisp {
            data.merge = self.stack.pop().expect("underflow").into_lisp().into_merge_strategy()
          } else {
            throw!(sp, format!("unknown definition '{}', cannot set merge strategy",
              self.print(&a)))
          }
          Ir::LocalDef(n) => {
            assert!(self.ctx.len() == n);
            let ret = self.pop_lisp();
            self.ctx.push(ret);
          }
          Ir::GlobalDef(sp1, sp2, a) => self.global_def(sp1, sp2, a)?,
          Ir::SetDoc(ref doc, a) => if let Some(data) = &mut self.data[a].lisp {
            if data.val.is_def_strict() { data.doc = Some(doc.clone()) }
          }
          Ir::Lambda(sp, ref args) => self.lambda(sp, args),
          Ir::Branch(vars, next, cont) => {
            let e = self.pop_lisp();
            self.stack.push(Stack::Branch(next, e.clone(), cont));
            self.stack.push(e.into());
            self.pattern_match(vec![LispVal::undef(); vars].into(), true)?
          }
          Ir::TestPatternResume => {
            let ok = self.pop_lisp().truthy();
            stack_match!(let Some(Stack::PatternPause(vars)) = self.stack.pop());
            self.pattern_match(vars, ok)?
          }
          Ir::BranchFail(sp) => {
            let e = self.pop_lisp();
            throw!(sp, format!("match failed: {}", self.print(&e)))
          }

          Ir::Map => self.map()?,
          Ir::Have => self.have()?,
          Ir::RefineResume => {
            let ret = self.pop_lisp();
            self.call_refine(true, RState::Ret(ret))?
          }
          Ir::RefineGoal(ret_val) => self.refine_goal(ret_val)?,
          Ir::AddThm => self.add_thm_resume()?,
          Ir::MergeMap => self.merge_map_resume()?,

          // Listing the instructions explicitly so that we get missing match arm errors
          Ir::PatternResult(_) | Ir::PatternAtom(_) | Ir::PatternQuoteAtom(_) |
          Ir::PatternString(_) | Ir::PatternBool(_) | Ir::PatternUndef |
          Ir::PatternNumber(_) | Ir::PatternMVar(_) | Ir::PatternGoal |
          Ir::PatternDottedList(_) | Ir::PatternList(_, _) | Ir::PatternTry(_, _) |
          Ir::PatternTestPause | Ir::PatternQExprAtom(_)
          => panic!("not in pattern mode"),
        }
      } else {
        let e = self.try_pop_lisp();
        match self.stack.pop() {
          Some(Stack::Ret) => {
            self.ret();
            if let Some(e) = e { self.stack.push(e.into()) }
          }
          Some(_) => panic!("stack type error"),
          None => return Ok(e.expect("stack type error"))
        }
      }
    }
  }
}
