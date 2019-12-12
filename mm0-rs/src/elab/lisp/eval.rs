use std::ops::Deref;
use std::mem;
use std::borrow::Cow;
use std::sync::{Arc, atomic::{AtomicBool, Ordering}};
use crate::util::*;
use super::super::{Result, AtomID, FileServer, Elaborator, ElabError, BoxError};
use super::*;
use super::parser::{IR, Branch, Pattern};

enum Stack<'a> {
  List(Vec<LispVal>, std::slice::Iter<'a, IR>),
  DottedList(Vec<LispVal>, std::slice::Iter<'a, IR>, &'a IR),
  DottedList2(Vec<LispVal>),
  App(Span, Span, &'a [IR]),
  App2(Span, Span, LispVal, Vec<LispVal>, std::slice::Iter<'a, IR>),
  If(&'a IR, &'a IR),
  Def(&'a Option<(Span, AtomID)>),
  Eval(std::slice::Iter<'a, IR>),
  Match(Span, std::slice::Iter<'a, Branch>),
  TestPattern(Span, LispVal, std::slice::Iter<'a, Branch>,
    &'a Branch, Vec<PatternStack<'a>>, Box<[LispVal]>),
  Drop_,
  Ret(ProcPos, Vec<LispVal>, Arc<IR>),
  MatchCont(Span, LispVal, std::slice::Iter<'a, Branch>, Arc<AtomicBool>),
}

impl Stack<'_> {
  fn supports_def(&self) -> bool {
    match self {
      Stack::App2(_, _, _, _, _) => true,
      Stack::Eval(_) => true,
      _ => false,
    }
  }
}
enum State<'a> {
  Eval(&'a IR),
  Ret(LispVal),
  List(Vec<LispVal>, std::slice::Iter<'a, IR>),
  DottedList(Vec<LispVal>, std::slice::Iter<'a, IR>, &'a IR),
  App(Span, Span, LispVal, Vec<LispVal>, std::slice::Iter<'a, IR>),
  Match(Span, LispVal, std::slice::Iter<'a, Branch>),
  Pattern(Span, LispVal, std::slice::Iter<'a, Branch>,
    &'a Branch, Vec<PatternStack<'a>>, Box<[LispVal]>, PatternState<'a>),
}

fn unref(e: &LispVal) -> Cow<LispVal> {
  let mut ret = Cow::Borrowed(e);
  while let LispKind::Ref(m) = &**ret {
    let e = m.lock().unwrap().clone();
    ret = Cow::Owned(e)
  }
  ret
}
fn truthy(e: &LispKind) -> bool {
  if let LispKind::Bool(false) = e {false} else {true}
}

#[derive(Clone)]
struct Uncons(LispVal, usize);
impl Uncons {
  fn from(e: &LispVal) -> Uncons { Uncons(unref(e).into_owned(), 0) }
  fn exactly(&self, n: usize) -> bool {
    match &*self.0 {
      LispKind::List(es) => self.1 + n == es.len(),
      LispKind::DottedList(es, _) if self.1 + n <= es.len() => false,
      LispKind::DottedList(es, r) => Self::from(r).exactly(n - es.len()),
      _ => false,
    }
  }
  fn is_list(&self) -> bool {
    match &*self.0 {
      LispKind::List(_) => true,
      LispKind::DottedList(_, r) => Self::from(r).is_list(),
      _ => false,
    }
  }
  fn at_least(&self, n: usize) -> bool {
    match &*self.0 {
      LispKind::List(es) => return self.1 + n == es.len(),
      LispKind::DottedList(es, r) if self.1 + n <= es.len() => Self::from(r).is_list(),
      LispKind::DottedList(es, r) => Self::from(r).at_least(n - es.len()),
      _ => false,
    }
  }
  fn uncons(&mut self) -> Option<LispVal> {
    loop {
      match &*self.0 {
        LispKind::List(es) => match es.get(self.1) {
          None => return None,
          Some(e) => {self.1 += 1; return Some(e.clone())}
        },
        LispKind::DottedList(es, r) => match es.get(self.1) {
          None => *self = Self::from(r),
          Some(e) => {self.1 += 1; return Some(e.clone())}
        }
        _ => return None
      }
    }
  }
  fn as_lisp(self) -> LispVal {
    if self.1 == 0 {return self.0}
    match &*self.0 {
      LispKind::List(es) if self.1 == es.len() => NIL.clone(),
      LispKind::List(es) => Arc::new(LispKind::List(es[self.1..].into())),
      LispKind::DottedList(es, r) if self.1 == es.len() => r.clone(),
      LispKind::DottedList(es, r) => Arc::new(LispKind::DottedList(es[self.1..].into(), r.clone())),
      _ => unreachable!()
    }
  }
}

enum Dot<'a> { List(Option<usize>), DottedList(&'a Pattern) }
enum PatternStack<'a> {
  List(Uncons, std::slice::Iter<'a, Pattern>, Dot<'a>),
  Binary(bool, bool, LispVal, std::slice::Iter<'a, Pattern>),
}

enum PatternState<'a> {
  Eval(&'a Pattern, LispVal),
  Ret(bool),
  List(Uncons, std::slice::Iter<'a, Pattern>, Dot<'a>),
  Binary(bool, bool, LispVal, std::slice::Iter<'a, Pattern>),
}

struct TestPending(Span, usize);

impl<'a, T: FileServer + ?Sized> Elaborator<'a, T> {
  fn pattern_match<'b>(&mut self, stack: &mut Vec<PatternStack<'b>>, ctx: &mut [LispVal],
      mut active: PatternState<'b>) -> std::result::Result<bool, TestPending> {
    loop {
      active = match active {
        PatternState::Eval(p, e) => match p {
          Pattern::Skip => PatternState::Ret(true),
          &Pattern::Atom(i) => {ctx[i] = e; PatternState::Ret(true)}
          &Pattern::QuoteAtom(a) => PatternState::Ret(
            match &**unref(&e) {&LispKind::Atom(a2) => a == a2, _ => false}),
          Pattern::String(s) => PatternState::Ret(
            match &**unref(&e) {LispKind::String(s2) => s.deref() == s2, _ => false}),
          &Pattern::Bool(b) => PatternState::Ret(
            match &**unref(&e) {&LispKind::Bool(b2) => b == b2, _ => false}),
          Pattern::Number(i) => PatternState::Ret(
            match &**unref(&e) {LispKind::Number(i2) => i == i2, _ => false}),
          &Pattern::QExprAtom(a) => PatternState::Ret(match &**unref(&e) {
            &LispKind::Atom(a2) => a == a2,
            LispKind::List(es) if es.len() == 1 => match &**unref(&es[0]) {
              &LispKind::Atom(a2) => a == a2,
              _ => false
            },
            _ => false
          }),
          Pattern::DottedList(ps, r) => PatternState::List(Uncons::from(&e), ps.iter(), Dot::DottedList(r)),
          &Pattern::List(ref ps, n) => PatternState::List(Uncons::from(&e), ps.iter(), Dot::List(n)),
          Pattern::And(ps) => PatternState::Binary(false, false, e, ps.iter()),
          Pattern::Or(ps) => PatternState::Binary(true, true, e, ps.iter()),
          Pattern::Not(ps) => PatternState::Binary(true, false, e, ps.iter()),
          &Pattern::Test(sp, i, ref ps) => {
            stack.push(PatternStack::Binary(false, false, e, ps.iter()));
            return Err(TestPending(sp, i))
          },
        },
        PatternState::Ret(b) => match stack.pop() {
          None => return Ok(b),
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
          Some(p) => match u.uncons() {
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

impl<'a, T: FileServer + ?Sized> Elaborator<'a, T> {
  fn throw_err(&mut self, stack: Vec<Stack>, mut fspan: FileSpan, e: impl Into<BoxError>) -> ElabError {
    let mut msg: BoxError = "error occurred here".into();
    let mut info = vec![];
    for s in stack.into_iter().rev() {
      if let Stack::Ret(pos, _, _) = s {
        let (fsp, x) = match pos {
          ProcPos::Named(fsp, a) => (fsp, format!("{}()", self.lisp_ctx[a].0).into()),
          ProcPos::Unnamed(fsp) => (fsp, "[fn]".into())
        };
        info.push((mem::replace(&mut fspan, fsp), mem::replace(&mut msg, x)))
      }
    }
    ElabError::with_info(fspan.span, e.into(), info)
  }

  pub fn print_lisp(&mut self, sp: Span, e: &LispVal) -> Result<()> {
    Ok(self.errors.push(ElabError::info(sp, format!("{}", self.printer(e)))))
  }

  pub fn evaluate<'b>(&'b mut self, ir: &'b IR) -> Result<LispVal> {
    self.evaluate_core(vec![], State::Eval(ir))
  }

  pub fn call_func(&mut self, sp: Span, f: LispVal, es: Vec<LispVal>) -> Result<LispVal> {
    self.evaluate_core(vec![], State::App(sp, sp, f, es, [].iter()))
  }

  pub fn call_overridable(&mut self, sp: Span, p: BuiltinProc, es: Vec<LispVal>) -> Result<LispVal> {
    let a = self.get_atom(p.to_str());
    let val = match &self.lisp_ctx[a].1 {
      Some((_, e)) => e.clone(),
      None => Arc::new(LispKind::Proc(Proc::Builtin(p)))
    };
    self.call_func(sp, val, es)
  }

  fn evaluate_core<'b>(&'b mut self, mut ctx: Vec<LispVal>, mut active: State<'b>) -> Result<LispVal> {
    let mut file = self.path.clone();
    let mut stack: Vec<Stack> = vec![];

    macro_rules! fsp {($e:expr) => {FileSpan {file: file.clone(), span: $e}}}
    macro_rules! throw {($sp:expr, $e:expr) => {{
      let err = $e;
      return Err(self.throw_err(stack, FileSpan {file, span: $sp}, err))
    }}}
    macro_rules! proc_pos {($sp:expr) => {
      if let Some(Stack::Def(&Some((sp, x)))) = stack.last() { ProcPos::Named(fsp!(sp), x) }
      else { ProcPos::Unnamed(fsp!($sp)) }
    }}

    loop {
      active = match active {
        State::Eval(ir) => match ir {
          &IR::Local(i) => State::Ret(ctx[i].clone()),
          &IR::Global(sp, a) => State::Ret(match &self.lisp_ctx[a] {
            (s, None) => match BuiltinProc::from_str(s) {
              None => throw!(sp, format!("Reference to unbound variable '{}'", s)),
              Some(p) => {
                let s = s.clone();
                let a = self.get_atom(&s);
                let ret = Arc::new(LispKind::Proc(Proc::Builtin(p)));
                self.lisp_ctx[a].1 = Some((None, ret.clone()));
                ret
              }
            },
            (_, Some((_, x))) => x.clone(),
          }),
          IR::Const(val) => State::Ret(val.clone()),
          IR::List(ls) => State::List(vec![], ls.iter()),
          IR::DottedList(ls, e) => State::DottedList(vec![], ls.iter(), e),
          IR::App(sp1, sp2, f, es) => {stack.push(Stack::App(*sp1, *sp2, es)); State::Eval(f)}
          IR::If(e) => {stack.push(Stack::If(&e.1, &e.2)); State::Eval(&e.0)}
          IR::Focus(es) => unimplemented!(),
          IR::Def(x, val) => {stack.push(Stack::Def(x)); State::Eval(val)}
          IR::Eval(es) => {
            let mut it = es.iter();
            match it.next() {
              None => State::Ret(UNDEF.clone()),
              Some(e) => { stack.push(Stack::Eval(it)); State::Eval(e) }
            }
          }
          &IR::Lambda(sp, spec, ref e) =>
            State::Ret(Arc::new(LispKind::Proc(Proc::Lambda {
              pos: proc_pos!(sp),
              env: ctx.clone(),
              spec,
              code: e.clone()
            }))),
          &IR::Match(sp, ref e, ref brs) => {stack.push(Stack::Match(sp, brs.iter())); State::Eval(e)}
        },
        State::Ret(ret) => match stack.pop() {
          None => return Ok(ret),
          Some(Stack::List(mut vec, it)) => { vec.push(ret); State::List(vec, it) }
          Some(Stack::DottedList(mut vec, it, e)) => { vec.push(ret); State::DottedList(vec, it, e) }
          Some(Stack::DottedList2(vec)) if vec.is_empty() => State::Ret(ret),
          Some(Stack::DottedList2(mut vec)) => State::Ret(Arc::new(match Arc::try_unwrap(ret) {
            Ok(LispKind::List(es)) => { vec.extend(es); LispKind::List(vec) }
            Ok(LispKind::DottedList(es, e)) => { vec.extend(es); LispKind::DottedList(vec, e) }
            Ok(e) => LispKind::DottedList(vec, Arc::new(e)),
            Err(ret) => LispKind::DottedList(vec, ret),
          })),
          Some(Stack::App(sp1, sp2, es)) => State::App(sp1, sp2, ret, vec![], es.iter()),
          Some(Stack::App2(sp1, sp2, f, mut vec, it)) => { vec.push(ret); State::App(sp1, sp2, f, vec, it) }
          Some(Stack::If(e1, e2)) => State::Eval(if truthy(&unref(&ret)) {e1} else {e2}),
          Some(Stack::Def(x)) => {
            match stack.pop() {
              None => if let &Some((sp, a)) = x {
                self.lisp_ctx[a].1 = Some((Some(fsp!(sp)), ret))
              },
              Some(s) if s.supports_def() => {
                stack.push(Stack::Drop_); stack.push(s); ctx.push(ret) }
              Some(s) => stack.push(s),
            }
            State::Ret(UNDEF.clone())
          }
          Some(Stack::Eval(mut it)) => match it.next() {
            None => State::Ret(ret),
            Some(e) => { stack.push(Stack::Eval(it)); State::Eval(e) }
          },
          Some(Stack::Match(sp, it)) => State::Match(sp, ret, it),
          Some(Stack::TestPattern(sp, e, it, br, pstack, vars)) =>
            State::Pattern(sp, e, it, br, pstack, vars, PatternState::Ret(truthy(&unref(&ret)))),
          Some(Stack::Drop_) => {ctx.pop(); State::Ret(ret)}
          Some(Stack::Ret(pos, old, _)) => {file = pos.fspan().file.clone(); ctx = old; State::Ret(ret)}
          Some(Stack::MatchCont(_, _, _, valid)) => {
            if let Err(valid) = Arc::try_unwrap(valid) {valid.store(false, Ordering::Relaxed)}
            State::Ret(ret)
          }
        },
        State::List(vec, mut it) => match it.next() {
          None => State::Ret(Arc::new(LispKind::List(vec))),
          Some(e) => { stack.push(Stack::List(vec, it)); State::Eval(e) }
        },
        State::DottedList(vec, mut it, r) => match it.next() {
          None => { stack.push(Stack::DottedList2(vec)); State::Eval(r) }
          Some(e) => { stack.push(Stack::DottedList(vec, it, r)); State::Eval(e) }
        },
        State::App(sp1, sp2, f, mut args, mut it) => match it.next() {
          None => match &**unref(&f) {
            LispKind::Proc(Proc::Builtin(p)) => match p {
              BuiltinProc::NewRef if args.len() != 1 =>
                throw!(sp2, "called with incorrect number of arguments"),
              BuiltinProc::NewRef => State::Ret(Arc::new(LispKind::Ref(Mutex::new(args[0].clone())))),
              BuiltinProc::SetRef if args.len() != 2 =>
                throw!(sp2, "called with incorrect number of arguments"),
              BuiltinProc::SetRef => {
                if let LispKind::Ref(m) = &*args[0] {*m.lock().unwrap() = args[1].clone()}
                else {throw!(sp2, "set!: not a ref")}
                State::Ret(UNDEF.clone())
              },
            }
            &LispKind::Proc(Proc::Lambda {ref pos, ref env, spec, ref code}) => {
              if !spec.valid(args.len()) {throw!(sp2, "called with incorrect number of arguments")}
              if let Some(Stack::Ret(_, _, _)) = stack.last() { // tail call
                if let Some(Stack::Ret(fsp, old, _)) = stack.pop() {
                  ctx = env.clone();
                  stack.push(Stack::Ret(fsp, old, code.clone()));
                } else {unsafe {std::hint::unreachable_unchecked()}}
              } else {
                stack.push(Stack::Ret(pos.clone(), mem::replace(&mut ctx, env.clone()), code.clone()));
              }
              match spec {
                ProcSpec::Exact(_) => ctx.extend(args),
                ProcSpec::AtLeast(nargs) => {
                  ctx.extend(args.drain(..nargs));
                  ctx.push(Arc::new(LispKind::List(args)));
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
            LispKind::Proc(Proc::MatchCont(valid)) => {
              if !valid.load(Ordering::Relaxed) {throw!(sp2, "continuation has expired")}
              loop {
                match stack.pop() {
                  Some(Stack::MatchCont(span, expr, it, a)) => {
                    a.store(false, Ordering::Relaxed);
                    if Arc::ptr_eq(&a, &valid) {
                      break State::Match(span, expr, it)
                    }
                  }
                  Some(Stack::Drop_) => {ctx.pop();}
                  Some(Stack::Ret(pos, old, _)) => {file = pos.into_fspan().file; ctx = old},
                  Some(_) => {}
                  None => throw!(sp2, "continuation has expired")
                }
              }
            }
            _ => throw!(sp2, "not a function, cannot apply")
          },
          Some(e) => { stack.push(Stack::App2(sp1, sp2, f, args, it)); State::Eval(e) }
        }
        State::Match(sp, e, mut it) => match it.next() {
          None => throw!(sp, "match failed"),
          Some(br) =>
            State::Pattern(sp, e.clone(), it, br, vec![], vec![UNDEF.clone(); br.vars].into(),
              PatternState::Eval(&br.pat, e))
        },
        State::Pattern(sp, e, it, br, mut pstack, mut vars, st) => {
          match self.pattern_match(&mut pstack, &mut vars, st) {
            Ok(false) => State::Match(sp, e, it),
            Ok(true) => {
              ctx.extend_from_slice(&vars);
              if br.cont {
                let valid = Arc::new(AtomicBool::new(true));
                ctx.push(Arc::new(LispKind::Proc(Proc::MatchCont(valid.clone()))));
                stack.push(Stack::MatchCont(sp, e.clone(), it, valid));
                stack.push(Stack::Drop_);
              }
              stack.resize_with(stack.len() + vars.len(), || Stack::Drop_);
              State::Eval(&br.eval)
            },
            Err(TestPending(sp, i)) => {
              stack.push(Stack::TestPattern(sp, e.clone(), it, br, pstack, vars));
              State::App(sp, sp, ctx[i].clone(), vec![e], [].iter())
            }
          }
        }
      }
    }
  }
}