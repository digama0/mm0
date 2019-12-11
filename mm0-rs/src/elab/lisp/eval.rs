use std::ops::{Deref, DerefMut};
use std::mem;
use std::sync::Arc;
use crate::util::*;
use super::super::{Result, AtomID, FileServer, Elaborator, ElabError, BoxError};
use super::*;
use super::parser::{IR, Branch, Pattern};

struct Evaluator<'a, T: FileServer + ?Sized> {
  elab: &'a mut Evaluator<'a, T>,
  ctx: Vec<LispVal>,
}
impl<'a, T: FileServer + ?Sized> Deref for Evaluator<'a, T> {
  type Target = Elaborator<'a, T>;
  fn deref(&self) -> &Elaborator<'a, T> { self.elab }
}
impl<'a, T: FileServer + ?Sized> DerefMut for Evaluator<'a, T> {
  fn deref_mut(&mut self) -> &mut Elaborator<'a, T> { self.elab }
}

enum Stack<'a> {
  List(Vec<LispVal>, std::slice::Iter<'a, IR>),
  DottedList(Vec<LispVal>, std::slice::Iter<'a, IR>, &'a IR),
  DottedList2(Vec<LispVal>),
  App(Span, Span, &'a [IR]),
  App2(Span, Span, LispVal, Vec<LispVal>, std::slice::Iter<'a, IR>),
  If(&'a IR, &'a IR),
  Def(&'a Option<(Span, AtomID)>),
  Eval(std::slice::Iter<'a, IR>),
  Match(Span, &'a Arc<[Branch]>, usize),
  Drop_,
  Call(Vec<LispVal>),
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
}

fn stack_e(stack: Vec<Stack>, pos: impl Into<Span>, e: impl Into<BoxError>) -> ElabError {
  unimplemented!()
}

fn unreffed<T>(e: &LispVal, f: impl FnOnce(&LispVal) -> T) -> T {
  if let LispKind::Ref(m) = e.deref() { unreffed(&m.lock().unwrap(), f) }
  else {f(e)}
}

fn unref(e: &LispVal) -> LispVal {
  if let LispKind::Ref(m) = e.deref() { unref(&m.lock().unwrap()) }
  else {e.clone()}
}
fn truthy(e: &LispKind) -> bool {
  if let LispKind::Bool(false) = e {false} else {true}
}

#[derive(Clone)]
struct Uncons(LispVal, usize);
impl Uncons {
  fn from(e: &LispVal) -> Uncons { Uncons(unref(e), 0) }
  fn exactly(&self, n: usize) -> bool {
    match self.0.deref() {
      LispKind::List(es) => self.1 + n == es.len(),
      LispKind::DottedList(es, r) if self.1 + n <= es.len() => false,
      LispKind::DottedList(es, r) => Self::from(r).exactly(n - es.len()),
      _ => false,
    }
  }
  fn is_list(&self) -> bool {
    match self.0.deref() {
      LispKind::List(_) => true,
      LispKind::DottedList(_, r) => Self::from(r).is_list(),
      _ => false,
    }
  }
  fn at_least(&self, n: usize) -> bool {
    match self.0.deref() {
      LispKind::List(es) => return self.1 + n == es.len(),
      LispKind::DottedList(es, r) if self.1 + n <= es.len() => Self::from(r).is_list(),
      LispKind::DottedList(es, r) => Self::from(r).at_least(n - es.len()),
      _ => false,
    }
  }
  fn uncons(&mut self) -> Option<LispVal> {
    loop {
      match self.0.deref() {
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
    match self.0.deref() {
      LispKind::List(es) if self.1 == es.len() => NIL.clone(),
      LispKind::List(es) => Arc::new(LispKind::List(es[self.1..].into())),
      LispKind::DottedList(es, r) if self.1 == es.len() => r.clone(),
      LispKind::DottedList(es, r) => Arc::new(LispKind::DottedList(es[self.1..].into(), r.clone())),
      _ => unreachable!()
    }
  }
}

impl Pattern {
  fn match_(&self, ctx: &mut [LispVal], e: &LispVal) -> bool {
    match self {
      Pattern::Skip => true,
      &Pattern::Atom(i) => {ctx[i] = e.clone(); true}
      &Pattern::QuoteAtom(a) => match &*unref(e) {&LispKind::Atom(a2) => a == a2, _ => false},
      Pattern::String(s) => match &*unref(e) {LispKind::String(s2) => s.deref() == s2, _ => false},
      &Pattern::Bool(b) => match &*unref(e) {&LispKind::Bool(b2) => b == b2, _ => false},
      Pattern::Number(i) => match &*unref(e) {LispKind::Number(i2) => i == i2, _ => false},
      Pattern::DottedList(ps, r) => {
        let mut u = Uncons::from(e);
        ps.iter().all(|p| u.uncons().map_or(false, |l| p.match_(ctx, &l))) &&
          self.match_(ctx, &u.as_lisp())
      }
      &Pattern::ListAtLeast(ref ps, n) => {
        let mut u = Uncons::from(e);
        ps.iter().all(|p| u.uncons().map_or(false, |l| p.match_(ctx, &l))) && u.at_least(n)
      }
      Pattern::ListExact(ps) => {
        let mut u = Uncons::from(e);
        ps.iter().all(|p| u.uncons().map_or(false, |l| p.match_(ctx, &l))) && u.exactly(0)
      }
      Pattern::And(ps) => ps.iter().all(|p| p.match_(ctx, e)),
      Pattern::Or(ps) => ps.iter().any(|p| p.match_(ctx, e)),
      Pattern::Not(ps) => !ps.iter().any(|p| p.match_(ctx, e)),
      &Pattern::Test(i, ref ps) => unimplemented!(),
      &Pattern::QExprAtom(a) => match &*unref(e) {
        &LispKind::Atom(a2) => a == a2,
        LispKind::List(es) if es.len() == 1 => match &*unref(&es[0]) {
          &LispKind::Atom(a2) => a == a2,
          _ => false
        },
        _ => false
      }
    }
  }
}
impl Branch {
  fn match_(&self, ctx: &mut Vec<LispVal>,
       sp: Span, e: &LispVal, brs: &Arc<[Branch]>, i: usize) -> Option<usize> {
    let start = ctx.len();
    ctx.resize_with(start + self.vars.len(), || UNDEF.clone());
    if !self.pat.match_(&mut ctx[start..], e) {
      ctx.truncate(start); return None
    }
    if self.cont.is_some() {
      ctx.push(Arc::new(LispKind::Proc(Proc::MatchCont(
        sp, ctx[..start].into(), e.clone(), brs.clone(), i))));
    }
    Some(ctx.len() - start)
  }
}

impl<'a, T: FileServer + ?Sized> Evaluator<'a, T> {
  pub fn evaluate(&mut self, ir: &IR) -> Result<LispVal> {
    let mut ctx: Vec<LispVal> = Vec::new();
    let mut stack: Vec<Stack> = vec![];
    let mut active = State::Eval(ir);

    loop {
      active = match active {
        State::Eval(ir) => match ir {
          &IR::Local(i) => State::Ret(self.ctx[i].clone()),
          &IR::Global(sp, a) => State::Ret(match &self.lisp_ctx[a] {
            (s, None) => return Err(stack_e(stack, sp,
              format!("Reference to unbound variable '{}'", s))),
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
          &IR::LambdaExact(sp, ref xs, ref e) =>
            State::Ret(Arc::new(LispKind::Proc(
              Proc::LambdaExact(sp, ctx.clone(), xs.len(), e.clone())))),
          &IR::LambdaAtLeast(sp, ref xs, _, ref e) =>
            State::Ret(Arc::new(LispKind::Proc(
              Proc::LambdaAtLeast(sp, ctx.clone(), xs.len(), e.clone())))),
          &IR::Match(sp, ref e, ref brs) => {stack.push(Stack::Match(sp, brs, 0)); State::Eval(e)}
          &IR::MatchFn(sp, ref brs) =>
            State::Ret(Arc::new(LispKind::Proc(Proc::LambdaExact(sp, ctx.clone(), 1,
              Arc::new(IR::Match(sp, Box::new(IR::Local(ctx.len())), brs.clone())))))),
          &IR::MatchFns(sp, ref brs) =>
            State::Ret(Arc::new(LispKind::Proc(Proc::LambdaAtLeast(sp, ctx.clone(), 0,
              Arc::new(IR::Match(sp, Box::new(IR::Local(ctx.len())), brs.clone())))))),
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
                self.lisp_ctx[a].1 = Some((self.fspan(sp), ret))
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
          Some(Stack::Match(sp, brs, mut i)) => loop {
            match brs.get(i) {
              None => return Err(stack_e(stack, sp, "match failed")),
              Some(br) => if let Some(n) = br.match_(&mut ctx, sp, &ret, &brs, i + 1) {
                stack.resize_with(stack.len() + n, || Stack::Drop_);
                break State::Eval(&br.eval)
              },
            }
            i += 1;
          }
          Some(Stack::Drop_) => {ctx.pop(); State::Ret(ret)}
          Some(Stack::Call(ctx2)) => {ctx = ctx2; State::Ret(ret)}
        },
        State::List(vec, mut it) => match it.next() {
          None => State::Ret(Arc::new(LispKind::List(vec))),
          Some(e) => { stack.push(Stack::List(vec, it)); State::Eval(e) }
        },
        State::DottedList(vec, mut it, r) => match it.next() {
          None => { stack.push(Stack::DottedList2(vec)); State::Eval(r) }
          Some(e) => { stack.push(Stack::DottedList(vec, it, r)); State::Eval(e) }
        },
        State::App(sp1, sp2, f, vec, mut it) => match it.next() {
          None => {
            if let LispKind::Proc(p) = &*unref(&f) {
              match p {
                Proc::Builtin(_) => unimplemented!(),
                &Proc::LambdaExact(sp, ref ctx2, n, ref ir) => {
                  if vec.len() != n {
                    return Err(stack_e(stack, sp2, "called with incorrect number of arguments"))
                  }
                  stack.push(Stack::Call(mem::replace(&mut ctx, ctx2.clone())));
                  ctx.extend(vec);
                  // State::Eval(ir)
                  unimplemented!()
                },
                &Proc::LambdaAtLeast(sp, ref ctx2, n, ref ir) => {
                  stack.push(Stack::Call(mem::replace(&mut ctx, ctx2.clone())));
                  unimplemented!()
                },
                Proc::MatchCont(sp, ref ctx2, ref e, ref brs, i) => {
                  stack.push(Stack::Call(mem::replace(&mut ctx, ctx2.clone())));
                  unimplemented!()
                },
              }
            } else {return Err(stack_e(stack, sp2, "not a function, cannot apply"))}
          }
          Some(e) => { stack.push(Stack::App2(sp1, sp2, f, vec, it)); State::Eval(e) }
        },
      }
    }
  }
}