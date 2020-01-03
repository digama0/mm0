use std::ops::{Deref, DerefMut};
use std::sync::Arc;
use std::collections::HashMap;
use num::{BigInt, ToPrimitive};
use itertools::Itertools;
use crate::parser::ast::{SExpr, SExprKind, Atom};
use crate::util::ArcString;
use super::super::{AtomID, Span, Elaborator, ElabError, ObjectKind};
use super::*;
use super::super::math_parser::{QExpr, QExprKind};
use super::print::{FormatEnv, EnvDisplay};

#[derive(Debug)]
pub enum IR {
  Local(usize),
  Global(Span, AtomID),
  Const(LispVal),
  List(Span, Box<[IR]>),
  DottedList(Box<[IR]>, Box<IR>),
  App(Span, Span, Box<IR>, Box<[IR]>),
  If(Box<(IR, IR, IR)>),
  Focus(Span, Box<[IR]>),
  Def(usize, Option<(Span, AtomID)>, Box<IR>),
  Eval(bool, Box<[IR]>),
  Lambda(Span, usize, ProcSpec, Arc<IR>),
  Match(Span, Box<IR>, Box<[Branch]>),
}

impl<'a> EnvDisplay for IR {
  fn fmt(&self, fe: FormatEnv, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      &IR::Local(i) => write!(f, "x{}", i),
      &IR::Global(_, a) => a.fmt(fe, f),
      IR::Const(e) => e.fmt(fe, f),
      IR::List(_, es) => write!(f, "(list {})", es.iter().map(|ir| fe.to(ir)).format(" ")),
      IR::DottedList(es, r) => write!(f, "(cons {})",
        es.iter().chain(Some(&**r)).map(|ir| fe.to(ir)).format(" ")),
      IR::App(_, _, e, es) => write!(f, "({})",
        Some(&**e).into_iter().chain(&**es).map(|ir| fe.to(ir)).format(" ")),
      IR::If(es) => write!(f, "(if {} {} {})",
        fe.to(&es.0), fe.to(&es.1), fe.to(&es.2)),
      IR::Focus(_, es) => write!(f, "(focus {})", es.iter().map(|ir| fe.to(ir)).format(" ")),
      IR::Def(n, a, e) => write!(f, "(def {}:{} {})",
        n, fe.to(&a.map_or(AtomID::UNDER, |a| a.1)), fe.to(e)),
      IR::Eval(false, es) => write!(f, "(def _ {})", es.iter().map(|ir| fe.to(ir)).format(" ")),
      IR::Eval(true, es) => write!(f, "(begin {})", es.iter().map(|ir| fe.to(ir)).format(" ")),
      IR::Lambda(_, n, sp, e) => {
        write!(f, "(lambda {}:", n)?;
        match sp {
          ProcSpec::Exact(n) => write!(f, "{}", n)?,
          ProcSpec::AtLeast(n) => write!(f, "{}+", n)?,
        }
        write!(f, " {})", fe.to(e))
      }
      IR::Match(_, e, bs) => write!(f, "(match {} {})", fe.to(e), fe.to(&**bs))
    }
  }
}

impl IR {
  fn eval(es: impl Into<Box<[IR]>>) -> IR {
    let es: Box<[IR]> = es.into();
    match es.len() {
      0 => IR::Const(LispVal::undef()),
      1 => es.into_vec().swap_remove(0),
      _ => IR::Eval(true, es)
    }
  }

  fn builtin_app(sp1: Span, sp2: Span, f: BuiltinProc, es: Box<[IR]>) -> IR {
    IR::App(sp1, sp2, Box::new(IR::Const(LispVal::proc(Proc::Builtin(f)))), es)
  }

  fn new_ref(sp1: Span, sp2: Span, e: IR) -> IR {
    IR::builtin_app(sp1, sp2, BuiltinProc::NewRef, Box::new([e]))
  }
  fn set_ref(sp1: Span, sp2: Span, e1: IR, e2: IR) -> IR {
    IR::builtin_app(sp1, sp2, BuiltinProc::SetRef, Box::new([e1, e2]))
  }
  fn match_fn_body(sp: Span, i: usize, brs: Box<[Branch]>) -> IR {
    IR::Match(sp, Box::new(IR::Local(i)), brs)
  }
  pub fn span(&self) -> Option<Span> {
    match self {
      &IR::Global(sp, _) |
      &IR::List(sp, _) |
      &IR::App(sp, _, _, _) |
      &IR::Focus(sp, _) |
      &IR::Lambda(sp, _, _, _) |
      &IR::Match(sp, _, _) => Some(sp),
      _ => None
    }
  }
}

#[derive(Debug)]
pub struct Branch {
  pub vars: usize,
  pub cont: bool,
  pub pat: Pattern,
  pub eval: Box<IR>,
}

impl<'a> EnvDisplay for Branch {
  fn fmt(&self, fe: FormatEnv, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    if self.cont {
      write!(f, "[{} (=> _) {}]", fe.to(&self.pat), fe.to(&self.eval))
    } else {
      write!(f, "[{} {}]", fe.to(&self.pat), fe.to(&self.eval))
    }
  }
}

#[derive(Debug)]
pub enum Pattern {
  Skip,
  Atom(usize),
  QuoteAtom(AtomID),
  String(ArcString),
  Bool(bool),
  Number(BigInt),
  MVar(Option<Box<(Pattern, Pattern)>>),
  Goal(Box<Pattern>),
  DottedList(Box<[Pattern]>, Box<Pattern>),
  List(Box<[Pattern]>, Option<usize>),
  And(Box<[Pattern]>),
  Or(Box<[Pattern]>),
  Not(Box<[Pattern]>),
  Test(Span, Box<IR>, Box<[Pattern]>),
  QExprAtom(AtomID),
}

impl<'a> EnvDisplay for Pattern {
  fn fmt(&self, fe: FormatEnv, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match self {
      &Pattern::Skip => write!(f, "_"),
      &Pattern::Atom(i) => write!(f, "x{}", i),
      Pattern::QuoteAtom(a) => write!(f, "'{}", fe.to(a)),
      Pattern::String(s) => write!(f, "{:?}", s),
      Pattern::Bool(true) => write!(f, "#t"),
      Pattern::Bool(false) => write!(f, "#f"),
      Pattern::Number(n) => write!(f, "{}", n),
      Pattern::MVar(None) => write!(f, "(mvar)"),
      Pattern::MVar(Some(p)) => write!(f, "(mvar {} {})", fe.to(&p.0), fe.to(&p.1)),
      Pattern::Goal(p) => write!(f, "(goal {})", fe.to(p)),
      Pattern::DottedList(es, r) => write!(f, "({} . {})",
        es.iter().map(|ir| fe.to(ir)).format(" "), fe.to(r)),
      Pattern::List(es, None) => write!(f, "({})",
        es.iter().map(|ir| fe.to(ir)).format(" ")),
      Pattern::List(es, Some(0)) => write!(f, "({} ...)",
        es.iter().map(|ir| fe.to(ir)).format(" ")),
      Pattern::List(es, Some(n)) => write!(f, "({} __ {})",
        es.iter().map(|ir| fe.to(ir)).format(" "), n),
      Pattern::And(es) => write!(f, "(and {})", es.iter().map(|ir| fe.to(ir)).format(" ")),
      Pattern::Or(es) => write!(f, "(or {})", es.iter().map(|ir| fe.to(ir)).format(" ")),
      Pattern::Not(es) => write!(f, "(not {})", es.iter().map(|ir| fe.to(ir)).format(" ")),
      Pattern::Test(_, ir, p) => write!(f, "(? {} {})", fe.to(&**ir), fe.to(&**p)),
      Pattern::QExprAtom(a) => write!(f, "${}$", fe.to(a)),
    }
  }
}

impl Remap<LispRemapper> for IR {
  fn remap(&self, r: &mut LispRemapper) -> Self {
    match self {
      &IR::Local(i) => IR::Local(i),
      &IR::Global(sp, a) => IR::Global(sp, a.remap(r)),
      IR::Const(v) => IR::Const(v.remap(r)),
      IR::List(sp, v) => IR::List(*sp, v.remap(r)),
      IR::DottedList(v, e) => IR::DottedList(v.remap(r), e.remap(r)),
      &IR::App(s, t, ref e, ref es) => IR::App(s, t, e.remap(r), es.remap(r)),
      IR::If(e) => IR::If(e.remap(r)),
      IR::Focus(sp, e) => IR::Focus(*sp, e.remap(r)),
      &IR::Def(n, a, ref e) => IR::Def(n, a.map(|(sp, a)| (sp, a.remap(r))), e.remap(r)),
      &IR::Eval(b, ref e) => IR::Eval(b, e.remap(r)),
      &IR::Lambda(sp, n, spec, ref e) => IR::Lambda(sp, n, spec, e.remap(r)),
      &IR::Match(sp, ref e, ref br) => IR::Match(sp, e.remap(r), br.remap(r)),
    }
  }
}

impl Remap<LispRemapper> for Branch {
  fn remap(&self, r: &mut LispRemapper) -> Self {
    Self {
      vars: self.vars,
      cont: self.cont,
      pat: self.pat.remap(r),
      eval: self.eval.remap(r)
    }
  }
}

impl Remap<LispRemapper> for Pattern {
  fn remap(&self, r: &mut LispRemapper) -> Self {
    match self {
      Pattern::Skip => Pattern::Skip,
      &Pattern::Atom(i) => Pattern::Atom(i),
      Pattern::QuoteAtom(a) => Pattern::QuoteAtom(a.remap(r)),
      Pattern::String(s) => Pattern::String(s.clone()),
      &Pattern::Bool(b) => Pattern::Bool(b),
      Pattern::Number(i) => Pattern::Number(i.clone()),
      Pattern::MVar(p) => Pattern::MVar(p.remap(r)),
      Pattern::Goal(p) => Pattern::Goal(p.remap(r)),
      Pattern::DottedList(v, e) => Pattern::DottedList(v.remap(r), e.remap(r)),
      &Pattern::List(ref es, n) => Pattern::List(es.remap(r), n),
      Pattern::And(es) => Pattern::And(es.remap(r)),
      Pattern::Or(es) => Pattern::Or(es.remap(r)),
      Pattern::Not(es) => Pattern::Not(es.remap(r)),
      &Pattern::Test(sp, ref ir, ref es) => Pattern::Test(sp, ir.remap(r), es.remap(r)),
      Pattern::QExprAtom(a) => Pattern::QExprAtom(a.remap(r)),
    }
  }
}

impl IR {
  fn unconst(cs: Vec<IR>) -> Result<Vec<LispVal>, Vec<IR>> {
    if cs.iter().all(|c| if let IR::Const(_) = c {true} else {false}) {
      Ok(cs.into_iter().map(|c|
        if let IR::Const(v) = c {v}
        else {unsafe {std::hint::unreachable_unchecked()}}).collect())
    } else {Err(cs)}
  }
  fn list(fsp: FileSpan, cs: Vec<IR>) -> IR {
    match IR::unconst(cs) {
      Ok(es) => IR::Const(LispVal::list(es).span(fsp)),
      Err(cs) => IR::List(fsp.span, cs.into())
    }
  }
  fn dotted_list(sp: Span, mut cs: Vec<IR>, c: IR) -> IR {
    if cs.is_empty() {return c}
    match c {
      IR::Const(e) => match e.deref() {
        LispKind::List(es) => {
          cs.extend(es.iter().map(|e| IR::Const(e.clone())));
          IR::List(sp, cs.into())
        }
        LispKind::DottedList(es, e) => {
          cs.extend(es.iter().map(|e| IR::Const(e.clone())));
          IR::DottedList(cs.into(), Box::new(IR::Const(e.clone())))
        }
        _ => match IR::unconst(cs) {
          Ok(es) => IR::Const(LispVal::dotted_list(es, e)),
          Err(cs) => IR::DottedList(cs.into(), Box::new(IR::Const(e)))
        }
      },
      IR::List(_, cs2) => {
        cs.extend(cs2.into_vec());
        IR::List(sp, cs.into())
      }
      IR::DottedList(cs2, c) => {
        cs.extend(cs2.into_vec());
        IR::DottedList(cs.into(), c)
      }
      _ => IR::DottedList(cs.into(), Box::new(c))
    }
  }
}

struct LocalCtx {
  names: HashMap<AtomID, Vec<usize>>,
  ctx: Vec<AtomID>,
}

impl LocalCtx {
  fn new() -> Self { Self {names: HashMap::new(), ctx: vec![]} }
  fn len(&self) -> usize { self.ctx.len() }
  fn get(&self, x: AtomID) -> Option<usize> {
    self.names.get(&x).and_then(|v| v.last().cloned())
  }
  fn push(&mut self, x: AtomID) -> usize {
    let old = self.ctx.len();
    if x != AtomID::UNDER { self.names.entry(x).or_insert(vec![]).push(old) }
    self.ctx.push(x);
    old
  }
  fn push_list(&mut self, xs: &Vec<AtomID>) -> usize {
    let old = self.ctx.len();
    for &x in xs { self.push(x); }
    old
  }
  fn get_or_push(&mut self, x: AtomID) -> usize {
    self.get(x).unwrap_or_else(|| self.push(x))
  }

  fn pop(&mut self) {
    let x = self.ctx.pop().unwrap();
    if x != AtomID::UNDER {self.names.get_mut(&x).unwrap().pop();}
  }
  fn restore(&mut self, n: usize) {
    while self.ctx.len() > n { self.pop() }
  }
}

struct LispParser<'a> {
  elab: &'a mut Elaborator,
  ctx: LocalCtx,
}
impl<'a> Deref for LispParser<'a> {
  type Target = Elaborator;
  fn deref(&self) -> &Elaborator { self.elab }
}
impl<'a> DerefMut for LispParser<'a> {
  fn deref_mut(&mut self) -> &mut Elaborator { self.elab }
}

enum Item<'a> {
  List(&'a [SExpr]),
  DottedList(&'a [SExpr], &'a SExpr),
}

impl<'a> LispParser<'a> {
  fn def_var<'c>(&mut self, mut e: &'c SExpr) -> Result<(Span, AtomID, Vec<Item<'c>>), ElabError> {
    let mut stack = vec![];
    loop {
      match &e.k {
        &SExprKind::Atom(a) => break Ok((e.span, self.parse_ident(e.span, a)?, stack)),
        SExprKind::List(xs) if !xs.is_empty() =>
          {stack.push(Item::List(&xs[1..])); e = &xs[0]}
        SExprKind::DottedList(xs, y) if !xs.is_empty() =>
          {stack.push(Item::DottedList(&xs[1..], y)); e = &xs[0]}
        _ => Err(ElabError::new_e(e.span, "def: invalid spec"))?
      }
    }
  }

  fn def_ir(&mut self, sp: Span, es: &[SExpr], stack: Vec<Item>) -> Result<Vec<IR>, ElabError> {
    for e in stack.iter().rev() {
      match e {
        Item::List(xs) => {
          let xs = self.to_idents(xs)?;
          self.ctx.push_list(&xs);
        }
        Item::DottedList(xs, y) => {
          let xs = self.to_idents(xs)?;
          self.ctx.push_list(&xs);
          let y = self.to_ident(y)?;
          self.ctx.push(y);
        }
      }
    }
    let mut len = self.ctx.len();
    let mut ir = self.exprs(false, es)?;
    for e in stack {
      ir = match e {
        Item::List(xs) => {
          len -= xs.len();
          vec![IR::Lambda(sp, len, ProcSpec::Exact(xs.len()), IR::eval(ir).into())]
        }
        Item::DottedList(xs, _) => {
          len -= xs.len() + 1;
          vec![IR::Lambda(sp, len, ProcSpec::AtLeast(xs.len()), IR::eval(ir).into())]
        }
      }
    }
    self.ctx.restore(len);
    Ok(ir)
  }

  fn def(&mut self, e: &SExpr, es: &[SExpr]) -> Result<(Span, AtomID, Vec<IR>), ElabError> {
    let (sp, x, stack) = self.def_var(e)?;
    let ir = self.def_ir(sp, es, stack)?;
    Ok((sp, x, ir))
  }
}

impl<'a> LispParser<'a> {
  fn parse_ident_or_syntax(&mut self, sp: Span, a: Atom) -> Result<AtomID, Syntax> {
    match Syntax::parse(self.ast.clone().span(sp), a) {
      Ok(s) => Err(s),
      Err(s) => Ok(self.get_atom(s))
    }
  }

  fn parse_ident(&mut self, sp: Span, a: Atom) -> Result<AtomID, ElabError> {
    self.parse_ident_or_syntax(sp, a).map_err(|_|
      ElabError::new_e(sp, "keyword in invalid position"))
  }

  fn to_ident(&mut self, e: &SExpr) -> Result<AtomID, ElabError> {
    if let SExprKind::Atom(a) = e.k {
      self.parse_ident(e.span, a)
    } else {
      Err(ElabError::new_e(e.span, "expected an identifier"))
    }
  }

  fn to_idents(&mut self, es: &[SExpr]) -> Result<Vec<AtomID>, ElabError> {
    let mut xs = vec![];
    for e in es {xs.push(self.to_ident(e)?)}
    Ok(xs)
  }

  fn qexpr(&mut self, e: QExpr) -> Result<IR, ElabError> {
    match e.k {
      QExprKind::IdentApp(sp, es) => {
        let head = IR::Const(LispVal::atom(
          self.elab.env.get_atom(self.ast.clone().span(sp))).span(self.fspan(sp)));
        if es.is_empty() {Ok(head)} else {
          let mut cs = vec![head];
          for e in es { cs.push(self.qexpr(e)?) }
          Ok(IR::list(self.fspan(e.span), cs))
        }
      }
      QExprKind::App(sp, t, es) => {
        let a = self.terms[t].atom;
        let mut cs = vec![IR::Const(LispVal::atom(a).span(self.fspan(sp)))];
        for e in es { cs.push(self.qexpr(e)?) }
        Ok(IR::list(self.fspan(e.span), cs))
      }
      QExprKind::Unquote(e) => self.expr(false, &e)
    }
  }

  fn exprs(&mut self, quote: bool, es: &[SExpr]) -> Result<Vec<IR>, ElabError> {
    let mut cs = vec![];
    for e in es { cs.push(self.expr(quote, e)?) }
    Ok(cs)
  }

  fn let_var<'c>(&mut self, e: &'c SExpr) -> Result<((Span, AtomID, Vec<Item<'c>>), &'c [SExpr]), ElabError> {
    match &e.k {
      SExprKind::List(es) if !es.is_empty() => Ok((self.def_var(&es[0])?, &es[1..])),
      _ => Err(ElabError::new_e(e.span, "let: invalid spec"))
    }
  }

  fn let_(&mut self, rec: bool, es: &[SExpr]) -> Result<IR, ElabError> {
    if es.is_empty() {return Ok(IR::Const(LispVal::undef()).into())}
    let ls = if let SExprKind::List(ls) = &es[0].k {ls}
      else {Err(ElabError::new_e(es[0].span, "let: invalid spec"))?};
    let mut cs = vec![];
    if rec {
      let mut ds = Vec::with_capacity(ls.len());
      for l in ls {
        let ((sp, x, stk), e2) = self.let_var(l)?;
        let n = self.ctx.push(x);
        cs.push(IR::Def(n, if x == AtomID::UNDER {None} else {Some((sp, x))},
          Box::new(IR::new_ref(sp, sp, IR::Const(LispVal::undef())))));
        ds.push((sp, n, e2, stk));
      }
      for (sp, n, e2, stk) in ds {
        let mut v = self.def_ir(sp, e2, stk)?;
        if let Some(r) = v.pop() {
          cs.extend(v);
          cs.push(IR::set_ref(sp, sp, IR::Local(n), r))
        }
      }
    } else {
      for l in ls {
        let ((sp, x, stk), e2) = self.let_var(l)?;
        let v = self.def_ir(sp, e2, stk)?;
        if x == AtomID::UNDER {
          cs.push(IR::Eval(false, v.into()))
        } else {
          cs.push(IR::Def(self.ctx.push(x), Some((sp, x)), IR::eval(v).into()))
        }
      }
    }
    for e in &es[1..] { cs.push(self.expr(false, e)?) }
    Ok(IR::Eval(true, cs.into()))
  }

  fn list_pattern(&mut self, ctx: &mut LocalCtx, code: &mut Vec<IR>,
      quote: bool, es: &[SExpr]) -> Result<Pattern, ElabError> {
    let (en, es1) = es.split_last().unwrap();
    let (es, n) = match &en.k {
      &SExprKind::Atom(Atom::Ident) => match self.span(en.span) {
        "..." | "___" => (es1, Some(0)),
        _ => (es, None),
      }
      SExprKind::Number(n) => {
        if let Some((SExpr {span, k: SExprKind::Atom(Atom::Ident)}, es2)) = es1.split_last() {
          if let "__" = self.span(*span) {
            (es2, Some(n.to_usize().ok_or_else(||
              ElabError::new_e(en.span, "number out of range"))?))
          } else {(es, None)}
        } else {(es, None)}
      }
      _ => (es, None)
    };
    Ok(Pattern::List(self.patterns(ctx, code, quote, es)?, n))
  }

  fn qexpr_pattern(&mut self, ctx: &mut LocalCtx, code: &mut Vec<IR>, e: QExpr) -> Result<Pattern, ElabError> {
    match e.k {
      QExprKind::IdentApp(sp, es) => {
        let head = match self.ast.clone().span(sp) {
          "_" => Pattern::Skip,
          s if es.is_empty() => Pattern::QExprAtom(self.elab.env.get_atom(s)),
          s => Pattern::QuoteAtom(self.elab.env.get_atom(s)),
        };
        if es.is_empty() {Ok(head)} else {
          let mut cs = vec![head];
          for e in es { cs.push(self.qexpr_pattern(ctx, code, e)?) }
          Ok(Pattern::List(cs.into(), None))
        }
      }
      QExprKind::App(_, t, es) => {
        let x = self.terms[t].atom;
        if es.is_empty() {
          Ok(Pattern::QExprAtom(x))
        } else {
          let mut cs = vec![Pattern::QExprAtom(x)];
          for e in es { cs.push(self.qexpr_pattern(ctx, code, e)?) }
          Ok(Pattern::List(cs.into(), None))
        }
      }
      QExprKind::Unquote(e) => self.pattern(ctx, code, false, &e)
    }
  }


  fn patterns(&mut self, ctx: &mut LocalCtx, code: &mut Vec<IR>,
      quote: bool, es: &[SExpr]) -> Result<Box<[Pattern]>, ElabError> {
    let mut ps = vec![];
    for e in es {ps.push(self.pattern(ctx, code, quote, e)?)}
    Ok(ps.into())
  }

  fn pattern(&mut self, ctx: &mut LocalCtx, code: &mut Vec<IR>,
      quote: bool, e: &SExpr) -> Result<Pattern, ElabError> {
    match &e.k {
      &SExprKind::Atom(a) => Ok(
        if quote {
          Pattern::QuoteAtom(self.elab.env.get_atom(self.elab.ast.span_atom(e.span, a)))
        } else {
          let x = self.parse_ident(e.span, a)?;
          if x == AtomID::UNDER {Pattern::Skip}
          else {Pattern::Atom(ctx.get_or_push(x))}
        }
      ),
      SExprKind::DottedList(es, e) => Ok(Pattern::DottedList(
        self.patterns(ctx, code, quote, es)?,
        self.pattern(ctx, code, quote, e)?.into())),
      SExprKind::Number(n) => Ok(Pattern::Number(n.clone().into())),
      SExprKind::String(s) => Ok(Pattern::String(s.clone())),
      &SExprKind::Bool(b) => Ok(Pattern::Bool(b)),
      SExprKind::List(es) if es.is_empty() => Ok(Pattern::List(Box::new([]), None)),
      SExprKind::List(es) =>
        if quote {
          if let &[SExpr {span, k: SExprKind::Atom(a)}, ref e] = es.deref() {
            if self.ast.span_atom(span, a) == "unquote" {
              self.pattern(ctx, code, false, e)
            } else {self.list_pattern(ctx, code, quote, es)}
          } else {self.list_pattern(ctx, code, quote, es)}
        } else if let SExprKind::Atom(a) = es[0].k {
          match self.ast.span_atom(es[0].span, a) {
            "quote" if es.len() != 2 =>
              Err(ElabError::new_e(es[0].span, "expected one argument"))?,
            "quote" => self.pattern(ctx, code, true, &es[1]),
            "mvar" => match es.len() {
              1 => Ok(Pattern::MVar(None)),
              3 => Ok(Pattern::MVar(Some(Box::new((
                self.pattern(ctx, code, quote, &es[1])?,
                self.pattern(ctx, code, quote, &es[2])?))))),
              _ => Err(ElabError::new_e(es[0].span, "expected zero or two arguments"))?,
            },
            "goal" if es.len() != 2 =>
              Err(ElabError::new_e(es[0].span, "expected one argument"))?,
            "goal" => Ok(Pattern::Goal(Box::new(self.pattern(ctx, code, quote, &es[1])?))),
            "and" => Ok(Pattern::And(self.patterns(ctx, code, quote, &es[1..])?)),
            "or" => Ok(Pattern::Or(self.patterns(ctx, code, quote, &es[1..])?)),
            "not" => Ok(Pattern::Not(self.patterns(ctx, code, quote, &es[1..])?)),
            "?" if es.len() < 2 =>
              Err(ElabError::new_e(es[0].span, "expected at least one argument"))?,
            "?" => {
              let p = self.ctx.len();
              let ir = self.expr(false, &es[1])?;
              self.ctx.restore(p);
              Ok(Pattern::Test(es[1].span, Box::new(ir),
                self.patterns(ctx, code, quote, &es[2..])?))
            },
            _ => self.list_pattern(ctx, code, quote, es)
          }
        } else {self.list_pattern(ctx, code, quote, es)},
      &SExprKind::Formula(f) => {
        let q = self.parse_formula(f)?;
        self.qexpr_pattern(ctx, code, q)
      }
    }
  }

  fn branch(&mut self, code: &mut Vec<IR>, e: &SExpr) -> Result<Branch, ElabError> {
    let (e, mut es) = match &e.k {
      SExprKind::List(es) if !es.is_empty() => (&es[0], &es[1..]),
      _ => Err(ElabError::new_e(e.span, "match: improper syntax"))?
    };
    let mut cont = AtomID::UNDER;
    if let Some(e2) = es.get(1) {
      if let SExprKind::List(v) = &e2.k {
        if let &[SExpr {span, k: SExprKind::Atom(a)}, ref x] = v.deref() {
          if let "=>" = self.ast.span_atom(span, a) {
            cont = self.to_ident(x)?;
            es = &es[1..];
          }
        }
      }
    }
    let mut ctx = LocalCtx::new();
    let pat = self.pattern(&mut ctx, code, false, e)?;
    let vars = ctx.ctx.len();
    let start = self.ctx.push_list(&ctx.ctx);
    if cont != AtomID::UNDER {self.ctx.push(cont);}
    let eval = Box::new(IR::eval(self.exprs(false, es)?));
    self.ctx.restore(start);
    Ok(Branch {pat, vars, cont: cont != AtomID::UNDER, eval})
  }
  fn branches(&mut self, code: &mut Vec<IR>, es: &[SExpr]) -> Result<Box<[Branch]>, ElabError> {
    let mut bs = vec![];
    for e in es { bs.push(self.branch(code, e)?) }
    Ok(bs.into())
  }
  fn match_(&mut self, es: &[SExpr], f: impl FnOnce(Box<[Branch]>) -> IR) -> Result<IR, ElabError> {
    let mut code = vec![];
    let m = self.branches(&mut code, es)?;
    if code.is_empty() {
      Ok(f(m))
    } else {
      code.push(f(m));
      Ok(IR::Eval(true, code.into()))
    }
  }

  fn eval_atom(&mut self, sp: Span, x: AtomID) -> IR {
    match self.ctx.get(x) {
      None => {
        self.spans.insert(sp, ObjectKind::Global(x));
        IR::Global(sp, x)
      },
      Some(i) => IR::Local(i)
    }
  }

  fn expr(&mut self, quote: bool, e: &SExpr) -> Result<IR, ElabError> {
    macro_rules! span {($sp:expr, $e:expr) => {{$e.span(self.fspan($sp))}}}
    let mut restore = Some(self.ctx.len());
    let res = match &e.k {
      &SExprKind::Atom(a) => if quote {
        Ok(IR::Const(span!(e.span,
          match self.parse_ident_or_syntax(e.span, a) {
            Ok(x) => LispVal::atom(x),
            Err(s) => LispVal::syntax(s),
          }
        )))
      } else {
        Ok(match self.parse_ident(e.span, a)? {
          AtomID::UNDER => IR::Const(LispVal::atom(AtomID::UNDER)),
          x => self.eval_atom(e.span, x),
        })
      },
      SExprKind::DottedList(es, e) => {
        if !quote {Err(ElabError::new_e(e.span, "cannot evaluate an improper list"))?}
        let mut cs = vec![];
        for e in es {
          if let SExprKind::Atom(a) = es[0].k {
            if let Ok(Syntax::Unquote) = Syntax::parse(self.ast.span(e.span), a) {
              Err(ElabError::new_e(e.span, "cannot evaluate an improper list"))?
            }
          }
          cs.push(self.expr(quote, e)?)
        }
        Ok(IR::dotted_list(e.span, cs, self.expr(true, e)?))
      }
      SExprKind::Number(n) => Ok(IR::Const(LispVal::number(n.clone().into())).into()),
      SExprKind::String(s) => Ok(IR::Const(LispVal::string(s.clone())).into()),
      &SExprKind::Bool(b) => Ok(IR::Const(LispVal::bool(b)).into()),
      SExprKind::List(es) if es.is_empty() => Ok(IR::Const(span!(e.span, LispVal::nil())).into()),
      SExprKind::List(es) => if quote {
        let mut cs = vec![];
        let mut it = es.iter();
        Ok(loop {
          if let Some(arg) = it.next() {
            if let SExprKind::Atom(a) = arg.k {
              if let Ok(Syntax::Unquote) = Syntax::parse(self.ast.span(arg.span), a) {
                let r = it.next().ok_or_else(||
                  ElabError::new_e(arg.span, "expected at least one argument"))?;
                break IR::dotted_list(e.span, cs, self.expr(false, r)?)
              } else {cs.push(self.expr(true, arg)?)}
            } else {cs.push(self.expr(true, arg)?)}
          } else {break IR::list(self.fspan(e.span), cs)}
        })
      } else if let SExprKind::Atom(a) = es[0].k {
        match self.parse_ident_or_syntax(es[0].span, a) {
          Ok(AtomID::UNDER) => Err(ElabError::new_e(es[0].span, "'_' is not a function"))?,
          Ok(x) =>
            Ok(IR::App(e.span, es[0].span,
              Box::new(self.eval_atom(es[0].span, x)), self.exprs(false, &es[1..])?.into())),
          Err(Syntax::Define) if es.len() < 2 =>
            Err(ElabError::new_e(es[0].span, "expected at least one argument"))?,
          Err(Syntax::Define) =>
            Ok(match self.def(&es[1], &es[2..])? {
              (_, AtomID::UNDER, cs) => IR::Eval(false, cs.into()),
              (sp, x, cs) => {
                restore = None;
                IR::Def(self.ctx.push(x), Some((sp, x)), IR::eval(cs).into())
              }
            }),
          Err(Syntax::Lambda) if es.len() < 2 =>
            Err(ElabError::new_e(es[0].span, "expected at least one argument"))?,
          Err(Syntax::Lambda) => match &es[1].k {
            SExprKind::List(xs) => {
              let xs = self.to_idents(xs)?;
              Ok(IR::Lambda(es[0].span, self.ctx.push_list(&xs), ProcSpec::Exact(xs.len()),
                IR::eval(self.exprs(false, &es[2..])?).into()))
            }
            SExprKind::DottedList(xs, y) => {
              let xs = self.to_idents(xs)?;
              let y = self.to_ident(y)?;
              let n = self.ctx.push_list(&xs);
              self.ctx.push(y);
              Ok(IR::Lambda(es[0].span, n, ProcSpec::AtLeast(xs.len()),
                IR::eval(self.exprs(false, &es[2..])?).into()))
            }
            _ => {
              let x = self.to_ident(&es[1])?;
              Ok(IR::Lambda(es[0].span, self.ctx.push(x), ProcSpec::AtLeast(0),
                IR::eval(self.exprs(false, &es[2..])?).into()))
            }
          },
          Err(Syntax::Quote) if es.len() < 2 =>
            Err(ElabError::new_e(es[0].span, "expected at least one argument"))?,
          Err(Syntax::Quote) => self.expr(true, &es[1]),
          Err(Syntax::Unquote) if es.len() < 2 =>
            Err(ElabError::new_e(es[0].span, "expected at least one argument"))?,
          Err(Syntax::Unquote) => self.expr(false, &es[1]),
          Err(Syntax::If) if es.len() < 3 =>
            Err(ElabError::new_e(es[0].span, "expected at least two arguments"))?,
          Err(Syntax::If) => Ok(IR::If(Box::new((
            self.expr(false, &es[1])?,
            self.expr(false, &es[2])?,
            if let Some(e) = es.get(3) {
              self.expr(false, e)?
            } else { IR::Const(LispVal::undef()) }
          )))),
          Err(Syntax::Focus) => Ok(IR::Focus(es[0].span, self.exprs(false, &es[1..])?.into())),
          Err(Syntax::Let) => self.let_(false, &es[1..]),
          Err(Syntax::Letrec) => self.let_(true, &es[1..]),
          Err(Syntax::Match) if es.len() < 2 =>
            Err(ElabError::new_e(es[0].span, "expected at least one argument"))?,
          Err(Syntax::Match) => {
            let e = self.expr(false, &es[1])?;
            self.ctx.restore(restore.unwrap());
            self.match_(&es[2..], |m| IR::Match(es[0].span, Box::new(e), m))
          },
          Err(Syntax::MatchFn) => {
            let i = self.ctx.push(AtomID::UNDER);
            Ok(IR::Lambda(es[0].span, i, ProcSpec::Exact(1),
              Arc::new(self.match_(&es[1..], |m| IR::match_fn_body(es[0].span, i, m))?)))
          }
          Err(Syntax::MatchFns) => {
            let i = self.ctx.push(AtomID::UNDER);
            Ok(IR::Lambda(es[0].span, i, ProcSpec::AtLeast(0),
              Arc::new(self.match_(&es[1..], |m| IR::match_fn_body(es[0].span, i, m))?)))
          }
        }
      } else {
        Ok(IR::App(e.span, es[0].span, Box::new(self.expr(false, &es[0])?),
          self.exprs(false, &es[1..])?.into()))
      },
      &SExprKind::Formula(f) => {let q = self.parse_formula(f)?; self.qexpr(q)}
    };
    if let Some(old) = restore { self.ctx.restore(old) }
    res
  }
}

impl Elaborator {
  pub fn parse_lisp(&mut self, e: &SExpr) -> Result<IR, ElabError> {
    LispParser {elab: &mut *self, ctx: LocalCtx::new()}.expr(false, e)
  }
  pub fn parse_qexpr(&mut self, e: QExpr) -> Result<IR, ElabError> {
    LispParser {elab: &mut *self, ctx: LocalCtx::new()}.qexpr(e)
  }
}