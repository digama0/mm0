use std::ops::{Deref, DerefMut};
use std::sync::Arc;
use std::collections::HashMap;
use num::{BigInt, ToPrimitive};
use crate::parser::ast::{SExpr, SExprKind, Atom};
use crate::util::ArcString;
use super::super::{AtomID, Span, FileServer, Elaborator, Environment, ElabError};
use super::*;
use super::super::math_parser::{QExpr, QExprKind};

pub enum IR {
  Local(usize),
  Global(Span, AtomID),
  Const(LispVal),
  List(Box<[IR]>),
  DottedList(Box<[IR]>, Box<IR>),
  App(Span, Span, Box<IR>, Box<[IR]>),
  If(Box<(IR, IR, IR)>),
  Focus(Box<[IR]>),
  Def(Option<(Span, AtomID)>, Box<IR>),
  Eval(Box<[IR]>),
  Lambda(Span, ProcSpec, Arc<IR>),
  Match(Span, Box<IR>, Box<[Branch]>),
}

impl IR {
  fn eval(es: impl Into<Box<[IR]>>) -> IR {
    let es: Box<[IR]> = es.into();
    match es.len() {
      0 => IR::Const(UNDEF.clone()),
      1 => es.into_vec().drain(..).next().unwrap(), // why is this so hard
      _ => IR::Eval(es)
    }
  }

  fn builtin_app(sp1: Span, sp2: Span, f: BuiltinProc, es: Box<[IR]>) -> IR {
    IR::App(sp1, sp2, Box::new(IR::Const(Arc::new(LispKind::Proc(Proc::Builtin(f))))), es)
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
}

pub struct Branch {
  pub vars: usize,
  pub cont: bool,
  pub pat: Pattern,
  pub eval: Box<IR>,
}

pub enum Pattern {
  Skip,
  Atom(usize),
  QuoteAtom(AtomID),
  String(ArcString),
  Bool(bool),
  Number(BigInt),
  DottedList(Box<[Pattern]>, Box<Pattern>),
  List(Box<[Pattern]>, Option<usize>),
  And(Box<[Pattern]>),
  Or(Box<[Pattern]>),
  Not(Box<[Pattern]>),
  Test(Span, usize, Box<[Pattern]>),
  QExprAtom(AtomID),
}

impl Remap<LispRemapper> for IR {
  fn remap(&self, r: &mut LispRemapper) -> Self {
    match self {
      &IR::Local(i) => IR::Local(i),
      &IR::Global(sp, a) => IR::Global(sp, a.remap(r)),
      IR::Const(v) => IR::Const(v.remap(r)),
      IR::List(v) => IR::List(v.remap(r)),
      IR::DottedList(v, e) => IR::DottedList(v.remap(r), e.remap(r)),
      &IR::App(s, t, ref e, ref es) => IR::App(s, t, e.remap(r), es.remap(r)),
      IR::If(e) => IR::If(e.remap(r)),
      IR::Focus(e) => IR::Focus(e.remap(r)),
      IR::Def(a, e) => IR::Def(a.map(|(sp, a)| (sp, a.remap(r))), e.remap(r)),
      IR::Eval(e) => IR::Eval(e.remap(r)),
      &IR::Lambda(sp, spec, ref e) => IR::Lambda(sp, spec, e.remap(r)),
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
      Pattern::DottedList(v, e) => Pattern::DottedList(v.remap(r), e.remap(r)),
      &Pattern::List(ref es, n) => Pattern::List(es.remap(r), n),
      Pattern::And(es) => Pattern::And(es.remap(r)),
      Pattern::Or(es) => Pattern::Or(es.remap(r)),
      Pattern::Not(es) => Pattern::Not(es.remap(r)),
      &Pattern::Test(sp, i, ref es) => Pattern::Test(sp, i, es.remap(r)),
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
  fn list(cs: Vec<IR>) -> IR {
    match IR::unconst(cs) {
      Ok(es) => IR::Const(Arc::new(LispKind::List(es))),
      Err(cs) => IR::List(cs.into())
    }
  }
  fn dotted_list(mut cs: Vec<IR>, c: IR) -> IR {
    match c {
      IR::Const(e) => match e.deref() {
        LispKind::List(es) => {
          cs.extend(es.iter().map(|e| IR::Const(e.clone())));
          IR::List(cs.into())
        }
        LispKind::DottedList(es, e) => {
          cs.extend(es.iter().map(|e| IR::Const(e.clone())));
          IR::DottedList(cs.into(), Box::new(IR::Const(e.clone())))
        }
        _ => match IR::unconst(cs) {
          Ok(es) => IR::Const(Arc::new(LispKind::DottedList(es, e))),
          Err(cs) => IR::DottedList(cs.into(), Box::new(IR::Const(e)))
        }
      },
      IR::List(cs2) => {
        cs.extend(cs2.into_vec());
        IR::List(cs.into())
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
  ctx: Vec<Option<AtomID>>,
}

impl LocalCtx {
  fn new() -> Self { Self {names: HashMap::new(), ctx: vec![]} }
  fn len(&self) -> usize { self.ctx.len() }
  fn get(&self, x: AtomID) -> Option<usize> {
    self.names.get(&x).and_then(|v| v.last().cloned())
  }
  fn push(&mut self, x: AtomID) -> usize {
    self.push_opt(Some(x))
  }
  fn push_opt(&mut self, x: Option<AtomID>) -> usize {
    let old = self.ctx.len();
    if let Some(x) = x { self.names.entry(x).or_insert(vec![]).push(old) }
    self.ctx.push(x);
    old
  }
  fn push_list(&mut self, xs: &Vec<Option<AtomID>>) -> usize {
    let old = self.ctx.len();
    for &x in xs { self.push_opt(x); }
    old
  }
  fn get_or_push(&mut self, x: AtomID) -> usize {
    self.get(x).unwrap_or_else(|| self.push(x))
  }

  fn pop(&mut self) {
    if let Some(x) = self.ctx.pop().unwrap() {
      self.names.get_mut(&x).unwrap().pop();
    }
  }
  fn restore(&mut self, n: usize) {
    while self.ctx.len() > n { self.pop() }
  }
}

struct LispParser<'a: 'b, 'b, T: FileServer + ?Sized> {
  elab: &'b mut Elaborator<'a, T>,
  ctx: LocalCtx,
}
impl<'a: 'b, 'b, T: FileServer + ?Sized> Deref for LispParser<'a, 'b, T> {
  type Target = Elaborator<'a, T>;
  fn deref(&self) -> &Elaborator<'a, T> { self.elab }
}
impl<'a: 'b, 'b, T: FileServer + ?Sized> DerefMut for LispParser<'a, 'b, T> {
  fn deref_mut(&mut self) -> &mut Elaborator<'a, T> { self.elab }
}

fn quoted_ident(env: &mut Environment, s: &str, a: Atom) -> LispVal {
  Arc::new(match Syntax::parse(s, a) {
    Ok(s) => LispKind::Syntax(s),
    Err(s) => LispKind::Atom(env.get_atom(s))
  })
}

impl<'a: 'b, 'b, T: FileServer + ?Sized> LispParser<'a, 'b, T> {
  fn parse_ident_or_syntax(&mut self, sp: Span, a: Atom) -> Result<Option<AtomID>, Syntax> {
    match Syntax::parse(self.ast.span(sp), a) {
      Ok(s) => Err(s),
      Err("_") => Ok(None),
      Err(s) => Ok(Some(self.env.get_atom(s)))
    }
  }

  fn parse_ident(&mut self, sp: Span, a: Atom) -> Result<Option<AtomID>, ElabError> {
    self.parse_ident_or_syntax(sp, a).map_err(|_|
      ElabError::new_e(sp, "keyword in invalid position"))
  }

  fn to_ident(&mut self, e: &SExpr) -> Result<Option<AtomID>, ElabError> {
    if let SExprKind::Atom(a) = e.k {
      self.parse_ident(e.span, a)
    } else {
      Err(ElabError::new_e(e.span, "expected an identifier"))
    }
  }

  fn to_idents(&mut self, es: &[SExpr]) -> Result<Vec<Option<AtomID>>, ElabError> {
    let mut xs = vec![];
    for e in es {xs.push(self.to_ident(e)?)}
    Ok(xs)
  }

  fn qexpr(&mut self, e: QExpr) -> Result<IR, ElabError> {
    match e.k {
      QExprKind::Ident => Ok(IR::Const(Arc::new(LispKind::Atom(
        self.elab.env.get_atom(self.ast.span(e.span)))))),
      QExprKind::App(t, es) => {
        let s = self.ast.span(self.terms[t].id);
        let mut cs = vec![IR::Const(Arc::new(LispKind::Atom(self.get_atom(s))))];
        for e in es { cs.push(self.qexpr(e)?) }
        Ok(IR::list(cs))
      }
      QExprKind::Unquote(e) => self.expr(false, &e)
    }
  }

  fn exprs(&mut self, quote: bool, es: &[SExpr]) -> Result<Vec<IR>, ElabError> {
    let mut cs = vec![];
    for e in &es[1..] { cs.push(self.expr(quote, e)?) }
    Ok(cs.into())
  }

  fn def(&mut self, mut e: &SExpr, es: &[SExpr]) -> Result<(Span, Option<AtomID>, Vec<IR>), ElabError> {
    enum Item<'a> {
      List(&'a [SExpr]),
      DottedList(&'a [SExpr], &'a SExpr),
    }
    let mut stack: Vec<Item> = vec![];
    let (sp, x) = loop {
      match &e.k {
        &SExprKind::Atom(a) => break (e.span, self.parse_ident(e.span, a)?),
        SExprKind::List(xs) if !xs.is_empty() =>
          {stack.push(Item::List(xs)); e = &xs[0]}
        SExprKind::DottedList(xs, y) if !xs.is_empty() =>
          {stack.push(Item::DottedList(xs, y)); e = &xs[0]}
        _ => Err(ElabError::new_e(e.span, "def: invalid spec"))?
      }
    };
    for e in stack.iter().rev() {
      match e {
        Item::List(xs) => {
          let xs = self.to_idents(&xs[1..])?;
          self.ctx.push_list(&xs);
        }
        Item::DottedList(xs, y) => {
          let xs = self.to_idents(&xs[1..])?;
          self.ctx.push_list(&xs);
          let y = self.to_ident(y)?;
          self.ctx.push_opt(y);
        }
      }
    }
    let mut ir = self.exprs(false, es)?;
    for e in stack {
      ir = match e {
        Item::List(xs) =>
          vec![IR::Lambda(sp, ProcSpec::Exact(xs.len() - 1), IR::eval(ir).into())],
        Item::DottedList(xs, _) =>
          vec![IR::Lambda(sp, ProcSpec::AtLeast(xs.len() - 1), IR::eval(ir).into())],
      }
    }
    Ok((sp, x, ir))
  }

  fn let_var(&mut self, e: &SExpr) -> Result<(Span, Option<AtomID>, Vec<IR>), ElabError> {
    match &e.k {
      SExprKind::List(es) if !es.is_empty() => self.def(&es[0], &es[1..]),
      _ => Err(ElabError::new_e(e.span, "let: invalid spec"))
    }
  }

  fn let_(&mut self, rec: bool, es: &[SExpr]) -> Result<IR, ElabError> {
    if es.is_empty() {return Ok(IR::Const(UNDEF.clone()).into())}
    let ls = if let SExprKind::List(ls) = &es[0].k {ls}
      else {Err(ElabError::new_e(es[0].span, "let: invalid spec"))?};
    let mut cs = vec![];
    if rec {
      let mut ds = vec![];
      for l in ls {
        let (sp, x, v) = self.let_var(l)?;
        let n = if let Some(x) = x {
          cs.push(IR::Def(Some((sp, x)), Box::new(IR::new_ref(sp, sp, IR::Const(UNDEF.clone())))));
          Some(self.ctx.push(x))
        } else {None};
        ds.push((sp, n, v))
      }
      for (sp, n, mut v) in ds {
        if let Some(n) = n {
          if let Some(r) = v.pop() {
            cs.extend(v);
            cs.push(IR::set_ref(sp, sp, IR::Local(n), r))
          }
        } else {cs.extend(v)}
      }
    } else {
      for l in ls {
        cs.push(match self.let_var(l)? {
          (_, None, cs) => IR::Eval(cs.into()),
          (sp, Some(x), cs) => {self.ctx.push(x); IR::Def(Some((sp, x)), IR::eval(cs).into())}
        })
      }
    }
    for e in &es[1..] { cs.push(self.expr(false, e)?) }
    Ok(IR::Eval(cs.into()))
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
      QExprKind::Ident => match self.ast.span(e.span) {
        "_" => Ok(Pattern::Skip),
        s => Ok(Pattern::QExprAtom(self.elab.env.get_atom(s))),
      },
      QExprKind::App(t, es) => {
        let s = self.ast.span(self.terms[t].id);
        let x = self.get_atom(s);
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
      &SExprKind::Atom(a) => Ok(match (quote, self.parse_ident(e.span, a)?) {
        (true, x) => Pattern::QuoteAtom(x.unwrap_or_else(|| self.get_atom("_"))),
        (false, None) => Pattern::Skip,
        (false, Some(x)) => Pattern::Atom(ctx.get_or_push(x)),
      }),
      SExprKind::DottedList(es, e) => Ok(Pattern::DottedList(
        self.patterns(ctx, code, quote, es)?,
        self.pattern(ctx, code, quote, e)?.into())),
      SExprKind::Number(n) => Ok(Pattern::Number(n.clone().into())),
      SExprKind::String(s) => Ok(Pattern::String(ArcString::new(s.clone()))),
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
            "and" => Ok(Pattern::And(self.patterns(ctx, code, quote, &es[1..])?)),
            "or" => Ok(Pattern::Or(self.patterns(ctx, code, quote, &es[1..])?)),
            "not" => Ok(Pattern::Not(self.patterns(ctx, code, quote, &es[1..])?)),
            "?" if es.len() < 2 =>
              Err(ElabError::new_e(es[0].span, "expected at least one argument"))?,
            "?" => {
              code.push(IR::Def(None, Box::new(self.expr(false, &es[1])?)));
              let p = self.ctx.len();
              self.ctx.ctx.push(None);
              Ok(Pattern::Test(es[1].span, p, self.patterns(ctx, code, quote, &es[2..])?))
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
    let mut cont = None;
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
    if let Some(x) = cont {self.ctx.push(x);}
    let eval = Box::new(IR::eval(self.exprs(false, es)?));
    self.ctx.restore(start);
    Ok(Branch {pat, vars, cont: cont.is_some(), eval})
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
      Ok(IR::Eval(code.into()))
    }
  }

  fn eval_atom(&self, sp: Span, x: AtomID) -> IR {
    match self.ctx.get(x) {
      None => IR::Global(sp, x),
      Some(i) => IR::Local(i)
    }
  }

  fn expr(&mut self, quote: bool, e: &SExpr) -> Result<IR, ElabError> {
    let mut restore = Some(self.ctx.len());
    let res = match &e.k {
      &SExprKind::Atom(a) => Ok(match self.parse_ident(e.span, a)? {
        None => IR::Const(Arc::new(LispKind::Atom(self.get_atom("_")))),
        Some(x) => self.eval_atom(e.span, x),
      }),
      SExprKind::DottedList(es, e) => {
        if !quote {Err(ElabError::new_e(e.span, "cannot evaluate an improper list"))?}
        Ok(IR::dotted_list(self.exprs(true, &es)?.into(), self.expr(true, e)?))
      }
      SExprKind::Number(n) => Ok(IR::Const(Arc::new(LispKind::Number(n.clone().into()))).into()),
      SExprKind::String(s) => Ok(IR::Const(Arc::new(LispKind::String(s.clone()))).into()),
      SExprKind::Bool(true) => Ok(IR::Const(TRUE.clone()).into()),
      SExprKind::Bool(false) => Ok(IR::Const(FALSE.clone()).into()),
      SExprKind::List(es) if es.is_empty() => Ok(IR::Const(NIL.clone()).into()),
      SExprKind::List(es) =>
        if quote {
          Ok(IR::list(self.exprs(true, &es)?))
        } else if let SExprKind::Atom(a) = es[0].k {
          match self.parse_ident_or_syntax(e.span, a) {
            Ok(None) => Err(ElabError::new_e(e.span, "'_' is not a function"))?,
            Ok(Some(x)) =>
              Ok(IR::App(e.span, es[0].span,
                Box::new(self.eval_atom(es[0].span, x)), self.exprs(true, &es[1..])?.into())),
            Err(Syntax::Define) if es.len() < 2 =>
              Err(ElabError::new_e(es[0].span, "expected at least one argument"))?,
            Err(Syntax::Define) =>
              Ok(match self.def(&es[1], &es[2..])? {
                (_, None, cs) => IR::eval(cs),
                (sp, Some(x), cs) => {
                  restore = None;
                  self.ctx.push(x);
                  IR::Def(Some((sp, x)), IR::eval(cs).into())
                }
              }),
            Err(Syntax::Lambda) if es.len() < 2 =>
              Err(ElabError::new_e(es[0].span, "expected at least one argument"))?,
            Err(Syntax::Lambda) => match &es[1].k {
              SExprKind::List(xs) => {
                let xs = self.to_idents(xs)?;
                self.ctx.push_list(&xs);
                Ok(IR::Lambda(es[0].span, ProcSpec::Exact(xs.len()),
                  IR::eval(self.exprs(false, &es[2..])?).into()))
              }
              SExprKind::DottedList(xs, y) => {
                let xs = self.to_idents(xs)?;
                let y = self.to_ident(y)?;
                self.ctx.push_list(&xs);
                self.ctx.push_opt(y);
                Ok(IR::Lambda(es[0].span, ProcSpec::AtLeast(xs.len()),
                  IR::eval(self.exprs(false, &es[2..])?).into()))
              }
              _ => {
                let x = self.to_ident(&es[1])?;
                self.ctx.push_opt(x);
                Ok(IR::Lambda(es[0].span, ProcSpec::AtLeast(0),
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
              } else { IR::Const(UNDEF.clone()) }
            )))),
            Err(Syntax::Focus) => Ok(IR::Focus(self.exprs(false, &es[1..])?.into())),
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
              let i = self.ctx.len();
              self.match_(&es[2..], |m| IR::Lambda(es[0].span, ProcSpec::Exact(1),
                Arc::new(IR::Match(es[0].span, Box::new(IR::Local(i)), m))))
            }
            Err(Syntax::MatchFns) => {
              let i = self.ctx.len();
              self.match_(&es[2..], |m| IR::Lambda(es[0].span, ProcSpec::AtLeast(0),
                Arc::new(IR::Match(es[0].span, Box::new(IR::Local(i)), m))))
            }
          }
        } else {
          Ok(IR::App(e.span, es[0].span, Box::new(self.expr(true, &es[0])?),
            self.exprs(true, &es[1..])?.into()))
        },
      &SExprKind::Formula(f) => {let q = self.parse_formula(f)?; self.qexpr(q)}
    };
    if let Some(old) = restore { self.ctx.restore(old) }
    res
  }
}

impl<'a, T: FileServer + ?Sized> Elaborator<'a, T> {
  pub fn parse_lisp<'b, 'c>(&'b mut self, e: &'c SExpr) -> Result<IR, ElabError> {
    LispParser {elab: &mut *self, ctx: LocalCtx::new()}.expr(false, e)
  }
}