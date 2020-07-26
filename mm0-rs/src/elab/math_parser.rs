use std::ops::{Deref, DerefMut};
use std::mem;
use std::fmt::{self, Display};
use crate::parser::{Parser, ParseError, ident_start, ident_rest, whitespace};
use crate::elab::{Elaborator, ElabError, ObjectKind};
use crate::elab::ast::{Formula, SExpr};
use crate::elab::lisp::print::{EnvDisplay, FormatEnv};
use crate::elab::spans::Spans;
use crate::util::*;
use crate::elab::environment::*;

#[derive(Debug)]
pub struct QExpr {
  pub span: Span,
  pub k: QExprKind,
}
#[derive(Debug)]
pub enum QExprKind {
  IdentApp(Span, Vec<QExpr>),
  App(Span, TermID, Vec<QExpr>),
  Unquote(SExpr),
}

impl EnvDisplay for QExpr {
  fn fmt(&self, fe: FormatEnv, f: &mut fmt::Formatter) -> fmt::Result {
    match &self.k {
      &QExprKind::IdentApp(sp, ref es) if es.is_empty() => fe.source[sp].fmt(f),
      &QExprKind::IdentApp(sp, ref es) => {
        write!(f, "({}", &fe.source[sp])?;
        for e in es {write!(f, " {}", fe.to(e))?}
        write!(f, ")")
      }
      QExprKind::App(_, t, es) => {
        write!(f, "({}", fe.to(t))?;
        for e in es {write!(f, " {}", fe.to(e))?}
        write!(f, ")")
      }
      QExprKind::Unquote(e) => write!(f, ",{}", fe.to(e))
    }
  }
}

impl Elaborator {
  pub fn parse_formula(&mut self, f: Formula) -> Result<QExpr, ElabError> {
    let mut p = MathParser {
      pe: &self.env.pe,
      p: Parser {
        source: self.ast.source.as_bytes(),
        errors: vec![],
        imports: vec![],
        idx: f.0.start + 1,
        restart_pos: Some(0), // skip command checks
      },
      spans: &mut self.spans,
    };
    p.ws();
    let expr = p.expr(Prec::Prec(0))?;
    if let Some(tk) = p.token() {Err(ElabError::new_e(tk, "expected '$'"))?}
    assert!(p.imports.is_empty());
    for e in p.p.errors { self.report(e.into()) }
    Ok(expr)
  }
}

pub const APP_PREC: Prec = Prec::Prec(1024);

struct MathParser<'a> {
  p: Parser<'a>,
  pe: &'a ParserEnv,
  spans: &'a mut Spans<ObjectKind>,
}
impl<'a> Deref for MathParser<'a> {
  type Target = Parser<'a>;
  fn deref(&self) -> &Parser<'a> { &self.p }
}
impl<'a> DerefMut for MathParser<'a> {
  fn deref_mut(&mut self) -> &mut Parser<'a> { &mut self.p }
}

impl<'a> MathParser<'a> {
  fn ws(&mut self) {
    loop {
      match self.cur() {
        b' ' | b'\n' => self.idx += 1,
        _ => return
      }
    }
  }

  fn token(&mut self) -> Option<Span> {
    let start = self.idx;
    loop {
      match self.cur() {
        c if self.pe.delims_r.get(c) && self.idx != start =>
          return Some((start..(self.idx, self.ws()).0).into()),
        c if self.pe.delims_l.get(c) => {
          self.idx += 1;
          return Some((start..(self.idx, self.ws()).0).into())
        }
        b'$' if start == self.idx => return None,
        b'$' => return Some((start..self.idx).into()),
        b' ' | b'\n' =>
          return Some((start..(self.idx, self.ws()).0).into()),
        _ => self.idx += 1,
      }
    }
  }

  fn peek_token(&mut self) -> (Option<Span>, usize) {
    let start = self.idx;
    let tk = self.token();
    (tk, mem::replace(&mut self.idx, start))
  }

  fn literals(&mut self, res: &mut VecUninit<QExpr>, lits: &[Literal],
      consts: &mut Vec<Span>, mut end: usize) -> Result<usize, ParseError> {
    for lit in lits {
      match lit {
        &Literal::Var(i, q) => {
          let e = self.expr(q)?;
          end = e.span.end;
          res.set(i, e);
        },
        &Literal::Const(ref c) => {
          let tk = self.token().ok_or_else(|| self.err(format!("expecting '{}'", c).into()))?;
          if self.span(tk) != c.deref() {
            Err(ParseError::new(tk, format!("expecting '{}'", c).into()))?
          }
          consts.push(tk);
          end = tk.end;
        }
      }
    }
    Ok(end)
  }

  fn prefix(&mut self, p: Prec) -> Result<QExpr, ParseError> {
    let start = self.idx;
    let c = match self.cur() {
      b',' if {
        let c = self.source[self.idx+1];
        !(whitespace(c) || c == b'$')
      } => {
        self.idx += 1;
        let e = self.sexpr()?;
        return Ok(QExpr {span: (start..e.span.end).into(), k: QExprKind::Unquote(e) })
      }
      b'(' => {
        self.idx += 1;
        self.ws();
        let mut e = self.expr(Prec::Prec(0))?;
        e.span = (start..self.chr_err(b')')?).into();
        return Ok(e)
      }
      c => c
    };
    let sp = self.token().ok_or_else(|| self.err("expecting expression".into()))?;
    let v = self.span(sp);
    if let Some(&(_, q)) = self.pe.consts.get(v) {
      if q >= p {
        if let Some(info) = self.pe.prefixes.get(v) {
          let mut args = VecUninit::new(info.nargs);
          let mut consts = vec![sp];
          let end = self.literals(&mut args, &info.lits, &mut consts, sp.end)?;
          let span = (start..end).into();
          for sp in consts {self.spans.insert(sp, ObjectKind::Term(info.term, span));}
          return Ok(QExpr {
            span,
            k: QExprKind::App(sp, info.term, unsafe { args.assume_init() })
          })
        }
      }
    } else if ident_start(c) && (sp.start + 1..sp.end).all(|i| ident_rest(self.source[i])) {
      let mut args = Vec::new();
      let mut start = self.idx;
      let mut span = sp;
      if p <= APP_PREC {
        while let Ok(e) = self.expr(Prec::Max) {
          span.end = e.span.end;
          start = self.idx;
          args.push(e);
        }
      }
      self.idx = start;
      return Ok(QExpr {span, k: QExprKind::IdentApp(sp, args)})
    }
    Err(ParseError::new(sp, format!("expecting prefix expression >= {}", p).into()))?
  }

  fn lhs(&mut self, p: Prec, mut lhs: QExpr) -> Result<QExpr, ParseError> {
    let mut tok_end = self.peek_token();
    loop {
      let tk = if let Some(tk) = tok_end.0 {tk} else {break};
      let s = self.span(tk);
      let p1 = if let Some(&(_, q)) = self.pe.consts.get(s) {q} else {break};
      if p1 < p {break}
      let info = if let Some(i) = self.pe.infixes.get(s) {i} else {break};
      self.idx = tok_end.1;
      let mut args = VecUninit::new(info.nargs);
      let start = lhs.span.start;
      if let Literal::Var(i, _) = info.lits[0] {args.set(i, lhs)} else {unreachable!()}
      let mut consts = vec![tk];
      self.literals(&mut args, &info.lits[2..info.lits.len()-1], &mut consts, 0)?;
      let (i, mut rhs) = if let Some(&Literal::Var(i, q)) = info.lits.last() {
        (i, self.prefix(q)?)
      } else {unreachable!()};
      loop {
        tok_end = self.peek_token();
        let s = if let Some(tk) = tok_end.0 {self.span(tk)} else {break};
        let info2 = if let Some(i) = self.pe.infixes.get(s) {i} else {break};
        let q = self.pe.consts[s].1;
        if !(if info2.rassoc.unwrap() {q >= p1} else {q > p1}) {break}
        rhs = self.lhs(q, rhs)?;
      }
      let span = (start..rhs.span.end).into();
      args.set(i, rhs);
      for sp in consts {self.spans.insert(sp, ObjectKind::Term(info.term, span));}
      lhs = QExpr { span, k: QExprKind::App(tk, info.term, unsafe { args.assume_init() }) };
    }
    return Ok(lhs)
  }

  fn expr(&mut self, p: Prec) -> Result<QExpr, ParseError> {
    let lhs = self.prefix(p)?;
    self.lhs(p, lhs)
  }
}