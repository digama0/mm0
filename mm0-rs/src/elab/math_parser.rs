use std::ops::{Deref, DerefMut};
use std::mem;
use crate::parser::{Parser, ParseError, ident_start, ident_rest, whitespace};
use crate::elab::{FileServer, Elaborator, ElabError};
use crate::elab::ast::{Formula, SExpr};
use crate::util::*;
use crate::elab::environment::*;

#[derive(Debug)]
pub struct QExpr {
  pub span: Span,
  pub k: QExprKind,
}
#[derive(Debug)]
pub enum QExprKind {
  Ident,
  App(TermID, Vec<QExpr>),
  Unquote(SExpr),
}

impl QExpr {
  fn offset(&mut self, off: usize) {
    self.span += off;
    match &mut self.k {
      QExprKind::Ident => {}
      QExprKind::App(_, qs) => for q in qs {q.offset(off)},
      QExprKind::Unquote(e) => e.offset(off),
    }
  }
}

impl<'a, T: FileServer + ?Sized> Elaborator<'a, T> {
  pub fn parse_formula(&mut self, f: Formula) -> Result<QExpr, ElabError> {
    let mut p = MathParser {
      pe: &self.pe,
      p: Parser {
        source: self.ast.source.as_bytes(),
        errors: vec![],
        imports: vec![],
        idx: f.0.start + 1,
      }
    };
    p.ws();
    let expr = p.expr(Prec::Prec(0))?;
    assert!(p.imports.is_empty());
    for e in p.p.errors { self.report(e.into()) }
    Ok(expr)
  }

  pub fn parse_formula_str(&mut self, s: &str, off: usize) -> Result<QExpr, ElabError> {
    let mut p = MathParser {
      pe: &self.pe,
      p: Parser {
        source: s.as_bytes(),
        errors: vec![],
        imports: vec![],
        idx: 0,
      }
    };
    p.ws();
    let mut expr = p.expr(Prec::Prec(0))?;
    assert!(p.imports.is_empty());
    for mut e in p.p.errors { e.pos += off; self.report(e.into()) }
    expr.offset(off);
    Ok(expr)
  }
}

struct MathParser<'a> {
  p: Parser<'a>,
  pe: &'a ParserEnv,
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
        b'$' => return None,
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

  fn literals(&mut self, res: &mut VecUninit<QExpr>, lits: &[Literal], mut end: usize) ->
      Result<usize, ParseError> {
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
      b'(' => return Ok((self.idx += 1, self.expr(Prec::Prec(0))?, self.chr_err(b')')?).1),
      c => c
    };
    let sp = self.token().ok_or_else(|| self.err("expecting expression".into()))?;
    let v = self.span(sp);
    if let Some(&(_, q)) = self.pe.consts.get(v) {
      if q >= p {
        if let Some(info) = self.pe.prefixes.get(v) {
          let mut args = VecUninit::new(info.nargs);
          let end = self.literals(&mut args, &info.lits, sp.end)?;
          return Ok(QExpr {
            span: (start..end).into(),
            k: QExprKind::App(info.term, unsafe { args.assume_init() })
          })
        }
      }
    } else if ident_start(c) && (sp.start + 1..sp.end).all(|i| ident_rest(self.source[i])) {
      return Ok(QExpr {span: sp, k: QExprKind::Ident})
    }
    Err(ParseError::new(sp, format!("expecting prefix expression >= {}", p).into()))?
  }

  fn lhs(&mut self, p: Prec, mut lhs: QExpr) -> Result<QExpr, ParseError> {
    let mut tok_end = self.peek_token();
    loop {
      let s = if let Some(tk) = tok_end.0 {self.span(tk)} else {break};
      if !self.pe.consts.get(s).map_or(false, |&(_, q)| q >= p) {break}
      let info = if let Some(i) = self.pe.infixes.get(s) {i} else {break};
      self.idx = tok_end.1;
      let mut args = VecUninit::new(info.nargs);
      let start = lhs.span.start;
      if let Literal::Var(i, _) = info.lits[0] {args.set(i, lhs)} else {unreachable!()}
      self.literals(&mut args, &info.lits[2..info.lits.len()-1], 0)?;
      let (i, mut rhs) = if let Some(&Literal::Var(i, q)) = info.lits.last() {
        (i, self.prefix(q)?)
      } else {unreachable!()};
      tok_end = self.peek_token();
      loop {
        let s = if let Some(tk) = tok_end.0 {self.span(tk)} else {break};
        let info2 = if let Some(i) = self.pe.infixes.get(s) {i} else {break};
        let q = self.pe.consts[s].1;
        if !(if info2.rassoc.unwrap() {q >= p} else {q > p}) {break}
        rhs = self.lhs(q, rhs)?;
        tok_end = self.peek_token();
      }
      let span = (start..rhs.span.end).into();
      args.set(i, rhs);
      lhs = QExpr { span, k: QExprKind::App(info.term, unsafe { args.assume_init() }) };
    }
    return Ok(lhs)
  }

  fn expr(&mut self, p: Prec) -> Result<QExpr, ParseError> {
    let lhs = self.prefix(p)?;
    self.lhs(p, lhs)
  }
}