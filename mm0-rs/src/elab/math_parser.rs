//! Secondary / dynamic parser for MM0 math formulas.
//!
//! The main grammar of MM0 math parsing is described in [`mm0.md`],
//! but MM1 also includes antiquotations `,e` for splicing evaluated lisp
//! expressions into math formulas. These can also be used for capturing
//! subterms when a math formula is used as a pattern in a `match` statement.
//!
//! [`mm0.md`]: https://github.com/digama0/mm0/blob/master/mm0.md#secondary-parsing

use std::ops::{Deref, DerefMut};
use std::mem;
use std::fmt::{self, Display};
use mm1_parser::{Parser, ParseError, ident_start, ident_rest, whitespace, ErrorLevel};
use crate::elab::{Elaborator, ElabError, ObjectKind};
use crate::elab::ast::{Formula, SExpr};
use crate::elab::lisp::print::{EnvDisplay, FormatEnv};
use crate::elab::spans::Spans;
use crate::{SliceUninit, Span, Literal, ParserEnv, Prec, TermId, APP_PREC};

/// A parsed math expression (quoted expression). This is like [`SExpr`] but it
/// has a much simpler grammar.
#[derive(Debug)]
pub struct QExpr {
  /// The span of the expression.
  pub span: Span,
  /// The kind of expression, together with its associated data.
  pub k: QExprKind,
}
#[derive(Debug)]
/// A math expression like `$ 2 + foo (x, y) z $` is parsed by the math parser
/// into a representation such as `'(add (two (foo (pair x y) z)))`, and these
/// are mostly interchangeable. The `QExpr` type is slightly different from
/// [`SExpr`] because we cannot immediately resolve some aspects like whether a
/// bare name like `x` refers to a local variable or a constant or term
/// constructor.
pub enum QExprKind {
  /// An identifier or n-ary application `foo`. (We can't tell at this stage
  /// of processing whether it is a hypothesis or a constant term, which have
  /// elaborated representations `foo` and `(foo)` respectively.) This
  /// is created by basic prefix applications like `foo a b c`
  /// where `foo` isn't a notation.
  IdentApp(Span, Box<[QExpr]>),
  /// An application of a known term to the appropriate number of arguments.
  /// This is created by notations like `x + y` - since we resolve `+` to
  /// the `add` term constructor, we know that it is a term constructor and
  /// we have ensured it has the right number of arguments.
  App(Span, TermId, Box<[QExpr]>),
  /// An unquotation `,e`. Here `e` can be any lisp expression, and its
  /// interpretation depends on whether the formula is being evaluated or
  /// is being used as a pattern.
  Unquote(SExpr),
}

impl EnvDisplay for QExpr {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &self.k {
      QExprKind::IdentApp(sp, es) if es.is_empty() =>
        fe.source.str_at(sp.clone()).fmt(f),
      QExprKind::IdentApp(sp, es) => {
        write!(f, "({}", fe.source.str_at(sp.clone()))?;
        for e in &**es {write!(f, " {}", fe.to(e))?}
        write!(f, ")")
      }
      QExprKind::App(_, t, es) => {
        write!(f, "({}", fe.to(t))?;
        for e in &**es {write!(f, " {}", fe.to(e))?}
        write!(f, ")")
      }
      QExprKind::Unquote(e) => write!(f, ",{}", fe.to(e))
    }
  }
}

impl Elaborator {
  /// Parse a [`Formula`] object into a [`QExpr`].
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
      check_parens: self.options.check_parens,
      mm0_mode: self.mm0_mode,
      spans: &mut self.spans,
    };
    p.ws();
    let expr = p.expr(Prec::Prec(0))?.0;
    if let Some(tk) = p.token() {
      return Err(ElabError::new_e(tk, "expected '$'"))
    }
    assert!(p.imports.is_empty());
    for e in p.p.errors { self.report(e.into()) }
    Ok(expr)
  }
}

struct MathParser<'a> {
  check_parens: bool,
  mm0_mode: bool,
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
        b'-' if !self.mm0_mode && self.source[self.idx + 1] == b'-' => {
          let start = self.idx;
          self.idx += 2;
          // End the comment skip when you find a line break.
          while !matches!(self.cur(), b'\n' | b'$') { self.idx += 1 }
          self.spans.insert((start..self.idx).into(), ObjectKind::MathComment);
        }
        _ => return
      }
    }
  }

  fn chr(&mut self, c: u8) -> Option<usize> {
    if self.cur_opt()? != c {
      return None
    }
    self.idx += 1;
    (Some(self.idx), self.ws()).0
  }

  fn chr_err(&mut self, c: u8) -> Result<usize, ParseError> {
    self.chr(c).ok_or_else(|| self.err(format!("expecting '{}'", c as char).into()))
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

  fn literals(&mut self, res: &mut SliceUninit<QExpr>, lits: &[Literal],
      consts: &mut Vec<Span>, mut end: usize) -> Result<usize, ParseError> {
    for lit in lits {
      match *lit {
        Literal::Var(i, q) => {
          let e = self.expr(q)?.0;
          end = e.span.end;
          res.set(i, e);
        },
        Literal::Const(ref c) => {
          let tk = self.token().ok_or_else(|| self.err(format!("expecting '{c}'").into()))?;
          if *self.span(tk.clone()) != **c {
            return Err(ParseError::new(tk, format!("expecting '{c}'").into()))
          }
          consts.push(tk.clone());
          end = tk.end;
        }
      }
    }
    Ok(end)
  }

  fn prefix(&mut self, p: Prec) -> Result<(QExpr, Prec, Option<Prec>), ParseError> {
    let start = self.idx;
    let c = match self.cur() {
      b',' if {
        let c = self.source[self.idx+1];
        !(whitespace(c) || c == b'$')
      } => {
        self.idx += 1;
        let e = self.sexpr()?;
        let e = QExpr {span: (start..e.span.end).into(), k: QExprKind::Unquote(e) };
        return Ok((e, Prec::Max, None))
      }
      b'(' => {
        self.idx += 1;
        self.ws();
        let (mut e, actual) = self.expr(Prec::Prec(0))?;
        e.span = (start..self.chr_err(b')')?).into();
        return Ok((e, Prec::Max, Some(actual)))
      }
      c => c
    };
    let sp = self.token().ok_or_else(|| self.err("expecting expression".into()))?;
    let v = self.span(sp.clone());
    if let Some(&(_, q)) = self.pe.consts.get(v) {
      if q >= p {
        if let Some(info) = self.pe.prefixes.get(v) {
          let mut args = SliceUninit::new(info.nargs);
          let mut consts = vec![sp.clone()];
          let end = self.literals(&mut args, &info.lits, &mut consts, sp.end)?;
          let span: Span = (start..end).into();
          for sp in consts { self.spans.insert(sp, ObjectKind::TermNota(info.term, span.clone())); }
          // Safety: We checked in elab_gen_nota that the lits array contains every index,
          // so every item in `args` gets initialized exactly once by the literals() call
          let k = QExprKind::App(sp, info.term, unsafe { args.assume_init() });
          return Ok((QExpr { span, k }, q, None))
        }
      }
    } else if ident_start(c) && (sp.start + 1..sp.end).all(|i| ident_rest(self.source[i])) {
      let mut args = Vec::new();
      let mut start = self.idx;
      let mut span = sp.clone();
      if p <= APP_PREC {
        while let Ok((e, _)) = self.expr(Prec::Max) {
          span.end = e.span.end;
          start = self.idx;
          args.push(e);
        }
      }
      self.idx = start;
      let actual = if args.is_empty() { Prec::Max } else { APP_PREC };
      let e = QExpr {span, k: QExprKind::IdentApp(sp, args.into_boxed_slice())};
      return Ok((e, actual, None))
    }
    Err(ParseError::new(sp, format!("expecting prefix expression >= {p}").into()))
  }

  fn check_paren(&mut self, e: &mut (QExpr, Prec, Option<Prec>), p: Prec) {
    if !self.check_parens { return }
    if let Some(actual) = e.2.take() {
      if p <= actual {
        self.p.errors.push(ParseError {
          pos: e.0.span.clone(), level: ErrorLevel::Warning,
          msg: "unnecessary parentheses".into()
        })
      }
    }
  }

  fn lhs(&mut self,
    p: Prec, mut lhs: (QExpr, Prec, Option<Prec>),
  ) -> Result<(QExpr, Prec, Option<Prec>), ParseError> {
    let mut tok_end = self.peek_token();
    while let Some(tk) = tok_end.0.clone() {
      let s = self.span(tk.clone());
      let Some(&(_, p1)) = self.pe.consts.get(s) else { break };
      if p1 < p { break }
      let Some(info) = self.pe.infixes.get(s) else { break };
      self.idx = tok_end.1;
      let mut args = SliceUninit::new(info.nargs);
      let start = lhs.0.span.start;
      let lits = {
        let Some((&Literal::Var(i, q), lits)) = info.lits.split_first() else { unreachable!() };
        self.check_paren(&mut lhs, q);
        args.set(i, lhs.0); lits
      };
      let mut consts = vec![tk.clone()];
      let end;
      if let Some((&Literal::Var(i, q), mid)) = lits.split_last() {
        self.literals(&mut args, &mid[1..], &mut consts, 0)?;
        let mut rhs = self.prefix(q)?;
        loop {
          tok_end = self.peek_token();
          let Some(tk) = tok_end.0.clone() else { break };
          let s = self.span(tk);
          let Some(info2) = self.pe.infixes.get(s) else { break };
          let q = self.pe.consts[s].1;
          let assoc = info2.rassoc.expect("infix with no associativity");
          if !(if assoc {q >= p1} else {q > p1}) { break }
          rhs = self.lhs(q, rhs)?;
        }
        self.check_paren(&mut rhs, q);
        end = rhs.0.span.end;
        args.set(i, rhs.0)
      } else if lits.is_empty() {
        end = tk.end
      } else {
        end = self.literals(&mut args, &lits[1..], &mut consts, tk.end)?;
        tok_end = self.peek_token();
      }
      let span: Span = (start..end).into();
      for sp in consts { self.spans.insert(sp, ObjectKind::TermNota(info.term, span.clone())); }
      // Safety: We checked in elab_gen_nota that the lits array contains every index,
      // and also lits[1] must be Const(..) since lits[0] is Var(..), so even though
      // we skip lits[1] in the cases above, every item in `args` gets initialized
      // exactly once by the literals() call, because all the indices are in Var(..) entries
      let k = QExprKind::App(tk, info.term, unsafe { args.assume_init() });
      lhs.0 = QExpr { span, k };
      lhs.1 = lhs.1.min(p1);
    }
    Ok(lhs)
  }

  fn expr(&mut self, p: Prec) -> Result<(QExpr, Prec), ParseError> {
    let lhs = self.prefix(p)?;
    let mut e = self.lhs(p, lhs)?;
    self.check_paren(&mut e, p);
    Ok((e.0, e.1))
  }
}
