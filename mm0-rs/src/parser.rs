mod ast;

use std::mem;
use std::sync::Arc;
use std::error::Error;
use lsp_types::{Diagnostic, DiagnosticSeverity};
use num::BigUint;
use num::cast::ToPrimitive;
use crate::lined_string::*;
pub use ast::{AST, Span};
use ast::*;

#[derive(Copy, Clone)]
pub enum ErrorLevel {
  Warning,
  Error
}
impl ErrorLevel {
  pub fn to_diag_severity(self) -> DiagnosticSeverity {
    match self {
      ErrorLevel::Warning => DiagnosticSeverity::Warning,
      ErrorLevel::Error => DiagnosticSeverity::Error,
    }
  }
}
pub type BoxError = Box<dyn Error + Send + Sync>;
pub struct ParseError {
  pub pos: Span,
  pub level: ErrorLevel,
  pub msg: BoxError,
}
type Result<T> = std::result::Result<T, ParseError>;

impl ParseError {
  pub fn new(pos: impl Into<Span>, msg: BoxError) -> ParseError {
    ParseError { pos: pos.into(), level: ErrorLevel::Error, msg }
  }

  pub fn to_diag(&self, file: &LinedString) -> Diagnostic {
    Diagnostic {
      range: file.to_range(self.pos),
      severity: Some(self.level.to_diag_severity()),
      code: None,
      source: Some("mm0-rs".to_owned()),
      message: format!("{}", self.msg),
      related_information: None,
    }
  }
}

struct Parser<'a> {
  source: &'a [u8],
  errors: Vec<ParseError>,
  imports: Vec<(Span, String)>,
  idx: usize,
}

fn ident_start(c: u8) -> bool { b'a' <= c && c <= b'z' || b'A' <= c && c <= b'Z' || c == b'_' }
fn ident_rest(c: u8) -> bool { ident_start(c) || b'0' <= c && c <= b'9' }
fn lisp_ident(c: u8) -> bool { ident_rest(c) || b"!%&*/:<=>?^~+-.@".contains(&c) }

impl<'a> Parser<'a> {
  fn cur(&self) -> u8 { self.source[self.idx] }
  fn cur_opt(&self) -> Option<u8> { self.source.get(self.idx).cloned() }

  fn err(&self, msg: BoxError) -> ParseError {
    ParseError::new(self.idx..self.idx, msg)
  }

  fn err_str<T>(&self, msg: &'static str) -> Result<T> {
    Err(self.err(msg.into()))
  }

  fn push_err(&mut self, r: Result<()>) {
    r.unwrap_or_else(|e| self.errors.push(e))
  }

  fn ws(&mut self) {
    while self.idx < self.source.len() {
      let c = self.cur();
      if c == b' ' || c == b'\n' {self.idx += 1; continue}
      if c == b'-' && self.source.get(self.idx + 1) == Some(&b'-') {
        self.idx += 1;
        while self.idx < self.source.len() {
          let c = self.cur();
          self.idx += 1;
          if c == b'\n' {break}
        }
      } else {break}
    }
  }

  fn span(&self, s: Span) -> &'a str {
    unsafe { std::str::from_utf8_unchecked(&self.source[s.start..s.end]) }
  }

  fn chr(&mut self, c: u8) -> Option<usize> {
    if self.cur_opt()? != c {return None}
    self.idx += 1;
    (Some(self.idx), self.ws()).0
  }

  fn chr_err(&mut self, c: u8) -> Result<usize> {
    self.chr(c).ok_or_else(|| self.err(format!("expecting '{}'", c as char).into()))
  }

  fn ident_(&mut self) -> Option<Span> {
    let c = self.cur_opt()?;
    if !ident_start(c) {return None}
    let start = self.idx;
    loop {
      self.idx += 1;
      if !self.cur_opt().map_or(false, ident_rest) {
        return (Some((start..self.idx).into()), self.ws()).0
      }
    }
  }

  fn ident(&mut self) -> Option<Span> {
    self.ident_().filter(|&s| self.span(s) != "_")
  }

  fn ident_err_(&mut self) -> Result<Span> {
    self.ident_().ok_or_else(|| self.err("expecting identifier".into()))
  }

  fn ident_err(&mut self) -> Result<Span> {
    self.ident().ok_or_else(|| self.err("expecting identifier".into()))
  }

  fn formula(&mut self) -> Result<Option<Formula>> {
    if self.cur_opt() != Some(b'$') {return Ok(None)}
    let start = self.idx;
    self.idx += 1;
    while self.idx < self.source.len() {
      let c = self.cur();
      self.idx += 1;
      if c == b'$' {
        let end = self.idx;
        self.ws();
        return Ok(Some(Formula((start..end).into())))
      }
    }
    Err(ParseError::new(
      start..mem::replace(&mut self.idx, start),
      "unclosed formula literal".into()))
  }

  fn modifiers(&mut self) -> (Modifiers, Option<Span>) {
    let mut modifiers = Modifiers::empty();
    loop {
      match self.ident_() {
        None => return (modifiers, None),
        Some(id) => match Modifiers::from_name(self.span(id)) {
          None => return (modifiers, Some(id)),
          Some(m) => {
            if modifiers.intersects(m) { self.push_err(self.err_str("double modifier")) }
            modifiers |= m;
          }
        }
      }
    }
  }

  fn ty(&mut self) -> Result<Type> {
    if let Some(fmla) = self.formula()? {
      Ok(Type::Formula(fmla))
    } else {
      let sort = self.ident_err()?;
      let mut deps = Vec::new();
      while let Some(x) = self.ident() {deps.push(x)}
      Ok(Type::DepType(DepType {sort, deps}))
    }
  }

  fn binder_group(&mut self) ->
      Result<Option<(Span, Vec<(Span, LocalKind)>, Option<Type>)>> {
    let start = self.idx;
    let curly = self.chr(b'{').is_some();
    if !curly && self.chr(b'(').is_none() {return Ok(None)}
    let mut locals = Vec::new();
    loop {
      let dummy = self.chr(b'.').is_some();
      let x = if dummy {Some(self.ident_err_()?)} else {self.ident_()};
      if let Some(x) = x {
        let k =
          if self.span(x) == "_" {LocalKind::Anon}
          else if dummy {LocalKind::Dummy}
          else if curly {LocalKind::Bound}
          else {LocalKind::Reg};
        locals.push((x, k))
      } else {break}
    }
    let ty = if let Some(_) = self.chr(b':') {Some(self.ty()?)} else {None};
    let end = self.chr_err(if curly {b'}'} else {b')'})?;
    Ok(Some(((start..end).into(), locals, ty)))
  }

  fn binders(&mut self) -> Result<Vec<Binder>> {
    let mut bis = Vec::new();
    while let Some((span, locals, ty)) = self.binder_group()? {
      bis.extend(locals.into_iter().map(|local|
        Binder { span, local, ty: ty.clone() }));
    }
    Ok(bis)
  }

  fn arrows(&mut self) -> Result<Vec<Type>> {
    let mut tys = vec![self.ty()?];
    while let Some(_) = self.chr(b'>') {tys.push(self.ty()?)}
    Ok(tys)
  }

  fn lisp_ident(&mut self) -> Result<Span> {
    let start = self.idx;
    while self.idx < self.source.len() {
      let c = self.cur();
      if !lisp_ident(c) {break}
      self.idx += 1;
    }
    if self.idx == start {return self.err_str("expected an s-expression")}
    (Ok((start..self.idx).into()), self.ws()).0
  }

  fn string(&mut self) -> Result<(Span, String)> {
    let start = self.idx;
    if self.cur_opt() != Some(b'\"') {return self.err_str("expected an string literal")}
    self.idx += 1;
    let mut s = String::new();
    while self.idx < self.source.len() {
      match (self.cur(), self.idx += 1).0 {
        b'\\' => s.push(match (self.cur_opt(), self.idx += 1).0 {
          None => break,
          Some(b'\\') => '\\',
          Some(b'n') => '\n',
          Some(b'r') => '\r',
          Some(b'\"') => '\"',
          Some(c) => {
            self.errors.push(ParseError {
              pos: (self.idx - 2..self.idx).into(),
              level: ErrorLevel::Warning,
              msg: "unknown escape sequence".into()
            });
            s.push('\\'); s.push(c as char);
            continue
          }
        }),
        b'\"' => return (Ok(((start..self.idx).into(), s)), self.ws()).0,
        c => s.push(c as char)
      }
    }
    Err(ParseError::new(
      start..mem::replace(&mut self.idx, start),
      "unclosed string literal".into()))
  }

  fn number(&mut self) -> Result<(Span, BigUint)> {
    let start = self.idx;
    let mut val: BigUint = 0u8.into();
    while self.idx < self.source.len() {
      let c = self.cur();
      if !(b'0' <= c && c <= b'9') {break}
      self.idx += 1;
      val = 10u8 * val + (c - b'0');
    }
    if self.idx == start {return self.err_str("expected a number")}
    (Ok(((start..self.idx).into(), val)), self.ws()).0
  }

  pub fn is_atom(&self, e: &SExpr, s: &str) -> bool {
    if let SExpr {span, k: SExprKind::Atom(Atom::Ident)} = e {
      self.span(*span) == s
    } else {false}
  }

  fn sexpr(&mut self) -> Result<SExpr> {
    let e = self.sexpr_dot()?;
    if self.is_atom(&e, ".") {
      Err(ParseError::new(e.span, "'.' is not a valid s-expression".into()))
    } else {Ok(e)}
  }

  fn sexpr_list(&mut self, start: usize, curly: bool, c: u8) -> Result<SExpr> {
    let mut es = Vec::new();
    loop {
      if let Some(end) = self.chr(c) {
        return Ok(SExpr::list(start..end, false, curly, es))
      }
      let e = self.sexpr_dot()?;
      if self.is_atom(&e, ".") {
        if es.is_empty() {
          return Err(ParseError::new(e.span,
            "(. x) partial dotted list is invalid".into()))
        }
        es.push(self.sexpr()?);
        return Ok(SExpr::list(start..self.chr_err(c)?, true, curly, es))
      } else if !curly && self.is_atom(&e, "@") {
        let e = self.sexpr_list(e.span.start, false, c)?;
        return Ok(SExpr::list(start..e.span.end, false, false, {es.push(e); es}))
      }
      es.push(e);
    }
  }

  fn sexpr_dot(&mut self) -> Result<SExpr> {
    let start = self.idx;
    match self.cur_opt() {
      Some(b'\'') => {
        self.idx += 1;
        let e = self.sexpr()?;
        Ok(SExpr::list(start..e.span.end, false, false,
          vec![SExpr::atom(start..start+1, Atom::Quote), e]))
      }
      Some(b',') => {
        self.idx += 1;
        let e = self.sexpr()?;
        Ok(SExpr::list(start..e.span.end, false, false,
          vec![SExpr::atom(start..start+1, Atom::Unquote), e]))
      }
      Some(b'(') => {
        let start = self.idx; self.idx += 1; self.ws();
        self.sexpr_list(start, false, b')')
      }
      Some(b'[') => {
        let start = self.idx; self.idx += 1; self.ws();
        self.sexpr_list(start, false, b']')
      }
      Some(b'{') => {
        let start = self.idx; self.idx += 1; self.ws();
        self.sexpr_list(start, true, b'}')
      }
      Some(b'\"') => {
        let (span, s) = self.string()?;
        Ok(SExpr {span, k: SExprKind::String(s)})
      }
      Some(b'#') => {
        self.idx += 1;
        let mut span = self.ident_err()?;
        match (self.span(span), span.start -= 1).0 {
          "t" => Ok(SExpr {span, k: SExprKind::Bool(true)}),
          "f" => Ok(SExpr {span, k: SExprKind::Bool(false)}),
          k => Err(ParseError {
            pos: span,
            level: ErrorLevel::Error,
            msg: format!("unknown keyword '{}'", k.clone()).into()
          })
        }
      }
      Some(b'$') => {
        let f = self.formula()?.unwrap();
        Ok(SExpr {span: f.0, k: SExprKind::Formula(f)})
      }
      Some(c) if b'0' <= c && c <= b'9' => {
        let (span, n) = self.number()?;
        Ok(SExpr {span, k: SExprKind::Number(n)})
      }
      _ => Ok(SExpr::atom(self.lisp_ident()?, Atom::Ident)),
    }
  }

  fn decl(&mut self, mods: Modifiers, sp: Span, k: DeclKind) -> Result<(usize, Decl)> {
    if !mods.allowed_visibility(k) {
      return Err(ParseError::new(sp, "invalid modifiers for this keyword".into()))
    }
    let id = self.ident_err()?;
    let bis = self.binders()?;
    let ty = if self.chr(b':').is_some() {Some(self.arrows()?)} else {None};
    let val = if self.chr(b'=').is_some() {Some(self.sexpr()?)} else {None};
    Ok((self.chr_err(b';')?, Decl {mods, k, bis, id, ty, val}))
  }

  fn decl_stmt(&mut self, start: usize, m: Modifiers, sp: Span, k: DeclKind) -> Result<Option<Stmt>> {
    let (end, d) = self.decl(m, sp, k)?;
    Ok(Some(Stmt {span: (start..end).into(), k: StmtKind::Decl(d)}))
  }

  fn cnst(&mut self) -> Result<Const> {
    let fmla = self.formula()?.ok_or_else(|| self.err("expected a constant".into()))?;
    let mut trim = fmla.inner();
    for i in trim.rev() {
      if b" \n".contains(&self.source[i]) {trim.end -= 1}
      else {break}
    }
    for i in trim {
      if b" \n".contains(&self.source[i]) {trim.start += 1}
      else {break}
    }
    if trim.any(|i| b" \n".contains(&self.source[i])) {
      return Err(ParseError::new(trim, "constant contains embedded whitespace".into()))
    }
    Ok(Const {fmla, trim})
  }

  fn prec(&mut self) -> Result<Prec> {
    match self.cur_opt() {
      Some(c) if b'0' <= c && c <= b'9' => {
        let (span, n) = self.number()?;
        Ok(Prec::Prec(n.to_u32().ok_or_else(||
          ParseError::new(span, "precedence out of range".into()))?))
      }
      _ => {
        self.ident_().filter(|&id| self.span(id) == "max")
          .ok_or_else(|| self.err("expected number or 'max'".into()))?;
        Ok(Prec::Max)
      }
    }
  }

  fn simple_nota(&mut self, k: SimpleNotaKind) -> Result<(usize, SimpleNota)> {
    let id = self.ident_err()?;
    self.chr_err(b':')?;
    let c = self.cnst()?;
    self.ident_().filter(|&id| self.span(id) == "prec")
      .ok_or_else(|| self.err("expected 'prec'".into()))?;
    let prec = self.prec()?;
    Ok((self.chr_err(b';')?, SimpleNota {k, id, c, prec}))
  }

  fn nota_modifiers(&mut self, m: Modifiers, sp: Span) {
    if !m.is_empty() {
      self.push_err(Err(ParseError::new(sp,
        "notation commands do not take modifiers".into())));
    }
  }

  fn simple_nota_stmt(&mut self, start: usize, m: Modifiers, sp: Span, k: SimpleNotaKind) -> Result<Option<Stmt>> {
    self.nota_modifiers(m, sp);
    let (end, n) = self.simple_nota(k)?;
    Ok(Some(Stmt {span: (start..end).into(), k: StmtKind::SimpleNota(n)}))
  }

  fn literals(&mut self) -> Result<Vec<Literal>> {
    let mut lits = Vec::new();
    loop {
      if self.chr(b'(').is_some() {
        let c = self.cnst()?;
        self.chr_err(b':')?;
        let p = self.prec()?;
        self.chr_err(b')')?;
        lits.push(Literal::Const(c, p));
      } else if let Some(x) = self.ident() {
        lits.push(Literal::Var(x))
      } else {return Ok(lits)}
    }
  }

  fn inout_stmt(&mut self, start: usize, m: Modifiers, sp: Span, out: bool) -> Result<Option<Stmt>> {
    if !m.is_empty() {
      self.push_err(Err(ParseError::new(sp,
        "input/output commands do not take modifiers".into())));
    }
    let mut hs = Vec::new();
    let k = self.ident_err()?;
    self.chr_err(b':')?;
    loop {
      if let Some(end) = self.chr(b';') {
        return Ok(Some(Stmt {span: (start..end).into(), k: StmtKind::Inout {out, k, hs}}))
      }
      hs.push(self.sexpr()?)
    }
  }

  fn stmt(&mut self) -> Result<Option<Stmt>> {
    let start = self.idx;
    if self.chr(b'@').is_some() {
      let e = self.sexpr()?;
      let s = self.stmt()?.ok_or_else(||
        self.err("statement expected after annotation".into()))?;
      return Ok(Some(Stmt {
        span: (start..s.span.end).into(),
        k: StmtKind::Annot(e, Box::new(s))
      }))
    }
    match self.modifiers() {
      (m, None) => {
        if m.is_empty() {Ok(None)}
        else {self.err_str("expected command keyword")}
      }
      (mut m, Some(id)) => match self.span(id) {
        "sort" => {
          if !Modifiers::sort_data().contains(m) {
            self.push_err(self.err_str("sorts do not take visibility modifiers"));
            m &= Modifiers::sort_data();
          }
          let id = self.ident_err()?;
          let end = self.chr_err(b';')?;
          Ok(Some(Stmt {span: (start..end).into(), k: StmtKind::Sort(id, m)}))
        }
        "delimiter" => {
          if !m.is_empty() {
            self.push_err(self.err_str("'delimiter' does not take modifiers"));
          }
          let f1 = self.formula()?.ok_or_else(|| self.err("expected formula".into()))?;
          let delim = match self.formula()? {
            None => Delimiter::Both(f1),
            Some(f2) => Delimiter::LeftRight(f1, f2),
          };
          let end = self.chr_err(b';')?;
          Ok(Some(Stmt {span: (start..end).into(), k: StmtKind::Delimiter(delim)}))
        }
        "term"    => self.decl_stmt(start, m, id, DeclKind::Term),
        "axiom"   => self.decl_stmt(start, m, id, DeclKind::Axiom),
        "theorem" => self.decl_stmt(start, m, id, DeclKind::Theorem),
        "def"     => self.decl_stmt(start, m, id, DeclKind::Def),
        "input"   => self.inout_stmt(start, m, id, false),
        "output"  => self.inout_stmt(start, m, id, true),
        "prefix"  => self.simple_nota_stmt(start, m, id, SimpleNotaKind::Prefix),
        "infixl"  => self.simple_nota_stmt(start, m, id, SimpleNotaKind::Infix {right: false}),
        "infixr"  => self.simple_nota_stmt(start, m, id, SimpleNotaKind::Infix {right: true}),
        "coercion" => {
          self.nota_modifiers(m, id);
          let id = self.ident_err()?;
          self.chr_err(b':')?;
          let from = self.ident_err()?;
          self.chr_err(b'>')?;
          let to = self.ident_err()?;
          let end = self.chr_err(b';')?;
          Ok(Some(Stmt {span: (start..end).into(), k: StmtKind::Coercion {id, from, to}}))
        }
        "notation" => {
          self.nota_modifiers(m, id);
          let id = self.ident_err()?;
          let bis = self.binders()?;
          let ty = if self.chr(b':').is_some() {Some(self.ty()?)} else {None};
          self.chr_err(b'=')?;
          let lits = self.literals()?;
          let prec = if self.chr(b':').is_some() {
            let prec = self.prec()?;
            let r = self.ident_().and_then(|s| match self.span(s) {
              "lassoc" => Some(false),
              "rassoc" => Some(true),
              _ => None
            }).ok_or_else(|| self.err("expected 'lassoc' or 'rassoc'".into()))?;
            Some((prec, r))
          } else {None};
          let end = self.chr_err(b';')?;
          Ok(Some(Stmt {span: (start..end).into(), k: StmtKind::Notation(
            GenNota {id, bis, ty, lits, prec})}))
        }
        "do" => {
          let mut es = Vec::new();
          if self.chr(b'{').is_some() {
            while self.chr(b'}').is_none() {es.push(self.sexpr()?)}
          } else {es.push(self.sexpr()?)}
          let end = self.chr_err(b';')?;
          Ok(Some(Stmt {span: (start..end).into(), k: StmtKind::Do(es)}))
        }
        "import" => {
          let (sp, s) = self.string()?;
          let span = (start..self.chr_err(b';')?).into();
          self.imports.push((sp, s.clone()));
          Ok(Some(Stmt {span, k: StmtKind::Import(sp, s)}))
        }
        k => {
          self.idx = start;
          Err(ParseError {
            pos: id,
            level: ErrorLevel::Error,
            msg: format!("unknown command '{}'", k.clone()).into()
          })
        }
      }
    }
  }

  fn stmt_recover(&mut self) -> Option<Stmt> {
    loop {
      match self.stmt() {
        Ok(d) => return d,
        Err(e) => {
          self.errors.push(e);
          while self.idx < self.source.len() {
            let c = self.cur();
            self.idx += 1;
            if c == b';' {self.ws(); break}
          }
        }
      }
    }
  }
}

pub fn parse(file: Arc<LinedString>, old: Option<(Position, AST)>) ->
    (usize, AST) {
  let (errors, imports, idx, mut stmts) =
    if let Some((pos, mut ast)) = old {
      let (ix, start) = ast.last_checkpoint(file.to_idx(pos).unwrap());
      ast.errors.retain(|e| e.pos.start < start);
      ast.imports.retain(|e| e.0.start < start);
      ast.stmts.truncate(ix);
      (ast.errors, ast.imports, start, ast.stmts)
    } else {Default::default()};
  let mut p = Parser {source: file.as_bytes(), errors, imports, idx};
  while let Some(d) = p.stmt_recover() { stmts.push(d) }
  (0, AST { errors: p.errors, imports: p.imports, source: file, stmts })
}
