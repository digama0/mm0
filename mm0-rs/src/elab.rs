pub mod environment;
pub mod lisp;

use std::ops::{Deref, DerefMut};
use std::sync::Arc;
use std::path::PathBuf;
use std::collections::{HashMap};
use lsp_types::{Diagnostic, DiagnosticRelatedInformation};
use environment::*;
use environment::Literal as ELiteral;
pub use environment::Environment;
pub use crate::parser::ErrorLevel;
use crate::util::*;
use crate::parser::{*, ast::*, ast::Literal as ALiteral};
use crate::lined_string::*;

pub enum ElabErrorKind {
  Boxed(BoxError, Option<Vec<(FileSpan, BoxError)>>),
}
impl ElabErrorKind {
  pub fn msg(&self) -> String {
    match self {
      ElabErrorKind::Boxed(e, _) => format!("{}", e),
    }
  }

  pub fn to_related_info(&self, file: &LinedString) -> Option<Vec<DiagnosticRelatedInformation>> {
    match self {
      ElabErrorKind::Boxed(_, Some(info)) =>
        Some(info.iter().map(|(fs, e)| DiagnosticRelatedInformation {
          location: file.to_loc(fs),
          message: format!("{}", e),
        }).collect()),
      _ => None
    }
  }
}

impl From<BoxError> for ElabErrorKind {
  fn from(e: BoxError) -> ElabErrorKind { ElabErrorKind::Boxed(e, None) }
}

pub struct ElabError {
  pub pos: Span,
  pub level: ErrorLevel,
  pub kind: ElabErrorKind,
}
pub type Result<T> = std::result::Result<T, ElabError>;

impl ElabError {
  pub fn new(pos: impl Into<Span>, kind: ElabErrorKind) -> ElabError {
    ElabError { pos: pos.into(), level: ErrorLevel::Error, kind }
  }
  pub fn new_e(pos: impl Into<Span>, e: impl Into<BoxError>) -> ElabError {
    ElabError::new(pos, ElabErrorKind::Boxed(e.into(), None))
  }
  pub fn with_info(pos: impl Into<Span>, msg: BoxError, v: Vec<(FileSpan, BoxError)>) -> ElabError {
    ElabError::new(pos, ElabErrorKind::Boxed(msg, Some(v)))
  }

  pub fn to_diag(&self, file: &LinedString) -> Diagnostic {
    Diagnostic {
      range: file.to_range(self.pos),
      severity: Some(self.level.to_diag_severity()),
      code: None,
      source: Some("mm0-rs".to_owned()),
      message: self.kind.msg(),
      related_information: self.kind.to_related_info(file),
    }
  }
}

pub struct Elaborator<'a, T: FileServer + ?Sized> {
  ast: &'a AST,
  fs: &'a T,
  path: FileRef,
  errors: Vec<ElabError>,
  toks: HashMap<Span, Option<T::WaitToken>>,
  env: Environment,
}

impl<T: FileServer + ?Sized> Deref for Elaborator<'_, T> {
  type Target = Environment;
  fn deref(&self) -> &Environment { &self.env }
}
impl<T: FileServer + ?Sized> DerefMut for Elaborator<'_, T> {
  fn deref_mut(&mut self) -> &mut Environment { &mut self.env }
}

impl<'a, T: FileServer + ?Sized> Elaborator<'a, T> {
  fn new(ast: &'a AST, path: FileRef, fs: &'a T) -> Elaborator<'a, T> {
    Elaborator {
      ast, fs, path,
      errors: Vec::new(),
      toks: HashMap::new(),
      env: Environment::default(),
    }
  }

  fn span(&self, s: Span) -> &str { self.ast.span(s) }
  fn fspan(&self, span: Span) -> FileSpan { FileSpan {file: self.path.clone(), span} }
  fn report(&mut self, e: ElabError) { self.errors.push(e) }
  fn catch(&mut self, r: Result<()>) { r.unwrap_or_else(|e| self.report(e)) }

  fn elab_decl(&mut self, d: &Decl) {
    match d.k {
      _ => self.report(ElabError::new_e(d.id, "unimplemented"))
    }
  }

  fn elab_simple_nota(&mut self, n: &SimpleNota) -> Result<()> {
    let term = self.term(self.span(n.id)).ok_or_else(|| ElabError::new_e(n.id, "term not declared"))?;
    let tk: ArcString = self.span(n.c.trim).into();
    let (rassoc, nargs, lits) = match n.k {
      SimpleNotaKind::Prefix => (true, 1, vec![ELiteral::Var(0, n.prec)]),
      SimpleNotaKind::Infix {right} =>
        if let Prec::Prec(i) = n.prec {
          let i2 = i.checked_add(1).ok_or_else(|| ElabError::new_e(n.id, "precedence out of range"))?;
          let (l, r) = if right {(i2, i)} else {(i, i2)};
          (right, 2, vec![
            ELiteral::Var(0, Prec::Prec(l)),
            ELiteral::Const(tk.clone()),
            ELiteral::Var(1, Prec::Prec(r))])
        } else {Err(ElabError::new_e(n.id, "max prec not allowed for infix"))?},
    };
    self.check_term_nargs(n.id, term, nargs)?;
    let info = NotaInfo { span: self.fspan(n.id), term, rassoc: Some(rassoc), lits };
    match n.k {
      SimpleNotaKind::Prefix => self.pe.add_prefix(tk.clone(), info),
      SimpleNotaKind::Infix {..} => self.pe.add_infix(tk.clone(), info),
    }.map_err(|r| ElabError::with_info(n.id,
      format!("constant '{}' already declared", tk).into(),
      vec![(r.decl1, "declared here".into())]))
  }

  fn elab_coe(&mut self, id: Span, from: Span, to: Span) -> Result<()> {
    let t = self.term(self.span(id)).ok_or_else(|| ElabError::new_e(id, "term not declared"))?;
    let &s1 = self.sort_keys.get(self.span(from)).ok_or_else(|| ElabError::new_e(from, "sort not declared"))?;
    let &s2 = self.sort_keys.get(self.span(to)).ok_or_else(|| ElabError::new_e(to, "sort not declared"))?;
    let fsp = self.fspan(id);
    self.check_term_nargs(id, t, 2)?;
    self.add_coe(s1, s2, fsp, t)
  }

  fn add_const(&mut self, tk: Span, p: Prec) -> Result<()> {
    let s = self.span(tk).into();
    let fsp = self.fspan(tk);
    self.pe.add_const(s, fsp, p).map_err(|r| ElabError::with_info(tk,
      "constant already declared with a different precedence".into(),
      vec![(r.decl1, "declared here".into())]))
  }

  fn elab_gen_nota(&mut self, n: &GenNota) -> Result<()> {
    let term = self.term(self.span(n.id)).ok_or_else(|| ElabError::new_e(n.id, "term not declared"))?;
    self.check_term_nargs(n.id, term, n.bis.len())?;
    let mut vars = HashMap::<&str, (usize, bool)>::new();
    for (i, bi) in n.bis.iter().enumerate() {
      match bi.local.1 {
        LocalKind::Dummy => Err(ElabError::new_e(bi.local.0,
          "dummies not permitted in notation declarations"))?,
        LocalKind::Anon => Err(ElabError::new_e(bi.local.0,
          "all variables must be used in notation declaration"))?,
        _ => { vars.insert(self.ast.span(bi.local.0), (i, false)); }
      }
    }

    fn bump(yes: bool, sp: Span, p: Prec) -> Result<Prec> {
      if !yes {return Ok(p)}
      if let Prec::Prec(n) = p {
        if let Some(i) = n.checked_add(1) { Ok(Prec::Prec(i)) }
        else {Err(ElabError::new_e(sp, "precedence out of range"))}
      } else {Err(ElabError::new_e(sp, "infix constants cannot have prec max"))}
    }
    let mut get_var = |elab: &mut Self, sp: Span| -> Result<usize> {
      let v = vars.get_mut(elab.span(sp))
        .ok_or_else(|| ElabError::new_e(sp, "variable not found"))?;
      v.1 = true;
      Ok(v.0)
    };

    let mut it = n.lits.iter().peekable();
    let (mut lits, mut rassoc, infix, tk, prec) = match it.next() {
      None => Err(ElabError::new_e(n.id, "notation requires at least one literal"))?,
      Some(&ALiteral::Const(ref c, p)) => (vec![], None, false, c, p),
      Some(&ALiteral::Var(v)) => match it.next() {
        None => Err(ElabError::new_e(v, "notation requires at least one constant"))?,
        Some(&ALiteral::Var(v)) => Err(ElabError::new_e(v, "notation cannot start with two variables"))?,
        Some(&ALiteral::Const(ref c, p)) => match n.prec {
          None => Err(ElabError::new_e(n.id, "notation requires at least one constant"))?,
          Some((q, _)) if q != p => Err(ElabError::new_e(c.fmla.0, "notation precedence must match first constant"))?,
          Some((_, r)) =>
            (vec![
              ELiteral::Var(get_var(self, v)?, bump(r, c.fmla.0, p)?),
              ELiteral::Const(self.span(c.trim).into())],
            Some(r), true, c, p)
        }
      }
    };

    self.add_const(tk.trim, prec)?;
    while let Some(lit) = it.next() {
      match lit {
        &ALiteral::Const(ref c, p) => {
          lits.push(ELiteral::Const(self.span(c.trim).into()));
          self.add_const(c.trim, p)?;
        }
        &ALiteral::Var(v) => {
          let prec = match it.peek() {
            None => bump(!rassoc.unwrap_or_else(|| {rassoc = Some(true); true}), tk.fmla.0, prec)?,
            Some(&&ALiteral::Const(ref c, p)) => bump(true, c.fmla.0, p)?,
            Some(ALiteral::Var(_)) => Prec::Max,
          };
          lits.push(ELiteral::Var(get_var(self, v)?, prec));
        }
      }
    }

    for (_, (i, b)) in vars {
      if !b { Err(ElabError::new_e(n.bis[i].local.0, "variable not used in notation"))? }
    }
    let s: ArcString = self.span(tk.trim).into();
    let info = NotaInfo { span: self.fspan(n.id), term, rassoc, lits };
    match infix {
      false => self.pe.add_prefix(s.clone(), info),
      true => self.pe.add_infix(s.clone(), info),
    }.map_err(|r| ElabError::with_info(n.id,
      format!("constant '{}' already declared", s).into(),
      vec![(r.decl1, "declared here".into())]))
  }

  fn elab_stmt(&mut self, stmt: &Stmt) -> Result<()> {
    match &stmt.k {
      &StmtKind::Sort(sp, sd) => {
        let s = ArcString::new(self.span(sp).to_owned());
        let fsp = self.fspan(sp);
        match self.add_sort(s.clone(), fsp, sd) {
          Ok(_) => {}
          Err(AddItemError::Redeclaration(_, r)) =>
            self.report(ElabError::with_info(sp, r.msg.into(), vec![(r.other, r.othermsg.into())])),
          Err(AddItemError::Overflow) =>
            self.report(ElabError::new_e(sp, "too many sorts")),
        }
      }
      StmtKind::Decl(d) => self.elab_decl(d),
      StmtKind::Delimiter(Delimiter::Both(f)) => self.pe.add_delimiters(f, f),
      StmtKind::Delimiter(Delimiter::LeftRight(ls, rs)) => self.pe.add_delimiters(ls, rs),
      StmtKind::SimpleNota(n) => self.elab_simple_nota(n)?,
      &StmtKind::Coercion {id, from, to} => self.elab_coe(id, from, to)?,
      StmtKind::Notation(n) => self.elab_gen_nota(n)?,
      &StmtKind::Import(sp, _) => if let Some(ref tok) = self.toks[&sp] {
        self.env.merge(&self.fs.get_elab(tok), sp, &mut self.errors)?
      },
      _ => Err(ElabError::new_e(stmt.span, "unimplemented"))?
    }
    Ok(())
  }
}

pub trait FileServer {
  type WaitToken: Clone;
  fn request_elab(&self, path: PathBuf, f: impl Fn(BoxError) -> ElabError) ->
    Result<(FileRef, Self::WaitToken)>;

  fn get_elab(&self, tok: &Self::WaitToken) -> Arc<Environment>;

  fn elaborate<'a>(&'a self, path: FileRef, ast: &'a AST,
      _old: Option<(usize, Vec<ElabError>, Arc<Environment>)>) ->
      (Vec<ElabError>, Environment, Vec<FileRef>) {
    let mut elab = Elaborator::new(ast, path, self);
    let mut deps: Vec<FileRef> = Vec::new();
    for (sp, f) in &ast.imports {
      match elab.path.path().join(f).canonicalize()
        .map_err(|e| ElabError::new_e(sp.clone(), e))
        .and_then(|p| self.request_elab(p, |e| ElabError::new_e(sp.clone(), e))) {
        Ok((buf, tok)) => { deps.push(buf); elab.toks.insert(sp.clone(), Some(tok)); }
        Err(e) => { elab.errors.push(e); elab.toks.insert(sp.clone(), None); }
      }
    }

    for s in ast.stmts.iter() {
      let r = elab.elab_stmt(s);
      elab.catch(r)
    }
    (elab.errors, elab.env, deps)
  }
}
