pub mod environment;

use std::ops::{Deref, DerefMut};
use std::path::PathBuf;
use std::collections::{HashMap};
use lsp_types::{Diagnostic, DiagnosticRelatedInformation};
pub use environment::Environment;
pub use crate::parser::{ErrorLevel, BoxError};
use crate::parser::{*, ast::*};
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
type Result<T> = std::result::Result<T, ElabError>;

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

struct Elaborator<'a, T> {
  ast: &'a AST,
  path: FileRef,
  errors: Vec<ElabError>,
  toks: HashMap<Span, Option<T>>,
  env: Environment,
}

impl<T> Deref for Elaborator<'_, T> {
  type Target = Environment;
  fn deref(&self) -> &Environment { &self.env }
}
impl<T> DerefMut for Elaborator<'_, T> {
  fn deref_mut(&mut self) -> &mut Environment { &mut self.env }
}

impl<T> Elaborator<'_, T> {
  fn new(ast: &AST, path: FileRef) -> Elaborator<T> {
    Elaborator {
      ast,
      path,
      errors: Vec::new(),
      toks: HashMap::new(),
      env: Environment::default(),
    }
  }

  fn span(&self, s: Span) -> &str { self.ast.span(s) }
  fn fspan(&self, span: Span) -> FileSpan { FileSpan {file: self.path.clone(), span} }
  fn report(&mut self, e: ElabError) { self.errors.push(e) }

  fn add_delimiters(&mut self, ls: &[u8], rs: &[u8]) {
    for &c in ls { self.env.delims_l.set(c) }
    for &c in rs { self.env.delims_r.set(c) }
  }

  fn elaborate_decl(&mut self, stmt: &Stmt, d: &Decl) {
    match d.k {
      _ => self.report(ElabError::new_e(stmt.span, "unimplemented"))
    }
  }

  fn elaborate_stmt(&mut self, stmt: &Stmt) {
    match &stmt.k {
      &StmtKind::Sort(sp, sd) => {
        let s = self.span(sp).to_owned();
        let fsp = self.fspan(sp);
        self.add_sort(s.clone(), fsp, sd).unwrap_or_else(|r|
          self.report(ElabError::with_info(sp, r.msg.into(), vec![(r.other, r.othermsg.into())])))
      }
      StmtKind::Decl(d) => self.elaborate_decl(stmt, d),
      StmtKind::Delimiter(Delimiter::Both(f)) => self.add_delimiters(f, f),
      StmtKind::Delimiter(Delimiter::LeftRight(ls, rs)) => self.add_delimiters(ls, rs),
      _ => self.report(ElabError::new_e(stmt.span, "unimplemented"))
    }
  }
}

pub trait FileServer {
  type WaitToken;
  fn request_elab(&self, path: PathBuf, f: impl Fn(BoxError) -> ElabError) ->
    Result<(FileRef, Self::WaitToken)>;

  fn elaborate(&self, path: FileRef, ast: &AST,
      _old: Option<(usize, Vec<ElabError>, Environment)>) ->
      (Vec<ElabError>, Environment, Vec<FileRef>) {
    let mut elab = Elaborator::new(ast, path);
    let mut deps: Vec<FileRef> = Vec::new();
    for (sp, f) in &ast.imports {
      match elab.path.path().join(f).canonicalize()
        .map_err(|e| ElabError::new_e(sp.clone(), e))
        .and_then(|p| self.request_elab(p, |e| ElabError::new_e(sp.clone(), e))) {
        Ok((buf, tok)) => { deps.push(buf); elab.toks.insert(sp.clone(), Some(tok)); }
        Err(e) => { elab.errors.push(e); elab.toks.insert(sp.clone(), None); }
      }
    }

    for s in ast.stmts.iter() { elab.elaborate_stmt(s) }
    // unimplemented!()
    (elab.errors, elab.env, deps)
  }
}
