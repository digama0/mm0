pub mod environment;

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

struct Elaborator<'a, T: FileServer + ?Sized> {
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
    let ref t = self.env.terms[term.0];
    if t.args.len() != nargs {
      Err(ElabError::with_info(n.id, "incorrect number of arguments".into(),
        vec![(t.span.clone(), "declared here".into())]))?
    }
    let info = NotaInfo { span: self.fspan(n.id), term, rassoc: Some(rassoc), lits };
    match n.k {
      SimpleNotaKind::Prefix => self.pe.add_prefix(tk.clone(), info),
      SimpleNotaKind::Infix {..} => self.pe.add_infix(tk.clone(), info),
    }.map_err(|r| ElabError::with_info(n.id,
      format!("constant '{}' already declared", tk).into(),
      vec![(r.decl1, "declared here".into())]))
  }

  fn elab_stmt(&mut self, stmt: &Stmt) {
    match &stmt.k {
      &StmtKind::Sort(sp, sd) => {
        let s = ArcString::new(self.span(sp).to_owned());
        let fsp = self.fspan(sp);
        if let (_, Err(r)) = self.add_sort(s.clone(), fsp, sd) {
          self.report(ElabError::with_info(sp, r.msg.into(), vec![(r.other, r.othermsg.into())]));
        }
      }
      StmtKind::Decl(d) => self.elab_decl(d),
      StmtKind::Delimiter(Delimiter::Both(f)) => self.pe.add_delimiters(f, f),
      StmtKind::Delimiter(Delimiter::LeftRight(ls, rs)) => self.pe.add_delimiters(ls, rs),
      StmtKind::SimpleNota(n) => {let r = self.elab_simple_nota(n); self.catch(r)}
      &StmtKind::Import(sp, _) => if let Some(ref tok) = self.toks[&sp] {
        self.env.merge(&self.fs.get_elab(tok), sp, &mut self.errors)
      },
      _ => self.report(ElabError::new_e(stmt.span, "unimplemented"))
    }
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

    for s in ast.stmts.iter() { elab.elab_stmt(s) }
    // unimplemented!()
    (elab.errors, elab.env, deps)
  }
}
