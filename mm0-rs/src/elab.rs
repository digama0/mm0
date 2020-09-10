//! The elaborator - the MM1 execution and proof engine.
//!
//! Elaboration is the process of executing all the scripts in an MM1 file in order to
//! obtain a completed proof object (an [`Environment`]) for everything in the file.
//! The [`Elaborator`] struct contains the working data for elaboration, and it is discarded
//! once the file is completed. Elaborators are not shared between files, and
//! [`Environment`]s are copied on import.
//!
//! [`Environment`]: environment/struct.Environment.html
//! [`Elaborator`]: struct.Elaborator.html

pub mod environment;
pub mod spans;
pub mod lisp;
#[macro_use] mod frozen;
pub mod math_parser;
pub mod local_context;
pub mod refine;
pub mod proof;

use std::ops::{Deref, DerefMut};
use std::mem;
use std::result::Result as StdResult;
use std::sync::{Arc, atomic::{AtomicBool, Ordering}};
use std::time::{Instant, Duration};
use std::path::PathBuf;
use std::collections::HashMap;
use std::{future::Future, pin::Pin, task::{Context, Poll}};
use futures::channel::oneshot::{Receiver, channel};
use environment::*;
use environment::Literal as ELiteral;
use lisp::LispVal;
use spans::Spans;
pub use {environment::Environment, local_context::LocalContext};
pub use crate::parser::ErrorLevel;
pub use frozen::{FrozenEnv, FrozenLispKind, FrozenLispVal, FrozenAtomData};
use crate::util::*;
use crate::parser::{*, ast::*, ast::Literal as ALiteral};
use crate::lined_string::*;

#[cfg(feature = "server")]
use lsp_types::{Diagnostic, DiagnosticRelatedInformation, Location};

/// An error payload.
#[derive(Debug, DeepSizeOf)]
pub enum ElabErrorKind {
  /// A boxed error. The main [`BoxError`] is the error message,
  /// and the `Vec<(FileSpan, BoxError)>` is a list of other positions
  /// related to the error, along with short descriptions.
  ///
  /// [`BoxError`]: ../util/type.BoxError.html
  Boxed(BoxError, Option<Vec<(FileSpan, BoxError)>>),
}
impl ElabErrorKind {
  /// Converts the error message to a `String`.
  pub fn msg(&self) -> String {
    match self {
      ElabErrorKind::Boxed(e, _) => format!("{}", e),
    }
  }

  /// Converts the error's related info to the LSP version, a list of
  /// [`DiagnosticRelatedInformation`].
  ///
  /// # Parameters
  ///
  /// - `to_loc`: A function to convert the `FileSpan` locations into the LSP [`Location`]
  ///   type. (This is basically [`LinedString::to_loc`] but can't be done locally because
  ///   it requires the [`LinedString`] for the file to convert the index to line/col.)
  ///
  /// [`DiagnosticRelatedInformation`]: ../../lsp_types/struct.DiagnosticRelatedInformation.html
  /// [`Location`]: ../../lsp_types/struct.Location.html
  /// [`LinedString`]: ../lined_string/struct.LinedString.html
  /// [`LinedString::to_loc`]: ../lined_string/struct.LinedString.html#method.to_loc
  #[cfg(feature = "server")]
  pub fn to_related_info(&self, mut to_loc: impl FnMut(&FileSpan) -> Location) -> Option<Vec<DiagnosticRelatedInformation>> {
    match self {
      ElabErrorKind::Boxed(_, Some(info)) =>
        Some(info.iter().map(|(fs, e)| DiagnosticRelatedInformation {
          location: to_loc(fs),
          message: format!("{}", e),
        }).collect()),
      _ => None
    }
  }
}

impl From<BoxError> for ElabErrorKind {
  fn from(e: BoxError) -> ElabErrorKind { ElabErrorKind::Boxed(e, None) }
}

/// The main error type for the elaborator. Each error has a location (which must be in
/// the currently elaborating file), an error level, a message, and an optional list of
/// related locations (possibly in other files) along with short messages.
#[derive(Debug, DeepSizeOf)]
pub struct ElabError {
  /// The location of the error in the current file.
  pub pos: Span,
  /// The severity of the error or message
  pub level: ErrorLevel,
  /// The type of error (currently there is only [`ElabErrorKind::Boxed`])
  ///
  /// [`ElabErrorKind::Boxed`]: enum.ElabErrorKind.html#variant.Boxed
  pub kind: ElabErrorKind,
}

/// The main result type used by functions in the elaborator.
pub type Result<T> = StdResult<T, ElabError>;

impl ElabError {

  /// Make an elaboration error from a position and an [`ElabErrorKind`].
  ///
  /// [`ElabErrorKind`]: enum.ElabErrorKind.html
  pub fn new(pos: impl Into<Span>, kind: ElabErrorKind) -> ElabError {
    ElabError { pos: pos.into(), level: ErrorLevel::Error, kind }
  }

  /// Make an elaboration error from a position and anything that can be converted to a [`BoxError`].
  ///
  /// [`BoxError`]: ../util/type.BoxError.html
  pub fn new_e(pos: impl Into<Span>, e: impl Into<BoxError>) -> ElabError {
    ElabError::new(pos, ElabErrorKind::Boxed(e.into(), None))
  }

  /// Make an elaboration error from a position, a message, and a list of related info
  pub fn with_info(pos: impl Into<Span>, msg: BoxError, v: Vec<(FileSpan, BoxError)>) -> ElabError {
    ElabError::new(pos, ElabErrorKind::Boxed(msg, Some(v)))
  }

  /// Make an elaboration warning from a position and a message.
  pub fn warn(pos: impl Into<Span>, e: impl Into<BoxError>) -> ElabError {
    ElabError { pos: pos.into(), level: ErrorLevel::Warning, kind: ElabErrorKind::Boxed(e.into(), None)}
  }

  /// Make an info message at a position
  pub fn info(pos: impl Into<Span>, e: impl Into<BoxError>) -> ElabError {
    ElabError { pos: pos.into(), level: ErrorLevel::Info, kind: ElabErrorKind::Boxed(e.into(), None)}
  }

  /// Convert an `ElabError` into the LSP [`Diagnostic`] type.
  /// Uses `file` to convert the error position to a range, and uses `to_loc` to convert
  /// the positions in other files for the related info.
  ///
  /// [`Diagnostic`]: ../../lsp_types/struct.Diagnostic.html
  #[cfg(feature = "server")]
  pub fn to_diag(&self, file: &LinedString, to_loc: impl FnMut(&FileSpan) -> Location) -> Diagnostic {
    Diagnostic {
      range: file.to_range(self.pos),
      severity: Some(self.level.to_diag_severity()),
      code: None,
      source: Some("mm0-rs".to_owned()),
      message: self.kind.msg(),
      related_information: self.kind.to_related_info(to_loc),
      tags: None,
    }
  }
}

impl From<ParseError> for ElabError {
  fn from(e: ParseError) -> Self {
    ElabError {pos: e.pos, level: e.level, kind: ElabErrorKind::Boxed(e.msg, None) }
  }
}

/// Records the current reporting setting. A report that is suppressed by the reporting mode
/// will not appear in the error list / as a diagnostic, but a fatal error will still prevent
/// proof export.
#[derive(Debug)]
struct ReportMode {
  /// Do we report on errors?
  error: bool,
  /// Do we report on warnings?
  warn: bool,
  /// Do we report on info messages?
  info: bool,
}

impl ReportMode {
  fn new() -> ReportMode {
    ReportMode {error: true, warn: true, info: true}
  }

  fn active(&self, lvl: ErrorLevel) -> bool {
    match lvl {
      ErrorLevel::Error => self.error,
      ErrorLevel::Warning => self.warn,
      ErrorLevel::Info => self.info,
    }
  }
}

/// The `Elaborator` struct contains the working data for elaboration, and is the
/// main interface to MM1 operations (along with [`Evaluator`], which a lisp
/// execution context).
///
/// [`Evaluator`]: lisp/eval/struct.Evaluator.html
#[derive(Debug)]
pub struct Elaborator {
  /// The parsed abstract syntax tree for the file
  ast: Arc<AST>,
  /// The location and name of the currently elaborating file
  path: FileRef,
  /// A flag that will be flipped from another thread to signal that this elaboration
  /// should be abandoned
  cancel: Arc<AtomicBool>,
  /// The accumulated list of errors
  errors: Vec<ElabError>,
  /// The permanent data of the elaborator: the completed proofs and lisp definitions
  pub env: Environment,
  /// The maximum time spent on one lisp evaluation (default 5 seconds)
  timeout: Option<Duration>,
  /// The time at which the current lisp evaluation will be aborted
  cur_timeout: Option<Instant>,
  /// The current proof context
  lc: LocalContext,
  /// Information attached to spans, used for hover queries
  spans: Spans<ObjectKind>,
  /// True if we are currently elaborating an MM0 file
  mm0_mode: bool,
  /// True if we are checking proofs (otherwise we pretend every proof says `theorem foo = '?;`)
  check_proofs: bool,
  /// The current reporting mode, whether we will report each severity of error
  reporting: ReportMode,
}

impl Deref for Elaborator {
  type Target = Environment;
  fn deref(&self) -> &Environment { &self.env }
}
impl DerefMut for Elaborator {
  fn deref_mut(&mut self) -> &mut Environment { &mut self.env }
}

impl Elaborator {
  /// Creates a new `Elaborator` from a parsed [`AST`].
  ///
  /// # Parameters
  ///
  /// - `ast`: The [`AST`] of the parsed MM1/MM0 file (as created by [`parser::parse`])
  /// - `path`: The location of the file being elaborated.
  /// - `mm0_mode`: True if this file is being elaborated in MM0 mode. In MM0 mode,
  ///   the `do` command is disabled, type inference is disabled, modifiers are treated
  ///   differently, and proofs of `theorem` are not allowed.
  /// - `cancel`: An atomic flag that can be flipped in another thread in order to cancel
  ///   the elaboration before completion.
  ///
  /// [`AST`]: ../parser/ast/struct.AST.html
  /// [`parser::parse`]: ../parser/fn.parse.html
  pub fn new(ast: Arc<AST>, path: FileRef, mm0_mode: bool, cancel: Arc<AtomicBool>) -> Elaborator {
    Elaborator {
      ast, path, cancel,
      errors: Vec::new(),
      env: Environment::new(),
      timeout: Some(Duration::from_secs(5)),
      cur_timeout: None,
      lc: LocalContext::new(),
      spans: Spans::new(),
      mm0_mode,
      check_proofs: true,
      reporting: ReportMode::new(),
    }
  }

  fn span(&self, s: Span) -> &str { self.ast.span(s) }

  /// Converts a [`Span`] in the current elaboration file to a [`FileSpan`].
  ///
  /// [`Span`]: ../util/struct.Span.html
  /// [`FileSpan`]: ../util/struct.FileSpan.html
  pub fn fspan(&self, span: Span) -> FileSpan { FileSpan {file: self.path.clone(), span} }

  fn report(&mut self, e: ElabError) {
    if self.reporting.active(e.level) {self.errors.push(e)}
  }
  fn catch(&mut self, r: Result<()>) { r.unwrap_or_else(|e| self.report(e)) }

  fn push_spans(&mut self) {
    self.env.spans.push(mem::take(&mut self.spans));
  }

  fn name_of(&mut self, stmt: &Stmt) -> LispVal {
    match &stmt.k {
      StmtKind::Annot(_, s) => self.name_of(s),
      StmtKind::Decl(d) => LispVal::atom(self.env.get_atom(self.ast.span(d.id))),
      &StmtKind::Sort(id, _) => LispVal::atom(self.env.get_atom(self.ast.span(id))),
      _ => LispVal::bool(false),
    }
  }

  fn elab_simple_nota(&mut self, n: &SimpleNota) -> Result<()> {
    let a = self.env.get_atom(self.ast.span(n.id));
    let term = self.term(a).ok_or_else(|| ElabError::new_e(n.id, "term not declared"))?;
    self.spans.insert(n.id, ObjectKind::Term(term, n.id));
    let tk: ArcString = self.span(n.c.trim).into();
    let (rassoc, nargs, lits) = match n.k {
      SimpleNotaKind::Prefix => {
        let nargs = self.terms[term].args.len();
        let mut lits = Vec::with_capacity(nargs);
        if let Some(m) = nargs.checked_sub(1) {
          for i in 0..m {lits.push(ELiteral::Var(i, Prec::Max))};
          lits.push(ELiteral::Var(m, n.prec));
        }
        (true, nargs, lits)
      }
      SimpleNotaKind::Infix {right} =>
        if let Prec::Prec(i) = n.prec {
          let i2 = i.checked_add(1).ok_or_else(|| ElabError::new_e(n.id, "precedence out of range"))?;
          let (l, r) = if right {(i2, i)} else {(i, i2)};
          self.check_term_nargs(n.id, term, 2)?;
          (right, 2, vec![
            ELiteral::Var(0, Prec::Prec(l)),
            ELiteral::Const(tk.clone()),
            ELiteral::Var(1, Prec::Prec(r))])
        } else {
          return Err(ElabError::new_e(n.id, "max prec not allowed for infix"))
        }
    };
    self.add_const(n.c.trim, n.prec)?;
    let info = NotaInfo { span: self.fspan(n.id), term, nargs, rassoc: Some(rassoc), lits };
    match n.k {
      SimpleNotaKind::Prefix => self.pe.add_prefix(tk.clone(), info),
      SimpleNotaKind::Infix {..} => self.pe.add_infix(tk.clone(), info),
    }.map_err(|r| ElabError::with_info(n.id,
      format!("constant '{}' already declared", tk).into(),
      vec![(r.decl1, "declared here".into())]))
  }

  fn elab_coe(&mut self, id: Span, from: Span, to: Span) -> Result<()> {
    let aid = self.env.get_atom(self.ast.span(id));
    let afrom = self.env.get_atom(self.ast.span(from));
    let ato = self.env.get_atom(self.ast.span(to));
    let t = self.term(aid).ok_or_else(|| ElabError::new_e(id, "term not declared"))?;
    let s1 = self.data[afrom].sort.ok_or_else(|| ElabError::new_e(from, "sort not declared"))?;
    let s2 = self.data[ato].sort.ok_or_else(|| ElabError::new_e(to, "sort not declared"))?;
    self.check_term_nargs(id, t, 1)?;
    self.spans.insert(id, ObjectKind::Term(t, id));
    self.spans.insert(from, ObjectKind::Sort(s1));
    self.spans.insert(to, ObjectKind::Sort(s2));
    let fsp = self.fspan(id);
    self.add_coe(s1, s2, fsp, t)
  }

  fn add_const(&mut self, tk: Span, p: Prec) -> Result<()> {
    let s = self.span(tk).into();
    let fsp = self.fspan(tk);
    self.pe.add_const(s, fsp, p).map_err(|r| ElabError::with_info(tk,
      "constant already declared with a different precedence".into(),
      vec![(r.decl1, "declared here".into())]))
  }

  fn elab_gen_nota(&mut self, nota: &GenNota) -> Result<()> {
    let a = self.env.get_atom(self.ast.span(nota.id));
    let term = self.term(a).ok_or_else(|| ElabError::new_e(nota.id, "term not declared"))?;
    let nargs = nota.bis.len();
    self.check_term_nargs(nota.id, term, nargs)?;
    self.spans.insert(nota.id, ObjectKind::Term(term, nota.id));
    let ast = self.ast.clone();
    let mut vars = HashMap::<&str, (usize, bool)>::new();
    for (idx, bi) in nota.bis.iter().enumerate() {
      match bi.kind {
        LocalKind::Dummy => return Err(ElabError::new_e(bi.local.unwrap_or(bi.span),
          "dummies not permitted in notation declarations")),
        LocalKind::Anon => return Err(ElabError::new_e(bi.local.unwrap_or(bi.span),
          "all variables must be used in notation declaration")),
        _ => { vars.insert(ast.span(bi.local.unwrap_or(bi.span)), (idx, false)); }
      }
    }

    fn bump(yes: bool, sp: Span, p: Prec) -> Result<Prec> {
      if !yes {return Ok(p)}
      if let Prec::Prec(n) = p {
        if let Some(i) = n.checked_add(1) { Ok(Prec::Prec(i)) }
        else {Err(ElabError::new_e(sp, "precedence out of range"))}
      } else {Err(ElabError::new_e(sp, "infix constants cannot have prec max"))}
    }
    let mut get_var = |sp: Span| -> Result<usize> {
      let v = vars.get_mut(ast.span(sp))
        .ok_or_else(|| ElabError::new_e(sp, "variable not found"))?;
      v.1 = true;
      Ok(v.0)
    };

    let mut it = nota.lits.iter().peekable();
    let (mut lits, mut rassoc, infix, tk, prec) = match it.next() {
      None => return Err(ElabError::new_e(nota.id,
        "notation requires at least one literal")),
      Some(&ALiteral::Const(ref cnst, prec)) => (vec![], Some(true), false, cnst, prec),
      Some(&ALiteral::Var(var)) => match it.next() {
        None => return Err(ElabError::new_e(var,
          "notation requires at least one constant")),
        Some(&ALiteral::Var(var)) => return Err(ElabError::new_e(var,
          "notation cannot start with two variables")),
        Some(&ALiteral::Const(ref cnst, prec)) => {
          let rassoc = match nota.prec {
            None => None,
            Some((q, _)) if q != prec => return Err(ElabError::new_e(cnst.fmla.0,
              "notation precedence must match first constant")),
            Some((_, rassoc)) => Some(rassoc),
          };
          let lits = vec![
            ELiteral::Var(get_var(var)?, bump(rassoc.unwrap_or(false), cnst.fmla.0, prec)?),
            ELiteral::Const(self.span(cnst.trim).into())];
          (lits, rassoc, true, cnst, prec)
        }
      }
    };

    self.add_const(tk.trim, prec)?;
    while let Some(lit) = it.next() {
      match *lit {
        ALiteral::Const(ref cnst, prec) => {
          lits.push(ELiteral::Const(self.span(cnst.trim).into()));
          self.add_const(cnst.trim, prec)?;
        }
        ALiteral::Var(var) => {
          let prec = match it.peek() {
            None => {
              let r: bool =
                if let Some(r) = rassoc {r}
                else if let Some((_, r)) = nota.prec {r}
                else {
                  return Err(ElabError::new_e(nota.id,
                    "general infix notation requires explicit associativity"))
                };
              rassoc = Some(r);
              bump(!r, tk.fmla.0, prec)?
            }
            Some(&&ALiteral::Const(ref cnst, prec)) => bump(true, cnst.fmla.0, prec)?,
            Some(ALiteral::Var(_)) => Prec::Max,
          };
          lits.push(ELiteral::Var(get_var(var)?, prec));
        }
      }
    }

    for (_, (i, b)) in vars {
      if !b {
        return Err(ElabError::new_e(nota.bis[i].local.unwrap_or(nota.bis[i].span),
          "variable not used in notation"))
      }
    }
    let s: ArcString = self.span(tk.trim).into();
    let info = NotaInfo { span: self.fspan(nota.id), term, nargs, rassoc, lits };
    match infix {
      false => self.pe.add_prefix(s.clone(), info),
      true => self.pe.add_infix(s.clone(), info),
    }.map_err(|r| ElabError::with_info(nota.id,
      format!("constant '{}' already declared", s).into(),
      vec![(r.decl1, "declared here".into())]))
  }

  fn parse_and_print(&mut self, e: &SExpr) -> Result<()> {
    let val = self.eval_lisp(e)?;
    if val.is_def() {self.print_lisp(e.span, &val)}
    Ok(())
  }
}

/// The result type of [`Elaborator::elab_stmt`].
///
/// [`Elaborator::elab_stmt`]: struct.Elaborator.html#method.elab_stmt
enum ElabStmt { Ok, Import(Span) }

impl Elaborator {
  /// Elaborates a single statement.
  ///
  /// # Returns
  ///
  /// - `Ok(Ok)`: The statement was successfully elaborated
  /// - `Ok(Import(sp))`: The statement is an import statement, so we need to yield
  ///   to the VFS to get the file this statement is referring to.
  /// - `Err(e)`: A fatal error occurred in parsing the statement.
  ///   This can just be pushed to the error list.
  fn elab_stmt(&mut self, stmt: &Stmt, span: Span) -> Result<ElabStmt> {
    self.cur_timeout = self.timeout.and_then(|d| Instant::now().checked_add(d));
    self.spans.set_stmt(span);
    match &stmt.k {
      &StmtKind::Sort(sp, sd) => {
        let a = self.env.get_atom(self.ast.span(sp));
        let fsp = self.fspan(sp);
        let id = self.add_sort(a, fsp, span, sd).map_err(|e| e.into_elab_error(sp))?;
        self.spans.insert(sp, ObjectKind::Sort(id));
      }
      StmtKind::Decl(d) => self.elab_decl(span, d)?,
      StmtKind::Delimiter(Delimiter::Both(f)) => self.pe.add_delimiters(f, f),
      StmtKind::Delimiter(Delimiter::LeftRight(ls, rs)) => self.pe.add_delimiters(ls, rs),
      StmtKind::SimpleNota(n) => self.elab_simple_nota(n)?,
      &StmtKind::Coercion {id, from, to} => self.elab_coe(id, from, to)?,
      StmtKind::Notation(n) => self.elab_gen_nota(n)?,
      &StmtKind::Import(sp, _) => return Ok(ElabStmt::Import(sp)),
      StmtKind::Do(es) => {
        if self.mm0_mode {
          self.report(ElabError::warn(span, "(MM0 mode) do blocks not allowed"))
        }
        for e in es { self.parse_and_print(e)? }
      }
      StmtKind::Annot(e, s) => {
        let v = self.eval_lisp(e)?;
        self.elab_stmt(s, span)?;
        let ann = self.get_atom("annotate");
        let ann = match &self.data[ann].lisp {
          Some((_, e)) => e.clone(),
          None => return Err(ElabError::new_e(e.span, "define 'annotate' before using annotations")),
        };
        let args = vec![v, self.name_of(s)];
        self.call_func(e.span, ann, args)?;
      },
      _ => return Err(ElabError::new_e(span, "unimplemented"))
    }
    Ok(ElabStmt::Ok)
  }
}

/// Creates a future to poll for the completed environment, given an import resolver.
///
/// # Parameters
///
/// - `ast`, `path`, `mm0_mode`, `cancel`: Used to construct the inner `Elaborator`
///   (see [`Elaborator::new`]).
///
/// - `_old`: The last successful parse of the same file, used for incremental elaboration.
///   A value of `Some((idx, errs, env))` means that the new file first differs from the
///   old one at `idx`, and the last parse produced environment `env` with errors `errs`.
///
/// - `mk`: A function which is called when an `import` is encountered, with the [`FileRef`] of
///   the file being imported. It sets up a channel and passes the [`Receiver`] end here,
///   to transfer an [`Environment`] containing the elaborated theorems, as well as any
///   extra data `T`, which is collected and passed through the function.
///
/// # Returns
///
/// A [`Future`] which returns `(toks, errs, env)` with
///
/// - `toks`: The accumulated `T` values passed from `mk` (in the order that `import` statements
///   appeared in the file)
/// - `errs`: The elaboration errors found
/// - `env`: The final environment
///
/// If elaboration of an individual statement fails, the error is pushed and then elaboration
/// continues at the next statement, so the overall elaboration process cannot fail and an
/// environment is always produced.
///
/// [`Elaborator::new`]: struct.Elaborator.html#method.new
/// [`FileRef`]: ../util/struct.FileRef.html
/// [`Receiver`]: ../../futures_channel/oneshot/struct.Receiver.html
/// [`Environment`]: environment/struct.Environment.html
/// [`Future`]: https://doc.rust-lang.org/nightly/core/future/future/trait.Future.html
pub fn elaborate<T>(
  ast: Arc<AST>, path: FileRef, mm0_mode: bool, cancel: Arc<AtomicBool>,
  _old: Option<(usize, Vec<ElabError>, FrozenEnv)>,
  mut mk: impl FnMut(FileRef) -> StdResult<Receiver<(T, FrozenEnv)>, BoxError>
) -> impl Future<Output=(Vec<T>, Vec<ElabError>, FrozenEnv)> {

  type ImportMap<D> = HashMap<Span, (Option<FileRef>, D)>;
  #[derive(Debug)]
  struct FrozenElaborator(Elaborator);
  unsafe impl Send for FrozenElaborator {}

  enum UnfinishedStmt<T> {
    None,
    Import(Span, Receiver<(T, FrozenEnv)>),
  }

  struct ElabFutureInner<T> {
    elab: FrozenElaborator,
    toks: Vec<T>,
    recv: ImportMap<Receiver<(T, FrozenEnv)>>,
    idx: usize,
    progress: UnfinishedStmt<T>
  }

  struct ElabFuture<T>(Option<ElabFutureInner<T>>);

  impl<T> Future for ElabFuture<T> {
    type Output = (Vec<T>, Vec<ElabError>, FrozenEnv);
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
      let this = &mut unsafe { self.get_unchecked_mut() }.0;
      let ElabFutureInner {elab: FrozenElaborator(elab), toks, recv, idx, progress} =
        this.as_mut().expect("poll called after Ready");
      'l: loop {
        match progress {
          UnfinishedStmt::None => {},
          UnfinishedStmt::Import(sp, other) => {
            if let Ok((t, env)) = ready!(unsafe { Pin::new_unchecked(other) }.poll(cx)) {
              toks.push(t);
              let r = elab.env.merge(&env, *sp, &mut elab.errors);
              elab.catch(r);
            }
            *idx += 1;
          }
        }
        let ast = elab.ast.clone();
        while let Some(s) = ast.stmts.get(*idx) {
          if elab.cancel.load(Ordering::Relaxed) {break}
          match elab.elab_stmt(s, s.span) {
            Ok(ElabStmt::Ok) => {}
            Ok(ElabStmt::Import(sp)) => {
              let (file, recv) = recv.remove(&sp).unwrap();
              if let Some(file) = file {
                elab.spans.insert(sp, ObjectKind::Import(file));
              }
              *progress = UnfinishedStmt::Import(sp, recv);
              elab.push_spans();
              continue 'l
            }
            Err(e) => elab.report(e)
          }
          elab.push_spans();
          *idx += 1;
        }
        let ElabFutureInner {elab: FrozenElaborator(elab), toks, ..} = this.take().unwrap();
        return Poll::Ready((toks, elab.errors, FrozenEnv::new(elab.env)))
      }
    }
  }

  let mut recv = HashMap::new();
  let mut elab = Elaborator::new(ast.clone(), path, mm0_mode, cancel);
  for &(sp, ref f) in &ast.imports {
    let path = elab.path.path().parent().map_or_else(|| PathBuf::from(f), |p| p.join(f));
    (|| -> Result<_> {
      let r: FileRef = path.canonicalize().map_err(|e| ElabError::new_e(sp, e))?.into();
      let tok = mk(r.clone()).map_err(|e| ElabError::new_e(sp, e))?;
      recv.insert(sp, (Some(r), tok));
      Ok(())
    })().unwrap_or_else(|e| { elab.report(e); recv.insert(sp, (None, channel().1)); });
  }
  ElabFuture(Some(ElabFutureInner {
    elab: FrozenElaborator(elab),
    toks: vec![],
    recv,
    idx: 0,
    progress: UnfinishedStmt::None,
  }))
}