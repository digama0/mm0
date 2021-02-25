//! Front-facing parser for mm0-rs; responsible for actually parsing mm0/mm1 files into an AST.
//!
//! In accordance with the grammar's description of mm0/mm1 files as a sequence of
//! statements, the parser's entry point [`parse`] will attempt to construct an AST
//! from some input by calling [`stmt_recover`](Parser::stmt_recover), which loops over [`stmt`](Parser::stmt)
//! while attempting to recover from any parse errors. The actual [`Parser`]
//! struct is fairly standard; it holds the source as a byte slice, keeping track of the current
//! character as a usize among other things.

// rust lints we want
#![warn(
  bare_trait_objects,
  elided_lifetimes_in_paths,
  missing_copy_implementations,
  missing_debug_implementations,
  future_incompatible,
  rust_2018_idioms,
  trivial_numeric_casts,
  variant_size_differences,
  unreachable_pub,
  unused,
  missing_docs
)]
// all the clippy
#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
// all the clippy::restriction lints we want
#![warn(
  clippy::else_if_without_else,
  clippy::float_arithmetic,
  clippy::get_unwrap,
  clippy::inline_asm_x86_att_syntax,
  clippy::integer_division,
  clippy::rc_buffer,
  clippy::rest_pat_in_fully_bound_structs,
  clippy::string_add,
  clippy::unwrap_used,
  clippy::wrong_pub_self_convention
)]
// all the clippy lints we don't want
#![allow(
  clippy::cognitive_complexity,
  clippy::comparison_chain,
  clippy::default_trait_access,
  clippy::filter_map,
  clippy::inline_always,
  clippy::map_err_ignore,
  clippy::missing_const_for_fn,
  clippy::missing_errors_doc,
  clippy::missing_panics_doc,
  clippy::module_name_repetitions,
  clippy::multiple_crate_versions,
  clippy::option_if_let_else,
  clippy::shadow_unrelated,
  clippy::too_many_lines,
  clippy::use_self
)]

pub mod ast;

use annotate_snippets::snippet::AnnotationType;
use ast::{
  Atom, Binder, Const, Decl, DeclKind, Delimiter, DepType, Formula, GenNota, Literal, LocalKind,
  SExpr, SExprKind, SimpleNota, SimpleNotaKind, Stmt, StmtKind, Type,
};
use mm0_util::{
  let_unchecked, unwrap_unchecked, BoxError, LinedString, Modifiers, Position, Prec, Span,
};
use num::cast::ToPrimitive;
use num::BigUint;
use std::mem;
use std::sync::Arc;

#[cfg(feature = "memory")]
use deepsize_derive::DeepSizeOf;

#[cfg(feature = "server")]
use lsp_types::{Diagnostic, DiagnosticSeverity};

pub use ast::Ast;

/// A documentation comment on an item.
pub type DocComment = Arc<str>;

/// Determines how the error is displayed in an editor.
///
/// Corresponds to the lsp-type crate's [`DiagnosticSeverity`] enum, and is convertible using
/// [`to_diag_severity`](ErrorLevel::to_diag_severity).
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ErrorLevel {
  /// Error level for informational messages, such as the result of `(display)`.
  Info,
  /// Error level for warnings, such as an unfinished proof.
  Warning,
  /// Error level for errors (which may or may not be fatal).
  Error,
}
impl ErrorLevel {
  /// Convert an [`ErrorLevel`] to the LSP [`DiagnosticSeverity`] type.
  #[cfg(feature = "server")]
  #[must_use]
  pub fn to_diag_severity(self) -> DiagnosticSeverity {
    match self {
      ErrorLevel::Info => DiagnosticSeverity::Information,
      ErrorLevel::Warning => DiagnosticSeverity::Warning,
      ErrorLevel::Error => DiagnosticSeverity::Error,
    }
  }

  /// Convert an [`ErrorLevel`] to [`AnnotationType`], used by the CLI compiler.
  #[must_use]
  pub fn to_annotation_type(self) -> AnnotationType {
    match self {
      ErrorLevel::Info => AnnotationType::Info,
      ErrorLevel::Warning => AnnotationType::Warning,
      ErrorLevel::Error => AnnotationType::Error,
    }
  }
}

impl std::fmt::Display for ErrorLevel {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      ErrorLevel::Info => "info",
      ErrorLevel::Warning => "warning",
      ErrorLevel::Error => "error",
    }
    .fmt(f)
  }
}

/// Error type; extends an error message with the offending [`Span`], and an [`ErrorLevel`]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
#[derive(Debug)]
pub struct ParseError {
  /// The location of the error (possibly zero-length,
  /// possibly enclosing an identifier or other object)
  pub pos: Span,
  /// The severity of the error
  pub level: ErrorLevel,
  /// The error message
  pub msg: BoxError,
}

/// Newtype for `Result<T, ParseError>`.
type Result<T> = std::result::Result<T, ParseError>;

impl Clone for ParseError {
  fn clone(&self) -> Self {
    let &ParseError { pos, level, ref msg } = self;
    ParseError { pos, level, msg: format!("{}", msg).into() }
  }
}

impl ParseError {
  /// Construct a parse error at [`Error`](ErrorLevel::Error) severity
  /// from a position and a message
  pub fn new(pos: impl Into<Span>, msg: BoxError) -> ParseError {
    ParseError { pos: pos.into(), level: ErrorLevel::Error, msg }
  }

  /// Convert a parse error to an LSP [`Diagnostic`] object.
  #[cfg(feature = "server")]
  #[must_use]
  pub fn to_diag(&self, file: &LinedString) -> Diagnostic {
    Diagnostic {
      range: file.to_range(self.pos),
      severity: Some(self.level.to_diag_severity()),
      code: None,
      code_description: None,
      source: Some("mm0-rs".to_owned()),
      message: format!("{}", self.msg),
      related_information: None,
      tags: None,
      data: None,
    }
  }
}

/// Implements parser functions as associated methods.
#[derive(Debug)]
pub struct Parser<'a> {
  /// The input file as a byte slice
  pub source: &'a [u8],
  /// The set of accumulated (non-fatal) parse errors
  pub errors: Vec<ParseError>,
  /// The span and contents of all `import` statements spotted thus far
  pub imports: Vec<(Span, Vec<u8>)>,
  /// The current parser position in the string
  pub idx: usize,
  /// The beginning of the first word that looks like a command keyword
  /// after the keyword that begins the currently parsing statement. In the event of a fatal
  /// parse error when parsing a statement, this is used as the place to restart parsing,
  /// otherwise parsing restarts after the `;` that terminates every statement.
  pub restart_pos: Option<usize>,
}

/// return true iff a given character is an acceptable ident starter.
#[must_use]
pub fn ident_start(c: u8) -> bool {
  (b'a'..=b'z').contains(&c) || (b'A'..=b'Z').contains(&c) || c == b'_'
}

/// return true iff a given character is an acceptable ident character.
#[must_use]
pub fn ident_rest(c: u8) -> bool { ident_start(c) || (b'0'..=b'9').contains(&c) }

/// return true iff a given character is an acceptable lisp ident.
#[must_use]
pub fn lisp_ident(c: u8) -> bool { ident_rest(c) || b"!%&*/:<=>?^~+-.@".contains(&c) }

/// return true iff a given character is a space or newline character.
#[must_use]
pub fn whitespace(c: u8) -> bool { c == b' ' || c == b'\n' }

/// Convenience enum for identifying keywords.
enum CommandKeyword {
  Sort,
  Delimiter,
  Term,
  Axiom,
  Theorem,
  Def,
  Input,
  Output,
  Prefix,
  Infixl,
  Infixr,
  Coercion,
  Notation,
  Do,
  Import,
  Exit,
}

impl CommandKeyword {
  fn parse(s: &[u8]) -> Option<CommandKeyword> {
    match s {
      b"sort" => Some(CommandKeyword::Sort),
      b"delimiter" => Some(CommandKeyword::Delimiter),
      b"term" => Some(CommandKeyword::Term),
      b"axiom" => Some(CommandKeyword::Axiom),
      b"theorem" => Some(CommandKeyword::Theorem),
      b"def" => Some(CommandKeyword::Def),
      b"input" => Some(CommandKeyword::Input),
      b"output" => Some(CommandKeyword::Output),
      b"prefix" => Some(CommandKeyword::Prefix),
      b"infixl" => Some(CommandKeyword::Infixl),
      b"infixr" => Some(CommandKeyword::Infixr),
      b"coercion" => Some(CommandKeyword::Coercion),
      b"notation" => Some(CommandKeyword::Notation),
      b"do" => Some(CommandKeyword::Do),
      b"import" => Some(CommandKeyword::Import),
      b"exit" => Some(CommandKeyword::Exit),
      _ => None,
    }
  }
}

type BinderGroup = (Span, Vec<(Span, LocalKind)>, Option<Type>);

impl<'a> Parser<'a> {
  /// Get the character at the parser's index. Does not advance.
  #[must_use]
  pub fn cur(&self) -> u8 { self.source[self.idx] }
  /// Attempt to get the character at the parser's index. Does not advance.
  #[must_use]
  pub fn cur_opt(&self) -> Option<u8> { self.source.get(self.idx).cloned() }

  /// Create a parse error at the current location.
  #[must_use]
  pub fn err(&self, msg: BoxError) -> ParseError { ParseError::new(self.idx..self.idx, msg) }

  /// Create a parser error from a string.
  pub fn err_str<T>(&self, msg: &'static str) -> Result<T> { Err(self.err(msg.into())) }

  fn push_err(&mut self, r: Result<()>) { r.unwrap_or_else(|e| self.errors.push(e)) }

  /// Parse and return a doc comment if one is present,
  /// along with the index of the end of the comment.
  /// If not, just return None.
  fn doc_comment(&mut self) -> Option<(DocComment, usize)> {
    let mut doc = Vec::new();
    let mut end = mem::MaybeUninit::uninit();
    while self.source[self.idx..].starts_with(b"--|") {
      // move past `--|`
      self.idx += 3;
      // take everything up to the end of the line.
      let eol = {
        let slice = &self.source[self.idx..];
        match slice.iter().position(|&b| b == b'\n') {
          None => slice.len(),
          // Allow '\n' to be included so users make a linebreak by
          // inserting an empty doc comment line.
          Some(i) => i + 1,
        }
      };
      doc.extend_from_slice(&self.source[self.idx..self.idx + eol]);
      self.idx += eol;
      end = mem::MaybeUninit::new(self.idx);

      // Needed if doc comment lines are indented.
      while self.cur_opt() == Some(b' ') {
        self.idx += 1
      }
    }

    if doc.is_empty() {
      None
    } else {
      self.ws();
      Some((String::from_utf8(doc).ok()?.into(), unsafe { end.assume_init() }))
    }
  }

  /// Advance the parser past a region of whitespace AND skip past
  /// line comments (`--` style comments)
  fn ws(&mut self) {
    while self.idx < self.source.len() {
      let c = self.cur();
      match c {
        b' ' | b'\n' => {
          self.idx += 1;
          continue
        }
        b'\t' => {
          let start = self.idx;
          self.idx += 1;
          while let Some(b'\t') = self.cur_opt() {
            self.idx += 1
          }
          self
            .errors
            .push(ParseError::new(start..self.idx, "tabs are not permitted in MM0 files".into()))
        }
        b'\r' => {
          let start = self.idx;
          self.idx += 1;
          self.errors.push(ParseError::new(
            start..self.idx,
            "carriage return (windows style newlines) are not permitted in MM0 files".into(),
          ))
        }
        b'-'
          if self.source.get(self.idx + 1) == Some(&b'-')
            && self.source.get(self.idx + 2) != Some(&b'|') =>
        {
          self.idx += 1;
          // End the comment skip when you find a line break.
          while self.idx < self.source.len() {
            let c = self.cur();
            self.idx += 1;
            if c == b'\n' {
              break
            }
          }
        }
        _ => break,
      }
    }
  }

  /// Get the string slice corresponding to a region of the parser's source
  /// by passing a span.
  #[must_use]
  pub fn span(&self, s: Span) -> &'a [u8] { &self.source[s.start..s.end] }

  /// Attempt to parse a specific character `c` at the current parser index.
  /// On failure, returns `None` and does not advance.
  /// On success, advances one character and skips any trailing whitespace.
  fn chr(&mut self, c: u8) -> Option<usize> {
    // If out of input, None
    if self.cur_opt()? != c {
      return None
    }
    self.idx += 1;
    (Some(self.idx), self.ws()).0
  }

  /// Attempt to parse a given character, returning an error on failure.
  /// On failure, does not advance.
  /// On success, advances one character and skips any trailing whitespace.
  pub fn chr_err(&mut self, c: u8) -> Result<usize> {
    self.chr(c).ok_or_else(|| self.err(format!("expecting '{}'", c as char).into()))
  }

  /// Try to parse an `ident` item or the blank (`_`, which is not a valid `ident`).
  /// On failure, does not advance.
  /// On success, advances past the parsed item and any trailing whitespace.
  fn ident_(&mut self) -> Option<Span> {
    let c = self.cur_opt()?;
    if !ident_start(c) {
      return None
    }
    let start = self.idx;
    loop {
      self.idx += 1;
      if !self.cur_opt().map_or(false, ident_rest) {
        let sp = (start..self.idx).into();
        if self.restart_pos.is_none() && CommandKeyword::parse(self.span(sp)).is_some() {
          self.restart_pos = Some(start);
        }
        self.ws();
        break Some(sp)
      }
    }
  }

  /// Attempt to parse an `ident`. This is the same as [`ident_`](Self::ident_),
  /// except that `_` is not accepted.
  /// On success, advances past the ident and any trailing whitespace.
  fn ident(&mut self) -> Option<Span> { self.ident_().filter(|&s| self.span(s) != b"_") }

  /// Attempt to parse an ident or blank, returning an error on failure.
  fn ident_err_(&mut self) -> Result<Span> {
    self.ident_().ok_or_else(|| self.err("expecting identifier".into()))
  }

  fn ident_err(&mut self) -> Result<Span> {
    self.ident().ok_or_else(|| self.err("expecting identifier".into()))
  }

  /// Attempt to parse a `$ .. $` delimited formula.
  /// On success, advances the parser past the formula and any trailing whitespace.
  /// On failure, does not advance the parser.
  fn formula(&mut self) -> Result<Option<Formula>> {
    if self.cur_opt() != Some(b'$') {
      return Ok(None)
    }
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
      "unclosed formula literal".into(),
    ))
  }

  /// Try to parse visibility and sort modifiers.
  fn modifiers(&mut self) -> (Modifiers, Option<Span>) {
    let mut modifiers = Modifiers::empty();
    loop {
      match self.ident_() {
        None => return (modifiers, None),
        Some(id) => match Modifiers::from_name(self.span(id)) {
          Modifiers::NONE => return (modifiers, Some(id)),
          m => {
            if modifiers.intersects(m) {
              self.push_err(self.err_str("double modifier"))
            }
            modifiers |= m;
          }
        },
      }
    }
  }

  /// Try to parse a [`DepType`](Type::DepType) or [`Formula`](Type::Formula).
  /// Examples are the part after the colon in either `(_ : $ some formula $)`
  /// or `(_ : wff x)`, where `(_ : wff)` may or may not have dependencies.
  fn ty(&mut self) -> Result<Type> {
    if let Some(fmla) = self.formula()? {
      Ok(Type::Formula(fmla))
    } else {
      let sort = self.ident_err()?;
      let mut deps = Vec::new();
      while let Some(x) = self.ident() {
        deps.push(x)
      }
      Ok(Type::DepType(DepType { sort, deps: deps.into() }))
    }
  }

  fn binder_group(&mut self) -> Result<Option<BinderGroup>> {
    let start = self.idx;
    let curly = self.chr(b'{').is_some();
    if !curly && self.chr(b'(').is_none() {
      return Ok(None)
    }
    let mut locals = Vec::new();
    loop {
      let dummy = self.chr(b'.').is_some();
      let x = if dummy { Some(self.ident_err_()?) } else { self.ident_() };
      if let Some(x) = x {
        let k = if self.span(x) == b"_" {
          LocalKind::Anon
        } else if dummy {
          LocalKind::Dummy
        } else if curly {
          LocalKind::Bound
        } else {
          LocalKind::Reg
        };
        locals.push((x, k))
      } else {
        break
      }
    }
    let ty = if self.chr(b':').is_some() { Some(self.ty()?) } else { None };
    let end = self.chr_err(if curly { b'}' } else { b')' })?;
    Ok(Some(((start..end).into(), locals, ty)))
  }

  fn binders(&mut self) -> Result<Vec<Binder>> {
    let mut bis = Vec::new();
    while let Some((span, locals, ty)) = self.binder_group()? {
      bis.extend(locals.into_iter().map(|(x, kind)| Binder {
        span,
        local: Some(x),
        kind,
        ty: ty.clone(),
      }))
    }
    Ok(bis)
  }

  fn arrows(&mut self) -> Result<(Vec<Type>, Type)> {
    let mut tys = vec![];
    let mut ret = self.ty()?;
    while self.chr(b'>').is_some() {
      tys.push(mem::replace(&mut ret, self.ty()?))
    }
    Ok((tys, ret))
  }

  fn lisp_ident(&mut self) -> Result<Span> {
    let start = self.idx;
    while self.idx < self.source.len() {
      let c = self.cur();
      if !lisp_ident(c) {
        break
      }
      self.idx += 1;
    }
    if self.idx == start {
      return self.err_str("expected an s-expression")
    }
    (Ok((start..self.idx).into()), self.ws()).0
  }

  /// Try to parse a string literal beginning at the current parser position.
  /// Returns the span of the string literal (including the quotes), and the parsed string,
  /// and returns a failure if the string is not well formed or if there is no
  /// string at the current position.
  fn string(&mut self) -> Result<(Span, Vec<u8>)> {
    let start = self.idx;
    if self.cur_opt() != Some(b'\"') {
      return self.err_str("expected an string literal")
    }
    self.idx += 1;
    let mut s: Vec<u8> = Vec::new();
    while self.idx < self.source.len() {
      match (self.cur(), self.idx += 1).0 {
        b'\\' => s.push(match (self.cur_opt(), self.idx += 1).0 {
          None => break,
          Some(b'\\') => b'\\',
          Some(b'n') => b'\n',
          Some(b'r') => b'\r',
          Some(b'\"') => b'\"',
          Some(b'x') | Some(b'X') if self.idx + 2 <= self.source.len() => {
            let c1 = (self.cur(), self.idx += 1).0;
            let c2 = (self.cur(), self.idx += 1).0;
            if let (Some(h1), Some(h2)) = ((c1 as char).to_digit(16), (c2 as char).to_digit(16)) {
              #[allow(clippy::cast_possible_truncation)]
              {
                (h1 << 4 | h2) as u8
              }
            } else {
              self.errors.push(ParseError {
                pos: (self.idx - 4..self.idx).into(),
                level: ErrorLevel::Warning,
                msg: "invalid hex escape".into(),
              });
              self.idx -= 3;
              b'\\'
            }
          }
          Some(_) => {
            self.errors.push(ParseError {
              pos: (self.idx - 2..self.idx).into(),
              level: ErrorLevel::Warning,
              msg: "unknown escape sequence".into(),
            });
            self.idx -= 1;
            b'\\'
          }
        }),
        b'\"' => return (Ok(((start..self.idx).into(), s)), self.ws()).0,
        c => s.push(c),
      }
    }
    Err(ParseError::new(
      start..mem::replace(&mut self.idx, start),
      "unclosed string literal".into(),
    ))
  }

  /// Attempts to parse a sequence of decimal characters, pushing them on the input `val`.
  /// For example if `val = 23` and `self` contains `"05; ..."` then the parser is advanced to `"; ..."`
  /// and `2305` is returned.
  fn decimal(&mut self, mut val: BigUint) -> BigUint {
    while self.idx < self.source.len() {
      let c = self.cur();
      if !(b'0'..=b'9').contains(&c) {
        break
      }
      self.idx += 1;
      val = 10_u8 * val + (c - b'0');
    }
    val
  }

  /// Parser for number literals, which can be either decimal (`12345`) or hexadecimal (`0xd00d`).
  /// Hexadecimal digits and the `0x` prefix are case insensitive.
  /// This is used for lisp number literals, while MM0 number literals are decimal only and parsed
  /// by [`decimal`](Self::decimal). Does not advance the parser index on failure.
  fn number(&mut self) -> Result<(Span, BigUint)> {
    let start = self.idx;
    let mut val: BigUint = 0_u8.into();
    if self.cur() == b'0' {
      self.idx += 1;
      match self.cur_opt() {
        Some(b'x') | Some(b'X') => {
          self.idx += 1;
          while self.idx < self.source.len() {
            let c = self.cur();
            if (b'0'..=b'9').contains(&c) {
              self.idx += 1;
              val = 16_u8 * val + (c - b'0');
            } else if (b'A'..=b'F').contains(&c) {
              self.idx += 1;
              val = 16_u8 * val + (c - (b'A' - 10));
            } else if (b'a'..=b'f').contains(&c) {
              self.idx += 1;
              val = 16_u8 * val + (c - (b'a' - 10));
            } else {
              break
            }
          }
          if self.idx == start + 2 {
            return self.err_str("expected a number")
          }
        }
        _ => val = self.decimal(val),
      }
    } else {
      val = self.decimal(val);
      if self.idx == start {
        return self.err_str("expected a number")
      }
    }
    (Ok(((start..self.idx).into(), val)), self.ws()).0
  }

  fn is_atom(&self, e: &SExpr, s: &[u8]) -> bool {
    if let SExpr { span, k: SExprKind::Atom(Atom::Ident) } = e {
      self.span(*span) == s
    } else {
      false
    }
  }

  /// Parse an [`SExpr`].
  pub fn sexpr(&mut self) -> Result<SExpr> {
    if let (start, Some((doc, _))) = (self.idx, self.doc_comment()) {
      let e = self.sexpr()?;
      Ok(SExpr { span: (start..e.span.end).into(), k: SExprKind::DocComment(doc, Box::new(e)) })
    } else {
      let e = self.sexpr_dot()?;
      if self.is_atom(&e, b".") {
        Err(ParseError::new(e.span, "'.' is not a valid s-expression".into()))
      } else {
        Ok(e)
      }
    }
  }

  fn curly_list(
    &self, span: impl Into<Span>, curly: bool, es: Vec<SExpr>, dot: Option<SExpr>,
  ) -> SExpr {
    SExpr::curly_list(span.into(), curly, es, dot, |e1, e2| match (&e1.k, &e2.k) {
      (SExprKind::Atom(Atom::Ident), SExprKind::Atom(Atom::Ident)) =>
        self.span(e1.span) == self.span(e2.span),
      _ => false,
    })
  }

  fn sexpr_list(&mut self, start: usize, curly: bool, c: u8) -> Result<SExpr> {
    let mut es = Vec::new();
    loop {
      if let Some(end) = self.chr(c) {
        return Ok(self.curly_list(start..end, curly, es, None))
      }
      let e = self.sexpr_dot()?;
      if self.is_atom(&e, b".") {
        if es.is_empty() {
          return Err(ParseError::new(e.span, "(. x) partial dotted list is invalid".into()))
        }
        let e = self.sexpr()?;
        let end = self.chr_err(c)?;
        return Ok(self.curly_list(start..end, curly, es, Some(e)))
      }
      if !curly && self.is_atom(&e, b"@") {
        let e = self.sexpr_list(e.span.start, false, c)?;
        return Ok(SExpr::list(start..e.span.end, {
          es.push(e);
          es
        }))
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
        Ok(SExpr::list(start..e.span.end, vec![SExpr::atom(start..=start, Atom::Quote), e]))
      }
      Some(b',') => {
        self.idx += 1;
        let e = self.sexpr()?;
        Ok(SExpr::list(start..e.span.end, vec![SExpr::atom(start..=start, Atom::Unquote), e]))
      }
      Some(b'(') => {
        let start = self.idx;
        self.idx += 1;
        self.ws();
        self.sexpr_list(start, false, b')')
      }
      Some(b'[') => {
        let start = self.idx;
        self.idx += 1;
        self.ws();
        self.sexpr_list(start, false, b']')
      }
      Some(b'{') => {
        let start = self.idx;
        self.idx += 1;
        self.ws();
        self.sexpr_list(start, true, b'}')
      }
      Some(b'\"') => {
        let (span, s) = self.string()?;
        Ok(SExpr { span, k: SExprKind::String(s.into()) })
      }
      Some(b'#') => {
        self.idx += 1;
        let mut span = self.ident_err()?;
        match (self.span(span), span.start -= 1).0 {
          b"t" => Ok(SExpr { span, k: SExprKind::Bool(true) }),
          b"f" => Ok(SExpr { span, k: SExprKind::Bool(false) }),
          b"undef" => Ok(SExpr { span, k: SExprKind::Undef }),
          k => Err(ParseError {
            pos: span,
            level: ErrorLevel::Error,
            msg: format!("unknown keyword '{}'", unsafe { std::str::from_utf8_unchecked(k) })
              .into(),
          }),
        }
      }
      Some(b'$') => {
        let f = unwrap_unchecked!(self.formula()?);
        Ok(SExpr { span: f.0, k: SExprKind::Formula(f) })
      }
      Some(c) if (b'0'..=b'9').contains(&c) => {
        let (span, n) = self.number()?;
        Ok(SExpr { span, k: SExprKind::Number(n) })
      }
      _ => Ok(SExpr::atom(self.lisp_ident()?, Atom::Ident)),
    }
  }

  fn decl(&mut self, mods: Modifiers, sp: Span, k: DeclKind) -> Result<(usize, Decl)> {
    if !k.allowed_visibility(mods) {
      return Err(ParseError::new(sp, "invalid modifiers for this keyword".into()))
    }
    let id = self.ident_err_()?;
    let mut bis = self.binders()?;
    let ty = if self.chr(b':').is_some() {
      let (bis2, t) = self.arrows()?;
      bis.extend(bis2.into_iter().map(|ty| Binder {
        span: ty.span(),
        local: None,
        kind: LocalKind::Anon,
        ty: Some(ty),
      }));
      Some(t)
    } else {
      None
    };
    let val = if self.chr(b'=').is_some() { Some(self.sexpr()?) } else { None };
    if ty.is_none() && val.is_none() {
      return self.err_str("type or value expected")
    }
    Ok((self.chr_err(b';')?, Decl { mods, k, bis, id, ty, val }))
  }

  fn decl_stmt(
    &mut self, start: usize, m: Modifiers, sp: Span, k: DeclKind,
  ) -> Result<Option<Stmt>> {
    let (end, d) = self.decl(m, sp, k)?;
    Ok(Some(Stmt::new((start..end).into(), StmtKind::Decl(d))))
  }

  fn cnst(&mut self) -> Result<Const> {
    let fmla = self.formula()?.ok_or_else(|| self.err("expected a constant".into()))?;
    let mut trim = fmla.inner();
    for i in trim.into_iter().rev() {
      if whitespace(self.source[i]) {
        trim.end -= 1
      } else {
        break
      }
    }
    for i in trim {
      if whitespace(self.source[i]) {
        trim.start += 1
      } else {
        break
      }
    }
    if { trim }.any(|i| whitespace(self.source[i])) {
      return Err(ParseError::new(trim, "constant contains embedded whitespace".into()))
    }
    if trim.start >= trim.end {
      return Err(ParseError::new(fmla.0, "constant is empty".into()))
    }
    Ok(Const { fmla, trim })
  }

  fn prec(&mut self) -> Result<Prec> {
    match self.cur_opt() {
      Some(c) if (b'0'..=b'9').contains(&c) => {
        let (span, n) = self.number()?;
        Ok(Prec::Prec(
          n.to_u32().ok_or_else(|| ParseError::new(span, "precedence out of range".into()))?,
        ))
      }
      _ => {
        self
          .ident_()
          .filter(|&id| self.span(id) == b"max")
          .ok_or_else(|| self.err("expected number or 'max'".into()))?;
        Ok(Prec::Max)
      }
    }
  }

  fn simple_nota(&mut self, k: SimpleNotaKind) -> Result<(usize, SimpleNota)> {
    let id = self.ident_err()?;
    self.chr_err(b':')?;
    let c = self.cnst()?;
    self
      .ident_()
      .filter(|&id| self.span(id) == b"prec")
      .ok_or_else(|| self.err("expected 'prec'".into()))?;
    let prec = self.prec()?;
    Ok((self.chr_err(b';')?, SimpleNota { k, id, c, prec }))
  }

  fn modifiers_empty(&mut self, m: Modifiers, sp: Span, msg: &'static str) {
    if !m.is_empty() {
      self.push_err(Err(ParseError::new(sp, msg.into())));
    }
  }

  fn simple_nota_stmt(
    &mut self, start: usize, m: Modifiers, sp: Span, k: SimpleNotaKind,
  ) -> Result<Option<Stmt>> {
    self.modifiers_empty(m, sp, "notation commands do not take modifiers");
    let (end, n) = self.simple_nota(k)?;
    Ok(Some(Stmt::new((start..end).into(), StmtKind::SimpleNota(n))))
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
      } else {
        return Ok(lits)
      }
    }
  }

  fn inout_stmt(
    &mut self, start: usize, m: Modifiers, sp: Span, out: bool,
  ) -> Result<Option<Stmt>> {
    if !m.is_empty() {
      self.push_err(Err(ParseError::new(sp, "input/output commands do not take modifiers".into())));
    }
    let mut hs = Vec::new();
    let k = self.ident_err()?;
    self.chr_err(b':')?;
    loop {
      if let Some(end) = self.chr(b';') {
        return Ok(Some(Stmt::new((start..end).into(), StmtKind::Inout { out, k, hs })))
      }
      hs.push(self.sexpr()?)
    }
  }

  fn delim_chars(&mut self, f: Formula) -> Box<[u8]> {
    let end = f.inner().end;
    let mut it = self.span(f.inner()).iter();
    let mut delims = Vec::new();
    loop {
      match it.next() {
        None => return delims.into_boxed_slice(),
        Some(&c) if whitespace(c) => continue,
        Some(&c) => delims.push(c),
      }
      match it.next() {
        Some(&c) if !whitespace(c) => {
          delims.push(c);
          let mut delim_end = end - it.as_slice().len();
          let start = delim_end - 2;
          loop {
            match it.next() {
              Some(&c) if !whitespace(c) => {
                delims.push(c);
                delim_end += 1
              }
              _ =>
                break self
                  .errors
                  .push(ParseError::new(start..end, "delimiter must have one character".into())),
            }
          }
        }
        _ => (),
      }
    }
  }

  /// Try to parse a statement. Parsing essentially amounts to looping over this
  /// while handling errors.
  fn stmt(&mut self) -> Result<Option<Stmt>> {
    let start = self.idx;
    if let Some((doc, end)) = self.doc_comment() {
      let s = self.stmt()?.ok_or_else(|| {
        ParseError::new(start..end, "statement expected after doc comment".into())
      })?;
      return Ok(Some(Stmt::new((start..s.span.end).into(), StmtKind::DocComment(doc, Box::new(s)))))
    }

    if self.chr(b'@').is_some() {
      let e = self.sexpr()?;
      let s = self.stmt()?.ok_or_else(|| {
        ParseError::new(start..e.span.end, "statement expected after annotation".into())
      })?;
      return Ok(Some(Stmt::new((start..s.span.end).into(), StmtKind::Annot(e, Box::new(s)))))
    }

    let m = self.modifiers();
    self.restart_pos = None;

    match m {
      (m, None) =>
        if m.is_empty() && self.idx == self.source.len() {
          Ok(None)
        } else {
          self.err_str("expected command keyword")
        },
      (mut m, Some(id)) => {
        let k = self.span(id);
        match CommandKeyword::parse(k) {
          Some(CommandKeyword::Sort) => {
            if !Modifiers::sort_data().contains(m) {
              self.push_err(self.err_str("sorts do not take visibility modifiers"));
              m &= Modifiers::sort_data();
            }
            let id = self.ident_err()?;
            let end = self.chr_err(b';')?;
            Ok(Some(Stmt::new((start..end).into(), StmtKind::Sort(id, m))))
          }
          Some(CommandKeyword::Delimiter) => {
            if !m.is_empty() {
              self.push_err(self.err_str("'delimiter' does not take modifiers"));
            }
            let f1 = self.formula()?.ok_or_else(|| self.err("expected formula".into()))?;
            let cs1 = self.delim_chars(f1);
            let delim = match self.formula()? {
              None => Delimiter::Both(cs1),
              Some(f2) => Delimiter::LeftRight(cs1, self.delim_chars(f2)),
            };
            let end = self.chr_err(b';')?;
            Ok(Some(Stmt::new((start..end).into(), StmtKind::Delimiter(delim))))
          }
          Some(CommandKeyword::Term) => self.decl_stmt(start, m, id, DeclKind::Term),
          Some(CommandKeyword::Axiom) => self.decl_stmt(start, m, id, DeclKind::Axiom),
          Some(CommandKeyword::Theorem) => self.decl_stmt(start, m, id, DeclKind::Thm),
          Some(CommandKeyword::Def) => self.decl_stmt(start, m, id, DeclKind::Def),
          Some(CommandKeyword::Input) => self.inout_stmt(start, m, id, false),
          Some(CommandKeyword::Output) => self.inout_stmt(start, m, id, true),
          Some(CommandKeyword::Prefix) =>
            self.simple_nota_stmt(start, m, id, SimpleNotaKind::Prefix),
          Some(CommandKeyword::Infixl) =>
            self.simple_nota_stmt(start, m, id, SimpleNotaKind::Infix { right: false }),
          Some(CommandKeyword::Infixr) =>
            self.simple_nota_stmt(start, m, id, SimpleNotaKind::Infix { right: true }),
          Some(CommandKeyword::Coercion) => {
            self.modifiers_empty(m, id, "notation commands do not take modifiers");
            let id = self.ident_err()?;
            self.chr_err(b':')?;
            let from = self.ident_err()?;
            self.chr_err(b'>')?;
            let to = self.ident_err()?;
            let end = self.chr_err(b';')?;
            Ok(Some(Stmt::new((start..end).into(), StmtKind::Coercion { id, from, to })))
          }
          Some(CommandKeyword::Notation) => {
            self.modifiers_empty(m, id, "notation commands do not take modifiers");
            let id = self.ident_err()?;
            let bis = self.binders()?;
            let ty = if self.chr(b':').is_some() { Some(self.ty()?) } else { None };
            self.chr_err(b'=')?;
            let lits = self.literals()?;
            let prec = if self.chr(b':').is_some() {
              let prec = self.prec()?;
              let r = self
                .ident_()
                .and_then(|s| match self.span(s) {
                  b"lassoc" => Some(false),
                  b"rassoc" => Some(true),
                  _ => None,
                })
                .ok_or_else(|| self.err("expected 'lassoc' or 'rassoc'".into()))?;
              Some((prec, r))
            } else {
              None
            };
            let end = self.chr_err(b';')?;
            Ok(Some(Stmt::new(
              (start..end).into(),
              StmtKind::Notation(GenNota { id, bis, ty, lits, prec }),
            )))
          }
          Some(CommandKeyword::Do) => {
            self.modifiers_empty(m, id, "do blocks do not take modifiers");
            let mut es = Vec::new();
            if self.chr(b'{').is_some() {
              while self.chr(b'}').is_none() {
                es.push(self.sexpr()?)
              }
            } else {
              es.push(self.sexpr()?)
            }
            let end = self.chr_err(b';')?;
            Ok(Some(Stmt::new((start..end).into(), StmtKind::Do(es))))
          }
          Some(CommandKeyword::Import) => {
            self.modifiers_empty(m, id, "import statements do not take modifiers");
            let (sp, s) = self.string()?;
            let span = (start..self.chr_err(b';')?).into();
            self.imports.push((sp, s.clone()));
            Ok(Some(Stmt::new(span, StmtKind::Import(sp, s))))
          }
          Some(CommandKeyword::Exit) => {
            self.modifiers_empty(m, id, "exit does not take modifiers");
            self.chr_err(b';')?;
            self.errors.push(ParseError::new(id, "early exit on 'exit' command".into()));
            Ok(None)
          }
          None => {
            self.idx = start;
            Err(ParseError {
              pos: id,
              level: ErrorLevel::Error,
              msg: format!("unknown command '{}'", unsafe { std::str::from_utf8_unchecked(k) })
                .into(),
            })
          }
        }
      }
    }
  }

  /// Try to parse a [`Stmt`] item while recovering from errors.
  fn stmt_recover(&mut self) -> Option<Stmt> {
    loop {
      let start = self.idx;
      self.restart_pos = None;
      match self.stmt() {
        Ok(d) => return d,
        Err(e) => {
          while let Some(restart) = self.restart_pos {
            self.idx = restart;
            self.restart_pos = None;
            if let Ok(d) = self.stmt() {
              let idx = mem::replace(&mut self.idx, start);
              let src = self.source;
              self.source = &src[..restart];
              match self.stmt() {
                Ok(_) => panic!("expected a parse error"),
                Err(e) => self.errors.push(e),
              }
              self.source = src;
              self.idx = idx;
              return d
            }
          }
          self.errors.push(e);
          let mut last_ws = false;
          while self.idx < self.source.len() {
            let c = self.cur();
            if !mem::replace(&mut last_ws, whitespace(c)) {
              if c == b';' {
                self.idx += 1;
                self.ws();
                break
              }
              if self.ident_().is_some() {
                self.ws();
                if self.restart_pos.is_some() {
                  break
                }
                continue
              }
            }
            self.idx += 1;
          }
        }
      }
    }
  }
}

/// Main entry-point. Creates a [`Parser`] and parses a passed file.
/// `old` contains the last successful parse of the same file, in order to reuse
/// previous parsing work. The [`Position`] denotes the first byte where the
/// new file differs from the old one.
#[must_use]
pub fn parse(file: Arc<LinedString>, old: Option<(Position, Arc<Ast>)>) -> (usize, Ast) {
  let (errors, imports, idx, mut stmts) = if let Some((pos, ast)) = old {
    let (ix, start) = ast.last_checkpoint(file.to_idx(pos).expect("bad line position"));
    match Arc::try_unwrap(ast) {
      Ok(mut ast) => {
        ast.errors.retain(|e| e.pos.start < start);
        ast.imports.retain(|e| e.0.start < start);
        ast.stmts.truncate(ix);
        (ast.errors, ast.imports, start, ast.stmts)
      }
      Err(ast) => (
        ast.errors.iter().filter(|e| e.pos.start < start).cloned().collect(),
        ast.imports.iter().filter(|e| e.0.start < start).cloned().collect(),
        start,
        ast.stmts[..ix].into(),
      ),
    }
  } else {
    Default::default()
  };
  let mut p = Parser { source: file.as_bytes(), errors, imports, idx, restart_pos: None };
  p.ws();
  while let Some(d) = p.stmt_recover() {
    stmts.push(d)
  }
  (0, Ast { errors: p.errors, imports: p.imports, source: file, stmts })
}
