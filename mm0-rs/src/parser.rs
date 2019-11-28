mod ast;

use std::sync::Arc;
use lsp_types::{Diagnostic, DiagnosticSeverity};
use crate::lined_string::*;
pub use ast::{AST, Span};
use ast::*;

#[derive(Copy, Clone)]
pub enum ErrorLevel {
  Error
}
impl ErrorLevel {
  pub fn to_diag_severity(self) -> DiagnosticSeverity {
    match self {
      ErrorLevel::Error => DiagnosticSeverity::Error,
    }
  }
}

pub struct ParseError {
  pub pos: Span,
  pub level: ErrorLevel,
  pub msg: Box<dyn FnOnce() -> String>,
}
type Result<T> = std::result::Result<T, ParseError>;

impl ParseError {
  pub fn to_diag(self, file: &LinedString) -> Diagnostic {
    Diagnostic {
      range: file.to_range(self.pos),
      severity: Some(self.level.to_diag_severity()),
      code: None,
      source: Some("mm0-rs".to_owned()),
      message: (self.msg)(),
      related_information: None,
    }
  }
}

fn from_string(s: String) -> Box<dyn FnOnce() -> String> { Box::new(move || s) }

struct Parser<'a> {
  source: &'a [u8],
  errors: Vec<ParseError>,
  idx: usize,
}

fn ident_start(c: u8) -> bool { b'a' <= c && c <= b'z' || b'A' <= c && c <= b'Z' || c == b'_' }
fn ident_rest(c: u8) -> bool { ident_start(c) || b'0' <= c && c <= b'9' }

impl<'a> Parser<'a> {
  fn cur(&self) -> u8 { self.source[self.idx] }
  fn cur_opt(&self) -> Option<u8> { self.source.get(self.idx).cloned() }

  fn err(&self, msg: impl 'static + FnOnce() -> String) -> ParseError {
    ParseError {
      pos: self.idx..self.idx,
      level: ErrorLevel::Error,
      msg: Box::new(msg)
    }
  }

  fn err_str<T>(&self, msg: &'static str) -> Result<T> {
    Err(self.err(move || msg.to_owned()))
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

  fn span(&self, s: &Span) -> &'a str {
    unsafe { std::str::from_utf8_unchecked(&self.source[s.clone()]) }
  }

  fn chr(&mut self, c: u8) -> Option<()> {
    if self.cur_opt()? != c {return None}
    self.idx += 1;
    self.ws();
    Some(())
  }

  fn chr_err(&mut self, c: u8) -> Result<()> {
    self.chr(c).ok_or_else(|| ParseError {
      pos: self.idx..self.idx + 1,
      level: ErrorLevel::Error,
      msg: Box::new(move || format!("expecting '{}'", c as char)),
    })
  }

  fn ident(&mut self) -> Option<Span> {
    let c = self.cur_opt()?;
    if !ident_start(c) {return None}
    let start = self.idx;
    loop {
      self.idx += 1;
      if !self.cur_opt().map_or(false, ident_rest) {
        return (Some(start..self.idx), self.ws()).0
      }
    }
  }

  fn ident_err(&mut self) -> Result<Span> {
    self.ident().ok_or_else(|| self.err(|| "expecting identifier".to_owned()))
  }

  fn modifiers(&mut self) -> (Modifiers, Option<Span>) {
    let mut modifiers = Modifiers::empty();
    loop {
      match self.ident() {
        None => return (modifiers, None),
        Some(id) => match Modifiers::from_name(self.span(&id)) {
          None => return (modifiers, Some(id)),
          Some(m) => {
            if modifiers.intersects(m) { self.push_err(self.err_str("double modifier")) }
            modifiers |= m;
          }
        }
      }
    }
  }

  fn decl(&mut self) -> Result<Option<Decl>> {
    match self.modifiers() {
      (m, None) => {
        if m.is_empty() {Ok(None)}
        else {self.err_str("expected command keyword")}
      }
      (mut m, Some(id)) => match self.span(&id) {
        "sort" => {
          if !Modifiers::sort_data().contains(m) {
            self.push_err(self.err_str("sorts do not take visibility modifiers"));
            m &= Modifiers::sort_data();
          }
          let id = self.ident_err()?;
          self.chr_err(b';')?;
          Ok(Some(Decl::Sort(id, m)))
        },
        k => Err(ParseError {
          pos: id,
          level: ErrorLevel::Error,
          msg: from_string(format!("unknown command '{}'", k.clone()))
        })
      }
    }
  }

  fn decl_recover(&mut self) -> Option<Decl> {
    loop {
      match self.decl() {
        Ok(d) => return d,
        Err(e) => {
          self.errors.push(e);
          while self.idx < self.source.len() {
            let c = self.cur();
            self.idx += 1;
            if c == b';' {break}
          }
        }
      }
    }
  }
}

pub fn parse(file: Arc<LinedString>, _old: Option<(Position, AST)>) ->
    (usize, Vec<ParseError>, AST) {
  let mut p = Parser {
    source: file.as_bytes(),
    errors: Vec::new(),
    idx: 0
  };
  let mut decls = Vec::new();
  while let Some(d) = p.decl_recover() { decls.push(d) }
  (0, p.errors, AST { source: file, decls })
}

