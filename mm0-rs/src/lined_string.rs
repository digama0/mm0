use std::mem;
use std::ops::Deref;
pub use lsp_types::Position;
use lsp_types::{Range, TextDocumentContentChangeEvent};
use crate::parser::Span;

#[derive(Default, Clone)]
pub struct LinedString { s: String, pub lines: Vec<usize> }

impl LinedString {

  fn get_lines(s: &str) -> Vec<usize> {
    let mut lines = vec![];
    for (b, c) in s.char_indices() {
      if c == '\n' { lines.push(b + 1) }
    }
    lines
  }

  pub fn to_pos(&self, idx: usize) -> Position {
    let (pos, line) = match self.lines.binary_search(&idx) {
      Ok(n) => (idx, n+1),
      Err(n) => (n.checked_sub(1).map_or(0, |i| self.lines[i]), n)
    };
    Position::new(line as u64, (idx - pos) as u64)
  }

  pub fn to_range(&self, s: Span) -> Range {
    Range {start: self.to_pos(s.start), end: self.to_pos(s.end)}
  }

  pub fn num_lines(&self) -> u64 { self.lines.len() as u64 }
  pub fn end(&self) -> Position { self.to_pos(self.s.len()) }

  pub fn to_idx(&self, pos: Position) -> Option<usize> {
    match pos.line.checked_sub(1) {
      None => Some(pos.character as usize),
      Some(n) => self.lines.get(n as usize)
        .map(|&idx| idx + (pos.character as usize))
    }
  }

  pub fn extend(&mut self, s: &str) {
    let len = self.s.len();
    self.s.push_str(s);
    for (b, c) in s.char_indices() {
      if c == '\n' { self.lines.push(b + len + 1) }
    }
  }

  pub fn extend_until<'a>(&mut self, s: &'a str, pos: Position) -> &'a str {
    let end = self.end();
    debug_assert!(end <= pos);
    let (off, tail) = if pos.line == end.line {
      ((pos.character - end.character) as usize, s)
    } else {
      let len = self.s.len();
      self.s.push_str(s);
      let mut it = s.char_indices();
      (pos.character as usize, loop {
        if let Some((b, c)) = it.next() {
          if c == '\n' {
            self.lines.push(b + len + 1);
            if pos.line == self.num_lines() {
              break unsafe { s.get_unchecked(b+1..) }
            }
          }
        } else {break ""}
      })
    };
    let (left, right) = if off < tail.len() {tail.split_at(off)} else {(tail, "")};
    self.extend(left);
    right
  }

  pub fn truncate(&mut self, pos: Position) {
    if let Some(idx) = self.to_idx(pos) {
      if idx < self.s.len() {
        self.s.truncate(idx);
        self.lines.truncate(pos.line as usize);
      }
    }
  }

  pub fn apply_changes(&self, changes: impl Iterator<Item=TextDocumentContentChangeEvent>) ->
      (Position, LinedString) {
    let mut old: LinedString;
    let mut out = LinedString::default();
    let mut uncopied: &str = &self.s;
    let mut first_change = None;
    for TextDocumentContentChangeEvent {range, text: change, ..} in changes {
      if let Some(Range {start, end}) = range {
        if first_change.map_or(true, |c| start < c) { first_change = Some(start) }
        if out.end() > start {
          out.extend(uncopied);
          old = mem::replace(&mut out, LinedString::default());
          uncopied = &old;
        }
        uncopied = out.extend_until(uncopied, end);
        out.truncate(start);
        out.extend(&change);
      } else {
        out = change.into();
        first_change = Some(Position::default());
        uncopied = "";
      }
    }
    out.extend(uncopied);
    if let Some(pos) = first_change {
      let start = out.to_idx(pos).unwrap();
      let from = unsafe { self.s.get_unchecked(start..) };
      let to = unsafe { out.s.get_unchecked(start..) };
      for ((b, c1), c2) in from.char_indices().zip(to.chars()) {
        if c1 != c2 {return (out.to_pos(b + start), out)}
      }
    }
    crate::server::log(format!("{}", out.s));
    (out.end(), out)
  }
}

impl Deref for LinedString {
  type Target = String;
  fn deref(&self) -> &String { &self.s }
}

impl From<String> for LinedString {
  fn from(s: String) -> LinedString {
    LinedString {lines: LinedString::get_lines(&s), s}
  }
}
