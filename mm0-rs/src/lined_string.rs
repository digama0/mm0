//! Embellished String which carries additional data useful for interacting with language server messages.
//!
//! The [`LinedString::apply_changes`] function is used to realize changes made to a string once those
//! changes are received by mm0-rs from a language server. [`LinedString`] Implements associated
//! methods allowing it to be used nicely with the [`Position`] type specified by the language server protocol.
//!
//! [`LinedString::apply_changes`]: struct.LinedString.html#method.apply_changes
//! [`LinedString`]: struct.LinedString.html
//! [`Position`]: ../../lsp_types/struct.Position.html

use std::mem;
use std::ops::{Deref, Index};
pub use lsp_types::{Position, Url};
use lsp_types::{TextDocumentContentChangeEvent};
use crate::util::{Span, FileSpan};

/// Wrapper around std's String which stores data about the positions of any newline characters.
///
/// Also contains a boolean indicating whether the string has any unicode characters.
/// Unicode is currently unsupported, but this allows the lexer to gracefully handle
/// errors arising from the presence of unicode characters in input.
/// The indices stored in `lines` are the successors of any newline characters.
#[derive(Default, Clone, Debug)]
pub struct LinedString { pub s: String, pub unicode: bool, pub lines: Vec<usize> }

/// Allows [`LinedString`] to be indexed with a [`Span`], since [`Span`] is essentially a range.
///
/// # Safety
/// This function uses `str::get_unchecked()` internally, so it is *unsafe* unless the `Span` used in the index
/// was generated from the file that is being indexed.
/// [`LinedString`]: struct.LinedString.html
/// [`Span`]: ../utils/struct.Span.html
impl Index<Span> for LinedString {
  type Output = str;
  fn index(&self, s: Span) -> &str {
    unsafe { self.get_unchecked(s.start..s.end) }
  }
}

/// Calculates the largest index `n` (on a UTF8 boundary) such that `s[..n]` is at most `chs` UTF-16 codepoints.
/// Used in [`LinedString::lsp_to_idx`] to account for additional character offset introduced by unicode.
///
/// [`LinedString::lsp_to_idx`]: struct.LinedString.html#method.lsp_to_idx
fn lsp_to_idx(s: &str, mut chs: usize) -> usize {
  for (n, c) in s.char_indices() {
    let i = c.len_utf16();
    if chs < i {return n}
    chs -= i;
  }
  s.len()
}

impl LinedString {
  /// Calculate and store information about the positions of any newline
  /// characters in the string, and set 'unicode' to true if the string contains unicode.
  /// The data in 'lines' is actually the positions of the characters immediately after
  /// the line break (so \n.pos + 1).
  fn get_lines(unicode: &mut bool, s: &str) -> Vec<usize> {
    let mut lines = vec![];
    for (b, c) in s.char_indices() {
      if c == '\n' { lines.push(b + 1) }
      if !c.is_ascii() {*unicode = true}
    }
    lines
  }

  /// Turn a character index into an LSP [`Position`]
  ///
  /// [`Position`]: ../../lsp_types/struct.Position.html
  pub fn to_pos(&self, idx: usize) -> Position {
    let (pos, line) = match self.lines.binary_search(&idx) {
      Ok(n) => (idx, n+1),
      Err(n) => (n.checked_sub(1).map_or(0, |i| self.lines[i]), n)
    };
    Position::new(line as u64,
      if self.unicode {
        self[(pos..idx).into()].chars().map(char::len_utf16).sum()
      } else { idx - pos } as u64)
  }

  pub fn to_range(&self, s: Span) -> lsp_types::Range {
    lsp_types::Range {start: self.to_pos(s.start), end: self.to_pos(s.end)}
  }

  pub fn to_loc(&self, fs: &FileSpan) -> lsp_types::Location {
    lsp_types::Location {uri: fs.file.url().clone(), range: self.to_range(fs.span)}
  }

  pub fn num_lines(&self) -> u64 { self.lines.len() as u64 }
  pub fn end(&self) -> Position { self.to_pos(self.s.len()) }

  /// Calculates the byte index of the position `chs` UTF-16 code units after
  /// byte index `start` in the string.
  /// If there's no unicode, we can just use (start + idx).
  /// In the presence of unicode, use the helper function [`lsp_to_idx`] to account
  /// for any additional character offset.
  ///
  /// # Safety
  /// `start` must be a valid index in the string.
  ///
  /// [`to_idx`]: struct.LinedString.html#method.to_idx
  /// [`lsp_to_idx`]: fn.lsp_to_idx.html
  fn lsp_to_idx(&self, start: usize, chs: usize) -> usize {
    start + if self.unicode {
      lsp_to_idx(unsafe { self.get_unchecked(start..) }, chs)
    } else {chs}
  }

  /// Turn an lsp [`Position`] into a usize index. [`Position`] is already zero-based,
  /// but LinedString.lines stores (1 + position) of the actual linebreak characters,
  /// so lines[0] points to the start of line 1, lines[1] points to the start of line 2, etc.
  /// with the start of line 0 just being s.0.
  ///
  /// [`Position`]: ../../lsp_types/struct.Position.html
  pub fn to_idx(&self, pos: Position) -> Option<usize> {
    match pos.line.checked_sub(1) {
      None => Some(self.lsp_to_idx(0, pos.character as usize)),
      Some(n) => self.lines.get(n as usize)
        .map(|&idx| self.lsp_to_idx(idx, pos.character as usize))
    }
  }

  /// Extend a LinedString with the contents of a &str, adding additional newline info as needed.
  pub fn extend(&mut self, s: &str) {
    let len = self.s.len();
    self.s.push_str(s);
    for (b, c) in s.char_indices() {
      if c == '\n' { self.lines.push(b + len + 1) }
      if !c.is_ascii() {self.unicode = true}
    }
  }

  /// Extend a LinedString's contents with the contents of a passed string slice
  /// until it reaches some [`Position`]. Return the portion of the passed string slice
  /// that was not added to the LinedString
  ///
  /// [`Position`]: ../../lsp_types/struct.Position.html
  pub fn extend_until<'a>(&mut self, unicode: bool, s: &'a str, pos: Position) -> &'a str {
    self.unicode |= unicode;
    let end = self.end();
    debug_assert!(end <= pos);
    let (chs, off) = if pos.line == end.line {
      ((pos.character - end.character) as usize, 0)
    } else {
      let len = self.s.len();
      let mut it = s.char_indices();
      (pos.character as usize, loop {
        if let Some((b, c)) = it.next() {
          if c == '\n' {
            self.lines.push(b + len + 1);
            if pos.line == self.num_lines() {
              break b+1
            }
          }
        } else {break s.len()}
      })
    };
    let tail = unsafe { s.get_unchecked(off..) };
    let idx = if unicode { lsp_to_idx(tail, chs) } else {chs};
    let len = self.s.len() + off;
    for (b, c) in unsafe { tail.get_unchecked(..idx) }.char_indices() {
      if c == '\n' { self.lines.push(b + len + 1) }
    }
    let (left, right) = s.split_at(off + idx);
    self.s.push_str(left);
    right
  }

  /// Truncate a LinedString's contents so that it's equal to the character position
  /// indicated by some lsp [`Position`], discarding any unneeded newline data.
  /// Does nothing if the LinedString's contents were already less than or equal
  /// in length to the [`Position`]'s index.
  ///
  /// [`Position`]: ../../lsp_types/struct.Position.html
   pub fn truncate(&mut self, pos: Position) {
    if let Some(idx) = self.to_idx(pos) {
      if idx < self.s.len() {
        self.s.truncate(idx);
        self.lines.truncate(pos.line as usize);
      }
    }
  }

  /// Does a bunch of string juggling to actually realize the contents of an iterator
  /// containing a sequence of [`TextDocumentContentChangeEvent`] messages.
  ///
  /// [`TextDocumentContentChangeEvent`]: ../../lsp_types/struct.TextDocumentContentChangeEvent.html
  pub fn apply_changes(&self, changes: impl Iterator<Item=TextDocumentContentChangeEvent>) ->
      (Position, LinedString) {
    let mut old: LinedString;
    let mut out = LinedString::default();
    let mut uncopied: &str = &self.s;
    let mut first_change = None;
      for TextDocumentContentChangeEvent {range, text: change, ..} in changes {
      if let Some(lsp_types::Range {start, end}) = range {
        if first_change.map_or(true, |c| start < c) { first_change = Some(start) }
        if out.end() > start {
          out.extend(uncopied);
          old = mem::take(&mut out);
          uncopied = &old;
        }
        uncopied = out.extend_until(self.unicode, uncopied, end);
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
    (out.end(), out)
  }
}

impl Deref for LinedString {
  type Target = String;
  fn deref(&self) -> &String { &self.s }
}

impl From<String> for LinedString {
  fn from(s: String) -> LinedString {
    let mut unicode = false;
    let lines = LinedString::get_lines(&mut unicode, &s);
    LinedString {unicode, lines, s}
  }
}
