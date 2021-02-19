//! Parser for MMB binary proof files.
use std::{mem, io};
use std::convert::{TryFrom, TryInto};
use byteorder::LE;
use zerocopy::{LayoutVerified, FromBytes, U16, U32, U64};
use super::{Header, StmtCmd, TermEntry, ThmEntry, IndexEntry,
  Arg, IndexKind, UnifyCmd, ProofCmd, SortData};
use crate::elab::environment::{SortId, TermId, ThmId};
use crate::util::{Position, cstr_from_bytes_prefix};

/// An iterator over the declaration stream.
#[derive(Debug, Clone)]
pub struct DeclIter<'a> {
  /// The full source file.
  buf: &'a [u8],
  /// The index of the current declaration in the file.
  pub pos: usize,
}

/// A parsed `MMB` file, as a borrowed type. This does only shallow parsing;
/// additional parsing is done on demand via functions on this type.
#[derive(Debug)]
pub struct MmbFile<'a> {
  /// The full file
  buf: &'a [u8],
  /// The sort table
  sorts: &'a [SortData],
  /// The term table
  terms: &'a [TermEntry],
  /// The theorem table
  thms: &'a [ThmEntry],
  /// The index of the beginning of the proof stream
  proof: usize,
  /// The index, if provided.
  index: Option<MmbIndex<'a>>,
}

/// A parsed `MMB` file index.
#[derive(Debug)]
pub struct MmbIndex<'a> {
  /// The full file
  buf: &'a [u8],
  /// A pointer to the root of the binary search tree, for searching based on name.
  root: U64<LE>,
  /// Pointers to the index entries for the sorts
  sorts: &'a [U64<LE>],
  /// Pointers to the index entries for the terms
  terms: &'a [U64<LE>],
  /// Pointers to the index entries for the theorems
  thms: &'a [U64<LE>],
}

/// A handle to an entry in the index.
#[derive(Debug, Clone, Copy)]
pub struct IndexEntryRef<'a> {
  /// The full file
  buf: &'a [u8],
  /// The index entry itself
  entry: &'a IndexEntry,
  /// The C string for the value (actually a suffix of the file
  /// starting at the appropriate location). Note that `strlen` has to be called
  /// to get the end of the string in [`value()`](Self::value()).
  value: &'a [u8],
}

impl<'a> std::ops::Deref for IndexEntryRef<'a> {
  type Target = IndexEntry;
  fn deref(&self) -> &IndexEntry { self.entry }
}

/// An iterator over a proof command stream.
#[derive(Debug, Clone)]
pub struct ProofIter<'a> {
  /// The full source file, but trimmed such that the end
  /// is the expected end of the proof stream. The final call to `next`
  /// will fail if it does not hit the expected end when the
  /// proof stream runs out.
  buf: &'a [u8],
  /// The index of the current proof command in the file.
  pub pos: usize,
}

/// An iterator over a unify command stream.
#[derive(Debug, Clone)]
pub struct UnifyIter<'a> {
  /// The full source file.
  buf: &'a [u8],
  /// The index of the current declaration in the file.
  pub pos: usize,
}

/// A reference to an entry in the term table.
#[derive(Debug, Clone)]
pub struct TermRef<'a> {
  /// The sort of the term.
  sort: u8,
  /// The array of arguments, including the `ret` element at the end.
  args: &'a [Arg],
  /// The pointer to the start of the unify stream.
  unify: UnifyIter<'a>,
}

/// A reference to an entry in the theorem table.
#[derive(Debug, Clone)]
pub struct ThmRef<'a> {
  /// The array of arguments.
  args: &'a [Arg],
  /// The pointer to the start of the unify stream.
  unify: UnifyIter<'a>,
}

/// An error during parsing of an `MMB` file.
#[derive(Debug)]
pub enum ParseError {
  /// The header is bad; this probably means this is not an MMB file.
  BadHeader,
  /// The version is unrecognized.
  BadVersion,
  /// The index is malformed.
  BadIndex,
  /// An error with the provided message and location.
  StrError(&'static str, usize),
  /// An error in IO.
  IoError(io::Error)
}

impl From<io::Error> for ParseError {
  fn from(e: io::Error) -> Self { Self::IoError(e) }
}

impl From<ParseError> for crate::elab::ElabError {
  fn from(e: ParseError) -> Self {
    match e {
      ParseError::BadHeader => Self::new_e(0, "Bad header (not an MMB file?)"),
      ParseError::BadVersion => Self::new_e(0, "Unknown MMB version"),
      ParseError::BadIndex => Self::new_e(0, "MMB index is malformed"),
      ParseError::StrError(s, p) => Self::new_e(p, s),
      ParseError::IoError(e) => Self::new_e(0, e),
    }
  }
}

#[inline] pub(crate) fn u32_as_usize(n: u32) -> usize {
  n.try_into().expect("here's a nickel, get a better computer")
}
#[inline] fn u64_as_usize(n: U64<LE>) -> usize {
  n.get().try_into().expect("here's a nickel, get a better computer")
}

#[inline] fn new_slice_prefix<T: FromBytes>(bytes: &[u8], n: usize) -> Option<(&[T], &[u8])> {
  let mid = mem::size_of::<T>().checked_mul(n)?;
  if mid <= bytes.len() {
    let (left, right) = bytes.split_at(mid);
    Some((LayoutVerified::new_slice(left)?.into_slice(), right))
  } else {
    None
  }
}

fn parse_cmd(bytes: &[u8]) -> Option<(u8, u32, &[u8])> {
  use super::cmd::{DATA_8, DATA_16, DATA_32, DATA_MASK};
  let (cmd, rest) = bytes.split_first()?;
  let val = cmd & !DATA_MASK;
  match cmd & DATA_MASK {
    0 => Some((val, 0, rest)),
    DATA_8 => rest.split_first().map(|(&n, rest)| (val, n.into(), rest)),
    DATA_16 => LayoutVerified::<_, U16<LE>>::
      new_from_prefix(rest).map(|(n, rest)| (val, n.get().into(), rest)),
    DATA_32 => LayoutVerified::<_, U32<LE>>::
      new_from_prefix(rest).map(|(n, rest)| (val, n.get(), rest)),
    _ => unreachable!()
  }
}

impl<'a> MmbFile<'a> {
  /// Parse a `MMBFile` from a file, provided as a byte slice.
  /// This does the minimum checking to construct the parsed object,
  /// it is not a verifier.
  pub fn parse(buf: &'a [u8]) -> Result<MmbFile<'a>, ParseError> {
    use ParseError::{BadHeader, BadVersion, BadIndex};
    use super::cmd::{MM0B_MAGIC, MM0B_VERSION};
    let (header, sorts) = LayoutVerified::<_, Header>::
      new_unaligned_from_prefix(buf).ok_or(BadHeader)?;
    let header = header.into_ref();
    if header.magic != MM0B_MAGIC { return Err(BadHeader) }
    if header.version != MM0B_VERSION { return Err(BadVersion) }
    let sorts = sorts.get(..header.num_sorts.into())
      .and_then(LayoutVerified::new_slice_unaligned)
      .ok_or(BadHeader)?.into_slice();
    let terms = buf.get(u32_as_usize(header.p_terms.get())..)
      .and_then(|s| new_slice_prefix(s, u32_as_usize(header.num_terms.get())))
      .ok_or(BadHeader)?.0;
    let thms = buf.get(u32_as_usize(header.p_thms.get())..)
      .and_then(|s| new_slice_prefix(s, u32_as_usize(header.num_thms.get())))
      .ok_or(BadHeader)?.0;
    let proof = u32_as_usize(header.p_proof.get());
    let index = match u64_as_usize(header.p_index) {
      0 => None,
      n => Some((|| -> Option<_> {
        let (root, rest) = LayoutVerified::<_, U64<LE>>::
        new_unaligned_from_prefix(&*buf.get(n..)?)?;
        let (sorts, rest) = new_slice_prefix(rest, sorts.len())?;
        let (terms, rest) = new_slice_prefix(rest, terms.len())?;
        let (thms, _) = new_slice_prefix(rest, thms.len())?;
        Some(MmbIndex {buf, root: *root, sorts, terms, thms})
      })().ok_or(BadIndex)?)
    };
    Ok(MmbFile {buf, sorts, terms, thms, proof, index})
  }
}

#[inline] fn index_ref(buf: &[u8], n: U64<LE>) -> Option<IndexEntryRef<'_>> {
  let (entry, value) = LayoutVerified::<_, IndexEntry>::
    new_unaligned_from_prefix(&*buf.get(u64_as_usize(n)..)?)?;
  let entry = entry.into_ref();
  Some(IndexEntryRef {buf, entry, value})
}

#[inline] fn term_ref(buf: &[u8], t: TermEntry) -> Option<TermRef<'_>> {
  let (args, unify) = new_slice_prefix(
    buf.get(u32_as_usize(t.p_args.get())..)?, usize::from(t.num_args.get()) + 1)?;
  let unify = UnifyIter {buf, pos: buf.len() - unify.len()};
  Some(TermRef {sort: t.sort, args, unify})
}

#[inline] fn thm_ref(buf: &[u8], t: ThmEntry) -> Option<ThmRef<'_>> {
  let (args, unify) = new_slice_prefix(
    buf.get(u32_as_usize(t.p_args.get())..)?, t.num_args.get().into())?;
  let unify = UnifyIter {buf, pos: buf.len() - unify.len()};
  Some(ThmRef {args, unify})
}

impl<'a> MmbFile<'a> {
  /// Get the sort data for a [`SortId`].
  #[inline] #[must_use] pub fn sort(&self, n: SortId) -> Option<SortData> {
    self.sorts.get(usize::from(n.0)).copied()
  }
  /// Get the term data for a [`TermId`].
  #[inline] #[must_use] pub fn term(&self, n: TermId) -> Option<TermRef<'_>> {
    term_ref(self.buf, *self.terms.get(u32_as_usize(n.0))?)
  }
  /// Get the theorem data for a [`ThmId`].
  #[inline] #[must_use] pub fn thm(&self, n: ThmId) -> Option<ThmRef<'_>> {
    thm_ref(self.buf, *self.thms.get(u32_as_usize(n.0))?)
  }
  /// Get the proof stream for the file.
  #[inline] #[must_use] pub fn proof(&self) -> DeclIter<'a> {
    DeclIter {buf: self.buf, pos: self.proof}
  }

  /// Get the name of a term, supplying a default name
  /// of the form `t123` if the index is not present.
  #[must_use] pub fn term_name<T>(&self, n: TermId, f: impl FnOnce(&str) -> T) -> Option<T> {
    if let Some(index) = &self.index {
      Some(f(index.term(n)?.value()?))
    } else {
      Some(f(&format!("t{}", n.0)))
    }
  }
  /// Get the name of a theorem, supplying a default name
  /// of the form `T123` if the index is not present.
  #[must_use] pub fn thm_name<T>(&self, n: ThmId, f: impl FnOnce(&str) -> T) -> Option<T> {
    if let Some(index) = &self.index {
      Some(f(index.thm(n)?.value()?))
    } else {
      Some(f(&format!("T{}", n.0)))
    }
  }
  /// Get the name of a sort, supplying a default name
  /// of the form `s123` if the index is not present.
  #[must_use] pub fn sort_name<T>(&self, n: SortId, f: impl FnOnce(&str) -> T) -> Option<T> {
    if let Some(index) = &self.index {
      Some(f(index.sort(n)?.value()?))
    } else {
      Some(f(&format!("s{}", n.0)))
    }
  }
}
impl<'a> MmbIndex<'a> {
  /// Get the index entry for a sort.
  #[must_use] pub fn sort(&self, n: SortId) -> Option<IndexEntryRef<'_>> {
    index_ref(self.buf, *self.sorts.get(usize::from(n.0))?)
  }
  /// Get the index entry for a term.
  #[must_use] pub fn term(&self, n: TermId) -> Option<IndexEntryRef<'_>> {
    index_ref(self.buf, *self.terms.get(u32_as_usize(n.0))?)
  }
  /// Get the index entry for a theorem.
  #[must_use] pub fn thm(&self, n: ThmId) -> Option<IndexEntryRef<'_>> {
    index_ref(self.buf, *self.thms.get(u32_as_usize(n.0))?)
  }
}

impl<'a> TermRef<'a> {
  /// Returns true if this is a `def`, false for a `term`.
  #[inline] #[must_use] pub fn def(&self) -> bool { self.sort & 0x80 != 0 }
  /// The return sort of this term/def.
  #[inline] #[must_use] pub fn sort(&self) -> SortId { SortId(self.sort & 0x7F) }
  /// The list of arguments of this term/def (not including the return).
  #[inline] #[must_use] pub fn args(&self) -> &[Arg] { self.args.split_last().expect("nonempty").1 }
  /// The return sort and dependencies.
  #[inline] #[must_use] pub fn ret(&self) -> Arg { *self.args.last().expect("nonempty") }
  /// The beginning of the unify stream for the term.
  #[inline] #[must_use] pub fn unify(&self) -> UnifyIter<'_> { self.unify.clone() }
}

impl<'a> ThmRef<'a> {
  /// The list of arguments of this axiom/theorem.
  #[inline] #[must_use] pub fn args(&self) -> &[Arg] { self.args }
  /// The beginning of the unify stream.
  #[inline] #[must_use] pub fn unify(&self) -> UnifyIter<'_> { self.unify.clone() }
}

impl Arg {
  /// True if this argument is a bound variable.
  #[inline] #[must_use] pub fn bound(self) -> bool { self.0.get() & (1 << 63) != 0 }
  /// The sort of this variable.
  #[allow(clippy::cast_possible_truncation)]
  #[inline] #[must_use] pub fn sort(self) -> SortId { SortId(((self.0.get() >> 56) & 0x7F) as u8) }
  /// The set of dependencies of this variable, as a bitset.
  #[inline] #[must_use] pub fn deps(self) -> u64 { self.0.get() & !(0xFF << 56) }
}

#[allow(clippy::option_option)]
fn try_next_decl(buf: &[u8], n: usize) -> Option<Option<(StmtCmd, ProofIter<'_>, usize)>> {
  let bytes = buf.get(n..)?;
  let (cmd, data, next) = parse_cmd(bytes)?;
  if cmd == 0 {return Some(None)}
  let stmt = cmd.try_into().ok()?;
  let next2 = n + u32_as_usize(data);
  let pos = buf.len() - next.len();
  if next2 < pos {return None}
  let pr = ProofIter {buf: buf.get(..next2)?, pos};
  Some(Some((stmt, pr, next2)))
}

#[allow(clippy::option_option)]
fn try_next_cmd<T: TryFrom<(u8, u32)>>(buf: &[u8], n: usize) -> Option<Option<(T, usize)>> {
  let bytes = buf.get(n..)?;
  let (cmd, data, next) = parse_cmd(bytes)?;
  if cmd == 0 {return Some(None)}
  Some(Some(((cmd, data).try_into().ok()?, buf.len() - next.len())))
}

impl<'a> Iterator for DeclIter<'a> {
  type Item = Result<(StmtCmd, ProofIter<'a>), usize>;
  fn next(&mut self) -> Option<Self::Item> {
    match try_next_decl(self.buf, self.pos) {
      None => Some(Err(self.pos)),
      Some(None) => None,
      Some(Some((stmt, pr, rest))) => { self.pos = rest; Some(Ok((stmt, pr))) }
    }
  }
}

impl<'a> ProofIter<'a> {
  /// True if this iterator is "null", meaning that it has zero commands.
  /// This is not the same as being empty, which happens when there is one command
  /// which is the terminating `CMD_END` command.
  #[must_use] pub fn is_null(&self) -> bool { self.buf.len() == self.pos }
}


impl<'a> Iterator for ProofIter<'a> {
  type Item = Result<ProofCmd, usize>;
  fn next(&mut self) -> Option<Self::Item> {
    match try_next_cmd(self.buf, self.pos) {
      Some(None) if self.buf.len() == self.pos + 1 => None,
      Some(Some((stmt, rest))) => { self.pos = rest; Some(Ok(stmt)) }
      _ => Some(Err(self.pos)),
    }
  }
}

impl<'a> Iterator for UnifyIter<'a> {
  type Item = Result<UnifyCmd, usize>;
  fn next(&mut self) -> Option<Self::Item> {
    match try_next_cmd(self.buf, self.pos) {
      None => Some(Err(self.pos)),
      Some(None) => None,
      Some(Some((stmt, rest))) => { self.pos = rest; Some(Ok(stmt)) }
    }
  }
}

impl<'a> IndexEntryRef<'a> {
  /// The left child of this entry.
  #[must_use] pub fn left(&self) -> Option<Self> { index_ref(self.buf, self.p_left) }
  /// The right child of this entry.
  #[must_use] pub fn right(&self) -> Option<Self> { index_ref(self.buf, self.p_right) }
  /// Extract the name of this index entry as a `&str`.
  #[must_use] pub fn value(&self) -> Option<&'a str> {
    cstr_from_bytes_prefix(self.value)?.0.to_str().ok()
  }
  /// The index kind of this entry.
  #[must_use] pub fn kind(&self) -> Option<IndexKind> { self.kind.try_into().ok() }
  /// The statement that sourced this entry.
  #[must_use] pub fn decl(&self) -> Option<(StmtCmd, ProofIter<'_>)> {
    let (stmt, pf, _) = try_next_decl(self.buf, u64_as_usize(self.p_proof))??;
    Some((stmt, pf))
  }
  /// Convert the location information of this entry into a [`Position`].
  #[must_use] pub fn to_pos(&self) -> Position {
    Position {line: self.row.get(), character: self.col.get() }
  }
}

#[cfg(test)]
mod tests {
  use super::MmbFile;

  #[repr(align(8))]
  struct AlignFile<const N: usize>([u8; N]);

  #[test]
  fn try_next_decl_infinite_loop() {
    let filedata = AlignFile([
      77, 77, 48, 66, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 8, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0]);
    let mut iter = MmbFile::parse(&filedata.0).unwrap().proof();
    assert_eq!(iter.next().unwrap().unwrap_err(), 40);
  }
}
