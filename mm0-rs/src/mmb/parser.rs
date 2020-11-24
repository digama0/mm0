//! Parser for MMB binary proof files.
use std::{mem, io};
use std::convert::{TryFrom, TryInto};
use std::fs::File;
use memmap::{MmapOptions, Mmap};
use byteorder::LE;
use zerocopy::{LayoutVerified, FromBytes, Unaligned, U16, U32, U64};
use super::{Header, StmtCmd, TermEntry, ThmEntry, IndexEntry, IndexKind, UnifyCmd, ProofCmd};
use crate::elab::environment::{SortID, TermID, ThmID, Modifiers};
use crate::util::{Position, cstr_from_bytes_prefix};

#[repr(C)]
#[derive(Debug, Clone, Copy, FromBytes, Unaligned)]
pub struct SortData(u8);

impl TryFrom<SortData> for Modifiers {
  type Error = ();
  fn try_from(s: SortData) -> Result<Modifiers, ()> {
    let m = Modifiers::new(s.0);
    if Modifiers::sort_data().contains(m) {Ok(m)} else {Err(())}
  }
}

#[repr(C)]
#[derive(Debug, Clone, Copy, FromBytes, Unaligned)]
pub struct Arg(U64<LE>);

#[derive(Debug, Clone)]
pub struct DeclIter<'a> {buf: &'a [u8], pub pos: usize}

#[derive(Debug)]
pub struct Buffer(Mmap);

impl std::ops::Deref for Buffer {
  type Target = [u8];
  fn deref(&self) -> &[u8] { &self.0 }
}

#[derive(Debug)]
pub struct MMBFile<'a> {
  buf: &'a [u8],
  sorts: &'a [SortData],
  terms: &'a [TermEntry],
  thms: &'a [ThmEntry],
  proof: usize,
  pub index: Option<MMBIndex<'a>>,
}

#[derive(Debug)]
pub struct MMBIndex<'a> {
  buf: &'a [u8],
  root: U64<LE>,
  sorts: &'a [U64<LE>],
  terms: &'a [U64<LE>],
  thms: &'a [U64<LE>],
}

#[derive(Debug, Clone, Copy)]
pub struct IndexEntryRef<'a> {
  buf: &'a [u8],
  entry: &'a IndexEntry,
  value: &'a [u8],
}

impl<'a> std::ops::Deref for IndexEntryRef<'a> {
  type Target = IndexEntry;
  fn deref(&self) -> &IndexEntry { self.entry }
}

#[derive(Debug, Clone)]
pub struct ProofIter<'a> {buf: &'a [u8], pub pos: usize}

#[derive(Debug, Clone)]
pub struct UnifyIter<'a> {buf: &'a [u8], pub pos: usize}

#[derive(Debug, Clone)]
pub struct TermRef<'a> {
  sort: u8,
  args: &'a [Arg],
  unify: UnifyIter<'a>,
}

#[derive(Debug, Clone)]
pub struct ThmRef<'a> {
  args: &'a [Arg],
  unify: UnifyIter<'a>,
}

#[derive(Debug)]
pub enum ParseError {
  BadHeader,
  BadVersion,
  BadIndex,
  StrError(&'static str, usize),
  IOError(io::Error)
}

impl From<io::Error> for ParseError {
  fn from(e: io::Error) -> Self { Self::IOError(e) }
}

impl From<ParseError> for crate::elab::ElabError {
  fn from(e: ParseError) -> Self {
    match e {
      ParseError::BadHeader => Self::new_e(0, "Bad header (not an MMB file?)"),
      ParseError::BadVersion => Self::new_e(0, "Unknown MMB version"),
      ParseError::BadIndex => Self::new_e(0, "MMB index is malformed"),
      ParseError::StrError(s, p) => Self::new_e(p, s),
      ParseError::IOError(e) => Self::new_e(0, e),
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

impl Buffer {
  pub fn new(file: &File) -> io::Result<Self> {
    Ok(Self(unsafe { MmapOptions::new().map(file)? }))
  }
}

impl<'a> MMBFile<'a> {
  pub fn parse(buf: &'a [u8]) -> Result<MMBFile<'a>, ParseError> {
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
        Some(MMBIndex {buf, root: *root, sorts, terms, thms})
      })().ok_or(BadIndex)?)
    };
    Ok(MMBFile {buf, sorts, terms, thms, proof, index})
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

impl<'a> MMBFile<'a> {
  #[inline] #[must_use] pub fn sort(&self, n: SortID) -> Option<SortData> {
    self.sorts.get(usize::from(n.0)).copied()
  }
  #[inline] #[must_use] pub fn term(&self, n: TermID) -> Option<TermRef<'_>> {
    term_ref(self.buf, *self.terms.get(u32_as_usize(n.0))?)
  }
  #[inline] #[must_use] pub fn thm(&self, n: ThmID) -> Option<ThmRef<'_>> {
    thm_ref(self.buf, *self.thms.get(u32_as_usize(n.0))?)
  }
  #[inline] #[must_use] pub fn proof(&self) -> DeclIter<'a> {
    DeclIter {buf: self.buf, pos: self.proof}
  }

  #[must_use] pub fn term_name<T>(&self, n: TermID, f: impl FnOnce(&str) -> T) -> Option<T> {
    if let Some(index) = &self.index {
      Some(f(index.term(n)?.value()?))
    } else {
      Some(f(&format!("t{}", n.0)))
    }
  }
  #[must_use] pub fn thm_name<T>(&self, n: ThmID, f: impl FnOnce(&str) -> T) -> Option<T> {
    if let Some(index) = &self.index {
      Some(f(index.thm(n)?.value()?))
    } else {
      Some(f(&format!("T{}", n.0)))
    }
  }
  #[must_use] pub fn sort_name<T>(&self, n: SortID, f: impl FnOnce(&str) -> T) -> Option<T> {
    if let Some(index) = &self.index {
      Some(f(index.sort(n)?.value()?))
    } else {
      Some(f(&format!("s{}", n.0)))
    }
  }
}
impl<'a> MMBIndex<'a> {
  #[must_use] pub fn sort(&self, n: SortID) -> Option<IndexEntryRef<'_>> {
    index_ref(self.buf, *self.sorts.get(usize::from(n.0))?)
  }
  #[must_use] pub fn term(&self, n: TermID) -> Option<IndexEntryRef<'_>> {
    index_ref(self.buf, *self.terms.get(u32_as_usize(n.0))?)
  }
  #[must_use] pub fn thm(&self, n: ThmID) -> Option<IndexEntryRef<'_>> {
    index_ref(self.buf, *self.thms.get(u32_as_usize(n.0))?)
  }
}

impl<'a> TermRef<'a> {
  #[inline] #[must_use] pub fn def(&self) -> bool { self.sort & 0x80 != 0 }
  #[inline] #[must_use] pub fn sort(&self) -> SortID { SortID(self.sort & 0x7F) }
  #[inline] #[must_use] pub fn args(&self) -> &[Arg] { self.args.split_last().expect("nonempty").1 }
  #[inline] #[must_use] pub fn ret(&self) -> Arg { *self.args.last().expect("nonempty") }
  #[inline] #[must_use] pub fn unify(&self) -> UnifyIter<'_> { self.unify.clone() }
}

impl<'a> ThmRef<'a> {
  #[inline] #[must_use] pub fn args(&self) -> &[Arg] { self.args }
  #[inline] #[must_use] pub fn unify(&self) -> UnifyIter<'_> { self.unify.clone() }
}

impl Arg {
  #[inline] #[must_use] pub fn bound(self) -> bool { self.0.get() & (1 << 63) != 0 }
  #[allow(clippy::cast_possible_truncation)]
  #[inline] #[must_use] pub fn sort(self) -> SortID { SortID(((self.0.get() >> 56) & 0x7F) as u8) }
  #[inline] #[must_use] pub fn deps(self) -> u64 { self.0.get() & !(0xFF << 56) }
}

#[allow(clippy::option_option)]
fn try_next_decl(buf: &[u8], n: usize) -> Option<Option<(StmtCmd, ProofIter<'_>, usize)>> {
  let bytes = buf.get(n..)?;
  let (cmd, data, next) = parse_cmd(bytes)?;
  if cmd == 0 {return Some(None)}
  let stmt = cmd.try_into().ok()?;
  let next2 = n + u32_as_usize(data);
  let pr = ProofIter {buf: buf.get(..next2)?, pos: buf.len() - next.len()};
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
  #[must_use] pub fn left(&self) -> Option<Self> { index_ref(self.buf, self.p_left) }
  #[must_use] pub fn right(&self) -> Option<Self> { index_ref(self.buf, self.p_right) }
  #[must_use] pub fn value(&self) -> Option<&'a str> {
    cstr_from_bytes_prefix(self.value)?.0.to_str().ok()
  }
  #[must_use] pub fn kind(&self) -> Option<IndexKind> { self.kind.try_into().ok() }
  #[must_use] pub fn decl(&self) -> Option<(StmtCmd, ProofIter<'_>)> {
    let (stmt, pf, _) = try_next_decl(self.buf, u64_as_usize(self.p_proof))??;
    Some((stmt, pf))
  }
  #[must_use] pub fn to_pos(&self) -> Position {
    Position {line: self.row.get(), character: self.col.get() }
  }
}