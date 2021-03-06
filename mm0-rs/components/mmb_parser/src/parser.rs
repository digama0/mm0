//! Parser for MMB binary proof files.
use crate::{
  exhausted, u32_as_usize, u64_as_usize, Arg, Header, IndexEntry, IndexKind, NumdStmtCmd, ProofCmd,
  SortData, StmtCmd, TermEntry, ThmEntry, UnifyCmd,
};
use byteorder::LE;
use mm0_util::{cstr_from_bytes_prefix, Position, SortId, TermId, ThmId};
use std::borrow::Cow;
use std::convert::{TryFrom, TryInto};
use std::ops::Range;
use std::{io, mem, mem::size_of};
use zerocopy::{FromBytes, LayoutVerified, U16, U32, U64};

/// A parsed `MMB` file, as a borrowed type. This does only shallow parsing;
/// additional parsing is done on demand via functions on this type.
#[derive(Debug)]
pub struct MmbFile<'a> {
  /// The file's header.
  pub header: Header,
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
  pub index: Option<MmbIndex<'a>>,
}

impl<'a> std::default::Default for MmbFile<'a> {
  fn default() -> Self {
    MmbFile {
      header: Header::default(),
      buf: &[],
      sorts: &[],
      terms: &[],
      thms: &[],
      proof: 0,
      index: None,
    }
  }
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
  /// to get the end of the string in [value()](Self::value()).
  value: &'a [u8],
}

impl<'a> std::ops::Deref for IndexEntryRef<'a> {
  type Target = IndexEntry;
  fn deref(&self) -> &IndexEntry { self.entry }
}

/// Return the raw command data (a pair `[(u8, u32)]`)
/// while ensuring that an iterator which is literally empty
/// has terminated at the correct location, where the correct
/// location is signalled by the presence of a `0` command.
//
// IMO extracting this logic into parse_cmd would make it too noisy.
pub fn try_next_cmd(mmb: &[u8], start_at: usize) -> Result<Option<(u8, u32, usize)>, ParseError> {
  let (cmd, data, new_start_at) = parse_cmd(mmb, start_at)?;
  if cmd == 0 {
    return Ok(None)
  }

  assert!(new_start_at > start_at);
  Ok(Some((cmd, data, new_start_at)))
}

/// From a (full) mmb file and a start position, parse the raw data
/// for a command, which is a `[(u8, u32)]` pair of `(cmd, data)`.
/// Also returns the new start position, which is the old position
/// plus the size of `cmd`, and the size of `data` _which varies_
/// despite ending up as a `u32`.
///
/// For `UnifyCmd` and `ProofCmd`, the `(u8, u32)` pair is used to make the corresponding cmd.
///
/// For [`DeclIter`], the `u8` is a [`StmtCmd`], and the `u32` is the length of the proof iterator
/// that should be constructed for that statement.
pub fn parse_cmd(mmb: &[u8], starts_at: usize) -> Result<(u8, u32, usize), ParseError> {
  use super::cmd::{DATA_16, DATA_32, DATA_8, DATA_MASK};
  match mmb.get(starts_at..) {
    None | Some([]) => Err(exhausted!()),
    Some([cmd, tl @ ..]) => {
      let val = cmd & !DATA_MASK;
      #[allow(clippy::unnecessary_lazy_evaluations)]
      match cmd & DATA_MASK {
        0 => Ok((val, 0, starts_at + size_of::<u8>())),
        DATA_8 => tl
          .first()
          .map(|&n| (val, n.into(), starts_at + size_of::<u8>() + size_of::<u8>()))
          .ok_or_else(|| exhausted!()),
        DATA_16 => LayoutVerified::<_, U16<LE>>::new_from_prefix(tl)
          .map(|(n, _)| (val, n.get().into(), starts_at + size_of::<u8>() + size_of::<u16>()))
          .ok_or_else(|| exhausted!()),
        DATA_32 => LayoutVerified::<_, U32<LE>>::new_from_prefix(tl)
          .map(|(n, _)| (val, n.get(), starts_at + size_of::<u8>() + size_of::<u32>()))
          .ok_or_else(|| exhausted!()),
        _ => unreachable!(),
      }
    }
  }
}

/// An iterator over a proof command stream.
#[derive(Debug, Clone)]
pub struct ProofIter<'a> {
  /// The full mmb file
  mmb_source: &'a [u8],
  /// The index of the current proof command in the file.
  pub pos: usize,
  /// The position at which the proof stream ends. This is preferred to
  /// carrying a truncated slice to make the behavior copascetic, and to give
  /// users easier access to the context should they want it.
  pub ends_at: usize,
}

impl<'a> ProofIter<'a> {
  /// True if this iterator is "null", meaning that it has zero commands.
  /// This is not the same as being empty, which happens when there is one command
  /// which is the terminating `CMD_END` command.
  #[must_use]
  pub fn is_null(&self) -> bool { self.pos == self.ends_at }
}

impl<'a> ProofIter<'a> {
  /// Peek the next element.
  #[must_use]
  pub fn peek(&self) -> Option<Result<ProofCmd, ParseError>> { self.clone().next() }
}

impl<'a> Iterator for ProofIter<'a> {
  type Item = Result<ProofCmd, ParseError>;
  fn next(&mut self) -> Option<Self::Item> {
    match try_next_cmd(self.mmb_source, self.pos) {
      // An actual error.
      Err(e) => Some(Err(e)),
      // `try_next_cmd` got `Ok(None)` by receiving a 0 command at the correct position
      Ok(None) if self.ends_at == self.pos + 1 => None,
      // `try_next_cmd` got `Ok(None)` by receiving a 0 command at the WRONG position
      Ok(None) => Some(Err(exhausted!())),
      // `try_next_cmd` parsed a new command.
      Ok(Some((cmd, data, rest))) => match ProofCmd::try_from((cmd, data)) {
        Err(e) => Some(Err(e)),
        Ok(proof_cmd) => {
          self.pos = rest;
          Some(Ok(proof_cmd))
        }
      },
    }
  }
}

/// An iterator over a unify command stream.
#[derive(Debug, Clone)]
pub struct UnifyIter<'a> {
  /// The full mmb file.
  mmb_file: &'a [u8],
  /// The index of the current declaration in the file.
  pub pos: usize,
}

impl<'a> UnifyIter<'a> {
  #[inline]
  fn new((mmb_file, pos): (&'a [u8], usize)) -> UnifyIter<'a> { Self { mmb_file, pos } }

  /// Peek the next element.
  #[must_use]
  pub fn peek(&self) -> Option<Result<UnifyCmd, ParseError>> { self.clone().next() }
}

impl<'a> Iterator for UnifyIter<'a> {
  type Item = Result<UnifyCmd, ParseError>;
  fn next(&mut self) -> Option<Self::Item> {
    match try_next_cmd(self.mmb_file, self.pos) {
      // err
      Err(e) => Some(Err(e)),
      // Exhausted
      Ok(None) => None,
      // next
      Ok(Some((cmd, data, rest))) => match UnifyCmd::try_from((cmd, data)) {
        Err(e) => Some(Err(e)),
        Ok(unify_cmd) => {
          self.pos = rest;
          Some(Ok(unify_cmd))
        }
      },
    }
  }
}

/// A reference to an entry in the term table.
#[derive(Debug, Clone, Copy)]
pub struct TermRef<'a> {
  /// The index into the term table.
  pub tid: TermId,
  /// The sort of the term.
  sort: u8,
  /// The array of arguments, including the `ret` element at the end.
  args_and_ret: &'a [Arg],
  /// The pointer to the start of the unify stream.
  unify: (&'a [u8], usize),
}

/// A reference to an entry in the theorem table.
#[derive(Debug, Clone, Copy)]
pub struct ThmRef<'a> {
  /// The index into the theorem table.
  pub tid: ThmId,
  /// The array of arguments.
  args: &'a [Arg],
  /// The pointer to the start of the unify stream.
  unify: (&'a [u8], usize),
}

/// An error during parsing of an `MMB` file.
#[derive(Debug)]
pub enum ParseError {
  /// If a malformed mmb file tries to sneak in a declar with a (cmd, data) pair
  /// whose data is a 0, `try_next_decl` will loop forever.
  BadProofLen(usize),
  /// The u8 could not be converted to a [StmtCmd] via TryFrom
  StmtCmdConv(u8),
  /// The u8 could not be converted to an [IndexKind] via TryFrom
  IndexKindConv(u8),
  /// The pair could not be converted to a [ProofCmd] via TryFrom
  ProofCmdConv(u8, u32),
  /// The pair could not be converted to a [UnifyCmd] via TryFrom
  UnifyCmdConv(u8, u32),
  /// Wrap other errors to allow for some backtracing.
  Trace(&'static str, u32, Box<ParseError>),
  /// Something using an mmb file unexpectedly exhausted its input source.
  Exhausted(&'static str, u32),
  /// The parser wasn't able to find the mmb magic number in the expected location.
  BadMagic {
    /// The magic value that we actually found
    parsed_magic: [u8; 4],
  },
  /// The file is not aligned to a multiple of 8 bytes, which is required for
  /// parsing the term table. (This is generally true automatically for buffers sourced
  /// from a file or mmap, but it has to be explicitly ensured in unit tests.)
  Unaligned,
  /// The header parsed "correctly", but the data in the header indicates that
  /// either the header's numbers are off, or the rest of the MMB file is bad.
  /// For example, a header stating that the term declarations begin at a
  /// position greater than the length of the MMB file.
  SuspectHeader,
  /// Used in cases where the parser fails trying to get the header, because there
  /// were too few bytes in the file to form a full header. Users might like to know
  /// how long the actual file was, just as a sanity check.
  IncompleteHeader {
    /// The file length
    file_len: usize,
  },
  /// The version is unrecognized.
  BadVersion {
    /// The MMB file version, greater than [`MM0B_VERSION`](crate::cmd::MM0B_VERSION)
    parsed_version: u8,
  },
  /// The portion of the mmb file that's supposed to contain sorts was malformed.
  BadSorts(Range<usize>),
  /// The portion of the mmb file that's supposed to contain terms was malformed.
  BadTerms(Range<usize>),
  /// The portion of the mmb file that's supposed to contain thms was malformed.
  BadThms(Range<usize>),
  /// The portion of the mmb file that's supposed to contain proofs was malformed.
  BadProofs(Range<usize>),
  /// There was an issue parsing the index
  BadIndexParse {
    /// The (ostensible) location of the index in the file
    p_index: usize,
  },
  /// An index lookup failed
  BadIndexLookup {
    /// The (ostensible) location of the index in the file, or `None` if there is no index
    p_index: Option<usize>,
  },
  /// A 'sorry' was detected and the function has no support for it
  SorryError,
  /// An error with the provided message and location.
  StrError(&'static str, usize),
  /// An error in IO.
  IoError(io::Error),
}

/// Something using an mmb file unexpectedly exhausted its input source.
#[macro_export]
macro_rules! exhausted {
  () => {
    ParseError::Exhausted(file!(), line!())
  };
}

/// Wrap other errors to allow for some backtracing.
#[macro_export]
macro_rules! trace {
  ($e:expr) => {
    ParseError::Trace(file!(), line!(), Box::new($e))
  };
}

const HEADER_CAVEAT: &str = "\
    Be advised that the given position(s) may be the result of an \
    untrustworthy header, and should therefore be considered \
    suggestions for where to begin troubleshooting.";

impl std::fmt::Display for ParseError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      ParseError::BadProofLen(start) =>
        write!(f, "proof starting at byte {} has an incorrect length", start),
      ParseError::IndexKindConv(cmd) =>
        write!(f, "bad IndexKind conversion (`TryFrom`); cmd was {}", cmd),
      ParseError::StmtCmdConv(cmd) =>
        write!(f, "bad StmtCmd conversion (`TryFrom`); cmd was {}", cmd),
      ParseError::ProofCmdConv(cmd, data) =>
        write!(f, "bad ProofCmd conversion (`TryFrom`). data: ({}, {})", cmd, data),
      ParseError::UnifyCmdConv(cmd, data) =>
        write!(f, "bad UnifyCmd conversion (`TryFrom`). data: ({}, {})", cmd, data),

      ParseError::Trace(file, line, inner) => write!(f, "trace {} : {} -> {}", file, line, inner),
      ParseError::Exhausted(file, line) =>
        write!(f, "mmb parser was prematurely exhausted at {} : {}", file, line),
      ParseError::BadSorts(range) => write!(
        f,
        "Failed to parse list of sorts in MMB file. \
        According to the header, `sorts` should inhabit {:?}. {}",
        range, HEADER_CAVEAT
      ),
      ParseError::BadTerms(range) => write!(
        f,
        "Failed to parse list of terms in MMB file. \
        According to the header, `terms` should inhabit {:?}. {}",
        range, HEADER_CAVEAT
      ),
      ParseError::BadThms(range) => write!(
        f,
        "Failed to parse list of thms in MMB file. \
        According to the header, `thms` should inhabit {:?}. {}",
        range, HEADER_CAVEAT
      ),
      ParseError::BadProofs(range) => write!(
        f,
        "Failed to parse list of proofs in MMB file. \
        According to the header, `proofs` should inhabit {:?}. {}",
        range, HEADER_CAVEAT
      ),
      ParseError::BadMagic { parsed_magic } => write!(
        f,
        "Bad header; unable to find MMB magic number at expected location \
        (MMB magic number is {:?} ('MM0B' in bytes), found {:?})",
        crate::cmd::MM0B_MAGIC,
        parsed_magic
      ),
      ParseError::Unaligned => write!(f, "The MMB file is not 8-byte aligned."),
      // This should be broken up into more specific errors.
      ParseError::SuspectHeader => write!(
        f,
        "The MMB file's header parsed correctly, \
        but the parsed header indicates an improperly constructed MMB file."
      ),
      ParseError::IncompleteHeader { file_len } => write!(
        f,
        "Received an mmb file with length {} bytes. \
        This is too short to contain a header, and cannot be well-formed",
        file_len
      ),
      ParseError::BadVersion { parsed_version } => write!(
        f,
        "MMB version mismatch: File header specifies version {}, but verifier version is {}",
        parsed_version,
        crate::cmd::MM0B_VERSION
      ),
      ParseError::BadIndexParse { p_index } => write!(
        f,
        "MMB index is malformed. According to the header, it begins at byte {}. {}",
        p_index, HEADER_CAVEAT
      ),
      ParseError::BadIndexLookup { p_index: None } => write!(
        f,
        "There was an error looking up an item in the MMB index, \
        and the header didn't specify its location in the file"
      ),
      ParseError::BadIndexLookup { p_index: Some(b) } => write!(
        f,
        "MMB index is malformed. According to the header, it begins at byte {}. {}",
        b, HEADER_CAVEAT
      ),
      ParseError::SorryError => write!(f, "Proof uses 'sorry'."),
      ParseError::StrError(s, _) => write!(f, "{}", s),
      ParseError::IoError(e) => write!(f, "{}", e),
    }
  }
}

impl From<io::Error> for ParseError {
  fn from(e: io::Error) -> Self { Self::IoError(e) }
}

#[inline]
fn new_slice_prefix<T: FromBytes>(bytes: &[u8], n: usize) -> Option<(&[T], &[u8])> {
  let mid = mem::size_of::<T>().checked_mul(n)?;
  if mid <= bytes.len() {
    let (left, right) = bytes.split_at(mid);
    Some((LayoutVerified::new_slice(left)?.into_slice(), right))
  } else {
    None
  }
}

impl<'a> MmbFile<'a> {
  /// For error reporting after the initial parse.
  #[must_use]
  pub fn bad_index_lookup(&self) -> ParseError {
    ParseError::BadIndexLookup { p_index: self.p_index() }
  }

  /// For error reporting after the initial parse.
  #[must_use]
  pub fn p_index(&self) -> Option<usize> {
    self.index.as_ref().map(|ii| self.buf.len() - ii.buf.len())
  }

  /// Parse a [`MmbFile`] from a file, provided as a byte slice.
  /// This does the minimum checking to construct the parsed object,
  /// it is not a verifier.
  pub fn parse(buf: &'a [u8]) -> Result<MmbFile<'a>, ParseError> {
    use ParseError::{BadIndexParse, BadSorts, BadTerms, BadThms};
    let (zc_header, sorts) =
      LayoutVerified::<_, Header>::new_from_prefix(buf).ok_or_else(|| find_header_error(buf))?;
    // For potential error reporting
    let p_sorts = zc_header.bytes().len();
    let header = zc_header.into_ref();
    header.check(buf)?;
    // This only parses a newtyped &[u8] that hasn't done any validation
    // wrt whether the contents are valid sets of sort modifiers,
    // so if this fails, it's a size issue.
    let sorts = sorts
      .get(..header.num_sorts.into())
      .and_then(LayoutVerified::new_slice_unaligned)
      .ok_or_else(|| BadSorts(p_sorts..u32_as_usize(header.p_terms.get())))?
      .into_slice();
    let terms = buf
      .get(u32_as_usize(header.p_terms.get())..)
      .and_then(|s| new_slice_prefix(s, u32_as_usize(header.num_terms.get())))
      .ok_or_else(|| {
        BadTerms(u32_as_usize(header.p_terms.get())..u32_as_usize(header.p_thms.get()))
      })?
      .0;
    let thms = buf
      .get(u32_as_usize(header.p_thms.get())..)
      .and_then(|s| new_slice_prefix(s, u32_as_usize(header.num_thms.get())))
      .ok_or_else(|| {
        BadThms(u32_as_usize(header.p_thms.get())..u32_as_usize(header.p_proof.get()))
      })?
      .0;
    let proof = u32_as_usize(header.p_proof.get());
    let index = match u64_as_usize(header.p_index) {
      0 => None,
      n => Some(
        (|| -> Option<_> {
          let (root, rest) =
            LayoutVerified::<_, U64<LE>>::new_unaligned_from_prefix(&*buf.get(n..)?)?;
          let (sorts, rest) = new_slice_prefix(rest, sorts.len())?;
          let (terms, rest) = new_slice_prefix(rest, terms.len())?;
          let (thms, _) = new_slice_prefix(rest, thms.len())?;
          Some(MmbIndex { buf, root: *root, sorts, terms, thms })
        })()
        .ok_or_else(|| BadIndexParse { p_index: u64_as_usize(header.p_index) })?,
      ),
    };
    Ok(MmbFile { header: *header, buf, sorts, terms, thms, proof, index })
  }
}

/// Create a very thin error-reporting wrapper around std functions for parsing u8, u16, u32, and u64.
/// Use in methods intended to find the source of failures in the zerocopy parser methods.
macro_rules! bin_parser {
  ($(($name: ident, $t:ident))*) => {
    $(
      fn $name((mmb_file, pos): (&[u8], usize)) -> Result<($t, usize), ParseError> {
        let int_bytes = mmb_file
          .get(pos..(pos + size_of::<$t>()))
          .ok_or_else(|| ParseError::IncompleteHeader { file_len: mmb_file.len() })?;

        if int_bytes.len() != size_of::<$t>() {
          return Err(ParseError::IncompleteHeader { file_len: mmb_file.len()})
        }

        Ok(($t::from_le_bytes(int_bytes.try_into().unwrap()), pos + size_of::<$t>()))
      }
    )*
  };
}

bin_parser! {
  (parse_u8,  u8)
  (parse_u16, u16)
  (parse_u32, u32)
  (parse_u64, u64)
}

/// In the event that [`MmbFile::parse`] fails when parsing the header, use this
/// to get a more detailed error report (since the zerocopy parser for `Header` is just pass/fail).
/// This method will panic if it's not able to find a problem with the header, since a disagreement
/// with [`MmbFile::parse`] means something else is going on that needs to looked at.
#[must_use]
pub fn find_header_error(mmb: &[u8]) -> ParseError {
  fn find_header_error_aux(mmb: &[u8]) -> Result<(), ParseError> {
    if <*const [u8]>::cast::<u8>(mmb).align_offset(8) != 0 {
      return Err(ParseError::Unaligned)
    }
    let (magic0, pos) = parse_u8((mmb, 0))?;
    let (magic1, pos) = parse_u8((mmb, pos))?;
    let (magic2, pos) = parse_u8((mmb, pos))?;
    let (magic3, pos) = parse_u8((mmb, pos))?;
    let magic = [magic0, magic1, magic2, magic3];
    if magic != crate::cmd::MM0B_MAGIC {
      return Err(ParseError::BadMagic { parsed_magic: magic })
    }
    let (version, pos) = parse_u8((mmb, pos))?;
    if version != crate::cmd::MM0B_VERSION {
      return Err(ParseError::BadVersion { parsed_version: version })
    }
    let (_num_sorts, pos) = parse_u8((mmb, pos))?;
    let (_reserved, pos) = parse_u16((mmb, pos))?;
    let (_num_terms, pos) = parse_u32((mmb, pos))?;
    let (_num_thms, pos) = parse_u32((mmb, pos))?;
    let (_terms_start, pos) = parse_u32((mmb, pos))?;
    let (_thms_start, pos) = parse_u32((mmb, pos))?;
    let (_proof_stream_start, pos) = parse_u32((mmb, pos))?;
    let (_reserved2, pos) = parse_u32((mmb, pos))?;
    let (_index_start, _) = parse_u64((mmb, pos))?;
    Ok(())
  }
  match find_header_error_aux(mmb) {
    Err(e) => e,
    Ok(_) => panic!(
      "zerocopy errored out when parsing mmb header, \
       but `inspect_header_aux` wasn't able to find a problem"
    ),
  }
}

#[inline]
fn index_ref(buf: &[u8], n: U64<LE>) -> Option<IndexEntryRef<'_>> {
  let (entry, value) =
    LayoutVerified::<_, IndexEntry>::new_unaligned_from_prefix(&*buf.get(u64_as_usize(n)..)?)?;
  let entry = entry.into_ref();
  Some(IndexEntryRef { buf, entry, value })
}

#[inline]
fn term_ref(buf: &[u8], t: TermEntry, tid: TermId) -> Option<TermRef<'_>> {
  let (args_and_ret, unify) =
    new_slice_prefix(buf.get(u32_as_usize(t.p_args.get())..)?, usize::from(t.num_args.get()) + 1)?;
  let unify = (buf, buf.len() - unify.len());
  Some(TermRef { tid, sort: t.sort, args_and_ret, unify })
}

#[inline]
fn thm_ref(buf: &[u8], t: ThmEntry, tid: ThmId) -> Option<ThmRef<'_>> {
  let (args, unify) =
    new_slice_prefix(buf.get(u32_as_usize(t.p_args.get())..)?, t.num_args.get().into())?;
  let unify = (buf, buf.len() - unify.len());
  Some(ThmRef { tid, args, unify })
}

impl<'a> MmbFile<'a> {
  /// Get the sort data for a [`SortId`].
  #[inline]
  #[must_use]
  pub fn sort(&self, n: SortId) -> Option<SortData> { self.sorts.get(usize::from(n.0)).copied() }

  /// Get the term data for a [`TermId`].
  #[inline]
  #[must_use]
  pub fn term(&self, n: TermId) -> Option<TermRef<'a>> {
    term_ref(self.buf, *self.terms.get(u32_as_usize(n.0))?, n)
  }

  /// Get the theorem data for a [`ThmId`].
  #[inline]
  #[must_use]
  pub fn thm(&self, n: ThmId) -> Option<ThmRef<'a>> {
    thm_ref(self.buf, *self.thms.get(u32_as_usize(n.0))?, n)
  }

  /// Get the proof stream for the file.
  #[inline]
  #[must_use]
  pub fn proof(&self) -> DeclIter<'a> {
    DeclIter {
      mmb_file: self.buf,
      pos: self.proof,
      next_sort_id: 0_u8,
      next_term_id: 0_u32,
      next_thm_id: 0_u32,
    }
  }

  /// Get the name of a term, supplying a default name
  /// of the form `t123` if the index is not present.
  #[must_use]
  pub fn term_name(&self, n: TermId) -> Option<Cow<'a, str>> {
    if let Some(index) = &self.index {
      Some(Cow::Borrowed(index.term(n)?.value()?))
    } else {
      Some(Cow::Owned(format!("t{}", n.0)))
    }
  }

  /// Get the name of a theorem, supplying a default name
  /// of the form `T123` if the index is not present.
  #[must_use]
  pub fn thm_name(&self, n: ThmId) -> Option<Cow<'a, str>> {
    if let Some(index) = &self.index {
      Some(Cow::Borrowed(index.thm(n)?.value()?))
    } else {
      Some(Cow::Owned(format!("T{}", n.0)))
    }
  }

  /// Get the name of a sort, supplying a default name
  /// of the form `s123` if the index is not present.
  #[must_use]
  pub fn sort_name(&self, n: SortId) -> Option<Cow<'a, str>> {
    if let Some(index) = &self.index {
      Some(Cow::Borrowed(index.sort(n)?.value()?))
    } else {
      Some(Cow::Owned(format!("s{}", n.0)))
    }
  }
}

impl<'a> MmbIndex<'a> {
  /// Get the index entry for a sort.
  #[must_use]
  pub fn sort(&self, n: SortId) -> Option<IndexEntryRef<'a>> {
    index_ref(self.buf, *self.sorts.get(usize::from(n.0))?)
  }

  /// Get the index entry for a term.
  #[must_use]
  pub fn term(&self, n: TermId) -> Option<IndexEntryRef<'a>> {
    index_ref(self.buf, *self.terms.get(u32_as_usize(n.0))?)
  }

  /// Get the index entry for a theorem.
  #[must_use]
  pub fn thm(&self, n: ThmId) -> Option<IndexEntryRef<'a>> {
    index_ref(self.buf, *self.thms.get(u32_as_usize(n.0))?)
  }

  /// Convenience function for getting an index without having to destructure
  /// the [`StmtCmd`] every time.
  #[must_use]
  pub fn stmt(&self, stmt: NumdStmtCmd) -> Option<IndexEntryRef<'a>> {
    use crate::NumdStmtCmd::{Axiom, Sort, TermDef, Thm};
    match stmt {
      Sort { sort_id } => self.sort(sort_id),
      Axiom { thm_id } | Thm { thm_id, .. } => self.thm(thm_id),
      TermDef { term_id, .. } => self.term(term_id),
    }
  }
}

impl<'a> TermRef<'a> {
  /// Returns true if this is a `def`, false for a `term`.
  #[inline]
  #[must_use]
  pub fn def(&self) -> bool { self.sort & 0x80 != 0 }

  /// The return sort of this term/def.
  #[inline]
  #[must_use]
  pub fn sort(&self) -> SortId { SortId(self.sort & 0x7F) }

  /// The list of arguments of this term/def, not including the return).
  #[inline]
  #[must_use]
  pub fn args(&self) -> &[Arg] { self.args_and_ret.split_last().expect("nonempty").1 }

  #[inline]
  #[must_use]
  /// Get the termdef's arguments as a slice, INCLUDING the
  /// return type
  pub fn args_and_ret(&self) -> &[Arg] { self.args_and_ret }

  /// The return sort and dependencies.
  #[inline]
  #[must_use]
  pub fn ret(&self) -> Arg { *self.args_and_ret.last().expect("nonempty") }

  /// The beginning of the unify stream for the term.
  #[inline]
  #[must_use]
  pub fn unify(&self) -> UnifyIter<'a> { UnifyIter::new(self.unify) }
}

impl<'a> ThmRef<'a> {
  /// The list of arguments of this axiom/theorem.
  #[inline]
  #[must_use]
  pub fn args(&self) -> &[Arg] { self.args }

  /// The beginning of the unify stream.
  #[inline]
  #[must_use]
  pub fn unify(&self) -> UnifyIter<'a> { UnifyIter::new(self.unify) }
}

// This always gets the full mmb file. It's not an associated function
// for DeclIter because it's also used by the Index.
//
/// Try to parse the next declaration in the mmb file; in this case, a
/// declaration is represented by a pair `[(StmtCmd, ProofIter)]`.
/// On success, will also return the new start position for the [`DeclIter`]
fn try_next_decl(
  mmb: &[u8], pos: usize,
) -> Result<Option<(StmtCmd, ProofIter<'_>, usize)>, ParseError> {
  // The `data` u32 you get back from try_next_cmd is (in this context)
  // the length of the corresponding proof. `new_start_pos` is just
  // the position after the (u8, u32) pair in the mmb stream.
  let (stmt_cmd, proof_len, proof_starts_at) = match try_next_cmd(mmb, pos)? {
    None => return Ok(None),
    Some((cmd, data, rest)) => (cmd, data, rest),
  };

  let proof_ends_at = pos + proof_len as usize;

  if (pos + proof_len as usize) < proof_starts_at {
    return Err(ParseError::BadProofLen(pos))
  }

  let pr = ProofIter { mmb_source: mmb, pos: proof_starts_at, ends_at: pos + (proof_len as usize) };

  Ok(Some((StmtCmd::try_from(stmt_cmd)?, pr, proof_ends_at)))
}

/// An iterator over the declaration stream.
#[derive(Debug, Clone)]
pub struct DeclIter<'a> {
  /// The full source file.
  mmb_file: &'a [u8],
  /// The index of the current declaration in the file.
  pub pos: usize,
  next_sort_id: u8,
  next_term_id: u32,
  next_thm_id: u32,
}

impl<'a> DeclIter<'a> {
  /// Peek the next element.
  #[must_use]
  pub fn peek(&self) -> Option<Result<(NumdStmtCmd, ProofIter<'a>), ParseError>> {
    self.clone().next()
  }
}

impl<'a> Iterator for DeclIter<'a> {
  type Item = Result<(NumdStmtCmd, ProofIter<'a>), ParseError>;
  fn next(&mut self) -> Option<Self::Item> {
    match try_next_decl(self.mmb_file, self.pos) {
      Err(e) => Some(Err(e)),
      Ok(None) => None,
      Ok(Some((stmt, proof_iter, rest))) => {
        self.pos = rest;
        let cmd = match stmt {
          StmtCmd::Sort => {
            let out = NumdStmtCmd::Sort { sort_id: SortId(self.next_sort_id) };
            self.next_sort_id += 1;
            out
          }
          StmtCmd::Axiom => {
            let out = NumdStmtCmd::Axiom { thm_id: ThmId(self.next_thm_id) };
            self.next_thm_id += 1;
            out
          }
          StmtCmd::TermDef { local } => {
            let out = NumdStmtCmd::TermDef { term_id: TermId(self.next_term_id), local };
            self.next_term_id += 1;
            out
          }
          StmtCmd::Thm { local } => {
            let out = NumdStmtCmd::Thm { thm_id: ThmId(self.next_thm_id), local };
            self.next_thm_id += 1;
            out
          }
        };
        Some(Ok((cmd, proof_iter)))
      }
    }
  }
}

impl<'a> IndexEntryRef<'a> {
  /// The left child of this entry.
  #[must_use]
  pub fn left(&self) -> Option<Self> { index_ref(self.buf, self.p_left) }

  /// The right child of this entry.
  #[must_use]
  pub fn right(&self) -> Option<Self> { index_ref(self.buf, self.p_right) }

  /// Extract the name of this index entry as a `&str`.
  #[must_use]
  pub fn value(&self) -> Option<&'a str> { cstr_from_bytes_prefix(self.value)?.0.to_str().ok() }

  /// The index kind of this entry.
  #[must_use]
  pub fn kind(&self) -> Option<IndexKind> { self.kind.try_into().ok() }

  /// The statement that sourced this entry.
  pub fn decl(&self) -> Result<Option<(StmtCmd, ProofIter<'a>)>, ParseError> {
    Ok(try_next_decl(self.buf, u64_as_usize(self.p_proof))?.map(|(stmt, proof, _)| (stmt, proof)))
  }

  /// Convert the location information of this entry into a [Position].
  #[must_use]
  pub fn to_pos(&self) -> Position { Position { line: self.row.get(), character: self.col.get() } }
}
