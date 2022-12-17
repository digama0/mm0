//! Parser for MMB binary proof files.
use crate::{
  cmd, cstr_from_bytes_prefix, exhausted, u32_as_usize, u64_as_usize, Arg, Header, NameEntry,
  NumdStmtCmd, ProofCmd, SortData, StmtCmd, TableEntry, TermEntry, ThmEntry, UnifyCmd,
};
use byteorder::LE;
use mm0_util::{SortId, TermId, ThmId};
use std::borrow::Cow;
use std::ops::Range;
use std::{io, mem, mem::size_of};
use zerocopy::{FromBytes, LayoutVerified, U16, U32, U64};

/// A parsed `MMB` file, as a borrowed type. This does only shallow parsing;
/// additional parsing is done on demand via functions on this type.
#[derive(Debug, Default)]
#[non_exhaustive]
pub struct MmbFile<'a, X = BasicIndex<'a>> {
  /// The file's header.
  pub header: Header,
  /// The full file
  pub buf: &'a [u8],
  /// The sort table
  pub sorts: &'a [SortData],
  /// The term table
  pub terms: &'a [TermEntry],
  /// The theorem table
  pub thms: &'a [ThmEntry],
  /// The index, if provided.
  pub index: X,
}

/// An MMB file parser with a basic index, usable for getting names of declarations and variables.
pub type BasicMmbFile<'a> = MmbFile<'a, BasicIndex<'a>>;
/// An MMB file parser with no index parser.
pub type BareMmbFile<'a> = MmbFile<'a, ()>;

/// A trait for populating the `data` field on the index `X` of an [`MmbFile`] given a table entry.
pub trait MmbIndexBuilder<'a>: Default {
  /// Implementors are expected to match on the [`TableEntry::id`] field, and use the data if it
  /// matches a particular name.
  fn build<X>(&mut self, f: &mut MmbFile<'a, X>, e: &'a TableEntry) -> Result<(), ParseError>;
}

impl<'a> MmbIndexBuilder<'a> for () {
  #[inline]
  fn build<X>(&mut self, _: &mut MmbFile<'a, X>, _: &'a TableEntry) -> Result<(), ParseError> {
    Ok(())
  }
}

impl<'a, A: MmbIndexBuilder<'a>, B: MmbIndexBuilder<'a>> MmbIndexBuilder<'a> for (A, B) {
  #[inline]
  fn build<X>(&mut self, f: &mut MmbFile<'a, X>, e: &'a TableEntry) -> Result<(), ParseError> {
    self.0.build(f, e)?;
    self.1.build(f, e)
  }
}

/// Constructs a new trait for accessing a subcomponent of the index data, with automatic
/// impls for `()`, `(A, B)` and the subcomponent itself.
#[macro_export]
macro_rules! make_index_trait {
  ([<$($lft:lifetime),*>, $ty:ident, $trait:ident, $notrait:ident, $f:ident, $f_mut:ident]
    $($fns:item)*) => {
    /// A trait for looking up a subcomponent of the index data.
    pub trait $trait<$($lft),*> {
      /// Get shared access to the subcomponent.
      fn $f(&self) -> Option<&$ty<$($lft),*>>;
      /// Get mutable access to the subcomponent.
      fn $f_mut(&mut self) -> Option<&mut $ty<$($lft),*>>;
      $($fns)*
    }
    /// Signals that this type does not implement the respective index trait.
    pub trait $notrait {}

    impl $notrait for () {}

    impl<$($lft),*, T: $notrait> $trait<$($lft),*> for T {
      #[inline]
      fn $f(&self) -> Option<&$ty<$($lft),*>> { None }
      #[inline]
      fn $f_mut(&mut self) -> Option<&mut $ty<$($lft),*>> { None }
    }

    impl<$($lft),*> $trait<$($lft),*> for $ty<$($lft),*> {
      #[inline]
      fn $f(&self) -> Option<&$ty<$($lft),*>> { Some(self) }
      #[inline]
      fn $f_mut(&mut self) -> Option<&mut $ty<$($lft),*>> { Some(self) }
    }

    impl<$($lft),*> $trait<$($lft),*> for Option<$ty<$($lft),*>> {
      #[inline]
      fn $f(&self) -> Option<&$ty<$($lft),*>> { self.as_ref() }
      #[inline]
      fn $f_mut(&mut self) -> Option<&mut $ty<$($lft),*>> { self.as_mut() }
    }

    impl<$($lft),*, A: $trait<$($lft),*>, B: $trait<$($lft),*>> $trait<$($lft),*> for (A, B) {
      #[inline]
      fn $f(&self) -> Option<&$ty<$($lft),*>> {
        match self.0 .$f() {
          Some(e) => Some(e),
          None => self.1 .$f()
        }
      }
      #[inline]
      fn $f_mut(&mut self) -> Option<&mut $ty<$($lft),*>> {
        match self.0 .$f_mut() {
          Some(e) => Some(e),
          None => self.1 .$f_mut()
        }
      }
    }
  }
}

/// This index subcomponent supplies names for sorts, terms, and theorems.
#[derive(Debug)]
pub struct SymbolNames<'a> {
  /// Pointers to the index entries for the sorts
  sorts: &'a [NameEntry],
  /// Pointers to the index entries for the terms
  terms: &'a [NameEntry],
  /// Pointers to the index entries for the theorems
  thms: &'a [NameEntry],
}

impl<'a> MmbIndexBuilder<'a> for Option<SymbolNames<'a>> {
  fn build<X>(&mut self, f: &mut MmbFile<'a, X>, e: &'a TableEntry) -> Result<(), ParseError> {
    if e.id == cmd::INDEX_NAME {
      let rest = f.buf.get(u64_as_usize(e.ptr)..).ok_or_else(|| f.bad_index_parse())?;
      let (sorts, rest) =
        new_slice_prefix(rest, f.sorts.len()).ok_or_else(|| f.bad_index_parse())?;
      let (terms, rest) =
        new_slice_prefix(rest, f.terms.len()).ok_or_else(|| f.bad_index_parse())?;
      let (thms, _) = new_slice_prefix(rest, f.thms.len()).ok_or_else(|| f.bad_index_parse())?;
      if self.replace(SymbolNames { sorts, terms, thms }).is_some() {
        return Err(ParseError::DuplicateIndexTable {
          p_index: u64_as_usize(f.header.p_index),
          id: e.id,
        })
      }
    }
    Ok(())
  }
}

make_index_trait! {
  [<'a>, SymbolNames, HasSymbolNames, NoSymbolNames, get_symbol_names, get_symbol_names_mut]
}
impl<'a> NoSymbolNames for Option<VarNames<'a>> {}
impl<'a> NoSymbolNames for Option<HypNames<'a>> {}

/// This index subcomponent supplies variable names for terms and theorems.
#[derive(Debug)]
pub struct VarNames<'a> {
  /// Pointers to the index entries for the terms
  terms: &'a [U64<LE>],
  /// Pointers to the index entries for the theorems
  thms: &'a [U64<LE>],
}

impl<'a> MmbIndexBuilder<'a> for Option<VarNames<'a>> {
  fn build<X>(&mut self, f: &mut MmbFile<'a, X>, e: &'a TableEntry) -> Result<(), ParseError> {
    if e.id == cmd::INDEX_VAR_NAME {
      let rest = f.buf.get(u64_as_usize(e.ptr)..).ok_or_else(|| f.bad_index_parse())?;
      let (terms, rest) =
        new_slice_prefix(rest, f.terms.len()).ok_or_else(|| f.bad_index_parse())?;
      let (thms, _) = new_slice_prefix(rest, f.thms.len()).ok_or_else(|| f.bad_index_parse())?;
      if self.replace(VarNames { terms, thms }).is_some() {
        return Err(ParseError::DuplicateIndexTable {
          p_index: u64_as_usize(f.header.p_index),
          id: e.id,
        })
      }
    }
    Ok(())
  }
}

make_index_trait! {
  [<'a>, VarNames, HasVarNames, NoVarNames, get_var_names, get_var_names_mut]
}
impl<'a> NoVarNames for Option<SymbolNames<'a>> {}
impl<'a> NoVarNames for Option<HypNames<'a>> {}

/// This index subcomponent supplies hypothesis names for theorems.
#[derive(Debug)]
pub struct HypNames<'a> {
  /// Pointers to the index entries for the theorems
  thms: &'a [U64<LE>],
}

impl<'a> MmbIndexBuilder<'a> for Option<HypNames<'a>> {
  fn build<X>(&mut self, f: &mut MmbFile<'a, X>, e: &'a TableEntry) -> Result<(), ParseError> {
    if e.id == cmd::INDEX_HYP_NAME {
      let rest = f.buf.get(u64_as_usize(e.ptr)..).ok_or_else(|| f.bad_index_parse())?;
      let (thms, _) = new_slice_prefix(rest, f.thms.len()).ok_or_else(|| f.bad_index_parse())?;
      if self.replace(HypNames { thms }).is_some() {
        return Err(ParseError::DuplicateIndexTable {
          p_index: u64_as_usize(f.header.p_index),
          id: e.id,
        })
      }
    }
    Ok(())
  }
}

make_index_trait! {
  [<'a>, HypNames, HasHypNames, NoHypNames, get_hyp_names, get_hyp_names_mut]
}
impl<'a> NoHypNames for Option<SymbolNames<'a>> {}
impl<'a> NoHypNames for Option<VarNames<'a>> {}

/// A basic index, usable for getting names of declarations and variables.
pub type BasicIndex<'a> = (Option<SymbolNames<'a>>, (Option<VarNames<'a>>, Option<HypNames<'a>>));

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
#[must_use]
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
#[must_use]
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

  /// Scan until the `END` command, and return the file position just after the `END` command.
  pub fn after_end(&self) -> Result<usize, ParseError> {
    let UnifyIter { mmb_file: mmb, mut pos } = *self;
    loop {
      let (cmd, _, new_pos) = parse_cmd(mmb, pos)?;
      if cmd == 0 {
        return Ok(new_pos)
      }
      pos = new_pos;
    }
  }

  /// Scan until the `END` command, and return the byte slice from the current position until
  /// the `END` command (inclusive).
  pub fn as_bytes(&self) -> Result<&'a [u8], ParseError> {
    Ok(&self.mmb_file[self.pos..self.after_end()?])
  }
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
  /// The u8 could not be converted to a [`StmtCmd`] via TryFrom
  StmtCmdConv(u8),
  /// The pair could not be converted to a [`ProofCmd`] via TryFrom
  ProofCmdConv(u8, u32),
  /// The pair could not be converted to a [`UnifyCmd`] via TryFrom
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
  /// An index table ID was used more than once, for an ID that does not accept duplicates
  DuplicateIndexTable {
    /// The location of the index in the file
    p_index: usize,
    /// The duplicate ID
    id: [u8; 4],
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
    use crate::cmd::{MM0B_MAGIC, MM0B_VERSION};
    match self {
      ParseError::BadProofLen(start) =>
        write!(f, "proof starting at byte {start} has an incorrect length"),
      ParseError::StmtCmdConv(cmd) =>
        write!(f, "bad StmtCmd conversion (`TryFrom`); cmd was {cmd}"),
      ParseError::ProofCmdConv(cmd, data) =>
        write!(f, "bad ProofCmd conversion (`TryFrom`). data: ({cmd}, {data})"),
      ParseError::UnifyCmdConv(cmd, data) =>
        write!(f, "bad UnifyCmd conversion (`TryFrom`). data: ({cmd}, {data})"),

      ParseError::Trace(file, line, inner) => write!(f, "trace {file} : {line} -> {inner}"),
      ParseError::Exhausted(file, line) =>
        write!(f, "mmb parser was prematurely exhausted at {file} : {line}"),
      ParseError::BadSorts(range) => write!(
        f,
        "Failed to parse list of sorts in MMB file. \
        According to the header, `sorts` should inhabit {range:?}. {HEADER_CAVEAT}"
      ),
      ParseError::BadTerms(range) => write!(
        f,
        "Failed to parse list of terms in MMB file. \
        According to the header, `terms` should inhabit {range:?}. {HEADER_CAVEAT}"
      ),
      ParseError::BadThms(range) => write!(
        f,
        "Failed to parse list of thms in MMB file. \
        According to the header, `thms` should inhabit {range:?}. {HEADER_CAVEAT}"
      ),
      ParseError::BadProofs(range) => write!(
        f,
        "Failed to parse list of proofs in MMB file. \
        According to the header, `proofs` should inhabit {range:?}. {HEADER_CAVEAT}"
      ),
      ParseError::BadMagic { parsed_magic } => write!(
        f,
        "Bad header; unable to find MMB magic number at expected location \
        (MMB magic number is {MM0B_MAGIC:?} ('MM0B' in bytes), found {parsed_magic:?})"
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
        "Received an mmb file with length {file_len} bytes. \
        This is too short to contain a header, and cannot be well-formed"
      ),
      ParseError::BadVersion { parsed_version } => write!(
        f,
        "MMB version mismatch: File header specifies version {parsed_version}, \
        but verifier version is {MM0B_VERSION}"
      ),
      ParseError::BadIndexParse { p_index } => write!(
        f,
        "MMB index is malformed. According to the header, it begins at byte {p_index}. \
        {HEADER_CAVEAT}",
      ),
      ParseError::DuplicateIndexTable { p_index, id } => {
        write!(f, "MMB index at {p_index} contains a duplicate index entry for key = ")?;
        match std::str::from_utf8(id) {
          Ok(s) => write!(f, "'{s}'")?,
          Err(_) => write!(f, "{id:?}")?,
        }
        write!(f, ". {HEADER_CAVEAT}")
      }
      ParseError::BadIndexLookup { p_index: None } => write!(
        f,
        "There was an error looking up an item in the MMB index, \
        and the header didn't specify its location in the file"
      ),
      ParseError::BadIndexLookup { p_index: Some(b) } => write!(
        f,
        "MMB index is malformed. According to the header, it begins at byte {b}. {HEADER_CAVEAT}"
      ),
      ParseError::SorryError => write!(f, "Proof uses 'sorry'."),
      ParseError::StrError(s, _) => write!(f, "{s}"),
      ParseError::IoError(e) => write!(f, "{e}"),
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

impl<'a, X> MmbFile<'a, X> {
  /// For error reporting after the initial parse.
  #[must_use]
  pub fn bad_index_lookup(&self) -> ParseError {
    ParseError::BadIndexLookup { p_index: self.p_index() }
  }

  /// For error reporting after the initial parse.
  #[must_use]
  pub fn p_index(&self) -> Option<usize> {
    let n = u64_as_usize(self.header.p_index);
    if n == 0 {
      None
    } else {
      Some(n)
    }
  }

  /// Returns a bad index parse error, for error reporting during index parsing.
  pub fn bad_index_parse(&self) -> ParseError {
    ParseError::BadIndexParse { p_index: u64_as_usize(self.header.p_index) }
  }
}

impl<'a, X: MmbIndexBuilder<'a>> MmbFile<'a, X> {
  /// Parse a [`MmbFile`] from a file, provided as a byte slice.
  /// This does the minimum checking to construct the parsed object,
  /// it is not a verifier.
  pub fn parse(buf: &'a [u8]) -> Result<Self, ParseError> {
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
    let mut file = MmbFile { header: *header, buf, sorts, terms, thms, index: X::default() };
    let n = u64_as_usize(header.p_index);
    if n != 0 {
      let (entries, _) = (|| -> Option<_> {
        let (num_entries, rest) =
          LayoutVerified::<_, U64<LE>>::new_unaligned_from_prefix(buf.get(n..)?)?;
        new_slice_prefix(rest, num_entries.get().try_into().ok()?)
      })()
      .ok_or_else(|| BadIndexParse { p_index: u64_as_usize(header.p_index) })?;
      let mut index = X::default();
      for e in entries {
        index.build(&mut file, e)?
      }
      file.index = index;
    }
    Ok(file)
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

impl<'a, X> MmbFile<'a, X> {
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
  pub fn proof(&self) -> DeclIter<'a> {
    DeclIter {
      mmb_file: self.buf,
      pos: u32_as_usize(self.header.p_proof.get()),
      next_sort_id: 0_u8,
      next_term_id: 0_u32,
      next_thm_id: 0_u32,
    }
  }
}

/// A handle to an symbol name entry in the index.
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct NameEntryRef<'a> {
  /// The full file
  pub buf: &'a [u8],
  /// The proof stream index
  pub p_proof: U64<LE>,
  /// The C string for the value (actually a suffix of the file
  /// starting at the appropriate location). Note that `strlen` has to be called
  /// to get the end of the string in [value()](Self::value()).
  pub value: &'a [u8],
}

#[inline]
fn name_entry_ref(
  buf: &[u8], NameEntry { p_proof, p_name }: NameEntry,
) -> Option<NameEntryRef<'_>> {
  let value = buf.get(u64_as_usize(p_name)..)?;
  Some(NameEntryRef { buf, p_proof, value })
}

impl<'a, X: HasSymbolNames<'a>> MmbFile<'a, X> {
  /// Get the index entry for a sort.
  #[must_use]
  pub fn sort_index(&self, n: SortId) -> Option<NameEntryRef<'a>> {
    name_entry_ref(self.buf, *self.index.get_symbol_names()?.sorts.get(usize::from(n.0))?)
  }

  /// Get the index entry for a term.
  #[must_use]
  pub fn term_index(&self, n: TermId) -> Option<NameEntryRef<'a>> {
    name_entry_ref(self.buf, *self.index.get_symbol_names()?.terms.get(u32_as_usize(n.0))?)
  }

  /// Get the index entry for a theorem.
  #[must_use]
  pub fn thm_index(&self, n: ThmId) -> Option<NameEntryRef<'a>> {
    name_entry_ref(self.buf, *self.index.get_symbol_names()?.thms.get(u32_as_usize(n.0))?)
  }

  /// Convenience function for getting an index without having to destructure
  /// the [`StmtCmd`] every time.
  #[must_use]
  pub fn stmt_index(&self, stmt: NumdStmtCmd) -> Option<NameEntryRef<'a>> {
    use crate::NumdStmtCmd::{Axiom, Sort, TermDef, Thm};
    match stmt {
      Sort { sort_id } => self.sort_index(sort_id),
      Axiom { thm_id } | Thm { thm_id, .. } => self.thm_index(thm_id),
      TermDef { term_id, .. } => self.term_index(term_id),
    }
  }

  /// Get the name of a sort, if present.
  #[must_use]
  pub fn try_sort_name(&self, n: SortId) -> Option<&'a str> {
    self.sort_index(n).and_then(|t| t.value())
  }

  /// Get the name of a term, if present.
  #[must_use]
  pub fn try_term_name(&self, n: TermId) -> Option<&'a str> {
    self.term_index(n).and_then(|t| t.value())
  }

  /// Get the name of a theorem, if present.
  #[must_use]
  pub fn try_thm_name(&self, n: ThmId) -> Option<&'a str> {
    self.thm_index(n).and_then(|t| t.value())
  }

  /// Get the name of a sort, supplying a default name
  /// of the form `s123` if the index is not present.
  #[must_use]
  pub fn sort_name(&self, n: SortId) -> Cow<'a, str> {
    match self.try_sort_name(n) {
      Some(v) => Cow::Borrowed(v),
      None => Cow::Owned(format!("s{}", n.0)),
    }
  }

  /// Get the name of a term, supplying a default name
  /// of the form `t123` if the index is not present.
  #[must_use]
  pub fn term_name(&self, n: TermId) -> Cow<'a, str> {
    match self.try_term_name(n) {
      Some(v) => Cow::Borrowed(v),
      None => Cow::Owned(format!("t{}", n.0)),
    }
  }

  /// Get the name of a theorem, supplying a default name
  /// of the form `T123` if the index is not present.
  #[must_use]
  pub fn thm_name(&self, n: ThmId) -> Cow<'a, str> {
    match self.try_thm_name(n) {
      Some(v) => Cow::Borrowed(v),
      None => Cow::Owned(format!("T{}", n.0)),
    }
  }
}

/// A handle to an symbol name entry in the index.
#[derive(Debug, Clone, Copy)]
struct StrListRef<'a> {
  /// The full file
  buf: &'a [u8],
  /// The strings
  strs: &'a [U64<LE>],
}

impl<'a> StrListRef<'a> {
  /// Create a new empty [`StrListRef`].
  fn new(buf: &'a [u8]) -> Self { Self { buf, strs: &[] } }

  /// Get the name of the string with index `n`. The range of valid `n` is `self.strs.len()`,
  fn get(&self, n: usize) -> Option<&'a str> {
    cstr_from_bytes_prefix(self.buf.get(u64_as_usize(*self.strs.get(n)?)..)?)?.0.to_str().ok()
  }
}

macro_rules! str_list_wrapper {
  ($($(#[$m:meta])* $ty:ident($e:expr);)*) => {$(
    $(#[$m])*
    #[derive(Debug, Clone, Copy)]
    pub struct $ty<'a>(StrListRef<'a>);

    impl<'a> std::ops::Deref for $ty<'a> {
      type Target = &'a [U64<LE>];
      fn deref(&self) -> &&'a [U64<LE>] { &self.0.strs }
    }

    impl<'a> $ty<'a> {
      /// Create a new empty wrapper.
      fn new(buf: &'a [u8]) -> Self { Self(StrListRef::new(buf)) }

      /// Get the name of the string with index `n`. The range of valid `n` is `self.strs.len()`,
      #[must_use]
      pub fn get_opt(&self, n: usize) -> Option<&'a str> { self.0.get(n) }

      /// Get the name of the string with index `n`, with a fallback if the value cannot be found.
      #[must_use]
      pub fn get(&self, n: usize) -> Cow<'a, str> {
        match self.get_opt(n) {
          Some(v) => Cow::Borrowed(v),
          None => Cow::Owned(format!($e, n))
        }
      }
    }
  )*}
}

str_list_wrapper! {
  /// A handle to an list of variable names in the index.
  VarListRef("v{}");

  /// A handle to an list of hypothesis names in the index.
  HypListRef("h{}");
}

impl<'a, X> MmbFile<'a, X> {
  fn str_list_ref(&self, p_vars: U64<LE>) -> Option<StrListRef<'a>> {
    let (num_vars, rest) = LayoutVerified::<_, U64<LE>>::new_unaligned_from_prefix(
      self.buf.get(u64_as_usize(p_vars)..)?,
    )?;
    Some(StrListRef {
      buf: self.buf,
      strs: new_slice_prefix(rest, num_vars.get().try_into().ok()?)?.0,
    })
  }
}

impl<'a, X: HasVarNames<'a>> MmbFile<'a, X> {
  /// Get the list of variables used in a term, or `None` if the index does not exist.
  #[must_use]
  pub fn term_vars_opt(&self, n: TermId) -> Option<VarListRef<'a>> {
    let strs = self.str_list_ref(*self.index.get_var_names()?.terms.get(u32_as_usize(n.0))?)?;
    Some(VarListRef(strs))
  }

  /// Get the list of variables used in a term.
  #[must_use]
  pub fn term_vars(&self, n: TermId) -> VarListRef<'a> {
    self.term_vars_opt(n).unwrap_or_else(|| VarListRef::new(self.buf))
  }

  /// Get the list of variables used in a theorem, or `None` if the index does not exist.
  #[must_use]
  pub fn thm_vars_opt(&self, n: ThmId) -> Option<VarListRef<'a>> {
    let strs = self.str_list_ref(*self.index.get_var_names()?.thms.get(u32_as_usize(n.0))?)?;
    Some(VarListRef(strs))
  }

  /// Get the list of variables used in a theorem.
  #[must_use]
  pub fn thm_vars(&self, n: ThmId) -> VarListRef<'a> {
    self.thm_vars_opt(n).unwrap_or_else(|| VarListRef::new(self.buf))
  }

  /// Convenience function for getting an index without having to destructure
  /// the [`StmtCmd`] every time.
  #[must_use]
  pub fn stmt_vars(&self, stmt: NumdStmtCmd) -> VarListRef<'a> {
    use crate::NumdStmtCmd::{Axiom, Sort, TermDef, Thm};
    match stmt {
      Sort { .. } => VarListRef::new(self.buf),
      Axiom { thm_id } | Thm { thm_id, .. } => self.thm_vars(thm_id),
      TermDef { term_id, .. } => self.term_vars(term_id),
    }
  }
}

impl<'a, X: HasHypNames<'a>> MmbFile<'a, X> {
  /// Get the hypothesis name list for a theorem.
  #[must_use]
  pub fn thm_hyps_opt(&self, n: ThmId) -> Option<HypListRef<'a>> {
    let strs = self.str_list_ref(*self.index.get_hyp_names()?.thms.get(u32_as_usize(n.0))?)?;
    Some(HypListRef(strs))
  }

  /// Get the hypothesis name list for a theorem.
  #[must_use]
  pub fn thm_hyps(&self, n: ThmId) -> HypListRef<'a> {
    self.thm_hyps_opt(n).unwrap_or_else(|| HypListRef::new(self.buf))
  }

  /// Convenience function for getting an index without having to destructure
  /// the [`StmtCmd`] every time.
  #[must_use]
  pub fn stmt_hyps(&self, stmt: NumdStmtCmd) -> HypListRef<'a> {
    use crate::NumdStmtCmd::{Axiom, Sort, TermDef, Thm};
    match stmt {
      Sort { .. } | TermDef { .. } => HypListRef::new(self.buf),
      Axiom { thm_id } | Thm { thm_id, .. } => self.thm_hyps(thm_id),
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

  /// Get the termdef's arguments as a slice, INCLUDING the return type
  #[inline]
  #[must_use]
  pub fn args_and_ret(&self) -> &[Arg] { self.args_and_ret }

  /// The return sort and dependencies.
  #[inline]
  #[must_use]
  pub fn ret(&self) -> Arg { *self.args_and_ret.last().expect("nonempty") }

  /// The beginning of the unify stream for the term.
  #[inline]
  pub fn unify(&self) -> UnifyIter<'a> { UnifyIter::new(self.unify) }
}

impl<'a> ThmRef<'a> {
  /// The list of arguments of this axiom/theorem.
  #[inline]
  #[must_use]
  pub fn args(&self) -> &[Arg] { self.args }

  /// The beginning of the unify stream.
  #[inline]
  pub fn unify(&self) -> UnifyIter<'a> { UnifyIter::new(self.unify) }
}

// This always gets the full mmb file. It's not an associated function
// for DeclIter because it's also used by the Index.
//
/// Try to parse the next declaration in the mmb file; in this case, a
/// declaration is represented by a pair `[(StmtCmd, ProofIter)]`.
/// On success, will also return the new start position for the [`DeclIter`]
fn try_next_decl(mmb: &[u8], pos: usize) -> Result<Option<(StmtCmd, ProofIter<'_>)>, ParseError> {
  // The `data` u32 you get back from try_next_cmd is (in this context)
  // the length of the corresponding proof. `new_start_pos` is just
  // the position after the (u8, u32) pair in the mmb stream.
  let Some((stmt_cmd, proof_len, proof_starts_at)) = try_next_cmd(mmb, pos)? else {
    return Ok(None)
  };

  let proof_ends_at = pos + proof_len as usize;

  if proof_ends_at < proof_starts_at {
    return Err(ParseError::BadProofLen(pos))
  }

  let pr = ProofIter { mmb_source: mmb, pos: proof_starts_at, ends_at: proof_ends_at };

  Ok(Some((StmtCmd::try_from(stmt_cmd)?, pr)))
}

/// An iterator over the declaration stream.
#[must_use]
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

  /// Scan until the end of the proof stream, and return the file position just after the
  /// `END` command.
  pub fn after_end(&self) -> Result<usize, ParseError> {
    let mut pos = self.pos;
    loop {
      let (cmd, stmt_len, next_cmd) = parse_cmd(self.mmb_file, pos)?;
      if cmd == 0 {
        return Ok(next_cmd)
      }
      let new_pos = pos + (stmt_len as usize);
      if new_pos < next_cmd {
        return Err(ParseError::BadProofLen(pos))
      }
      pos = new_pos;
    }
  }
}

impl<'a> Iterator for DeclIter<'a> {
  type Item = Result<(NumdStmtCmd, ProofIter<'a>), ParseError>;
  fn next(&mut self) -> Option<Self::Item> {
    match try_next_decl(self.mmb_file, self.pos) {
      Err(e) => Some(Err(e)),
      Ok(None) => None,
      Ok(Some((stmt, proof_iter))) => {
        self.pos = proof_iter.ends_at;
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

impl<'a> NameEntryRef<'a> {
  /// Extract the name of this index entry as a `&str`.
  #[must_use]
  pub fn value(&self) -> Option<&'a str> { cstr_from_bytes_prefix(self.value)?.0.to_str().ok() }

  /// The statement that sourced this entry.
  pub fn decl(&self) -> Result<Option<(StmtCmd, ProofIter<'a>)>, ParseError> {
    try_next_decl(self.buf, u64_as_usize(self.p_proof))
  }
}
