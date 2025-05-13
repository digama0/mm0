//! Import and export functionality for MMB binary proof format
//!
//! See [`mm0-c/verifier.c`] for information on the MMB format.
//!
//! [`mm0-c/verifier.c`]: https://github.com/digama0/mm0/blob/master/mm0-c/verifier.c

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
#![deny(unsafe_op_in_unsafe_fn)]
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
  clippy::undocumented_unsafe_blocks,
  clippy::unwrap_used
)]
// all the clippy lints we don't want
#![allow(
  clippy::cognitive_complexity,
  clippy::comparison_chain,
  clippy::default_trait_access,
  clippy::inline_always,
  clippy::manual_filter_map,
  clippy::map_err_ignore,
  clippy::missing_const_for_fn,
  clippy::missing_errors_doc,
  clippy::missing_panics_doc,
  clippy::module_name_repetitions,
  clippy::multiple_crate_versions,
  clippy::option_if_let_else,
  clippy::redundant_pub_crate,
  clippy::semicolon_if_nothing_returned,
  clippy::shadow_unrelated,
  clippy::too_many_lines,
  clippy::use_self
)]

mod parser;
mod ty;
mod write;

use std::ffi::CStr;
use std::mem::size_of;

use mm0_util::{Modifiers, SortId, TermId, ThmId};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, LE, U16, U32, U64, Unaligned};

pub use mm0_util::u32_as_usize;
pub use {parser::*, ty::*, write::*};

/// The maximum number of bound variables supported by the MMB format.
pub const MAX_BOUND_VARS: usize = 55;

/// Constants used in the MMB specification.
pub mod cmd {
  /// `MM0B_MAGIC = "MM0B"`: Magic number signalling the MM0B format is in use.
  pub const MM0B_MAGIC: [u8; 4] = *b"MM0B";
  /// `MM0B_VERSION = 1`, maximum supported MMB version
  pub const MM0B_VERSION: u8 = 1;

  /// `DATA_8 = 0x40`, used as a command mask for an 8 bit data field
  pub const DATA_8: u8 = 0x40;
  /// `DATA_16 = 0x80`, used as a command mask for a 16 bit data field
  pub const DATA_16: u8 = 0x80;
  /// `DATA_32 = 0xC0`, used as a command mask for a 32 bit data field
  pub const DATA_32: u8 = 0xC0;
  /// `DATA_MASK = 0xC0`, selects one of `DATA_8`, `DATA_16`, or `DATA_32` for data size
  pub const DATA_MASK: u8 = 0xC0;

  /// `STMT_AXIOM = 0x02`, starts an `axiom` declaration
  pub const STMT_AXIOM: u8 = 0x02;
  /// `STMT_SORT = 0x04`, starts a `sort` declaration
  pub const STMT_SORT: u8 = 0x04;
  /// `STMT_TERM = 0x05`, starts a `term` declaration
  pub const STMT_TERM: u8 = 0x05;
  /// `STMT_DEF = 0x05`, starts a `def` declaration. (This is the same as
  /// `STMT_TERM` because the actual indication of whether this is a
  /// def is in the term header)
  pub const STMT_DEF: u8 = 0x05;
  /// `STMT_THM = 0x06`, starts a `theorem` declaration
  pub const STMT_THM: u8 = 0x06;
  /// `STMT_LOCAL = 0x08`, starts a `local` declaration
  /// (a bit mask to be combined with `STMT_THM` or `STMT_DEF`)
  pub const STMT_LOCAL: u8 = 0x08;
  /// `STMT_LOCAL_DEF = 0x0D`
  pub const STMT_LOCAL_DEF: u8 = STMT_LOCAL | STMT_DEF;
  /// `STMT_LOCAL_THM = 0x0E`
  pub const STMT_LOCAL_THM: u8 = STMT_LOCAL | STMT_THM;

  /// `PROOF_TERM = 0x10`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_TERM: u8 = 0x10;
  /// `PROOF_TERM_SAVE = 0x11`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_TERM_SAVE: u8 = 0x11;
  /// `PROOF_REF = 0x12`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_REF: u8 = 0x12;
  /// `PROOF_DUMMY = 0x13`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_DUMMY: u8 = 0x13;
  /// `PROOF_THM = 0x14`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_THM: u8 = 0x14;
  /// `PROOF_THM_SAVE = 0x15`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_THM_SAVE: u8 = 0x15;
  /// `PROOF_HYP = 0x16`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_HYP: u8 = 0x16;
  /// `PROOF_CONV = 0x17`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_CONV: u8 = 0x17;
  /// `PROOF_REFL = 0x18`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_REFL: u8 = 0x18;
  /// `PROOF_SYMM = 0x19`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_SYMM: u8 = 0x19;
  /// `PROOF_CONG = 0x1A`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_CONG: u8 = 0x1A;
  /// `PROOF_UNFOLD = 0x1B`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_UNFOLD: u8 = 0x1B;
  /// `PROOF_CONV_CUT = 0x1C`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_CONV_CUT: u8 = 0x1C;
  /// `PROOF_CONV_SAVE = 0x1E`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_CONV_SAVE: u8 = 0x1E;
  /// `PROOF_SAVE = 0x1F`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_SAVE: u8 = 0x1F;
  /// `PROOF_SORRY = 0x20`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_SORRY: u8 = 0x20;

  /// `UNIFY_TERM = 0x30`: See [`UnifyCmd`](super::UnifyCmd).
  pub const UNIFY_TERM: u8 = 0x30;
  /// `UNIFY_TERM_SAVE = 0x31`: See [`UnifyCmd`](super::UnifyCmd).
  pub const UNIFY_TERM_SAVE: u8 = 0x31;
  /// `UNIFY_REF = 0x32`: See [`UnifyCmd`](super::UnifyCmd).
  pub const UNIFY_REF: u8 = 0x32;
  /// `UNIFY_DUMMY = 0x33`: See [`UnifyCmd`](super::UnifyCmd).
  pub const UNIFY_DUMMY: u8 = 0x33;
  /// `UNIFY_HYP = 0x36`: See [`UnifyCmd`](super::UnifyCmd).
  pub const UNIFY_HYP: u8 = 0x36;

  /// `"Name"` is the magic number for the name table.
  pub const INDEX_NAME: [u8; 4] = *b"Name";
  /// `"VarN"` is the magic number for the variable name table.
  pub const INDEX_VAR_NAME: [u8; 4] = *b"VarN";
  /// `"HypN"` is the magic number for the hypothesis name table.
  pub const INDEX_HYP_NAME: [u8; 4] = *b"HypN";
}

#[inline]
fn u64_as_usize(n: U64<LE>) -> usize {
  n.get().try_into().expect("here's a nickel, get a better computer")
}

/// Construct a <code>&amp;[CStr]</code> from a prefix byte slice, by terminating at
/// the first nul character. The second output is the remainder of the slice.
#[must_use]
pub fn cstr_from_bytes_prefix(bytes: &[u8]) -> Option<(&CStr, &[u8])> {
  let mid = memchr::memchr(0, bytes)? + 1;
  // Safety: mid <= bytes.len()
  let (left, right) = unsafe { (bytes.get_unchecked(..mid), bytes.get_unchecked(mid..)) };
  // Safety: memchr ensures there are no internal NUL characters
  let cstr = unsafe { CStr::from_bytes_with_nul_unchecked(left) };
  Some((cstr, right))
}

/// The main part of the proof consists of a sequence of declarations,
/// and these commands denote the different kind of declaration that can
/// be introduced.
#[derive(Debug, Clone, Copy)]
pub enum StmtCmd {
  /// A new sort. Equivalent to `sort foo;`. This is followed by no data,
  /// as the sort data is stored in the header.
  Sort,
  /// A new axiom. Equivalent to `axiom foo ...`. This is followed by a proof
  /// sequence, that should unify with the unify sequence in the header.
  Axiom,
  /// A new term or def. Equivalent to `term/def foo ...`.
  /// If `local` is true, then this is `local def foo`. This is followed by
  /// no data, as the header contains the unify sequence and can be checked on its own.
  TermDef {
    /// Is this `local def`?
    local: bool,
  },
  /// A new theorem. Equivalent to `(pub) theorem foo ...`, where `local` means
  /// that the theorem is not `pub`. This is followed by a proof sequence,
  /// that will construct the statement and proof, and should unify
  /// with the unify sequence in the header.
  Thm {
    /// Is this not `pub theorem`?
    local: bool,
  },
}

// IMO breaking this out is preferred to making the id fields Option<A> in StmtCmd
// because the situations in which you will/won't have the id are known beforehand.
// The only case in which you won't have it is when fishing things out from the index
// with IndexEntryRef::decl
//
/// [`StmtCmd`] aware of its position (represented by a typesafe integer)
/// in the mmb file relative to other declarations.
#[derive(Debug, Clone, Copy)]
pub enum NumdStmtCmd {
  /// A new sort. Equivalent to `sort foo;`. This is followed by no data,
  /// as the sort data is stored in the header.
  Sort {
    /// The sort ID, the index into the sort table
    sort_id: SortId,
  },
  /// A new axiom. Equivalent to `axiom foo ...`. This is followed by a proof
  /// sequence, that should unify with the unify sequence in the header.
  Axiom {
    /// The theorem ID, the index into the axiom/theorem table
    thm_id: ThmId,
  },
  /// A new term or def. Equivalent to `term/def foo ...`.
  /// If `local` is true, then this is `local def foo`. This is followed by
  /// no data, as the header contains the unify sequence and can be checked on its own.
  TermDef {
    /// The term ID, the index into the term/def table
    term_id: TermId,
    /// Is this `local def`?
    local: bool,
  },
  /// A new theorem. Equivalent to `(pub) theorem foo ...`, where `local` means
  /// that the theorem is not `pub`. This is followed by a proof sequence,
  /// that will construct the statement and proof, and should unify
  /// with the unify sequence in the header.
  Thm {
    /// The theorem ID, the index into the axiom/theorem table
    thm_id: ThmId,
    /// Is this not `pub theorem`?
    local: bool,
  },
}

impl StmtCmd {
  /// Is this a "local" command, i.e. it does not appear in the corresponding MM0 file?
  #[must_use]
  pub fn is_local(self) -> bool {
    match self {
      Self::Sort | Self::Axiom => false,
      Self::TermDef { local } | Self::Thm { local } => local,
    }
  }
}

impl NumdStmtCmd {
  /// Is this a "local" command, i.e. it does not appear in the corresponding MM0 file?
  #[must_use]
  pub fn is_local(self) -> bool {
    match self {
      Self::Sort { .. } | Self::Axiom { .. } => false,
      Self::TermDef { local, .. } | Self::Thm { local, .. } => local,
    }
  }
}

impl TryFrom<u8> for StmtCmd {
  type Error = ParseError;
  fn try_from(cmd: u8) -> Result<Self, Self::Error> {
    Ok(match cmd {
      cmd::STMT_SORT => StmtCmd::Sort,
      cmd::STMT_AXIOM => StmtCmd::Axiom,
      cmd::STMT_DEF => StmtCmd::TermDef { local: false },
      cmd::STMT_LOCAL_DEF => StmtCmd::TermDef { local: true },
      cmd::STMT_THM => StmtCmd::Thm { local: false },
      cmd::STMT_LOCAL_THM => StmtCmd::Thm { local: true },
      _ => return Err(ParseError::StmtCmdConv(cmd)),
    })
  }
}

/// A proof command, which acts on a stack machine with the following components:
///
/// * `H: Vec<StackEl>`: a "heap" consisting of indexable elements that can be copied
///   onto the stack using [`Ref`](ProofCmd::Ref)
/// * `S: Stack<StackEl>`: The main stack, which most operations push and pop from.
/// * `HS: Vec<Expr>`: The hypothesis list, which grows only on [`Hyp`](ProofCmd::Hyp)
///   operations and collects the hypotheses of the theorem.
#[derive(Debug, Clone, Copy)]
pub enum ProofCmd {
  /// ```text
  /// Term t: H; S, e1, ..., en --> H; S, (t e1 .. en)
  /// Save: H; S, e --> H, e; S, e
  /// TermSave t = Term t; Save:
  ///   H; S, e1, ..., en --> H, (t e1 .. en); S, (t e1 .. en)
  /// ```
  ///
  /// Pop `n` elements from the stack and allocate a new term `t` applied to those
  /// expressions. When `save` is used, the new term is also saved to the heap
  /// (this is used if the term will ever be needed more than once).
  Term {
    /// The term to construct
    tid: TermId,
    /// True if we should save to the heap
    save: bool,
  },
  /// ```text
  /// Ref i: H; S --> H; S, Hi
  /// ConvRef i: H; S, e1 =?= e2 --> H; S   (where Hi is e1 = e2)
  /// ```
  /// Get the `i`-th heap element.
  /// * If it is `e1 = e2`, pop a convertibility obligation `e1 =?= e2`.
  /// * Otherwise push it on the stack.
  Ref(u32),
  /// ```text
  /// Dummy s: H; S --> H, x; S, x    alloc(x:s)
  /// ```
  /// Allocate a new variable `x` of sort `s`, and push it to the stack and the heap.
  Dummy(SortId),
  /// ```text
  /// Thm T: H; S, e1, ..., en, e --> H; S', |- e
  ///   (where Unify(T): S; e1, ... en; e --> S'; H'; .)
  /// Save: H; S, |- e --> H, |- e; S, |- e
  /// ```
  /// Pop `n` elements from the stack and put them on the unify heap, then call the
  /// unifier for `T` with `e` as the target. The unifier will pop additional
  /// proofs from the stack if the `UHyp` command is used, and when it is done,
  /// the conclusion is pushed as a proven statement.
  ///
  /// When Save is used, the proven statement is also saved to the heap.
  Thm {
    /// The theorem to apply
    tid: ThmId,
    /// True if we should save to the heap
    save: bool,
  },
  /// ```text
  /// Hyp: HS; H; S, e --> HS, e; H, |- e; S
  /// ```
  /// This command means that we are finished constructing the expression `e`
  /// which denotes a statement, and wish to assume it as a hypothesis.
  /// Push `e` to the hypothesis stack, and push `|- e` to the heap.
  Hyp,
  /// ```text
  /// Conv: S, e1, |- e2 --> S, |- e1, e1 =?= e2
  /// ```
  /// Pop `e1` and `|- e2`, and push `|- e1`, guarded by a convertibility obligation
  /// `e1 =?= e2`.
  Conv,
  /// ```text
  /// Refl: S, e =?= e --> S
  /// ```
  /// Pop a convertibility obligation where the two sides are equal.
  Refl,
  /// ```text
  /// Symm: S, e1 =?= e2 --> S, e2 =?= e1
  /// ```
  /// Swap the direction of a convertibility obligation.
  Sym,
  /// ```text
  /// Cong: S, (t e1 ... en) =?= (t e1' ... en') --> S, en =?= en', ..., e1 =?= e1'
  /// ```
  /// Pop a convertibility obligation for two term expressions, and
  /// push convertibility obligations for all the parts.
  /// The parts are pushed in reverse order so that they are dealt with
  /// in declaration order in the proof stream.
  Cong,
  /// ```text
  /// Unfold: S, (t e1 ... en) =?= e', e --> S, e =?= e'
  ///   (where Unify(t): e1, ..., en; e --> H'; .)
  /// ```
  /// Pop `e` and `(t e1 ... en) =?= e'` from the stack and run the unifier for `t`
  /// (which should be a definition) to make sure that `(t e1 ... en)` unfolds to `e`.
  /// Then push `e =?= e'`.
  Unfold,
  /// ```text
  /// ConvCut: S, e1 =?= e2 --> S, e1 = e2, e1 =?= e2
  /// ```
  /// Pop a convertibility obligation `e1 =?= e2`, and
  /// push a convertability assertion `e1 = e2` guarded by `e1 =?= e2`.
  ConvCut,
  /// ```text
  /// ConvSave: H; S, e1 = e2 --> H, e1 = e2; S
  /// ```
  /// Pop a convertibility proof `e1 = e2` and save it to the heap.
  ConvSave,
  /// ```text
  /// Save: H; S, s --> H, s; S, s
  /// ```
  /// Save the top of the stack to the heap, without popping it.
  Save,
  /// ```text
  /// Sorry: S, e -> S, |- e
  /// ConvSorry: S, e1 =?= e2 -> S
  /// ```
  /// * `Sorry`: Pop an expression `e` from the stack, and push `|- e`. This step exists
  ///   only for debugging purposes and incomplete proofs, it is not a valid step
  ///   under any circumstances, and verifiers are free to pretend it doesn't exist.
  ///
  /// * `ConvSorry`: Pop a convertibility obligation `e1 =?= e2`. This reuses the `Sorry`
  ///   command, and depends on the type of the head of stack for its behavior.
  Sorry,
}

impl TryFrom<(u8, u32)> for ProofCmd {
  type Error = ParseError;
  fn try_from((cmd, data): (u8, u32)) -> Result<Self, Self::Error> {
    Ok(match cmd {
      cmd::PROOF_TERM => ProofCmd::Term { tid: TermId(data), save: false },
      cmd::PROOF_TERM_SAVE => ProofCmd::Term { tid: TermId(data), save: true },
      cmd::PROOF_REF => ProofCmd::Ref(data),
      cmd::PROOF_DUMMY =>
        ProofCmd::Dummy(SortId(data.try_into().map_err(|_| ParseError::ProofCmdConv(cmd, data))?)),
      cmd::PROOF_THM => ProofCmd::Thm { tid: ThmId(data), save: false },
      cmd::PROOF_THM_SAVE => ProofCmd::Thm { tid: ThmId(data), save: true },
      cmd::PROOF_HYP => ProofCmd::Hyp,
      cmd::PROOF_CONV => ProofCmd::Conv,
      cmd::PROOF_REFL => ProofCmd::Refl,
      cmd::PROOF_SYMM => ProofCmd::Sym,
      cmd::PROOF_CONG => ProofCmd::Cong,
      cmd::PROOF_UNFOLD => ProofCmd::Unfold,
      cmd::PROOF_CONV_CUT => ProofCmd::ConvCut,
      cmd::PROOF_CONV_SAVE => ProofCmd::ConvSave,
      cmd::PROOF_SAVE => ProofCmd::Save,
      cmd::PROOF_SORRY => ProofCmd::Sorry,
      _ => return Err(ParseError::ProofCmdConv(cmd, data)),
    })
  }
}

/// A command in the unify stream.
///
/// Unify commands appear in the header data for a `def` or `axiom`/`theorem`.
/// They are executed by the [`ProofCmd::Thm`] command in order to perform
/// substitutions. The state of the unify stack machine is:
///
/// * `MS: Stack<StackEl>`: The main stack, called `S` in the [`ProofCmd`]
///   documentation.
///   Since a unification is called as a subroutine during a proof command,
///   the main stack is available, but most operations don't use it.
/// * `S: Stack<Expr>`: The unify stack, which contains expressions
///   from the target context that are being destructured.
/// * `H: Vec<Expr>`: The unify heap, also known as the substitution. This is
///   initialized with the expressions that the target context would like to
///   substitute for the variable names in the theorem being applied, but
///   it can be extended in order to support substitutions with sharing
///   as well as dummy variables.
#[derive(Debug, Clone, Copy)]
pub enum UnifyCmd {
  /// ```text
  /// UTerm t: S, (t e1 ... en) --> S, en, ..., e1
  /// USave: H; S, e --> H, e; S, e
  /// UTermSave t = USave; UTerm t:
  ///   H; S, (t e1 ... en) --> H, (t e1 ... en); S, en, ..., e1
  /// ```
  /// Pop an element from the stack, ensure that the head is `t`, then
  /// push the `n` arguments to the term (in reverse order, so that they
  /// are dealt with in the correct order in the command stream).
  /// `UTermSave` does the same thing but saves the term to the unify heap
  /// before the destructuring.
  Term {
    /// The term that should be at the head
    tid: TermId,
    /// True if we want to recall this substitution for later
    save: bool,
  },
  /// ```text
  /// URef i: H; S, Hi --> H; S
  /// ```
  /// Get the `i`-th element from the unify heap (the substitution),
  /// and match it against the head of the unify stack.
  Ref(u32),
  /// ```text
  /// UDummy s: H; S, x --> H, x; S   (where x:s)
  /// ```
  /// Pop a variable from the unify stack (ensure that it is a name of
  /// the appropriate sort) and push it to the heap (ensure that it is
  /// distinct from everything else in the substitution).
  Dummy(SortId),
  /// ```text
  /// UHyp (UThm mode):  MS, |- e; S --> MS; S, e
  /// UHyp (UThmEnd mode):  HS, e; S --> HS; S, e
  /// ```
  /// `UHyp` is a command that is used in theorem declarations to indicate that
  /// we are about to read a hypothesis. There are two contexts where we read
  /// this, when we are first declaring the theorem and check the statement (`UThmEnd` mode),
  /// and later when we are applying the theorem and have to apply a substitution (`UThm` mode).
  /// When we are applying the theorem, we have `|- e` on the main stack, and we
  /// pop that and load the expression onto the unify stack.
  /// When we are checking a theorem, we have been pushing hypotheses onto the
  /// hypothesis stack, so we pop it from there instead.
  Hyp,
}

impl TryFrom<(u8, u32)> for UnifyCmd {
  type Error = ParseError;
  fn try_from((cmd, data): (u8, u32)) -> Result<Self, Self::Error> {
    Ok(match cmd {
      cmd::UNIFY_TERM => UnifyCmd::Term { tid: TermId(data), save: false },
      cmd::UNIFY_TERM_SAVE => UnifyCmd::Term { tid: TermId(data), save: true },
      cmd::UNIFY_REF => UnifyCmd::Ref(data),
      cmd::UNIFY_DUMMY =>
        UnifyCmd::Dummy(SortId(data.try_into().map_err(|_| ParseError::UnifyCmdConv(cmd, data))?)),
      cmd::UNIFY_HYP => UnifyCmd::Hyp,
      _ => return Err(ParseError::UnifyCmdConv(cmd, data)),
    })
  }
}

/// The header of an MMB file, which is always in the first bytes of the file.
/// It is followed by a <code>sorts: [[SortData]; num_sorts]</code> array
/// (which we keep separate because of the dependency).
#[repr(C, align(8))]
#[derive(Debug, Clone, Copy, Default, FromBytes, Immutable, KnownLayout)]
pub struct Header {
  /// The magic number, which is used to identify this as an mmb file. Must be
  /// equal to [`MM0B_MAGIC`](cmd::MM0B_MAGIC) = `"MM0B"`.
  pub magic: [u8; 4],
  /// The MMB format version number. Must equal [`MM0B_VERSION`](cmd::MM0B_VERSION) = 1.
  pub version: u8,
  /// The number of sorts in the file. This is limited to 128.
  pub num_sorts: u8,
  /// Padding.
  pub reserved: [u8; 2],
  /// The number of terms and defs in the file.
  pub num_terms: U32<LE>,
  /// The number of axioms and theorems in the file.
  pub num_thms: U32<LE>,
  /// The pointer to the term table of type <code>[[TermEntry]; num_terms]</code>.
  pub p_terms: U32<LE>,
  /// The pointer to the theorem table of type <code>[[ThmEntry]; num_thms]</code>.
  pub p_thms: U32<LE>,
  /// The pointer to the declaration stream.
  pub p_proof: U32<LE>,
  /// Padding.
  pub reserved2: [u8; 4],
  /// The pointer to the index header, an array of `id, data` fields that are parsed by
  /// [`MmbIndexBuilder::build`].
  pub p_index: U64<LE>,
}

impl Header {
  /// On top of the magic number and version checks, perform a non-exhaustive list of
  /// miscellaneous checks to see whether there are issues with
  /// the header that won't be caught by the type system or the integer parsers.
  ///
  /// For example, none of the pointers in the header should be greater than the length
  /// of the file, the terms pointer should be less than the theorems pointer, etc.
  pub fn check(&self, mmb: &[u8]) -> Result<(), ParseError> {
    use crate::cmd::{MM0B_MAGIC, MM0B_VERSION};

    if self.magic != MM0B_MAGIC {
      return Err(ParseError::BadMagic { parsed_magic: self.magic })
    }
    if self.version != MM0B_VERSION {
      return Err(ParseError::BadVersion { parsed_version: self.version })
    }

    let p_terms = u32_as_usize(self.p_terms.get());
    let p_thms = u32_as_usize(self.p_thms.get());
    let p_proof = u32_as_usize(self.p_proof.get());
    let p_index = u64_as_usize(self.p_index);
    let headerspace = size_of::<Header>();
    let sortspace = self.num_sorts as usize;
    let termspace = size_of::<u32>() * u32_as_usize(self.num_terms.get());
    let thmspace = size_of::<u32>() * u32_as_usize(self.num_thms.get());
    if headerspace + sortspace <= p_terms
      && p_terms + termspace <= p_thms
      && p_thms + thmspace <= p_proof
      && p_proof <= mmb.len()
      && (p_index == 0 || p_proof < p_index && p_index <= mmb.len())
    {
      Ok(())
    } else {
      Err(ParseError::SuspectHeader)
    }
  }
}

/// A sort entry in the file header.
///
/// Each sort is one byte, which can be any combination
/// of the modifiers in [`Modifiers::sort_data`]: [`PURE`](Modifiers::PURE),
/// [`STRICT`](Modifiers::STRICT), [`PROVABLE`](Modifiers::PROVABLE), [`FREE`](Modifiers::FREE).
#[repr(C)]
#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, Immutable, Unaligned)]
pub struct SortData(pub u8);

impl TryFrom<SortData> for Modifiers {
  type Error = ();
  #[inline]
  fn try_from(s: SortData) -> Result<Modifiers, ()> {
    let m = Modifiers::new(s.0);
    if Modifiers::sort_data().contains(m) { Ok(m) } else { Err(()) }
  }
}

/// An entry in the term table, which describes the "signature" of the term/def,
/// the information needed to apply the term and use it in theorems.
#[repr(C, align(8))]
#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, Immutable)]
pub struct TermEntry {
  /// The number of arguments to the term.
  pub num_args: U16<LE>,
  /// The high bit is set if this is a `def`. The low 7 bits give the
  /// return sort of the term.
  pub sort: u8,
  /// Padding.
  pub reserved: u8,
  /// The pointer to an <code>args: [[Arg]; num_args + 1]</code> array, followed by the
  /// term's unify command sequence. `args[num_args]` is the return type and dependencies,
  /// and `args[..num_args]` are the actual arguments.
  pub p_args: U32<LE>,
}

/// An entry in the theorem table, which describes the "signature" of the axiom/theorem,
/// the information needed to apply the theorem to use it in other theorems.
#[repr(C, align(8))]
#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, Immutable)]
pub struct ThmEntry {
  /// The number of arguments to the theorem (exprs, not hyps).
  pub num_args: U16<LE>,
  /// Padding.
  pub reserved: [u8; 2],
  /// The pointer to an <code>args: [[Arg]; num_args]</code> array, followed by the
  /// theorem's unify command sequence.
  pub p_args: U32<LE>,
}

/// An index table entry, which is essentially an ID describing the table format, and some
/// additional data to find the actual table.
#[repr(C, align(8))]
#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, Immutable)]
pub struct TableEntry {
  /// A magic number that identifies this table entry, and determines the interpretation of the
  /// rest of the data.
  pub id: [u8; 4],
  /// A 4 byte data field whose interpretation depends on the entry type.
  pub data: U32<LE>,
  /// An 8 byte data field whose interpretation depends on the entry type, but is generally a
  /// pointer to the actual table data.
  pub ptr: U64<LE>,
}

/// An individual symbol name entry in the index.
#[repr(C, align(8))]
#[derive(Debug, Clone, Copy, FromBytes, IntoBytes, Immutable)]
pub struct NameEntry {
  /// A pointer to the location in the proof stream which introduced this entity.
  pub p_proof: U64<LE>,
  /// A pointer to the entity's name as a UTF-8 C string.
  pub p_name: U64<LE>,
}
