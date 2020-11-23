//! Import and export functionality for MMB binary proof format
//!
//! See [`mm0-c/verifier.c`] for information on the MMB format.
//!
//! [`mm0-c/verifier.c`]: https://github.com/digama0/mm0/blob/master/mm0-c/verifier.c
#![allow(unused, missing_docs)]
use crate::elab::environment::{SortID, TermID, ThmID};
use byteorder::LE;
use zerocopy::{FromBytes, Unaligned, U16, U32, U64};

pub mod parser;
pub mod import;
pub mod export;

/// Constants used in the MMB specification.
pub mod cmd {
  /// `MM0B_MAGIC = "MM0B"`: Magic number signalling the MM0B format is in use.
  pub const MM0B_MAGIC: [u8; 4] = *b"MM0B";
  /// `MM0B_VERSION = 1`, maximum supported MMB version
  pub const MM0B_VERSION: u8 = 1;

  /// `DATA_8 = 0x40`, used as a command mask for an 8 bit data field
  pub const DATA_8: u8  = 0x40;
  /// `DATA_16 = 0x80`, used as a command mask for a 16 bit data field
  pub const DATA_16: u8 = 0x80;
  /// `DATA_32 = 0xC0`, used as a command mask for a 32 bit data field
  pub const DATA_32: u8 = 0xC0;
  /// `DATA_MASK = 0xC0`, selects one of `DATA_8`, `DATA_16`, or `DATA_32` for data size
  pub const DATA_MASK: u8 = 0xC0;

  /// `STMT_SORT = 0x04`, starts a `sort` declaration
  pub const STMT_SORT: u8  = 0x04;
  /// `STMT_AXIOM = 0x02`, starts an `axiom` declaration
  pub const STMT_AXIOM: u8 = 0x02;
  /// `STMT_TERM = 0x05`, starts a `term` declaration
  pub const STMT_TERM: u8  = 0x05;
  /// `STMT_DEF = 0x05`, starts a `def` declaration. (This is the same as
  /// `STMT_TERM` because the actual indication of whether this is a
  /// def is in the term header)
  pub const STMT_DEF: u8   = 0x05;
  /// `STMT_THM = 0x06`, starts a `theorem` declaration
  pub const STMT_THM: u8   = 0x06;
  /// `STMT_LOCAL = 0x08`, starts a `local` declaration
  /// (a bit mask to be combined with `STMT_THM` or `STMT_DEF`)
  pub const STMT_LOCAL: u8 = 0x08;

  /// `PROOF_TERM = 0x10`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_TERM: u8      = 0x10;
  /// `PROOF_TERM_SAVE = 0x11`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_TERM_SAVE: u8 = 0x11;
  /// `PROOF_REF = 0x12`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_REF: u8       = 0x12;
  /// `PROOF_DUMMY = 0x13`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_DUMMY: u8     = 0x13;
  /// `PROOF_THM = 0x14`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_THM: u8       = 0x14;
  /// `PROOF_THM_SAVE = 0x15`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_THM_SAVE: u8  = 0x15;
  /// `PROOF_HYP = 0x16`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_HYP: u8       = 0x16;
  /// `PROOF_CONV = 0x17`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_CONV: u8      = 0x17;
  /// `PROOF_REFL = 0x18`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_REFL: u8      = 0x18;
  /// `PROOF_SYMM = 0x19`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_SYMM: u8      = 0x19;
  /// `PROOF_CONG = 0x1A`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_CONG: u8      = 0x1A;
  /// `PROOF_UNFOLD = 0x1B`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_UNFOLD: u8    = 0x1B;
  /// `PROOF_CONV_CUT = 0x1C`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_CONV_CUT: u8  = 0x1C;
  /// `PROOF_CONV_REF = 0x1D`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_CONV_REF: u8  = 0x1D;
  /// `PROOF_CONV_SAVE = 0x1E`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_CONV_SAVE: u8 = 0x1E;
  /// `PROOF_SAVE = 0x1F`: See [`ProofCmd`](../enum.ProofCmd.html).
  pub const PROOF_SAVE: u8      = 0x1F;

  /// `UNIFY_TERM = 0x30`: See [`UnifyCmd`](../enum.UnifyCmd.html).
  pub const UNIFY_TERM: u8      = 0x30;
  /// `UNIFY_TERM_SAVE = 0x31`: See [`UnifyCmd`](../enum.UnifyCmd.html).
  pub const UNIFY_TERM_SAVE: u8 = 0x31;
  /// `UNIFY_REF = 0x32`: See [`UnifyCmd`](../enum.UnifyCmd.html).
  pub const UNIFY_REF: u8       = 0x32;
  /// `UNIFY_DUMMY = 0x33`: See [`UnifyCmd`](../enum.UnifyCmd.html).
  pub const UNIFY_DUMMY: u8     = 0x33;
  /// `UNIFY_HYP = 0x36`: See [`UnifyCmd`](../enum.UnifyCmd.html).
  pub const UNIFY_HYP: u8       = 0x36;
}

#[derive(Debug, Clone, Copy)]
pub enum StmtCmd {
  Sort,
  Axiom,
  Term {local: bool},
  Thm {local: bool}
}

impl std::convert::TryFrom<u8> for StmtCmd {
  type Error = ();
  fn try_from(cmd: u8) -> Result<Self, ()> {
    const STMT_LOCAL_DEF: u8 = cmd::STMT_LOCAL | cmd::STMT_DEF;
    const STMT_LOCAL_THM: u8 = cmd::STMT_LOCAL | cmd::STMT_THM;
    Ok(match cmd {
      cmd::STMT_SORT => StmtCmd::Sort,
      cmd::STMT_AXIOM => StmtCmd::Axiom,
      cmd::STMT_TERM => StmtCmd::Term {local: false},
      STMT_LOCAL_DEF => StmtCmd::Term {local: true},
      cmd::STMT_THM => StmtCmd::Thm {local: false},
      STMT_LOCAL_THM => StmtCmd::Thm {local: true},
      _ => return Err(())
    })
  }
}

#[derive(Debug, Clone, Copy)]
pub enum ProofCmd {
  Term {tid: TermID, save: bool},
  Ref(u32),
  Dummy(SortID),
  Thm {tid: ThmID, save: bool},
  Hyp,
  Conv,
  Refl,
  Sym,
  Cong,
  Unfold,
  ConvCut,
  ConvRef(u32),
  ConvSave,
  Save,
}

impl std::convert::TryFrom<(u8, u32)> for ProofCmd {
  type Error = ();
  fn try_from((cmd, data): (u8, u32)) -> Result<Self, ()> {
    use std::convert::TryInto;
    Ok(match cmd {
      cmd::PROOF_TERM => ProofCmd::Term {tid: TermID(data), save: false},
      cmd::PROOF_TERM_SAVE => ProofCmd::Term {tid: TermID(data), save: true},
      cmd::PROOF_REF => ProofCmd::Ref(data),
      cmd::PROOF_DUMMY => ProofCmd::Dummy(SortID(data.try_into().map_err(|_| ())?)),
      cmd::PROOF_THM => ProofCmd::Thm {tid: ThmID(data), save: false},
      cmd::PROOF_THM_SAVE => ProofCmd::Thm {tid: ThmID(data), save: true},
      cmd::PROOF_HYP => ProofCmd::Hyp,
      cmd::PROOF_CONV => ProofCmd::Conv,
      cmd::PROOF_REFL => ProofCmd::Refl,
      cmd::PROOF_SYMM => ProofCmd::Sym,
      cmd::PROOF_CONG => ProofCmd::Cong,
      cmd::PROOF_UNFOLD => ProofCmd::Unfold,
      cmd::PROOF_CONV_CUT => ProofCmd::ConvCut,
      cmd::PROOF_CONV_REF => ProofCmd::ConvRef(data),
      cmd::PROOF_CONV_SAVE => ProofCmd::ConvSave,
      cmd::PROOF_SAVE => ProofCmd::Save,
      _ => return Err(())
    })
  }
}

#[derive(Debug, Clone, Copy)]
pub enum UnifyCmd {
  Term {tid: TermID, save: bool},
  Ref(u32),
  Dummy(SortID),
  Hyp,
}

impl std::convert::TryFrom<(u8, u32)> for UnifyCmd {
  type Error = ();
  fn try_from((cmd, data): (u8, u32)) -> Result<Self, ()> {
    use std::convert::TryInto;
    Ok(match cmd {
      cmd::UNIFY_TERM => UnifyCmd::Term {tid: TermID(data), save: false},
      cmd::UNIFY_TERM_SAVE => UnifyCmd::Term {tid: TermID(data), save: true},
      cmd::UNIFY_REF => UnifyCmd::Ref(data),
      cmd::UNIFY_DUMMY => UnifyCmd::Dummy(SortID(data.try_into().map_err(|_| ())?)),
      cmd::UNIFY_HYP => UnifyCmd::Hyp,
      _ => return Err(())
    })
  }
}

#[repr(C)]
#[derive(Debug, Clone, Copy, FromBytes, Unaligned)]
pub struct Header {
  magic: [u8; 4],
  version: u8,
  num_sorts: u8,
  reserved: [u8; 2],
  num_terms: U32<LE>,
  num_thms: U32<LE>,
  p_terms: U32<LE>,
  p_thms: U32<LE>,
  p_proof: U32<LE>,
  reserved2: [u8; 4],
  p_index: U64<LE>,
}

#[repr(C, align(8))]
#[derive(Debug, Clone, Copy, FromBytes)]
pub struct TermEntry {
  num_args: U16<LE>,
  sort: u8,
  reserved: u8,
  p_args: U32<LE>,
}

#[repr(C, align(4))]
#[derive(Debug, Clone, Copy, FromBytes)]
pub struct ThmEntry {
  num_args: U16<LE>,
  reserved: [u8; 2],
  p_args: U32<LE>,
}

#[repr(C)]
#[derive(Debug, Clone, Copy, FromBytes, Unaligned)]
pub struct IndexEntry {
  p_left: U64<LE>,
  p_right: U64<LE>,
  row: U32<LE>,
  col: U32<LE>,
  p_proof: U64<LE>,
  ix: U32<LE>,
}