use crate::{cmd::*, ProofCmd, UnifyCmd};
use byteorder::{WriteBytesExt, LE};
use std::convert::TryInto;
use std::io::{self, Write};

/// Encode the command `cmd` (one of the `STMT_*`, `PROOF_*` or `UNIFY_*` commands
/// in this module, which are all 6 bit numbers) with the given `data` field
/// according to the following scheme:
///
///   * `cmd | 0x00` for `data = 0`
///   * `cmd | 0x40, data:u8` for 8 bit `data`
///   * `cmd | 0x80, data:u16` for 16 bit `data`
///   * `cmd | 0xC0, data:u32` for 32 bit `data`
///
/// where we select the shortest available encoding given the value of `data`.
fn write_cmd(w: &mut impl Write, cmd: u8, data: u32) -> io::Result<()> {
  if data == 0 {
    w.write_u8(cmd)
  } else if let Ok(data) = data.try_into() {
    w.write_u8(cmd | DATA_8)?;
    w.write_u8(data)
  } else if let Ok(data) = data.try_into() {
    w.write_u8(cmd | DATA_16)?;
    w.write_u16::<LE>(data)
  } else {
    w.write_u8(cmd | DATA_32)?;
    w.write_u32::<LE>(data)
  }
}

/// This is like [`write_cmd`], but it is followed by
/// the byte array `buf`, and the initial `data` field is the length of the entire
/// expression (the initial command byte, the `data` field, and the buffer).
/// This can't be expressed with `write_cmd` directly because of the circular
/// dependency where the value of `data` determines the size of the initial command,
/// which affects the value of `data`.
pub fn write_cmd_bytes(w: &mut impl Write, cmd: u8, buf: &[u8]) -> io::Result<()> {
  if let Ok(data) = (buf.len() + 2).try_into() {
    w.write_u8(cmd | DATA_8)?;
    w.write_u8(data)?;
    w.write_all(buf)
  } else if let Ok(data) = (buf.len() + 3).try_into() {
    w.write_u8(cmd | DATA_16)?;
    w.write_u16::<LE>(data)?;
    w.write_all(buf)
  } else {
    w.write_u8(cmd | DATA_32)?;
    w.write_u32::<LE>((buf.len() + 5).try_into().expect("too large for format"))?;
    w.write_all(buf)
  }
}

impl UnifyCmd {
  /// Serialize a [`UnifyCmd`] to the given writer. Uses the `UNIFY_*` commands in
  /// [`mmb::export::cmd`](super::cmd).
  #[inline]
  pub fn write_to(self, w: &mut impl Write) -> io::Result<()> {
    match self {
      UnifyCmd::Term { tid, save } =>
        write_cmd(w, if save { UNIFY_TERM_SAVE } else { UNIFY_TERM }, tid.0),
      UnifyCmd::Ref(n) => write_cmd(w, UNIFY_REF, n),
      UnifyCmd::Dummy(sid) => write_cmd(w, UNIFY_DUMMY, sid.0.into()),
      UnifyCmd::Hyp => w.write_u8(UNIFY_HYP),
    }
  }
}

impl ProofCmd {
  /// Serialize a [`ProofCmd`] to the given writer. Uses the `PROOF_*` commands in
  /// [`mmb::export::cmd`](super::cmd).
  #[inline]
  pub fn write_to(self, w: &mut impl Write) -> io::Result<()> {
    match self {
      ProofCmd::Term { tid, save } =>
        write_cmd(w, if save { PROOF_TERM_SAVE } else { PROOF_TERM }, tid.0),
      ProofCmd::Ref(n) => write_cmd(w, PROOF_REF, n),
      ProofCmd::Dummy(sid) => write_cmd(w, PROOF_DUMMY, sid.0.into()),
      ProofCmd::Thm { tid, save } =>
        write_cmd(w, if save { PROOF_THM_SAVE } else { PROOF_THM }, tid.0),
      ProofCmd::Hyp => w.write_u8(PROOF_HYP),
      ProofCmd::Conv => w.write_u8(PROOF_CONV),
      ProofCmd::Refl => w.write_u8(PROOF_REFL),
      ProofCmd::Sym => w.write_u8(PROOF_SYMM),
      ProofCmd::Cong => w.write_u8(PROOF_CONG),
      ProofCmd::Unfold => w.write_u8(PROOF_UNFOLD),
      ProofCmd::ConvCut => w.write_u8(PROOF_CONV_CUT),
      ProofCmd::ConvRef(n) => write_cmd(w, PROOF_CONV_REF, n),
      ProofCmd::ConvSave => w.write_u8(PROOF_CONV_SAVE),
      ProofCmd::Save => w.write_u8(PROOF_SAVE),
      ProofCmd::Sorry => w.write_u8(PROOF_SORRY),
    }
  }
}
