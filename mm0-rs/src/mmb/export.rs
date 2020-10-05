//! MMB exporter, which produces `.mmb` binary proof files from an `Environment` object.
use std::convert::TryInto;
use std::mem;
use std::io::{self, Write, Seek, SeekFrom};
use byteorder::{LE, ByteOrder, WriteBytesExt};
use crate::elab::environment::{
  Type, Expr, Proof, SortID, TermID, ThmID, AtomID,
  TermVec, ExprNode, ProofNode, StmtTrace, DeclKey, Modifiers};
use crate::elab::FrozenEnv;
use crate::util::FileRef;
use crate::lined_string::LinedString;

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
use cmd::*;

#[derive(Debug)]
enum ProofCmd {
  Term(TermID),
  TermSave(TermID),
  Ref(u32),
  Dummy(SortID),
  Thm(ThmID),
  ThmSave(ThmID),
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

#[derive(Debug)]
enum UnifyCmd {
  Term(TermID),
  TermSave(TermID),
  Ref(u32),
  Dummy(SortID),
  Hyp,
}

#[derive(Debug)]
struct Reorder<T=u32> {
  map: Box<[Option<T>]>,
  idx: u32,
}

impl<T> Reorder<T> {
  fn new(nargs: u32, len: usize, mut f: impl FnMut(u32) -> T) -> Reorder<T> {
    assert!(nargs as usize <= len);
    let mut map = Vec::with_capacity(len);
    map.extend((0..nargs).map(|i| Some(f(i))));
    map.resize_with(len, Default::default);
    let mut map: Box<[Option<T>]> = map.into();
    for i in 0..nargs {map[i as usize] = Some(f(i))}
    Reorder {map, idx: nargs}
  }
}

struct IndexHeader<'a> {
  sorts: &'a mut [[u8; 8]],
  terms: &'a mut [[u8; 8]],
  thms: &'a mut [[u8; 8]]
}

impl<'a> IndexHeader<'a> {
  fn sort(&mut self, i: SortID) -> &mut [u8; 8] { &mut self.sorts[i.0 as usize] }
  fn term(&mut self, i: TermID) -> &mut [u8; 8] { &mut self.terms[i.0 as usize] }
  fn thm(&mut self, i: ThmID) -> &mut [u8; 8] { &mut self.thms[i.0 as usize] }
}

/// The main exporter structure. This keeps track of the underlying writer,
/// as well as tracking values that are written out of order.
#[derive(Debug)]
pub struct Exporter<'a, W: Write + Seek> {
  /// The name of the input file. This is only used in the debugging data.
  file: FileRef,
  /// The source text of the input file. This is only used in the debugging data.
  source: &'a LinedString,
  /// The input environment.
  env: &'a FrozenEnv,
  /// The underlying writer, which must support `Seek` because we write some parts
  /// of the file out of order. The [`BigBuffer`] wrapper can be used to equip a
  /// writer that doesn't support it with a `Seek` implementation.
  ///
  /// [`BigBuffer`]: struct.BigBuffer.html
  w: W,
  /// The current byte position of the writer.
  pos: u64,
  /// The calculated reorder maps for terms encountered so far (see [`Reorder`]).
  ///
  /// [`Reorder`]: struct.Reorder.html
  term_reord: TermVec<Option<Reorder>>,
  /// A list of "fixups", which are writes that have to occur in places other
  /// than the current writer location. We buffer these to avoid too many seeks
  /// of the underlying writer.
  fixups: Vec<(u64, Value)>,
}

/// A chunk of data that needs to be written out of order.
#[derive(Debug)]
enum Value {
  /// A (little endian) 32 bit value
  U32(u32),
  /// A (little endian) 64 bit value
  U64(u64),
  /// An arbitrary length byte slice. (We could store everything like this but
  /// the `U32` and `U64` cases are common and this avoids some allocation.)
  Box(Box<[u8]>),
}

/// A type for a 32 bit fixup, representing a promise to write 32 bits at the stored
/// location. It is generated by [`fixup32`](struct.Exporter.html#method.fixup32) method,
/// and it is marked `#[must_use]` because it should be consumed by
/// [`commit`](struct.Fixup32.html#method.commit), which requires fulfilling the promise.
#[must_use] struct Fixup32(u64);

/// A type for a 64 bit fixup, representing a promise to write 64 bits at the stored
/// location. It is generated by [`fixup64`](struct.Exporter.html#method.fixup64) method,
/// and it is marked `#[must_use]` because it should be consumed by
/// [`commit`](struct.Fixup64.html#method.commit), which requires fulfilling the promise.
#[must_use] struct Fixup64(u64);

/// A type for an arbitrary size fixup, representing a promise to write some number of bytes
/// bits at the given location. It is generated by
/// [`fixup_large`](struct.Exporter.html#method.fixup_large) method,
/// and it is marked `#[must_use]` because it should be consumed by
/// [`commit`](struct.FixupLarge.html#method.commit), which requires fulfilling the promise.
#[must_use] struct FixupLarge(u64, Box<[u8]>);

impl Fixup32 {
  /// Write `val` to this fixup, closing it.
  fn commit_val<'a, W: Write + Seek>(self, e: &mut Exporter<'a, W>, val: u32) {
    e.fixups.push((self.0, Value::U32(val)))
  }
  /// Write the current position of the exporter to this fixup, closing it.
  fn commit<'a, W: Write + Seek>(self, e: &mut Exporter<'a, W>) {
    let val = e.pos.try_into().unwrap();
    self.commit_val(e, val)
  }
}

impl Fixup64 {
  /// Write `val` to this fixup, closing it.
  fn commit_val<'a, W: Write + Seek>(self, e: &mut Exporter<'a, W>, val: u64) {
    e.fixups.push((self.0, Value::U64(val)))
  }
  /// Write the current position of the exporter to this fixup, closing it.
  fn commit<'a, W: Write + Seek>(self, e: &mut Exporter<'a, W>) {
    let val = e.pos;
    self.commit_val(e, val)
  }
  /// Drop the value, which has the effect of writing 0 to the original fixup.
  #[inline] fn cancel(self) {}
}

impl std::ops::Deref for FixupLarge {
  type Target = [u8];
  fn deref(&self) -> &[u8] { &self.1 }
}
impl std::ops::DerefMut for FixupLarge {
  fn deref_mut(&mut self) -> &mut [u8] { &mut self.1 }
}

impl FixupLarge {
  /// Assume that the construction of the fixup is complete, and write the stored value.
  fn commit<'a, W: Write + Seek>(self, e: &mut Exporter<'a, W>) {
    e.fixups.push((self.0, Value::Box(self.1)))
  }
}

impl<'a, W: Write + Seek> Write for Exporter<'a, W> {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    self.write_all(buf)?;
    Ok(buf.len())
  }
  fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
    self.pos += buf.len() as u64;
    self.w.write_all(buf)
  }
  fn flush(&mut self) -> io::Result<()> { self.w.flush() }
}

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

/// This is like [`write_cmd`](fn.write_cmd.html), but it is followed by
/// the byte array `buf`, and the initial `data` field is the length of the entire
/// expression (the initial command byte, the `data` field, and the buffer).
/// This can't be expressed with `write_cmd` directly because of the circular
/// dependency where the value of `data` determines the size of the initial command,
/// which affects the value of `data`.
fn write_cmd_bytes(w: &mut impl Write, cmd: u8, buf: &[u8]) -> io::Result<()> {
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
    w.write_u32::<LE>((buf.len() + 5).try_into().unwrap())?;
    w.write_all(buf)
  }
}

impl UnifyCmd {
  /// Serialize a `UnifyCmd` to the given writer. Uses the `UNIFY_*` commands in
  /// [`mmb::export::cmd`](cmd/index.html).
  #[inline] fn write_to(self, w: &mut impl Write) -> io::Result<()> {
    match self {
      UnifyCmd::Term(tid)     => write_cmd(w, UNIFY_TERM, tid.0),
      UnifyCmd::TermSave(tid) => write_cmd(w, UNIFY_TERM_SAVE, tid.0),
      UnifyCmd::Ref(n)        => write_cmd(w, UNIFY_REF, n),
      UnifyCmd::Dummy(sid)    => write_cmd(w, UNIFY_DUMMY, sid.0 as u32),
      UnifyCmd::Hyp           => w.write_u8(UNIFY_HYP),
    }
  }
}

impl ProofCmd {
  /// Serialize a `ProofCmd` to the given writer. Uses the `PROOF_*` commands in
  /// [`mmb::export::cmd`](cmd/index.html).
  #[inline] fn write_to(self, w: &mut impl Write) -> io::Result<()> {
    match self {
      ProofCmd::Term(tid)     => write_cmd(w, PROOF_TERM, tid.0),
      ProofCmd::TermSave(tid) => write_cmd(w, PROOF_TERM_SAVE, tid.0),
      ProofCmd::Ref(n)        => write_cmd(w, PROOF_REF, n),
      ProofCmd::Dummy(sid)    => write_cmd(w, PROOF_DUMMY, sid.0 as u32),
      ProofCmd::Thm(tid)      => write_cmd(w, PROOF_THM, tid.0),
      ProofCmd::ThmSave(tid)  => write_cmd(w, PROOF_THM_SAVE, tid.0),
      ProofCmd::Hyp           => w.write_u8(PROOF_HYP),
      ProofCmd::Conv          => w.write_u8(PROOF_CONV),
      ProofCmd::Refl          => w.write_u8(PROOF_REFL),
      ProofCmd::Sym           => w.write_u8(PROOF_SYMM),
      ProofCmd::Cong          => w.write_u8(PROOF_CONG),
      ProofCmd::Unfold        => w.write_u8(PROOF_UNFOLD),
      ProofCmd::ConvCut       => w.write_u8(PROOF_CONV_CUT),
      ProofCmd::ConvRef(n)    => write_cmd(w, PROOF_CONV_REF, n),
      ProofCmd::ConvSave      => w.write_u8(PROOF_CONV_SAVE),
      ProofCmd::Save          => w.write_u8(PROOF_SAVE),
    }
  }
}

fn write_expr_proof(w: &mut impl Write,
  heap: &[ExprNode],
  reorder: &mut Reorder,
  head: &ExprNode,
  save: bool
) -> io::Result<u32> {
  Ok(match *head {
    ExprNode::Ref(i) => match reorder.map[i] {
      None => {
        let n = write_expr_proof(w, heap, reorder, &heap[i], true)?;
        reorder.map[i] = Some(n);
        n
      }
      Some(n) => {ProofCmd::Ref(n).write_to(w)?; n}
    }
    ExprNode::Dummy(_, s) => {
      ProofCmd::Dummy(s).write_to(w)?;
      (reorder.idx, reorder.idx += 1).0
    }
    ExprNode::App(t, ref es) => {
      for e in &**es {write_expr_proof(w, heap, reorder, e, false)?;}
      if save {
        ProofCmd::TermSave(t).write_to(w)?;
        (reorder.idx, reorder.idx += 1).0
      } else {ProofCmd::Term(t).write_to(w)?; 0}
    }
  })
}

/// A wrapper around a writer that implements `Write + Seek` by internally buffering
/// all writes, writing to the underlying writer only once on `Drop`.
#[derive(Debug)]
pub struct BigBuffer<W: Write> {
  buffer: io::Cursor<Vec<u8>>,
  w: W,
}

impl<W: Write> BigBuffer<W> {
  /// Creates a new buffer given an underlying writer.
  pub fn new(w: W) -> Self { Self {buffer: Default::default(), w} }
  /// Flushes the buffer to the underlying writer, consuming the result.
  /// (The `Drop` implementation will also do this, but this allows us
  /// to catch IO errors.)
  pub fn finish(mut self) -> io::Result<()> {
    self.w.write_all(&mem::take(self.buffer.get_mut()))
  }
}

impl<W: Write> Write for BigBuffer<W> {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> { self.buffer.write(buf) }
  fn flush(&mut self) -> io::Result<()> { self.buffer.flush() }
}

impl<W: Write> Seek for BigBuffer<W> {
  fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> { self.buffer.seek(pos) }
}

impl<W: Write> Drop for BigBuffer<W> {
  fn drop(&mut self) {
    self.w.write_all(self.buffer.get_ref()).unwrap()
  }
}

impl<'a, W: Write + Seek> Exporter<'a, W> {
  /// Construct a new `Exporter` from an input file `file` with text `source`,
  /// a source environment containing proved theorems, and output writer `w`.
  pub fn new(file: FileRef, source: &'a LinedString, env: &'a FrozenEnv, w: W) -> Self {
    Self {
      term_reord: TermVec(Vec::with_capacity(env.terms().len())),
      file, source, env, w, pos: 0, fixups: vec![]
    }
  }

  fn write_u32(&mut self, n: u32) -> io::Result<()> {
    WriteBytesExt::write_u32::<LE>(self, n)
  }

  fn write_u64(&mut self, n: u64) -> io::Result<()> {
    WriteBytesExt::write_u64::<LE>(self, n)
  }

  fn fixup32(&mut self) -> io::Result<Fixup32> {
    let f = Fixup32(self.pos);
    self.write_u32(0)?;
    Ok(f)
  }

  fn fixup64(&mut self) -> io::Result<Fixup64> {
    let f = Fixup64(self.pos);
    self.write_u64(0)?;
    Ok(f)
  }

  fn fixup_large(&mut self, size: usize) -> io::Result<FixupLarge> {
    let f = FixupLarge(self.pos, vec![0; size].into());
    self.write_all(&f)?;
    Ok(f)
  }

  #[inline]
  fn align_to(&mut self, n: u8) -> io::Result<u64> {
    let i = n.wrapping_sub(self.pos as u8) & (n - 1);
    self.write_all(&vec![0; i as usize])?;
    Ok(self.pos)
  }

  #[inline]
  fn write_sort_deps(&mut self, bound: bool, sort: SortID, deps: u64) -> io::Result<()> {
    self.write_u64((bound as u64) << 63 | (sort.0 as u64) << 56 | deps)
  }

  #[inline]
  fn write_term_header(header: &mut [u8], nargs: u16, sort: SortID, has_def: bool, p_term: u32) {
    LE::write_u16(&mut header[0..], nargs);
    header[2] = sort.0 | if has_def {0x80} else {0};
    LE::write_u32(&mut header[4..], p_term);
  }

  fn write_binders<T>(&mut self, args: &[(T, Type)]) -> io::Result<()> {
    let mut bv = 1;
    for (_, ty) in args {
      match *ty {
        Type::Bound(s) => {
          if bv >= (1 << 55) {panic!("more than 55 bound variables")}
          self.write_sort_deps(true, s, bv)?;
          bv *= 2;
        }
        Type::Reg(s, deps) => self.write_sort_deps(false, s, deps)?,
      }
    }
    Ok(())
  }

  fn write_expr_unify(&mut self,
    heap: &[ExprNode],
    reorder: &mut Reorder,
    head: &ExprNode,
    save: &mut Vec<usize>
  ) -> io::Result<()> {
    macro_rules! commit {($n:expr) => {
      for i in save.drain(..) {reorder.map[i] = Some($n)}
    }}
    match *head {
      ExprNode::Ref(i) => match reorder.map[i] {
        None => {
          save.push(i);
          self.write_expr_unify(heap, reorder, &heap[i], save)?
        }
        Some(n) => {
          UnifyCmd::Ref(n).write_to(self)?;
          commit!(n)
        }
      }
      ExprNode::Dummy(_, s) => {
        commit!(reorder.idx); reorder.idx += 1;
        UnifyCmd::Dummy(s).write_to(self)?
      }
      ExprNode::App(t, ref es) => {
        if save.is_empty() {
          UnifyCmd::Term(t).write_to(self)?
        } else {
          commit!(reorder.idx); reorder.idx += 1;
          UnifyCmd::TermSave(t).write_to(self)?
        }
        for e in &**es {
          self.write_expr_unify(heap, reorder, e, save)?
        }
      }
    }
    Ok(())
  }

  fn write_proof(&self, w: &mut impl Write,
    heap: &[ProofNode],
    reorder: &mut Reorder,
    hyps: &[u32],
    head: &ProofNode,
    save: bool
  ) -> io::Result<u32> {
    Ok(match head {
      &ProofNode::Ref(i) => match reorder.map[i] {
        None => {
          let n = self.write_proof(w, heap, reorder, hyps, &heap[i], true)?;
          reorder.map[i] = Some(n);
          n
        }
        Some(n) => {ProofCmd::Ref(n).write_to(w)?; n}
      }
      &ProofNode::Dummy(_, s) => {
        ProofCmd::Dummy(s).write_to(w)?;
        (reorder.idx, reorder.idx += 1).0
      }
      &ProofNode::Term {term, ref args} => {
        for e in &**args {self.write_proof(w, heap, reorder, hyps, e, false)?;}
        if save {
          ProofCmd::TermSave(term).write_to(w)?;
          (reorder.idx, reorder.idx += 1).0
        } else {ProofCmd::Term(term).write_to(w)?; 0}
      }
      &ProofNode::Hyp(n, _) => {
        ProofCmd::Ref(hyps[n]).write_to(w)?;
        hyps[n]
      }
      &ProofNode::Thm {thm, ref args, ref res} => {
        let (args, hs) = args.split_at(self.env.thm(thm).args.len());
        for e in hs {self.write_proof(w, heap, reorder, hyps, e, false)?;}
        for e in args {self.write_proof(w, heap, reorder, hyps, e, false)?;}
        self.write_proof(w, heap, reorder, hyps, res, false)?;
        if save {
          ProofCmd::ThmSave(thm).write_to(w)?;
          (reorder.idx, reorder.idx += 1).0
        } else {ProofCmd::Thm(thm).write_to(w)?; 0}
      }
      ProofNode::Conv(p) => {
        let (e1, c, p) = &**p;
        self.write_proof(w, heap, reorder, hyps, e1, false)?;
        self.write_proof(w, heap, reorder, hyps, p, false)?;
        ProofCmd::Conv.write_to(w)?;
        self.write_conv(w, heap, reorder, hyps, c)?;
        if save {
          ProofCmd::Save.write_to(w)?;
          (reorder.idx, reorder.idx += 1).0
        } else {0}
      }
      ProofNode::Refl(_) |
      ProofNode::Sym(_) |
      ProofNode::Cong {..} |
      ProofNode::Unfold {..} => unreachable!(),
    })
  }

  fn write_conv(&self, w: &mut impl Write,
    heap: &[ProofNode],
    reorder: &mut Reorder,
    hyps: &[u32],
    head: &ProofNode,
  ) -> io::Result<()> {
    match head {
      &ProofNode::Ref(i) => match reorder.map[i] {
        None => {
          let e = &heap[i];
          match e {
            ProofNode::Refl(_) | ProofNode::Ref(_) =>
              self.write_conv(w, heap, reorder, hyps, e)?,
            _ => {
              ProofCmd::ConvCut.write_to(w)?;
              self.write_conv(w, heap, reorder, hyps, e)?;
              ProofCmd::ConvSave.write_to(w)?;
              reorder.map[i] = Some(reorder.idx);
              reorder.idx += 1;
            }
          };
        }
        Some(n) => ProofCmd::ConvRef(n).write_to(w)?,
      }
      ProofNode::Dummy(_, _) |
      ProofNode::Term {..} |
      ProofNode::Hyp(_, _) |
      ProofNode::Thm {..} |
      ProofNode::Conv(_) => unreachable!(),
      ProofNode::Refl(_) => ProofCmd::Refl.write_to(w)?,
      ProofNode::Sym(c) => {
        ProofCmd::Sym.write_to(w)?;
        self.write_conv(w, heap, reorder, hyps, c)?;
      }
      ProofNode::Cong {args, ..} => {
        ProofCmd::Cong.write_to(w)?;
        for a in &**args {self.write_conv(w, heap, reorder, hyps, a)?}
      }
      ProofNode::Unfold {res, ..} => {
        let (l, l2, c) = &**res;
        self.write_proof(w, heap, reorder, hyps, l, false)?;
        self.write_proof(w, heap, reorder, hyps, l2, false)?;
        ProofCmd::Unfold.write_to(w)?;
        self.write_conv(w, heap, reorder, hyps, c)?;
      }
    }
    Ok(())
  }

  #[inline]
  fn write_thm_header(header: &mut [u8], nargs: u16, p_thm: u32) {
    LE::write_u16(&mut header[0..], nargs);
    LE::write_u32(&mut header[4..], p_thm);
  }

  fn write_index_entry(&mut self, header: &mut IndexHeader<'_>, il: u64, ir: u64,
      (sort, a, cmd): (bool, AtomID, u64)) -> io::Result<u64> {
    let n = self.align_to(8)?;
    let (sp, ix, k, name) = if sort {
      let ad = &self.env.data()[a];
      let s = ad.sort().unwrap();
      LE::write_u64(header.sort(s), n);
      (&self.env.sort(s).span, s.0 as u32, STMT_SORT, ad.name())
    } else {
      let ad = &self.env.data()[a];
      match ad.decl().unwrap() {
        DeclKey::Term(t) => {
          let td = self.env.term(t);
          LE::write_u64(header.term(t), n);
          (&td.span, t.0,
            if td.val.is_none() {STMT_TERM}
            else if td.vis == Modifiers::LOCAL {STMT_DEF | STMT_LOCAL}
            else {STMT_DEF},
            ad.name())
        }
        DeclKey::Thm(t) => {
          let td = self.env.thm(t);
          LE::write_u64(header.thm(t), n);
          (&td.span, t.0,
            if td.proof.is_none() {STMT_AXIOM}
            else if td.vis == Modifiers::PUB {STMT_THM}
            else {STMT_THM | STMT_LOCAL},
            ad.name())
        }
      }
    };

    let pos = if sp.file.ptr_eq(&self.file) {
      self.source.to_pos(sp.span.start)
    } else {Default::default()};
    self.write_u64(il)?;
    self.write_u64(ir)?;
    self.write_u32(pos.line as u32)?;
    self.write_u32(pos.character as u32)?;
    self.write_u64(cmd)?;
    self.write_u32(ix)?;
    self.write_u8(k)?;
    self.write_all(name.as_bytes())?;
    self.write_u8(0)?;
    Ok(n)
  }

  fn write_index(&mut self, header: &mut IndexHeader<'_>, left: &[(bool, AtomID, u64)], map: &[(bool, AtomID, u64)]) -> io::Result<u64> {
    let mut lo = map.len() / 2;
    let a = match map.get(lo) {
      None => {
        let mut n = 0;
        for &t in left.iter().rev() {
          n = self.write_index_entry(header, 0, n, t)?
        }
        return Ok(n)
      }
      Some(&(_, a, _)) => a
    };
    let mut hi = lo + 1;
    loop {
      match lo.checked_sub(1) {
        Some(i) if map[i].1 == a => lo = i,
        _ => break,
      }
    }
    loop {
      match map.get(hi) {
        Some(k) if k.1 == a => hi += 1,
        _ => break,
      }
    }
    let il = self.write_index(header, left, &map[..lo])?;
    let ir = self.write_index(header, &map[lo+1..hi], &map[hi..])?;
    self.write_index_entry(header, il, ir, map[lo])
  }

  /// Perform the actual export. If `index` is true, also output the
  /// (optional) debugging table to the file.
  ///
  /// This does not finalize all writes. [`finish`] should be called after this
  /// to write the outstanding fixups.
  pub fn run(&mut self, index: bool) -> io::Result<()> {
    self.write_all(&MM0B_MAGIC)?; // magic
    let num_sorts = self.env.sorts().len();
    assert!(num_sorts <= 128, "too many sorts (max 128)");
    self.write_all(&[MM0B_VERSION, num_sorts as u8, 0, 0])?; // two bytes reserved
    let num_terms = self.env.terms().len();
    self.write_u32(num_terms.try_into().unwrap())?; // num_terms
    let num_thms = self.env.thms().len();
    self.write_u32(num_thms.try_into().unwrap())?; // num_thms
    let p_terms = self.fixup32()?;
    let p_thms = self.fixup32()?;
    let p_proof = self.fixup64()?;
    let p_index = self.fixup64()?;

    // sort data
    self.write_all(&self.env.sorts().iter().map(|s| s.mods.bits()).collect::<Vec<u8>>())?;

    // term header
    self.align_to(8)?; p_terms.commit(self);
    let mut term_header = self.fixup_large(num_terms * 8)?;
    for (head, t) in term_header.chunks_exact_mut(8).zip(&self.env.terms().0) {
      Self::write_term_header(head,
        t.args.len().try_into().expect("term has more than 65536 args"),
        t.ret.0,
        t.val.is_some(),
        self.align_to(8)?.try_into().unwrap());
      self.write_binders(&t.args)?;
      self.write_sort_deps(false, t.ret.0, t.ret.1)?;
      let reorder = if let Some(val) = &t.val {
        let Expr {heap, head} = val.as_ref().unwrap_or_else(||
          panic!("def {} missing value", self.env.data()[t.atom].name()));
        let mut reorder = Reorder::new(
          t.args.len().try_into().unwrap(), heap.len(), |i| i);
        self.write_expr_unify(heap, &mut reorder, head, &mut vec![])?;
        self.write_u8(0)?;
        Some(reorder)
      } else { None };
      self.term_reord.push(reorder)
    }
    term_header.commit(self);

    // theorem header
    self.align_to(8)?; p_thms.commit(self);
    let mut thm_header = self.fixup_large(num_thms * 8)?;
    for (head, t) in thm_header.chunks_exact_mut(8).zip(&self.env.thms().0) {
      Self::write_thm_header(head,
        t.args.len().try_into().expect("theorem has more than 65536 args"),
        self.align_to(8)?.try_into().unwrap());
      self.write_binders(&t.args)?;
      let nargs = t.args.len().try_into().unwrap();
      let mut reorder = Reorder::new(nargs, t.heap.len(), |i| i);
      let save = &mut vec![];
      self.write_expr_unify(&t.heap, &mut reorder, &t.ret, save)?;
      for (_, h) in t.hyps.iter().rev() {
        UnifyCmd::Hyp.write_to(self)?;
        self.write_expr_unify(&t.heap, &mut reorder, h, save)?;
      }
      self.write_u8(0)?;
    }
    thm_header.commit(self);

    // main body (proofs of theorems)
    p_proof.commit(self);
    let vec = &mut vec![];
    let mut index_map = Vec::with_capacity(if index {num_sorts + num_terms + num_thms} else {0});
    for s in self.env.stmts() {
      match *s {
        StmtTrace::Sort(a) => {
          if index {index_map.push((true, a, self.pos))}
          write_cmd_bytes(self, STMT_SORT, &[])?
        }
        StmtTrace::Decl(a) => {
          if index {index_map.push((false, a, self.pos))}
          match self.env.data()[a].decl().unwrap() {
            DeclKey::Term(t) => {
              let td = self.env.term(t);
              match &td.val {
                None => write_cmd_bytes(self, STMT_TERM, &[])?,
                Some(None) => panic!("def {} missing definition", self.env.data()[td.atom].name()),
                Some(Some(Expr {heap, head})) => {
                  let mut reorder = Reorder::new(
                    td.args.len().try_into().unwrap(), heap.len(), |i| i);
                  write_expr_proof(vec, heap, &mut reorder, head, false)?;
                  vec.write_u8(0)?;
                  let cmd = STMT_DEF | if td.vis == Modifiers::LOCAL {STMT_LOCAL} else {0};
                  write_cmd_bytes(self, cmd, vec)?;
                  vec.clear();
                }
              }
            }
            DeclKey::Thm(t) => {
              let td = self.env.thm(t);
              let cmd = match &td.proof {
                None => {
                  let mut reorder = Reorder::new(
                    td.args.len().try_into().unwrap(), td.heap.len(), |i| i);
                  for (_, h) in &*td.hyps {
                    write_expr_proof(vec, &td.heap, &mut reorder, h, false)?;
                    ProofCmd::Hyp.write_to(vec)?;
                  }
                  write_expr_proof(vec, &td.heap, &mut reorder, &td.ret, false)?;
                  STMT_AXIOM
                }
                Some(None) => panic!("proof {} missing", self.env.data()[td.atom].name()),
                Some(Some(Proof {heap, hyps, head})) => {
                  let mut reorder = Reorder::new(
                    td.args.len().try_into().unwrap(), heap.len(), |i| i);
                  let mut ehyps = Vec::with_capacity(hyps.len());
                  for h in &**hyps {
                    let e = match h.deref(heap) {
                      ProofNode::Hyp(_, ref e) => &**e,
                      _ => unreachable!()
                    };
                    self.write_proof(vec, heap, &mut reorder, &ehyps, e, false)?;
                    ProofCmd::Hyp.write_to(vec)?;
                    ehyps.push(reorder.idx);
                    reorder.idx += 1;
                  }
                  self.write_proof(vec, &heap, &mut reorder, &ehyps, head, false)?;
                  STMT_THM | if td.vis == Modifiers::PUB {0} else {STMT_LOCAL}
                }
              };
              vec.write_u8(0)?;
              write_cmd_bytes(self, cmd, vec)?;
              vec.clear();
            }
          }
        }
        StmtTrace::Global(_) |
        StmtTrace::OutputString(_) => {}
      }
    }
    self.write_u8(0)?;

    // debugging index
    if index {
      self.align_to(8)?; p_index.commit(self);
      index_map.sort_unstable_by_key(|k| &**self.env.data()[k.1].name());
      let size = 1 + num_sorts + num_terms + num_thms;
      let mut index_header = self.fixup_large(8 * size)?;
      // Safety: index_header points to a Box<[u8; 8*size]>, and we reinterpret it as [[u8; 8]; size]
      let header = unsafe {
        std::slice::from_raw_parts_mut(index_header.as_mut_ptr() as *mut [u8; 8], size)
      };
      let (root, header) = header.split_first_mut().unwrap();
      let (sorts, header) = header.split_at_mut(num_sorts);
      let (terms, thms) = header.split_at_mut(num_terms);
      LE::write_u64(root, self.write_index(&mut IndexHeader {sorts, terms, thms}, &[], &index_map)?);
      index_header.commit(self)
    } else {
      p_index.cancel();
      self.write_u32(0)?; // padding
    }
    Ok(())
  }

  /// Finalize the outstanding fixups, and flush the writer. Consumes self since we're done.
  pub fn finish(self) -> io::Result<()> {
    let Self {mut w, fixups, ..} = self;
    for (pos, f) in fixups {
      w.seek(SeekFrom::Start(pos))?;
      match f {
        Value::U32(n) => w.write_u32::<LE>(n)?,
        Value::U64(n) => w.write_u64::<LE>(n)?,
        Value::Box(buf) => w.write_all(&buf)?,
      }
    }
    w.flush()
  }
}