#[allow(clippy::wildcard_imports)]
use crate::cmd::*;
use crate::{
  Arg, HasSymbolNames, Header, MmbFile, NameEntryRef, ProofCmd, SortData, TableEntry, TermEntry,
  ThmEntry, UnifyCmd,
};
use byteorder::{WriteBytesExt, LE};
use mm0_util::{u32_as_usize, SortId, SortVec, TermId, TermVec, ThmId, ThmVec};
use std::io::{self, Cursor, Read, Write};
use zerocopy::{AsBytes, U32};

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
pub fn write_cmd(w: &mut impl Write, cmd: u8, data: u32) -> io::Result<()> {
  if data == 0 {
    w.write_u8(cmd)
  } else if let Ok(data) = u8::try_from(data) {
    w.write_u8(cmd | DATA_8)?;
    w.write_u8(data)
  } else if let Ok(data) = u16::try_from(data) {
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
  } else if let Ok(data) = (buf.len() + 3).try_into() {
    w.write_u8(cmd | DATA_16)?;
    w.write_u16::<LE>(data)?;
  } else {
    w.write_u8(cmd | DATA_32)?;
    w.write_u32::<LE>((buf.len() + 5).try_into().expect("too large for format"))?;
  }
  w.write_all(buf)
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
      ProofCmd::ConvSave => w.write_u8(PROOF_CONV_SAVE),
      ProofCmd::Save => w.write_u8(PROOF_SAVE),
      ProofCmd::Sorry => w.write_u8(PROOF_SORRY),
    }
  }
}

/// An implementation of `Reopen` is a writer that can be closed and reopened to read what was just
/// written.
pub trait Reopen: Write {
  /// The type returned by `reopen`, which must implement `Read`.
  type Reopened: Read;
  /// Consume this writer and reopen it as another type `Self::Reopened`, which supports reading to
  /// read what was just written.
  fn reopen(self) -> io::Result<Self::Reopened>;
}

impl Reopen for Vec<u8> {
  type Reopened = Cursor<Self>;
  fn reopen(self) -> io::Result<Self::Reopened> { Ok(Cursor::new(self)) }
}

#[derive(Debug)]
struct TrackSize<W>(W, usize);

impl<W: Write> Write for TrackSize<W> {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    let n = self.0.write(buf)?;
    self.1 += n;
    Ok(n)
  }

  fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
    self.0.write_all(buf)?;
    self.1 += buf.len();
    Ok(())
  }

  fn flush(&mut self) -> io::Result<()> { self.0.flush() }
}

/// An `Mm0Writer` is a buffer for constructing an MMB file when the total number of
/// sorts/terms/theorems is not yet known. It renders as much of the file as it can, so that the
/// actual file write consists mostly of `memcpy`s.
///
/// The proof stream is handled separately, since it is much larger than the other parts.
/// The provided writer `W` must implement the `Reopen` trait, which allows it to be written to and
/// then reopened and read back into the target file.
#[derive(Debug)]
#[must_use = "dropping an Mm0Writer will not produce an MMB file"]
pub struct Mm0Writer<W> {
  sorts: SortVec<SortData>,
  terms: TermVec<TermEntry>,
  thms: ThmVec<ThmEntry>,
  term_thm_buf: Vec<u8>,
  proof: TrackSize<W>,
  names_buf: Vec<u8>,
  sort_names: SortVec<(usize, usize)>,
  term_names: TermVec<(usize, usize)>,
  thm_names: ThmVec<(usize, usize)>,
}

fn push_name(buf: &mut Vec<u8>, name: Option<&str>) -> usize {
  if let Some(name) = name {
    let n = buf.len();
    let s = name.as_bytes();
    assert!(memchr::memchr(0, s).is_none());
    buf.extend_from_slice(s);
    buf.push(0);
    n
  } else {
    usize::MAX
  }
}

fn pad_to(pos: usize, n: u8) -> (usize, usize) {
  #[allow(clippy::cast_possible_truncation)] // actual truncation
  let i = (n.wrapping_sub(pos as u8) & (n - 1)).into();
  (i, pos + i)
}

impl<W: Reopen> Mm0Writer<W> {
  /// Create a new empty `Mm0Writer`. Takes as input a writer for the proof component
  /// (which is typically larger than the other components, and can be set to a temporary file or
  /// an in-memory buffer).
  pub fn new(proof: W) -> Mm0Writer<W> {
    Mm0Writer {
      sorts: Default::default(),
      terms: Default::default(),
      thms: Default::default(),
      term_thm_buf: Default::default(),
      proof: TrackSize(proof, 0),
      names_buf: Default::default(),
      sort_names: Default::default(),
      term_names: Default::default(),
      thm_names: Default::default(),
    }
  }

  /// Initialize an MMB writer with the entire contents of another MMB file.
  /// Requires that the writer is newly initialized, i.e. has no sorts/terms/thms declared yet.
  /// Performs only limited checks on the input file, i.e. a malformed input will cause this writer
  /// to produce a malformed output or possibly panic.
  pub fn init<'a, X: HasSymbolNames<'a>>(&mut self, mmb: &MmbFile<'a, X>) -> io::Result<()> {
    assert!(self.sorts.is_empty() && self.terms.is_empty() && self.thms.is_empty());
    self.sorts.extend_from_slice(mmb.sorts);
    self.terms.extend_from_slice(mmb.terms);
    self.thms.extend_from_slice(mmb.thms);
    let off = u64::from(mmb.header.p_proof.get());
    let push_entry = move |buf: &mut Vec<u8>, entry: Option<NameEntryRef<'_>>| {
      if let Some(entry) = entry {
        let n = buf.len();
        let zero = memchr::memchr(0, entry.value).expect("missing end");
        buf.extend_from_slice(&entry.value[..=zero]);
        ((entry.p_proof.get() - off).try_into().expect("overflow"), n)
      } else {
        (usize::MAX, usize::MAX)
      }
    };
    for (id, _) in self.sorts.enum_iter() {
      self.sort_names.push(push_entry(&mut self.names_buf, mmb.sort_index(id)));
    }
    for (id, t) in self.terms.enum_iter_mut() {
      let start = u32_as_usize(t.p_args.get());
      let end = mmb.term(id).expect("impossible").unify().after_end().expect("parse error");
      t.p_args.set(self.term_thm_buf.len().try_into().expect("overflow"));
      self.term_thm_buf.extend_from_slice(&mmb.buf[start..end]);
      self.term_names.push(push_entry(&mut self.names_buf, mmb.term_index(id)));
    }
    for (id, t) in self.thms.enum_iter_mut() {
      let start = u32_as_usize(t.p_args.get());
      let end = mmb.thm(id).expect("impossible").unify().after_end().expect("parse error");
      t.p_args.set(self.term_thm_buf.len().try_into().expect("overflow"));
      self.term_thm_buf.extend_from_slice(&mmb.buf[start..end]);
      self.thm_names.push(push_entry(&mut self.names_buf, mmb.thm_index(id)));
    }
    let start = u32_as_usize(mmb.header.p_proof.get());
    let end = mmb.proof().after_end().expect("parse error");
    self.proof.write_all(&mmb.buf[start..end])
  }

  fn add_term_core(&mut self, name: Option<&str>, sort_def: u8, args: &[Arg], ret: Arg) -> TermId {
    let n = self.terms.push(TermEntry {
      num_args: args.len().try_into().expect("overflow"),
      sort: sort_def,
      reserved: 0,
      p_args: U32::new(self.term_thm_buf.len().try_into().expect("overflow")),
    });
    self.term_names.push((self.proof.1, push_name(&mut self.names_buf, name)));
    self.term_thm_buf.extend_from_slice(args.as_bytes());
    self.term_thm_buf.extend_from_slice(ret.as_bytes());
    n
  }

  /// Add a new sort with the given name and sort modifiers. Returns the ID of the new sort.
  pub fn add_sort(&mut self, name: Option<&str>, data: SortData) -> SortId {
    let n = self.sorts.push(data);
    self.sort_names.push((self.proof.1, push_name(&mut self.names_buf, name)));
    n
  }

  /// Add a new term with the given name and arguments. Returns the ID of the new term.
  pub fn add_term(&mut self, name: Option<&str>, args: &[Arg], ret: Arg) -> io::Result<TermId> {
    let n = self.add_term_core(name, ret.sort().0, args, ret);
    write_cmd_bytes(&mut self.proof, STMT_TERM, &[])?;
    Ok(n)
  }

  /// Begin construction of a new def with the given name and arguments.
  /// The returned `DefBuilder` contains references to the unify and proof streams, where the
  /// value of the definition should be inserted.
  pub fn add_def(
    &mut self, local: bool, name: Option<&str>, args: &[Arg], ret: Arg,
  ) -> DefBuilder<'_, W> {
    let n = self.add_term_core(name, ret.sort().0 | 1 << 7, args, ret);
    DefBuilder(StmtBuilder::new(self, if local { STMT_LOCAL_DEF } else { STMT_DEF }), n)
  }

  /// Begin construction of a new theorem or axiom with the given name and arguments.
  /// The returned `ThmBuilder` contains references to the unify and proof streams, where the
  /// statement and proof of the theorem should be inserted.
  fn add_thm_core(&mut self, cmd: u8, name: Option<&str>, args: &[Arg]) -> ThmBuilder<'_, W> {
    let n = self.thms.push(ThmEntry {
      num_args: args.len().try_into().expect("overflow"),
      reserved: [0; 2],
      p_args: U32::new(self.term_thm_buf.len().try_into().expect("overflow")),
    });
    self.term_names.push((self.proof.1, push_name(&mut self.names_buf, name)));
    self.term_thm_buf.extend_from_slice(args.as_bytes());
    ThmBuilder(StmtBuilder::new(self, cmd), n)
  }

  /// Begin construction of a new axiom with the given name and arguments.
  /// The returned `ThmBuilder` contains references to the unify and proof streams, where the
  /// statement of the axiom should be inserted.
  pub fn add_axiom(&mut self, name: Option<&str>, args: &[Arg]) -> ThmBuilder<'_, W> {
    self.add_thm_core(STMT_AXIOM, name, args)
  }

  /// Begin construction of a new theorem with the given name and arguments.
  /// The returned `ThmBuilder` contains references to the unify and proof streams, where the
  /// statement and proof of the theorem should be inserted.
  pub fn add_thm(&mut self, local: bool, name: Option<&str>, args: &[Arg]) -> ThmBuilder<'_, W> {
    self.add_thm_core(if local { STMT_LOCAL_THM } else { STMT_THM }, name, args)
  }

  /// This function consumes the `Mm0Writer` instance and actually writes the MMB data to the given
  /// writer, given a function `reopen` which reads the data just written to `proof`.
  pub fn finish(self, w: &mut impl Write) -> io::Result<()> {
    use std::mem::size_of;
    let Mm0Writer {
      sorts,
      mut terms,
      mut thms,
      term_thm_buf,
      mut proof,
      names_buf,
      sort_names,
      term_names,
      thm_names,
    } = self;
    proof.write_u8(0)?;
    let (mut proof, proof_size) = (proof.0.reopen()?, proof.1);
    let num_sorts = sorts.len();
    assert!(num_sorts <= 128, "too many sorts (max 128)");
    let num_terms = terms.len();
    let num_thms = thms.len();
    let (pad1, p_terms) = pad_to(size_of::<Header>() + num_sorts * size_of::<SortData>(), 8);
    let p_thms = p_terms + num_terms * size_of::<TermEntry>();
    let p_term_thm_buf = p_thms + num_thms * size_of::<ThmEntry>();
    let p_proof = p_term_thm_buf + term_thm_buf.len();
    let (pad2, p_index) = pad_to(p_proof + proof_size, 8);
    let p_proof = p_proof.try_into().expect("term section overflow");

    // adjust offsets
    for t in &mut terms.0 {
      #[allow(clippy::cast_possible_truncation)] // impossible because of previous check
      t.p_args.set(t.p_args.get() + p_term_thm_buf as u32)
    }
    for t in &mut thms.0 {
      #[allow(clippy::cast_possible_truncation)] // impossible because of previous check
      t.p_args.set(t.p_args.get() + p_term_thm_buf as u32)
    }

    // header
    w.write_all(&MM0B_MAGIC)?; // magic
    #[allow(clippy::cast_possible_truncation)] // impossible
    w.write_all(&[MM0B_VERSION, num_sorts as u8, 0, 0])?; // two bytes reserved
    w.write_u32::<LE>(num_terms.try_into().expect("too many terms"))?; // num_terms
    w.write_u32::<LE>(num_thms.try_into().expect("too many thms"))?; // num_thms
    #[allow(clippy::cast_possible_truncation)] // impossible
    w.write_u32::<LE>(p_terms as u32)?;
    w.write_u32::<LE>(p_thms.try_into().expect("too many terms"))?;
    w.write_u32::<LE>(p_proof)?;
    w.write_u32::<LE>(0)?;
    w.write_u64::<LE>(p_index.try_into().expect("overflow"))?;

    w.write_all(sorts.as_bytes())?; // sort data
    w.write_all(&vec![0; pad1])?; // term header padding
    w.write_all(terms.as_bytes())?; // term header
    w.write_all(thms.as_bytes())?; // theorem header
    w.write_all(&term_thm_buf)?; // term/theorem data
    io::copy(&mut proof, w)?; // proof stream

    let num_entries = 1;
    let p_names_buf = p_index + 8 + num_entries * size_of::<TableEntry>();
    let p_names = p_names_buf + names_buf.len();
    let p_names_buf: u64 = p_names_buf.try_into().expect("overflow");
    let index = [(INDEX_NAME, p_names)];
    assert_eq!(index.len(), num_entries);
    w.write_all(&vec![0; pad2])?; // index padding
    w.write_u64::<LE>(num_entries.try_into().expect("overflow"))?; // index size
    for (ty, p) in index {
      w.write_all(&ty)?; // type
      w.write_u32::<LE>(0)?; // data (padding, unused)
      w.write_u64::<LE>(p.try_into().expect("overflow"))?; // ptr
    }

    w.write_all(&names_buf)?; // name string data
    let p_proof = u64::from(p_proof);
    let mut write = |vec| -> io::Result<()> {
      let offset = |off, i| match i {
        usize::MAX => 0,
        _ => off + u64::try_from(i).expect("overflow"),
      };
      for (decl, name) in vec {
        w.write_u64::<LE>(offset(p_proof, decl))?;
        w.write_u64::<LE>(offset(p_names_buf, name))?;
      }
      Ok(())
    };
    write(sort_names.0)?; // sort name data
    write(term_names.0)?; // term name data
    write(thm_names.0)?; // thm name data
    Ok(())
  }
}

#[derive(Debug)]
#[must_use]
struct StmtBuilder<'a, W> {
  w: &'a mut Mm0Writer<W>,
  cmd: u8,
  buf: Vec<u8>,
}

impl<'a, W: Reopen> StmtBuilder<'a, W> {
  fn new(w: &'a mut Mm0Writer<W>, cmd: u8) -> Self { Self { w, cmd, buf: vec![] } }
  fn unify(&mut self) -> &mut impl Write { &mut self.w.term_thm_buf }
  fn proof(&mut self) -> &mut impl Write { &mut self.buf }
  fn finish(self) -> io::Result<()> { write_cmd_bytes(&mut self.w.proof, self.cmd, &self.buf) }
}

/// An unfinished definition. The `unify` and `proof` streams should be used to write unify and
/// proof commands, respectively, and when completed the `finish` function will finalize the
/// streams and return the `TermId` of the new definition.
#[derive(Debug)]
#[must_use = "discarding a DefBuilder will result in a corrupted file"]
pub struct DefBuilder<'a, W>(StmtBuilder<'a, W>, TermId);

impl<'a, W: Reopen> DefBuilder<'a, W> {
  /// A reference to the unify stream for this definition. Use [`UnifyCmd::write_to`] to add
  /// commands to this stream. Do not add an `END` command at the end; [`finish`] will handle that.
  pub fn unify(&mut self) -> &mut (impl Write + 'a) { self.0.unify() }

  /// A reference to the proof stream for this definition. Use [`ProofCmd::write_to`] to add
  /// commands to this stream. Do not add an `END` command at the end; [`finish`] will handle that.
  pub fn proof(&mut self) -> &mut (impl Write + 'a) { self.0.proof() }

  /// Finish the unify and proof streams for this definition, and finalize the term addition.
  /// Returns the ID of the newly created term.
  pub fn finish(mut self) -> io::Result<TermId> {
    self.unify().write_u8(0)?;
    self.proof().write_u8(0)?;
    self.0.finish()?;
    Ok(self.1)
  }
}

/// An unfinished axiom or theorem. The `unify` and `proof` streams should be used to write unify
/// and proof commands, respectively, and when completed the `finish` function will finalize the
/// streams and return the `ThmId` of the new theorem.
#[derive(Debug)]
#[must_use = "discarding a ThmBuilder will result in a corrupted file"]
pub struct ThmBuilder<'a, W>(StmtBuilder<'a, W>, ThmId);

impl<'a, W: Reopen> ThmBuilder<'a, W> {
  /// A reference to the unify stream for this theorem. Use [`UnifyCmd::write_to`] to add
  /// commands to this stream. Do not add an `END` command at the end; [`finish`] will handle that.
  pub fn unify(&mut self) -> &mut (impl Write + 'a) { self.0.unify() }

  /// A reference to the proof stream for this theorem. Use [`ProofCmd::write_to`] to add
  /// commands to this stream. Do not add an `END` command at the end; [`finish`] will handle that.
  pub fn proof(&mut self) -> &mut (impl Write + 'a) { self.0.proof() }

  /// Finish the unify and proof streams for this theorem, and finalize the theorem addition.
  /// Returns the ID of the newly created theorem.
  pub fn finish(mut self) -> io::Result<ThmId> {
    self.unify().write_u8(0)?;
    self.proof().write_u8(0)?;
    self.0.finish()?;
    Ok(self.1)
  }
}
