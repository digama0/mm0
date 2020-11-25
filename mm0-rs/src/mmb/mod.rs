//! Import and export functionality for MMB binary proof format
//!
//! See [`mm0-c/verifier.c`] for information on the MMB format.
//!
//! [`mm0-c/verifier.c`]: https://github.com/digama0/mm0/blob/master/mm0-c/verifier.c
use std::convert::TryFrom;

use crate::elab::environment::{SortID, TermID, ThmID, Modifiers};
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
  pub const DATA_8: u8    = 0x40;
  /// `DATA_16 = 0x80`, used as a command mask for a 16 bit data field
  pub const DATA_16: u8   = 0x80;
  /// `DATA_32 = 0xC0`, used as a command mask for a 32 bit data field
  pub const DATA_32: u8   = 0xC0;
  /// `DATA_MASK = 0xC0`, selects one of `DATA_8`, `DATA_16`, or `DATA_32` for data size
  pub const DATA_MASK: u8 = 0xC0;

  /// `STMT_AXIOM = 0x02`, starts an `axiom` declaration
  pub const STMT_AXIOM: u8 = 0x02;
  /// `STMT_SORT = 0x04`, starts a `sort` declaration
  pub const STMT_SORT: u8  = 0x04;
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
  /// `STMT_LOCAL_DEF = 0x0D`
  pub const STMT_LOCAL_DEF: u8 = STMT_LOCAL | STMT_DEF;
  /// `STMT_LOCAL_THM = 0x0E`
  pub const STMT_LOCAL_THM: u8 = STMT_LOCAL | STMT_THM;

  /// `INDEX_KIND_TERM = 0x01`, starts a `term` declaration
  pub const INDEX_KIND_TERM: u8  = 0x01;
  /// `INDEX_KIND_AXIOM = 0x02`, starts an `axiom` declaration
  pub const INDEX_KIND_AXIOM: u8 = 0x02;
  /// `INDEX_KIND_VAR = 0x03`, starts a `local` declaration
  /// (a bit mask to be combined with `INDEX_KIND_THM` or `INDEX_KIND_DEF`)
  pub const INDEX_KIND_VAR: u8   = 0x03;
  /// `INDEX_KIND_SORT = 0x04`, starts a `sort` declaration
  pub const INDEX_KIND_SORT: u8  = 0x04;
  /// `INDEX_KIND_DEF = 0x05`, starts a `def` declaration. (This is the same as
  /// `INDEX_KIND_TERM` because the actual indication of whether this is a
  /// def is in the term header)
  pub const INDEX_KIND_DEF: u8   = 0x05;
  /// `INDEX_KIND_THM = 0x06`, starts a `theorem` declaration
  pub const INDEX_KIND_THM: u8   = 0x06;
  /// `INDEX_KIND_LOCAL_DEF = 0x0D`
  pub const INDEX_KIND_LOCAL_DEF: u8 = STMT_LOCAL_DEF;
  /// `INDEX_KIND_LOCAL_THM = 0x0E`
  pub const INDEX_KIND_LOCAL_THM: u8 = STMT_LOCAL_THM;

  /// `PROOF_TERM = 0x10`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_TERM: u8      = 0x10;
  /// `PROOF_TERM_SAVE = 0x11`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_TERM_SAVE: u8 = 0x11;
  /// `PROOF_REF = 0x12`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_REF: u8       = 0x12;
  /// `PROOF_DUMMY = 0x13`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_DUMMY: u8     = 0x13;
  /// `PROOF_THM = 0x14`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_THM: u8       = 0x14;
  /// `PROOF_THM_SAVE = 0x15`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_THM_SAVE: u8  = 0x15;
  /// `PROOF_HYP = 0x16`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_HYP: u8       = 0x16;
  /// `PROOF_CONV = 0x17`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_CONV: u8      = 0x17;
  /// `PROOF_REFL = 0x18`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_REFL: u8      = 0x18;
  /// `PROOF_SYMM = 0x19`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_SYMM: u8      = 0x19;
  /// `PROOF_CONG = 0x1A`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_CONG: u8      = 0x1A;
  /// `PROOF_UNFOLD = 0x1B`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_UNFOLD: u8    = 0x1B;
  /// `PROOF_CONV_CUT = 0x1C`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_CONV_CUT: u8  = 0x1C;
  /// `PROOF_CONV_REF = 0x1D`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_CONV_REF: u8  = 0x1D;
  /// `PROOF_CONV_SAVE = 0x1E`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_CONV_SAVE: u8 = 0x1E;
  /// `PROOF_SAVE = 0x1F`: See [`ProofCmd`](super::ProofCmd).
  pub const PROOF_SAVE: u8      = 0x1F;

  /// `UNIFY_TERM = 0x30`: See [`UnifyCmd`](super::UnifyCmd).
  pub const UNIFY_TERM: u8      = 0x30;
  /// `UNIFY_TERM_SAVE = 0x31`: See [`UnifyCmd`](super::UnifyCmd).
  pub const UNIFY_TERM_SAVE: u8 = 0x31;
  /// `UNIFY_REF = 0x32`: See [`UnifyCmd`](super::UnifyCmd).
  pub const UNIFY_REF: u8       = 0x32;
  /// `UNIFY_DUMMY = 0x33`: See [`UnifyCmd`](super::UnifyCmd).
  pub const UNIFY_DUMMY: u8     = 0x33;
  /// `UNIFY_HYP = 0x36`: See [`UnifyCmd`](super::UnifyCmd).
  pub const UNIFY_HYP: u8       = 0x36;
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
  TermDef {/** Is this `local def`? */ local: bool},
  /// A new theorem. Equivalent to `(pub) theorem foo ...`, where `local` means
  /// that the theorem is not `pub`. This is followed by a proof sequence,
  /// that will construct the statement and proof, and should unify
  /// with the unify sequence in the header.
  Thm {/** Is this not `pub theorem`? */ local: bool}
}

impl std::convert::TryFrom<u8> for StmtCmd {
  type Error = ();
  fn try_from(cmd: u8) -> Result<Self, ()> {
    Ok(match cmd {
      cmd::STMT_SORT => StmtCmd::Sort,
      cmd::STMT_AXIOM => StmtCmd::Axiom,
      cmd::STMT_DEF => StmtCmd::TermDef {local: false},
      cmd::STMT_LOCAL_DEF => StmtCmd::TermDef {local: true},
      cmd::STMT_THM => StmtCmd::Thm {local: false},
      cmd::STMT_LOCAL_THM => StmtCmd::Thm {local: true},
      _ => return Err(())
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
    /** The term to construct */              tid: TermID,
    /** True if we should save to the heap */ save: bool,
  },
  /// ```text
  /// Ref i: H; S --> H; S, Hi
  /// ```
  /// Get the `i`-th heap element and push it on the stack.
  Ref(u32),
  /// ```text
  /// Dummy s: H; S --> H, x; S, x    alloc(x:s)
  /// ```
  /// Allocate a new variable `x` of sort `s`, and push it to the stack and the heap.
  Dummy(SortID),
  /// ```text
  /// Thm T: H; S, e1, ..., en, e --> H; S', |- e
  ///   (where Unify(T): S; e1, ... en; e --> S'; H'; .)
  /// Save: H; S, |- e --> H, |- e; S, |- e
  /// ```
  /// Pop `n` elements from the stack and put them on the unify heap, then call the
  /// unifier for `T` with `e` as the target. The unifier will pop additional
  /// proofs from the stack if the UHyp command is used, and when it is done,
  /// the conclusion is pushed as a proven statement.
  ///
  /// When Save is used, the proven statement is also saved to the heap.
  Thm {
    /** The theorem to apply */               tid: ThmID,
    /** True if we should save to the heap */ save: bool,
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
  /// Unfold: S, (t e1 ... en) =?= e', (t e1 ... en), e --> S, e =?= e'
  ///   (where Unify(t): e1, ..., en; e --> H'; .)
  /// ```
  /// Pop terms `(t e1 ... en)`, `e` from the stack and run the unifier for `t`
  /// (which should be a definition) to make sure that `(t e1 ... en)` unfolds to `e`.
  /// Then pop `(t e1 ... en) =?= e'` and push `e =?= e'`.
  Unfold,
  /// ```text
  /// ConvCut: S, e1 =?= e2 --> S, e1 = e2, e1 =?= e2
  /// ```
  /// Pop a convertibility obligation `e1 =?= e2`, and
  /// push a convertability assertion `e1 = e2` guarded by `e1 =?= e2`.
  ConvCut,
  /// ```text
  /// ConvRef i: H; S, e1 =?= e2 --> H; S   (where Hi is e1 = e2)
  /// ```
  /// Pop a convertibility obligation `e1 =?= e2`, where `e1 = e2` is
  /// `i`-th on the heap.
  ConvRef(u32),
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
/// * `H: Vec<Expr>: The unify heap, also known as the substitution. This is
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
    /** The term that should be at the head */                   tid: TermID,
    /** True if we want to recall this substitution for later */ save: bool,
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
  Dummy(SortID),
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

/// The header of an MMB file, which is always in the first bytes of the file.
/// It is followed by a `sorts: [`[`SortData`]`; num_sorts]` array
/// (which we keep separate because of the dependency).
#[repr(C)]
#[derive(Debug, Clone, Copy, FromBytes, Unaligned)]
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
  /// The pointer to the term table of type `[`[`TermEntry`]`; num_terms]`.
  pub p_terms: U32<LE>,
  /// The pointer to the theorem table of type `[`[`ThmEntry`]`; num_thms]`.
  pub p_thms: U32<LE>,
  /// The pointer to the declaration stream.
  pub p_proof: U32<LE>,
  /// Padding.
  pub reserved2: [u8; 4],
  /// The pointer to the index header, an array of `1 + num_sorts + num_terms + num_thms`
  /// pointers to [`IndexEntry`] nodes.
  pub p_index: U64<LE>,
}

/// A sort entry in the file header. Each sort is one byte, which can be any combination
/// of the modifiers in [`Modifiers::sort_data`]: [`PURE`](Modifiers::PURE),
/// [`STRICT`](Modifiers::STRICT), [`PROVABLE`](Modifiers::PROVABLE), [`FREE`](Modifiers::FREE).
#[repr(C)]
#[derive(Debug, Clone, Copy, FromBytes, Unaligned)]
pub struct SortData(pub u8);

impl TryFrom<SortData> for Modifiers {
  type Error = ();
  fn try_from(s: SortData) -> Result<Modifiers, ()> {
    let m = Modifiers::new(s.0);
    if Modifiers::sort_data().contains(m) {Ok(m)} else {Err(())}
  }
}

/// An argument binder in a term/def or axiom/theorem.
/// * Bit 63 (the high bit of the high byte) is 1 if this is a bound variable.
/// * Bits 56-62 (the low 7 bits of the high byte) give the sort of the variable.
/// * Bits 0-55 (the low 7 bytes) are a bitset giving the set of bound variables
///   earlier in the list that this variable is allowed to depend on.
#[repr(C)]
#[derive(Debug, Clone, Copy, FromBytes, Unaligned)]
pub struct Arg(pub U64<LE>);

/// An entry in the term table, which describes the "signature" of the term/def,
/// the information needed to apply the term and use it in theorems.
#[repr(C, align(8))]
#[derive(Debug, Clone, Copy, FromBytes)]
pub struct TermEntry {
  /// The number of arguments to the term.
  pub num_args: U16<LE>,
  /// The high bit is set if this is a `def`. The low 7 bits give the
  /// return sort of the term.
  pub sort: u8,
  /// Padding.
  pub reserved: u8,
  /// The pointer to an `args: [`[`Arg`]`; num_args + 1]` array, followed by the
  /// term's unify command sequence. `args[num_args]` is the return type and dependencies,
  /// and `args[..num_args]` are the actual arguments.
  pub p_args: U32<LE>,
}

/// An entry in the term table, which describes the "signature" of the axiom/theorem,
/// the information needed to apply the theorem to use it in other theorems.
#[repr(C, align(4))]
#[derive(Debug, Clone, Copy, FromBytes)]
pub struct ThmEntry {
  /// The number of arguments to the theorem (exprs, not hyps).
  pub num_args: U16<LE>,
  /// Padding.
  pub reserved: [u8; 2],
  /// The pointer to an `args: [`[`Arg`]`; num_args]` array, followed by the
  /// theorem's unify command sequence.
  pub p_args: U32<LE>,
}

/// The kinds of entity that can appear in the index. This is similar to [`StmtCmd`],
/// but it distinguishes `term` and `def` and adds the [`Var`](Self::Var) constructor.
#[derive(Debug, Clone, Copy)]
pub enum IndexKind {
  /// This is a `sort`.
  Sort,
  /// This is an `axiom`.
  Axiom,
  /// This is an `term`.
  Term,
  /// This is a variable name,
  Var,
  /// This is a `(local) def`.
  Def {/** Is this `local def`? */ local: bool},
  /// This is a `(!pub) theorem`.
  Thm {/** Is this not `pub theorem`? */ local: bool}
}

impl std::convert::TryFrom<u8> for IndexKind {
  type Error = ();
  fn try_from(cmd: u8) -> Result<Self, ()> {
    Ok(match cmd {
      cmd::INDEX_KIND_TERM => IndexKind::Term,
      cmd::INDEX_KIND_AXIOM => IndexKind::Axiom,
      cmd::INDEX_KIND_VAR => IndexKind::Var,
      cmd::INDEX_KIND_SORT => IndexKind::Sort,
      cmd::INDEX_KIND_DEF => IndexKind::Def {local: false},
      cmd::INDEX_KIND_THM => IndexKind::Thm {local: false},
      cmd::INDEX_KIND_LOCAL_DEF => IndexKind::Def {local: true},
      cmd::INDEX_KIND_LOCAL_THM => IndexKind::Thm {local: true},
      _ => return Err(())
    })
  }
}

/// An individual entry in the index,
/// which is hooked up in a binary tree structure.
/// It is followed by a `CStr` (unsized) containing the entity's name.
#[repr(C)]
#[derive(Debug, Clone, Copy, FromBytes, Unaligned)]
pub struct IndexEntry {
  /// A pointer to the left child in the binary search tree, ordered by name.
  pub p_left: U64<LE>,
  /// A pointer to the right child in the binary search tree, ordered by name.
  pub p_right: U64<LE>,
  /// The line in the source file that introduced this entity.
  pub row: U32<LE>,
  /// The character in the source file that introduced this entity.
  pub col: U32<LE>,
  /// A pointer to the location in the proof stream which introduced this entity.
  pub p_proof: U64<LE>,
  /// The index ([`SortID`], [`TermID`], or [`ThmID`] or variable index) of the entity.
  pub ix: U32<LE>,
  /// The index entry kind as a [`IndexKind`].
  pub kind: u8,
}