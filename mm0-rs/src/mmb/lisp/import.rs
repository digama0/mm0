//! Importer for the `Lisp` index table: reconstructs the global lisp environment
//! from the value stream described in `mm0-rs/mmb-lisp.md`.
//!
//! The reader is fully iterative: [`read_value`](Reader::read_value) drives a single
//! explicit work stack of [`Frame`]s and never recurses. The stack top selects the
//! parse mode for the next token — an [`IrBody`](Frame::IrBody) means the next token is
//! an `Ir` instruction, anything else means a `value` — so the interleaved value/`Ir`
//! grammar (a lambda's code holds `Ir::Const` values, which may hold more lambdas, and
//! so on) is read in that one loop. Values and code therefore nest to any depth on the
//! heap-allocated stack, and no input, however deep, can overflow the machine stack.

use std::cell::Cell;
use std::collections::HashMap;
use std::path::Path;
use std::rc::Rc;
use std::sync::Arc;

use num::{BigInt, FromPrimitive};

use crate::elab::environment::{Environment, LispData, StmtTrace};
use crate::elab::lisp::parser::{Ir, MVarPattern};
use crate::elab::lisp::{
  BuiltinProc, InferTarget, LispKind, LispVal, Proc, ProcPos, ProcSpec, Syntax};
use crate::DocComment;
use mm0_util::{ArcString, AtomId, FileRef, FileSpan, Span};
use mm0b_parser::{parse_cmd, BasicMmbFile, ParseError};

use super::{custom, infer, ir, op, pat_mvar, spec, LAMBDA_NAMED, VERSION};

/// Reconstruct the global lisp definitions from a `.mmb`'s `Lisp` table into `env`.
///
/// Returns `false` if the file has no such table. Span file paths are stored relative to
/// `base`, the `.mmb`'s directory, and localized back against it.
pub fn deserialize(
  env: &mut Environment, file: &BasicMmbFile<'_>, base: &Path
) -> Result<bool, ParseError> {
  let Some((version, ptr)) = find_lisp_table(file)? else { return Ok(false) };
  if version != VERSION {
    return Err(ParseError::StrError("unsupported Lisp table version", ptr))
  }
  Reader { env, buf: file.buf, pos: ptr, heap: Vec::new(), base }.read_globals()?;
  Ok(true)
}

/// Read a bare value stream (starting at offset 0) into `env`, as produced by
/// [`serialize`]. `deserialize` is this preceded by locating the table.
#[cfg(test)]
fn deserialize_stream(env: &mut Environment, buf: &[u8], base: &Path) -> Result<(), ParseError> {
  Reader { env, buf, pos: 0, heap: Vec::new(), base }.read_globals()
}

/// Find the `Lisp` [`index_entry`](../../../mm0-c/mmb.md), returning its
/// `(version, stream offset)`.
fn find_lisp_table(file: &BasicMmbFile<'_>) -> Result<Option<(u32, usize)>, ParseError> {
  let buf = file.buf;
  let Some(p_index) = file.p_index() else { return Ok(None) };
  let bad = || ParseError::StrError("malformed Lisp index", p_index);
  let word = |o: usize| buf.get(o..o + 8).and_then(|b| b.try_into().ok()).map(u64::from_le_bytes);
  let count = word(p_index).ok_or_else(bad)?;
  for i in 0..usize::try_from(count).unwrap_or(0) {
    let off = p_index + 8 + 16 * i;
    let id = buf.get(off..off + 4).ok_or_else(bad)?;
    if id == mm0b_parser::cmd::INDEX_LISP {
      let version = u32::from_le_bytes(buf[off + 4..off + 8].try_into().expect("checked"));
      let ptr = word(off + 8).ok_or_else(bad)?;
      return Ok(Some((version, usize::try_from(ptr).unwrap_or(usize::MAX))));
    }
  }
  Ok(None)
}

/// A completed sub-result flowing up the reader's work stack. Most are `value`-space
/// results (a `LispVal`, a span consumed by `Annot`/spans, or a lambda code core), and
/// those three are also what the heap `H` stores. The `Ir` case is the exception: a
/// finished instruction, which only ever flows into the enclosing [`Frame::IrBody`] and
/// never reaches the heap.
#[derive(Clone)]
enum RVal {
  Val(LispVal),
  Span(FileSpan),
  /// A lambda `(spec, body)` core, saved to the heap by `Code` and `Ref`d wherever it
  /// recurs. It is not a `value`, so it appears only in a lambda's code-field slot.
  Code(ProcSpec, Arc<[Ir]>),
  /// One finished `Ir` instruction, en route to its [`Frame::IrBody`].
  Ir(Ir),
}

impl RVal {
  fn val(self, pos: usize) -> Result<LispVal, ParseError> {
    match self {
      RVal::Val(v) => Ok(v),
      RVal::Span(_) => Err(ParseError::StrError("expected a value, found a span", pos)),
      RVal::Code(..) => Err(ParseError::StrError("expected a value, found a code core", pos)),
      RVal::Ir(_) => Err(ParseError::StrError("expected a value, found an Ir instruction", pos)),
    }
  }
}

/// A pending parent on the reader's single work stack. The stack top also selects the
/// parse mode for the next token: an [`IrBody`](Frame::IrBody) on top means the next
/// token is an `Ir` instruction, and any other frame (or the empty stack) means it is a
/// `value`. That one rule is what lets a single loop read the interleaved value/`Ir`
/// grammar with no native recursion at all — values and lambda code nest to any depth
/// on this heap-allocated stack, so a deep input cannot overflow the machine stack.
enum Frame {
  /// `List`/`ListSave`: values until `END` become a proper list. `bool` = save.
  List(bool, Vec<LispVal>),
  /// `DottedList`: values until `END`, the last being the tail.
  Dotted(bool, Vec<LispVal>),
  /// `Map`: key/value `value`s until `END`.
  Map(bool, Vec<LispVal>),
  /// `Save`: save the next value, then pass it through.
  Save,
  /// `NewRef`: fill the pre-installed cell at this heap index with the next value.
  NewRef(usize),
  /// `Span`: after `lo`/`hi`, read the file `value` and build the span.
  SpanFile(u32, u32),
  /// `Annot`: read the span `value`.
  AnnotSpan,
  /// `Annot`: span read, now read the annotated `value`.
  AnnotVal(FileSpan),
  /// `Goal`: read the goal's type `value`.
  Goal,
  /// `MVar` `Bound`/`Reg`: read the `sort` atom `value`.
  MVar(usize, bool),
  /// `CustomProc` `MergeMap`: read the sub-strategy `value`.
  MergeMapProc,
  /// `CustomProc` `ProofThunk`: read the name atom `value`.
  ProofThunkProc,
  /// `Lambda` stage 1: gather the environment
  LamEnv(Box<Lam>),
  /// `Lambda` stage 2: gather the position
  LamSpan(Box<Lam>),
  /// `Lambda` stage 3: gather the name
  LamName(Box<Lam>),
  /// `Lambda` stage 4: gather the code core
  LamCode(Box<Lam>),
  /// A `Code` core's body: `Ir` instructions until `END`. The sole `Ir`-mode frame.
  IrBody(ProcSpec, Vec<Ir>),
  /// One `Ir` instruction awaiting its value/code operands. An `Ir::Lambda`'s code core
  /// is one such operand, itself read in value mode (a `Code` or a `Ref`).
  IrBuild { op: u8, data: u32, builtin: Option<BuiltinProc>, ops: Vec<RVal> },
}

/// The staged state of a lambda ([`Frame::LamEnv`] and friends), read in order:
/// environment, span, name (named
/// lambdas only), then the code core.
struct Lam {
  named: bool,
  env: Vec<LispVal>,
  fsp: Option<FileSpan>,
  nsp: Option<Span>,
  name: Option<AtomId>,
}

impl Lam {
  fn new(named: bool) -> Self { Lam { named, env: vec![], fsp: None, nsp: None, name: None } }
}

struct Reader<'a> {
  env: &'a mut Environment,
  buf: &'a [u8],
  pos: usize,
  /// The heap `H`: values saved by `Save`, the auto-saving leaves, and `NewRef`.
  heap: Vec<RVal>,
  /// The `.mmb`'s directory: span file paths are stored relative to it and localized
  /// against it on the way back in.
  base: &'a Path,
}

impl<'a> Reader<'a> {
  fn err(&self, msg: &'static str) -> ParseError { ParseError::StrError(msg, self.pos) }

  fn byte(&mut self) -> Result<u8, ParseError> {
    let b = *self.buf.get(self.pos).ok_or_else(|| self.err("unexpected end of stream"))?;
    self.pos += 1;
    Ok(b)
  }

  fn u32(&mut self) -> Result<u32, ParseError> {
    let b = self.buf.get(self.pos..self.pos + 4)
      .ok_or_else(|| self.err("unexpected end of stream"))?;
    self.pos += 4;
    Ok(u32::from_le_bytes(b.try_into().expect("checked")))
  }

  fn bytes(&mut self, len: usize) -> Result<&'a [u8], ParseError> {
    let buf = self.buf;
    let b = buf.get(self.pos..self.pos + len).ok_or_else(|| self.err("unexpected end of stream"))?;
    self.pos += len;
    Ok(b)
  }

  /// Read a NUL-terminated string.
  fn cstr(&mut self) -> Result<&'a [u8], ParseError> {
    let buf = &self.buf[self.pos..];
    let n = memchr::memchr(0, buf).ok_or_else(|| self.err("unterminated string"))?;
    self.pos += n + 1;
    Ok(&buf[..n])
  }

  /// Read a signed LEB128 into a `BigInt`. The common case accumulates in an `i64`,
  /// falling back to [`big_sleb`](Self::big_sleb) only once the value overflows it.
  fn sleb(&mut self) -> Result<BigInt, ParseError> {
    let (mut result, mut shift) = (0i64, 0u32);
    loop {
      let byte = self.byte()?;
      if shift >= 63 {
        // The next group would reach the `i64` sign bit; continue in `BigInt`.
        return self.big_sleb(result, shift, byte)
      }
      result |= i64::from(byte & 0x7f) << shift;
      shift += 7;
      if byte & 0x80 == 0 {
        if byte & 0x40 != 0 {
          result |= -1i64 << shift; // two's-complement sign extension
        }
        return Ok(result.into())
      }
    }
  }

  /// Finish a signed LEB128 too large for an `i64`, seeded with the non-negative
  /// `low` bits accumulated so far (up to bit `shift`) and the next `byte`.
  fn big_sleb(&mut self, low: i64, mut shift: u32, mut byte: u8) -> Result<BigInt, ParseError> {
    let mut result = BigInt::from(low);
    loop {
      for i in 0..7u32 {
        result.set_bit(u64::from(shift + i), (byte >> i) & 1 != 0);
      }
      shift += 7;
      if byte & 0x80 == 0 {
        if byte & 0x40 != 0 {
          result -= BigInt::from(1) << shift; // two's-complement sign extension
        }
        return Ok(result);
      }
      byte = self.byte()?;
    }
  }

  /// Intern an atom and auto-save it.
  fn atom(&mut self, s: &[u8]) -> RVal {
    let v = LispVal::atom(self.env.get_atom(s));
    self.heap.push(RVal::Val(v.clone()));
    RVal::Val(v)
  }

  /// Build a string and auto-save it.
  fn string(&mut self, s: &[u8]) -> RVal {
    let v = LispVal::string(ArcString::from(s));
    self.heap.push(RVal::Val(v.clone()));
    RVal::Val(v)
  }

  /// Read one complete value, driving the single work stack described on [`Frame`]. The
  /// stack top chooses whether the next token is a `value` or an `Ir` instruction, so
  /// values and lambda code may nest through each other to any depth without the reader
  /// ever recursing: the whole grammar runs in this one loop.
  fn read_value(&mut self) -> Result<RVal, ParseError> {
    let mut frames: Vec<Frame> = vec![];
    loop {
      // Produce the next completed sub-result, or push a frame and re-evaluate the mode.
      let step = if matches!(frames.last(), Some(Frame::IrBody(..))) {
        self.step_ir(&mut frames)?
      } else {
        self.step_value(&mut frames)?
      };
      let Some(mut rv) = step else { continue };
      // Fold the result up through its parents until one stashes it (needing another
      // token) or the stack empties (the whole value is done).
      loop {
        let Some(top) = frames.pop() else { return Ok(rv) };
        let Some(p) = self.combine(top, rv, &mut frames)? else { break };
        rv = p
      }
    }
  }

  /// Read one token in value mode: a leaf becomes a [`RVal`], an opener pushes a
  /// collector [`Frame`] (returning `None`), and `END` finalizes the top collector.
  #[allow(clippy::cast_possible_truncation, clippy::too_many_lines)]
  fn step_value(&mut self, frames: &mut Vec<Frame>) -> Result<Option<RVal>, ParseError> {
    let (op, data, next) = parse_cmd(self.buf, self.pos)?;
    self.pos = next;
    let v = match op {
      op::END => return self.finish_collector(frames),
      op::UNDEF => RVal::Val(LispVal::undef()),
      op::FALSE => RVal::Val(LispVal::bool(false)),
      op::TRUE => RVal::Val(LispVal::bool(true)),
      op::ATOM => { let s = self.cstr()?; self.atom(s) }
      op::ATOMZ => { let s = self.bytes(data as usize)?; self.atom(s) }
      op::STRING => { let s = self.cstr()?; self.string(s) }
      op::STRINGZ => { let s = self.bytes(data as usize)?; self.string(s) }
      op::NUMBER => RVal::Val(LispVal::number(self.sleb()?)),
      op::SYNTAX => RVal::Val(LispVal::syntax(
        Syntax::from_u32(data).ok_or_else(|| self.err("bad syntax code"))?)),
      op::BUILTIN => RVal::Val(LispVal::proc(Proc::Builtin(
        BuiltinProc::from_u32(data).ok_or_else(|| self.err("bad builtin code"))?))),
      op::REF => self.heap.get(data as usize).cloned()
        .ok_or_else(|| self.err("reference out of range"))?,
      op::DEAD_WEAK => RVal::Val(LispVal::weak_ref(&LispVal::undef())),
      op::LIST => { frames.push(Frame::List(false, vec![])); return Ok(None) }
      op::LIST_SAVE => { frames.push(Frame::List(true, vec![])); return Ok(None) }
      op::DOTTED_LIST => { frames.push(Frame::Dotted(false, vec![])); return Ok(None) }
      op::DOTTED_LIST_SAVE => { frames.push(Frame::Dotted(true, vec![])); return Ok(None) }
      op::MAP => { frames.push(Frame::Map(false, vec![])); return Ok(None) }
      op::SAVE => { frames.push(Frame::Save); return Ok(None) }
      op::NEW_REF => {
        let idx = self.heap.len();
        self.heap.push(RVal::Val(LispVal::new_ref(LispVal::undef())));
        frames.push(Frame::NewRef(idx));
        return Ok(None)
      }
      op::SPAN => { frames.push(Frame::SpanFile(self.u32()?, self.u32()?)); return Ok(None) }
      op::ANNOT => { frames.push(Frame::AnnotSpan); return Ok(None) }
      op::GOAL => { frames.push(Frame::Goal); return Ok(None) }
      op::MVAR => match self.byte()? {
        infer::UNKNOWN =>
          RVal::Val(LispVal::new(LispKind::MVar(data as usize, InferTarget::Unknown))),
        infer::PROVABLE =>
          RVal::Val(LispVal::new(LispKind::MVar(data as usize, InferTarget::Provable))),
        infer::BOUND => { frames.push(Frame::MVar(data as usize, true)); return Ok(None) }
        infer::REG => { frames.push(Frame::MVar(data as usize, false)); return Ok(None) }
        _ => return Err(self.err("bad infer_target tag")),
      }
      op::LAMBDA => {
        frames.push(Frame::LamEnv(Box::new(Lam::new(data & LAMBDA_NAMED != 0))));
        return Ok(None)
      }
      op::CUSTOM_PROC => match u8::try_from(data).map_err(|_| self.err("bad CustomProc kind"))? {
        // A match continuation is only valid in the dynamic extent that made it, long
        // gone by load time; reconstruct an invalidated one.
        custom::MATCH_CONT => RVal::Val(LispVal::proc(Proc::MatchCont(Rc::new(Cell::new(false))))),
        custom::REFINE_CALLBACK => RVal::Val(LispVal::proc(Proc::RefineCallback)),
        custom::MERGE_MAP => { frames.push(Frame::MergeMapProc); return Ok(None) }
        custom::PROOF_THUNK => { frames.push(Frame::ProofThunkProc); return Ok(None) }
        _ => return Err(self.err("bad CustomProc kind")),
      }
      op::CODE => {
        let spec = self.read_spec()?;
        frames.push(Frame::IrBody(spec, vec![]));
        return Ok(None)
      }
      _ => return Err(self.err("bad value opcode")),
    };
    Ok(Some(v))
  }

  /// Finalize the top value-mode collector on `END`: `List`/`DottedList`/`Map` yield
  /// their value; a `Lambda` environment instead advances to reading the span.
  fn finish_collector(&mut self, frames: &mut Vec<Frame>) -> Result<Option<RVal>, ParseError> {
    let Some(top) = frames.pop() else { return Err(self.err("unexpected END")) };
    let (save, v) = match top {
      Frame::List(save, es) => (save, LispVal::list(es)),
      Frame::Dotted(save, mut es) => {
        let tail = es.pop().ok_or_else(|| self.err("empty dotted list"))?;
        (save, LispVal::dotted_list(es, tail))
      }
      Frame::Map(save, es) => {
        let mut m = HashMap::new();
        let mut it = es.into_iter();
        while let Some(k) = it.next() {
          let val = it.next().ok_or_else(|| self.err("atom map has an odd number of entries"))?;
          m.insert(atom_of(&k, self.pos)?, val);
        }
        (save, LispVal::new(LispKind::AtomMap(m)))
      }
      Frame::LamEnv(lam) => {
        frames.push(Frame::LamSpan(lam));
        return Ok(None)
      }
      _ => return Err(self.err("END closing a non-collector")),
    };
    if save { self.heap.push(RVal::Val(v.clone())) }
    Ok(Some(RVal::Val(v)))
  }

  /// Read one token in `Ir` mode (the stack top is an [`IrBody`](Frame::IrBody)). A
  /// no-operand instruction becomes a [`RVal`]; one with value/code operands pushes an
  /// [`IrBuild`](Frame::IrBuild) and switches back to value mode; `END` finishes the core.
  #[allow(clippy::cast_possible_truncation, clippy::too_many_lines)]
  fn step_ir(&mut self, frames: &mut Vec<Frame>) -> Result<Option<RVal>, ParseError> {
    let (op, data, next) = parse_cmd(self.buf, self.pos)?;
    self.pos = next;
    let ir = match op {
      op::END => {
        let Some(Frame::IrBody(spec, code)) = frames.pop() else {
          return Err(self.err("unexpected Ir END"))
        };
        let rval = RVal::Code(spec, code.into());
        self.heap.push(rval.clone());
        return Ok(Some(rval))
      }
      ir::UNDEF => Ir::Undef,
      ir::DUP => Ir::Dup,
      ir::FOCUS_FINISH => Ir::FocusFinish,
      ir::TEST_PATTERN_RESUME => Ir::TestPatternResume,
      ir::MAP => Ir::Map,
      ir::HAVE => Ir::Have,
      ir::REFINE_RESUME => Ir::RefineResume,
      ir::ADD_THM => Ir::AddThm,
      ir::MERGE_MAP => Ir::MergeMap,
      ir::ON_DECLS => Ir::OnDecls,
      ir::PATTERN_UNDEF => Ir::PatternUndef,
      ir::PATTERN_GOAL => Ir::PatternGoal,
      ir::PATTERN_TEST_PAUSE => Ir::PatternTestPause,
      ir::DROP => Ir::Drop(data as usize),
      ir::DROP_ABOVE => Ir::DropAbove(data as usize),
      ir::ASSERT_SCOPE => Ir::AssertScope(data as usize),
      ir::END_SCOPE => Ir::EndScope(data as usize),
      ir::LOCAL => Ir::Local(data as usize),
      ir::DOTTED_LIST => Ir::DottedList(data as usize),
      ir::JUMP_UNLESS => Ir::JumpUnless(data as usize),
      ir::JUMP => Ir::Jump(data as usize),
      ir::LOCAL_DEF => Ir::LocalDef(data as usize),
      ir::PATTERN_ATOM => Ir::PatternAtom(data as usize),
      ir::PATTERN_EQ_ATOM => Ir::PatternEqAtom(data as usize),
      ir::PATTERN_DOTTED_LIST => Ir::PatternDottedList(data as usize),
      ir::REFINE_GOAL => Ir::RefineGoal(data != 0),
      ir::PATTERN_RESULT => Ir::PatternResult(data != 0),
      ir::PATTERN_BOOL => Ir::PatternBool(data != 0),
      ir::BRANCH => {
        let (target, cont) = (self.uleb()?, self.uleb()?);
        Ir::Branch(data as usize, self.jump(target)?, opt_index(cont))
      }
      ir::PATTERN_LIST => Ir::PatternList(data as usize, opt_index(self.uleb()?)),
      ir::PATTERN_TRY => { let err = self.uleb()?; Ir::PatternTry(data as usize, self.jump(err)?) }
      ir::PATTERN_MVAR => Ir::PatternMVar(self.mvar_pattern(data)?),
      // A builtin application's `builtin` byte comes before its span operands.
      ir::BUILTIN_APP | ir::BUILTIN_TAIL_APP => {
        frames.push(Frame::IrBuild { op, data, builtin: Some(self.read_builtin()?), ops: vec![] });
        return Ok(None)
      }
      // Every other operand-bearing instruction reads its operands as values.
      ir::PATTERN_QUOTE_ATOM | ir::PATTERN_QEXPR_ATOM | ir::CONST | ir::PATTERN_STRING
      | ir::PATTERN_NUMBER | ir::APP_HEAD | ir::FOCUS_START | ir::BRANCH_FAIL | ir::GLOBAL
      | ir::SET_MERGE_STRATEGY | ir::LIST | ir::GLOBAL_DEF | ir::SET_DOC | ir::APP
      | ir::TAIL_APP | ir::ARITY_ERROR | ir::LAMBDA => {
        frames.push(Frame::IrBuild { op, data, builtin: None, ops: vec![] });
        return Ok(None)
      }
      _ => return Err(self.err("bad Ir opcode")),
    };
    Ok(Some(RVal::Ir(ir)))
  }

  /// Fold a completed [`RVal`] into its parent `top`. Returns `Some` new product when
  /// the parent completes (keep folding), or `None` when it stashed the result and was
  /// re-pushed (read the next token).
  fn combine(
    &mut self, top: Frame, prod: RVal, frames: &mut Vec<Frame>
  ) -> Result<Option<RVal>, ParseError> {
    let pos = self.pos;
    Ok(match top {
      Frame::List(save, mut es) => {
        es.push(prod.val(pos)?);
        frames.push(Frame::List(save, es));
        None
      }
      Frame::Dotted(save, mut es) => {
        es.push(prod.val(pos)?);
        frames.push(Frame::Dotted(save, es));
        None
      }
      Frame::Map(save, mut es) => {
        es.push(prod.val(pos)?);
        frames.push(Frame::Map(save, es));
        None
      }
      Frame::Save => { self.heap.push(prod.clone()); Some(prod) }
      Frame::NewRef(idx) => {
        let contents = prod.val(pos)?;
        let RVal::Val(cv) = self.heap[idx].clone() else { unreachable!() };
        let LispKind::Ref(r) = &*cv else { unreachable!() };
        r.get_mut(|slot| *slot = contents);
        Some(RVal::Val(cv))
      }
      #[allow(clippy::cast_possible_truncation)]
      Frame::SpanFile(lo, hi) => {
        let file = fileref_of(&prod.val(pos)?, self.base, pos)?;
        let fsp = FileSpan { file, span: (lo as usize..hi as usize).into() };
        self.heap.push(RVal::Span(fsp.clone()));
        Some(RVal::Span(fsp))
      }
      Frame::AnnotSpan => match prod {
        RVal::Span(fsp) => { frames.push(Frame::AnnotVal(fsp)); None }
        _ => return Err(self.err("annotation is not a span")),
      }
      Frame::AnnotVal(fsp) => Some(RVal::Val(prod.val(pos)?.span(fsp))),
      Frame::Goal => Some(RVal::Val(LispVal::new(LispKind::Goal(prod.val(pos)?)))),
      Frame::MVar(idx, bound) => {
        let sort = atom_of(&prod.val(pos)?, pos)?;
        let tgt = if bound { InferTarget::Bound(sort) } else { InferTarget::Reg(sort) };
        Some(RVal::Val(LispVal::new(LispKind::MVar(idx, tgt))))
      }
      Frame::MergeMapProc =>
        Some(RVal::Val(LispVal::proc(Proc::MergeMap(prod.val(pos)?.into_merge_strategy())))),
      Frame::ProofThunkProc => {
        let a = atom_of(&prod.val(pos)?, pos)?;
        Some(RVal::Val(self.env.proof_thunk(a)))
      }
      Frame::LamEnv(mut lam) => {
        lam.env.push(prod.val(pos)?);
        frames.push(Frame::LamEnv(lam));
        None
      }
      Frame::LamSpan(mut lam) => {
        let RVal::Span(fsp) = prod else { return Err(self.err("lambda span is not a span")) };
        lam.fsp = Some(fsp);
        if lam.named {
          #[allow(clippy::cast_possible_truncation)]
          let (lo, hi) = (self.u32()? as usize, self.u32()? as usize);
          lam.nsp = Some((lo..hi).into());
          frames.push(Frame::LamName(lam));
        } else {
          frames.push(Frame::LamCode(lam));
        }
        None
      }
      Frame::LamName(mut lam) => {
        lam.name = Some(atom_of(&prod.val(pos)?, pos)?);
        frames.push(Frame::LamCode(lam));
        None
      }
      Frame::LamCode(lam) => {
        let RVal::Code(spec, code) = prod else {
          return Err(self.err("lambda code is not a code core"))
        };
        let fsp = lam.fsp.expect("span read before code");
        let loc = if lam.named {
          ProcPos::Named(fsp, lam.nsp.expect("named lambda has a name span"),
            lam.name.expect("named lambda has a name"))
        } else {
          ProcPos::Unnamed(fsp)
        };
        Some(RVal::Val(LispVal::proc(Proc::Lambda { pos: loc, env: lam.env.into(), spec, code })))
      }
      Frame::IrBuild { op, data, builtin, mut ops } => {
        ops.push(prod);
        if ops.len() == ir_arity(op) {
          Some(RVal::Ir(self.assemble_ir(op, data, builtin, &ops)?))
        } else {
          frames.push(Frame::IrBuild { op, data, builtin, ops });
          None
        }
      }
      // Only an `IrBody` consumes an `Ir`; every other frame consumes a value result.
      Frame::IrBody(spec, mut code) => {
        let RVal::Ir(ir) = prod else { return Err(self.err("expected an Ir instruction")) };
        code.push(ir);
        frames.push(Frame::IrBody(spec, code));
        None
      }
    })
  }

  /// Assemble an `Ir` instruction from its opcode, `data`, optional `builtin`, and the
  /// value/code operands collected by its [`IrBuild`](Frame::IrBuild) frame.
  #[allow(clippy::cast_possible_truncation)]
  fn assemble_ir(
    &mut self, op: u8, data: u32, builtin: Option<BuiltinProc>, ops: &[RVal]
  ) -> Result<Ir, ParseError> {
    let pos = self.pos;
    let n = data as usize;
    Ok(match op {
      ir::PATTERN_QUOTE_ATOM => Ir::PatternQuoteAtom(as_atom(&ops[0], pos)?),
      ir::PATTERN_QEXPR_ATOM => Ir::PatternQExprAtom(as_atom(&ops[0], pos)?),
      ir::CONST => Ir::Const(as_val(&ops[0], pos)?),
      ir::PATTERN_STRING => Ir::PatternString(as_string(&ops[0], pos)?),
      ir::PATTERN_NUMBER => Ir::PatternNumber(as_number(&ops[0], pos)?),
      ir::APP_HEAD => Ir::AppHead(as_span(&ops[0], pos)?),
      ir::FOCUS_START => Ir::FocusStart(as_span(&ops[0], pos)?),
      ir::BRANCH_FAIL => Ir::BranchFail(as_span(&ops[0], pos)?),
      ir::GLOBAL => Ir::Global(as_span(&ops[0], pos)?, as_atom(&ops[1], pos)?),
      ir::SET_MERGE_STRATEGY => Ir::SetMergeStrategy(as_span(&ops[0], pos)?, as_atom(&ops[1], pos)?),
      ir::LIST => Ir::List(as_span(&ops[0], pos)?, n),
      ir::GLOBAL_DEF =>
        Ir::GlobalDef(as_span(&ops[0], pos)?, as_span(&ops[1], pos)?, as_atom(&ops[2], pos)?),
      ir::SET_DOC => Ir::SetDoc(as_doc(&ops[0], pos)?, as_atom(&ops[1], pos)?),
      ir::APP => Ir::App(false, Box::new((as_span(&ops[0], pos)?, as_span(&ops[1], pos)?)), n),
      ir::TAIL_APP => Ir::App(true, Box::new((as_span(&ops[0], pos)?, as_span(&ops[1], pos)?)), n),
      ir::BUILTIN_APP => Ir::BuiltinApp(false, builtin.expect("builtin byte read"),
        Box::new((as_span(&ops[0], pos)?, as_span(&ops[1], pos)?)), n),
      ir::BUILTIN_TAIL_APP => Ir::BuiltinApp(true, builtin.expect("builtin byte read"),
        Box::new((as_span(&ops[0], pos)?, as_span(&ops[1], pos)?)), n),
      // The `spec` bytes follow the span operand, so they are read now, at assembly.
      ir::ARITY_ERROR => Ir::ArityError(as_span(&ops[0], pos)?, self.read_spec()?),
      ir::LAMBDA => {
        let name = u8::try_from(data).map_err(|_| self.err("bad lambda backref"))?;
        let (sp, (spec, code)) = (as_span(&ops[0], pos)?, as_code(&ops[1], pos)?);
        Ir::Lambda(name, Box::new((sp, spec, code)))
      }
      _ => return Err(self.err("bad Ir opcode")),
    })
  }

  /// Read an unsigned LEB128 (jump targets and optional-index operands in the `Ir` stream).
  fn uleb(&mut self) -> Result<u64, ParseError> {
    let (mut result, mut shift) = (0u64, 0u32);
    loop {
      let byte = self.byte()?;
      result |= u64::from(byte & 0x7f) << shift;
      shift += 7;
      if byte & 0x80 == 0 { return Ok(result); }
    }
  }

  /// Narrow a `uleb` jump target to a `usize` index.
  fn jump(&self, x: u64) -> Result<usize, ParseError> {
    usize::try_from(x).map_err(|_| self.err("jump target overflow"))
  }

  /// Read a `builtin` byte into a [`BuiltinProc`].
  fn read_builtin(&mut self) -> Result<BuiltinProc, ParseError> {
    let b = self.byte()?;
    BuiltinProc::from_u8(b).ok_or_else(|| self.err("bad builtin code"))
  }

  /// Read a `spec = (kind: u8, count: u8)` into a [`ProcSpec`].
  fn read_spec(&mut self) -> Result<ProcSpec, ParseError> {
    let (kind, count) = (self.byte()?, usize::from(self.byte()?));
    match kind {
      spec::EXACT => Ok(ProcSpec::Exact(count)),
      spec::AT_LEAST => Ok(ProcSpec::AtLeast(count)),
      _ => Err(self.err("bad spec kind")),
    }
  }

  /// The `tag` of a `PatternMVar` instruction.
  fn mvar_pattern(&self, tag: u32) -> Result<MVarPattern, ParseError> {
    match u8::try_from(tag).ok() {
      Some(pat_mvar::UNKNOWN) => Ok(MVarPattern::Unknown),
      Some(pat_mvar::ANY) => Ok(MVarPattern::Any),
      Some(pat_mvar::SIMPLE) => Ok(MVarPattern::Simple),
      _ => Err(self.err("bad PatternMVar tag")),
    }
  }

  /// The top level: one global record per turn (a name-first record) or a `SetWeak`,
  /// until `END`.
  fn read_globals(&mut self) -> Result<(), ParseError> {
    loop {
      let pos = self.pos;
      let (op, data, next) = parse_cmd(self.buf, self.pos)?;
      match op {
        op::END => { self.pos = next; return Ok(()) }
        op::SET_WEAK => {
          self.pos = next;
          let cell = data as usize;
          let target = self.read_value()?.val(next)?;
          let RVal::Val(cell) = self.heap.get(cell)
            .ok_or_else(|| self.err("set-weak cell out of range"))?
          else { return Err(self.err("set-weak target is not a ref")) };
          let LispKind::Ref(r) = &**cell else {
            return Err(self.err("set-weak target is not a ref"))
          };
          r.set_weak(&target)
        }
        _ => {
          // leave the name for `read_value`
          let name = atom_of(&self.read_value()?.val(pos)?, pos)?;
          let (lo, hi) = (self.u32()?, self.u32()?);
          let val = self.read_value()?.val(pos)?;
          let src = match self.read_value()? {
            RVal::Span(fsp) => Some((fsp, (lo as usize..hi as usize).into())),
            RVal::Val(v) if !v.is_def_strict() => None, // `#undef`
            _ => return Err(self.err("global src is not a span or #undef")),
          };
          let merge = self.read_value()?.val(pos)?.into_merge_strategy();
          let doc = doc_of(&self.read_value()?.val(pos)?);
          self.env.data[name].lisp = Some(LispData { src, doc, val, merge });
          // Record the global in the statement trace, like `global_def` does, so a
          // dependent file's `EnvMergeIter` (which walks `stmts`) picks it up.
          self.env.stmts.push(StmtTrace::Global(name));
        }
      }
    }
  }
}

/// Extract the [`AtomId`] of an `Atom` value.
fn atom_of(v: &LispVal, pos: usize) -> Result<AtomId, ParseError> {
  match &**v {
    LispKind::Atom(a) => Ok(*a),
    _ => Err(ParseError::StrError("expected an atom", pos)),
  }
}

/// Rebuild a [`FileRef`] from a span's file `value`: its path is stored relative to the
/// `.mmb`'s directory `base`, so resolve it against `base` (as `import` resolves a path
/// against the importing file's directory).
fn fileref_of(v: &LispVal, base: &Path, pos: usize) -> Result<FileRef, ParseError> {
  match &**v {
    LispKind::String(s) => Ok(FileRef::from(base.join(&*String::from_utf8_lossy(s)))),
    _ => Err(ParseError::StrError("span file is not a string", pos)),
  }
}

/// A doc comment is the `doc` field's string value, or `None` for `#undef`.
fn doc_of(v: &LispVal) -> Option<DocComment> {
  match &**v {
    LispKind::String(s) => Some(String::from_utf8_lossy(s).into()),
    _ => None,
  }
}

/// The number of value/code operands an operand-bearing `Ir` instruction reads (only
/// called for the opcodes that push an [`IrBuild`](Frame::IrBuild) frame).
fn ir_arity(op: u8) -> usize {
  match op {
    ir::GLOBAL_DEF => 3,
    ir::GLOBAL | ir::SET_MERGE_STRATEGY | ir::SET_DOC | ir::APP | ir::TAIL_APP
    | ir::BUILTIN_APP | ir::BUILTIN_TAIL_APP | ir::LAMBDA => 2,
    // PatternQuoteAtom, PatternQExprAtom, Const, PatternString, PatternNumber, AppHead,
    // FocusStart, BranchFail, List, ArityError.
    _ => 1,
  }
}

/// A `uleb` optional index: `0` is `None`, else the value minus one.
fn opt_index(x: u64) -> Option<usize> {
  usize::try_from(x).ok().and_then(|x| x.checked_sub(1))
}

/// Extract an `Ir` span operand: the byte range of a span [`RVal`].
fn as_span(rv: &RVal, pos: usize) -> Result<Span, ParseError> {
  match rv {
    RVal::Span(fsp) => Ok(fsp.span),
    _ => Err(ParseError::StrError("expected a span", pos)),
  }
}

/// Extract a `LispVal` operand.
fn as_val(rv: &RVal, pos: usize) -> Result<LispVal, ParseError> {
  match rv {
    RVal::Val(v) => Ok(v.clone()),
    _ => Err(ParseError::StrError("expected a value", pos)),
  }
}

/// Extract an atom operand.
fn as_atom(rv: &RVal, pos: usize) -> Result<AtomId, ParseError> {
  atom_of(&as_val(rv, pos)?, pos)
}

/// Extract a string operand.
fn as_string(rv: &RVal, pos: usize) -> Result<ArcString, ParseError> {
  match &*as_val(rv, pos)? {
    LispKind::String(s) => Ok(s.clone()),
    _ => Err(ParseError::StrError("expected a string", pos)),
  }
}

/// Extract a number operand.
fn as_number(rv: &RVal, pos: usize) -> Result<BigInt, ParseError> {
  match &*as_val(rv, pos)? {
    LispKind::Number(n) => Ok(n.clone()),
    _ => Err(ParseError::StrError("expected a number", pos)),
  }
}

/// Extract a doc-comment operand from a string [`RVal`].
fn as_doc(rv: &RVal, pos: usize) -> Result<DocComment, ParseError> {
  Ok(String::from_utf8_lossy(&as_string(rv, pos)?).into())
}

/// Extract a code-core operand `(spec, body)`.
fn as_code(rv: &RVal, pos: usize) -> Result<(ProcSpec, Arc<[Ir]>), ParseError> {
  match rv {
    RVal::Code(spec, code) => Ok((*spec, code.clone())),
    _ => Err(ParseError::StrError("expected a code core", pos)),
  }
}

#[cfg(test)]
mod test {
  use std::path::PathBuf;
  use std::sync::Arc;

  use super::{deserialize_stream, super::export::serialize};
  use crate::elab::environment::{Environment, LispData};
  use crate::elab::lisp::{
    LispKind, LispVal, LispWeak, Proc, ProcPos, ProcSpec, parser::{Ir, MVarPattern}};
  use crate::FrozenEnv;
  use mm0_util::{ArcString, FileRef, FileSpan};
  use num::BigInt;

  fn num(n: i64) -> LispVal { LispVal::number(BigInt::from(n)) }
  fn str(s: &str) -> LispVal { LispVal::string(ArcString::from(s.as_bytes())) }
  fn put(env: &mut Environment, name: &[u8], val: LispVal) {
    let a = env.get_atom(name);
    env.data[a].lisp = Some(LispData { src: None, doc: None, val, merge: None });
  }
  fn get(env: &mut Environment, name: &[u8]) -> LispVal {
    let a = env.get_atom(name);
    env.data[a].lisp.as_ref().expect("global missing").val.clone()
  }

  /// Round-trip the three mutable-cell shapes, which are the only places the stream can
  /// close a cycle: a `ref!` that contains itself (written `NewRef` pre-order, so the
  /// back-edge is a plain `Ref`), a live weak reference (a cell filled by a trailing
  /// `SetWeak` once its target exists), and a weak reference whose target no strong path
  /// reaches, which degrades to a `DeadWeak`.
  #[test]
  fn roundtrip_refs() {
    let mut env = Environment::new();

    // `cyc = (ref! (cyc))`: the cell's contents point back at the cell.
    let cyc = LispVal::new_ref(LispVal::undef());
    let LispKind::Ref(r) = &*cyc else { panic!("not a ref") };
    r.get_mut(|slot| *slot = LispVal::list(vec![cyc.clone()]));
    put(&mut env, b"cyc", cyc);

    // A live weak reference: `target` is kept alive by a strong path from `strong`.
    let target = LispVal::list(vec![num(1), str("t")]);
    put(&mut env, b"strong", target.clone());
    put(&mut env, b"weak", LispVal::weak_ref(&target));

    // A dead one: nothing else reaches `gone`, so the weak link has no target to keep.
    let gone = LispVal::list(vec![num(99)]);
    put(&mut env, b"dead", LispVal::weak_ref(&gone));
    drop(gone);

    let bytes = serialize(&FrozenEnv::new(env), std::path::Path::new(""),
      |m| panic!("unexpected: {m}"));
    let mut env = Environment::new();
    deserialize_stream(&mut env, &bytes, std::path::Path::new("")).expect("read");

    // The cycle came back as a cycle, not an infinite unrolling: the cell's contents are
    // a one-element list whose element is that very cell.
    let cyc = get(&mut env, b"cyc");
    let LispKind::Ref(r) = &*cyc else { panic!("cyc is not a ref") };
    let inner = r.get(Clone::clone);
    let LispKind::List(es) = &*inner else { panic!("cyc contents are not a list") };
    assert!(es.len() == 1 && es[0].ptr_eq(&cyc), "the cycle did not close on itself");

    // The live weak reference is still *weak* (not silently promoted to a strong one),
    // and still resolves to the very object the strong global holds — the `SetWeak`
    // target was `Ref`d, not copied.
    let (strong, weak) = (get(&mut env, b"strong"), get(&mut env, b"weak"));
    let LispKind::Ref(r) = &*weak else { panic!("weak is not a ref") };
    assert!(matches!(&*r.get_weak(), LispWeak::Weak(_)), "the weak reference became strong");
    assert!(r.get(Clone::clone).ptr_eq(&strong), "the weak reference lost its target");

    // The dead one reads back as a `ref!` with nothing behind it.
    let dead = get(&mut env, b"dead");
    let LispKind::Ref(r) = &*dead else { panic!("dead is not a ref") };
    assert!(matches!(&*r.get(Clone::clone), LispKind::Undef), "a dead weak should be #undef");
  }

  /// Round-trip a handful of data globals through the value stream: leaves, nested
  /// and dotted lists, and a value shared between two globals (a `Ref`).
  #[test]
  fn roundtrip_data() {
    let mut env = Environment::new();
    let shared = LispVal::list(vec![num(1), num(2), num(3)]);
    put(&mut env, b"gx", shared.clone());
    put(&mut env, b"gy", LispVal::list(vec![shared, str("hi"), LispVal::bool(true)]));
    put(&mut env, b"gz", LispVal::dotted_list(vec![num(-5), LispVal::undef()], str("tail")));
    // `i64::MAX`/`MIN` sit at the `i64` boundary; the two `2^80`-scale values overflow it,
    // exercising the writer's `sleb_big` and the reader's `big_sleb` in both signs.
    let big = BigInt::from(i64::MAX) * BigInt::from(1_000_000);
    let bigneg = -&big - BigInt::from(1);
    let bignums = || vec![num(0), num(i64::MAX), num(i64::MIN),
      LispVal::number(big.clone()), LispVal::number(bigneg.clone())];
    put(&mut env, b"gn", LispVal::list(bignums()));

    let bytes = serialize(&FrozenEnv::new(env), std::path::Path::new(""), |m| panic!("unexpected: {m}"));

    let mut env = Environment::new();
    deserialize_stream(&mut env, &bytes, std::path::Path::new("")).expect("read");
    assert_eq!(get(&mut env, b"gx"), LispVal::list(vec![num(1), num(2), num(3)]));
    assert_eq!(get(&mut env, b"gy"),
      LispVal::list(vec![LispVal::list(vec![num(1), num(2), num(3)]), str("hi"), LispVal::bool(true)]));
    assert_eq!(get(&mut env, b"gz"),
      LispVal::dotted_list(vec![num(-5), LispVal::undef()], str("tail")));
    assert_eq!(get(&mut env, b"gn"), LispVal::list(bignums()));
  }

  /// Round-trip lambdas: both `ProcPos` forms, a captured environment, a mix of `Ir`
  /// instructions, a nested `Ir::Lambda`, a `Code` core shared by two lambdas (so it
  /// is written once and `Ref`d), and a lambda value shared across two globals. The
  /// check is that re-serializing the imported environment reproduces the same bytes.
  #[test]
  fn roundtrip_procs() {
    let file = FileRef::from(PathBuf::from("t.mm1"));
    let fsp = |lo: usize, hi: usize| FileSpan { file: file.clone(), span: (lo..hi).into() };

    let mut env = Environment::new();
    let sym = env.get_atom(b"sym");
    let fname = env.get_atom(b"myfn");

    // A body exercising every operand shape: a `value`, a span+atom, spans, the
    // optional-index `uleb`s, an mvar tag, and jumps.
    let core: Arc<[Ir]> = vec![
      Ir::Undef,
      Ir::Local(2),
      Ir::Const(num(7)),
      Ir::Global((0..3).into(), sym),
      Ir::AppHead((4..5).into()),
      Ir::App(false, Box::new(((1..2).into(), (2..3).into())), 1),
      Ir::Branch(1, 8, Some(3)),
      Ir::PatternList(2, Some(1)),
      Ir::PatternList(0, None),
      Ir::PatternMVar(MVarPattern::Any),
      Ir::Jump(0),
    ].into();

    // An outer body whose nested lambda literal reuses `core` (a shared `Arc`).
    let outer: Arc<[Ir]> = vec![
      Ir::Lambda(0xFF, Box::new(((0..2).into(), ProcSpec::Exact(1), core.clone()))),
      Ir::Undef,
    ].into();

    let named = LispVal::proc(Proc::Lambda {
      pos: ProcPos::Named(fsp(0, 10), (2..4).into(), fname),
      env: Box::new([num(1), str("cap")]),
      spec: ProcSpec::AtLeast(2),
      code: core,
    });
    let unnamed = LispVal::proc(Proc::Lambda {
      pos: ProcPos::Unnamed(fsp(20, 30)),
      env: Box::new([]),
      spec: ProcSpec::Exact(0),
      code: outer,
    });

    // `named` appears in two globals, so it is a shared proc value (`Save`/`Ref`).
    put(&mut env, b"f", named.clone());
    put(&mut env, b"g", LispVal::list(vec![named, unnamed]));

    let bytes = serialize(&FrozenEnv::new(env), std::path::Path::new(""), |m| panic!("unexpected: {m}"));

    let mut env = Environment::new();
    deserialize_stream(&mut env, &bytes, std::path::Path::new("")).expect("read");

    // Spot-check the reconstructed named lambda.
    let f = get(&mut env, b"f");
    let LispKind::Proc(Proc::Lambda { pos, env: cap, spec, code }) = &*f else {
      panic!("global f is not a lambda")
    };
    assert!(matches!(pos, ProcPos::Named(..)));
    assert_eq!(cap.len(), 2);
    assert!(matches!(spec, ProcSpec::AtLeast(2)));
    assert_eq!(code.len(), 11);

    // A full structural check: re-export must reproduce the original bytes.
    let bytes2 = serialize(&FrozenEnv::new(env), std::path::Path::new(""), |m| panic!("unexpected: {m}"));
    assert_eq!(bytes, bytes2);
  }

  /// A deeply nested value must read back without overflowing the machine stack: the
  /// reader's work stack lives on the heap, so nesting depth costs heap, not stack. A
  /// recursive reader would overflow here. We build the byte stream by hand and `forget`
  /// the result, because a `LispVal` this deep cannot even be constructed and dropped
  /// through its recursive `Drop`/`PartialEq` without overflowing — the reader is the
  /// only part of the pipeline that is iterative in the nesting depth.
  #[test]
  fn deep_nesting_no_overflow() {
    use super::super::op;
    const DEPTH: usize = 200_000;

    let mut bytes = vec![op::ATOM, b'd', 0]; // the global's name atom "d"
    bytes.extend_from_slice(&[0; 8]); // its (lo, hi) byte range
    bytes.extend(std::iter::repeat_n(op::LIST, DEPTH)); // DEPTH nested list openers
    bytes.extend_from_slice(&[op::NUMBER, 0]); // the innermost element, `0`
    bytes.extend(std::iter::repeat_n(op::END, DEPTH)); // and their terminators
    bytes.extend_from_slice(&[op::UNDEF, op::UNDEF, op::UNDEF]); // src, merge, doc
    bytes.push(op::END); // the `read_globals` terminator

    let mut env = Environment::new();
    deserialize_stream(&mut env, &bytes, std::path::Path::new("")).expect("deep read");
    std::mem::forget(env); // a value this deep overflows a recursive `Drop`; leak it
  }
}
