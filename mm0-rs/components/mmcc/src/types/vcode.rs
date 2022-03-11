//! The low level IR, based on cranelift's `VCode`.

use std::{collections::HashMap, fmt::{Debug, Display}, iter::FromIterator};

use crate::{Idx, types::{IdxVec, mir}, arch::PReg};

use mm0_util::u32_as_usize;
pub(crate) use regalloc2::{RegClass, InstRange, Operand, Inst as InstId};
pub use regalloc2::Block as BlockId;

use super::{Size, classify::Trace};

/// A trait to factor the commonalities of [`VReg`] and [`PReg`].
pub trait IsReg: Sized + Eq {
  /// A special value of the type representing the invalid value.
  fn invalid() -> Self;
  /// Is this value not the invalid values?
  fn is_valid(&self) -> bool { *self != Self::invalid() }
}

/// A virtual register, which is a stand-in for physical registers before register allocation.
#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct VReg(pub regalloc2::VReg);

impl VReg {
  #[inline(always)]
  pub(crate) const fn new(reg: usize) -> Self { Self(regalloc2::VReg::new(reg, RegClass::Int)) }
}

impl IsReg for VReg {
  fn invalid() -> Self { Self(regalloc2::VReg::invalid()) }
}

impl Debug for VReg {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self)
  }
}

impl Display for VReg {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.is_valid() {
      write!(f, "%{}", self.0.vreg())
    } else {
      write!(f, "%-")
    }
  }
}

impl Idx for BlockId {
  fn into_usize(self) -> usize { self.index() }
  fn from_usize(n: usize) -> Self { Self::new(n) }
}
impl Idx for InstId {
  fn into_usize(self) -> usize { self.index() }
  fn from_usize(n: usize) -> Self { Self::new(n) }
}
mk_id! {
  /// An ID for a global static variable to be placed in the global area.
  GlobalId(Debug("g")),
  /// An ID for a (monomorphized) function that can be called.
  ProcId(Debug("f")),
  /// An ID for a spill slot (a piece of the stack frame)
  SpillId(Debug("sp")),
}

impl SpillId {
  /// The spill slot corresponding to the incoming arguments from the caller.
  pub const INCOMING: SpillId = SpillId(0);
  /// The spill slot corresponding to the outgoing arguments, to functions called by this one.
  pub const OUTGOING: SpillId = SpillId(1);
}

/// The ABI of a constant.
#[derive(Copy, Clone, Debug)]
pub enum ConstRef {
  /// The value is stored inline. Values of less than 8 bytes are zero-padded to 8 bytes here.
  Value(u64),
  /// The value is stored at this relative offset into the read-only section.
  Ptr(u32),
}

/// A type for instruction data in a `VCode<I>`.
pub trait Inst: Sized {
  /// Determine whether an instruction is a call instruction. This is used
  /// only for splitting heuristics.
  fn is_call(&self) -> bool;

  /// Determine whether an instruction is a return instruction.
  fn is_ret(&self) -> bool;

  /// Determine whether an instruction is the end-of-block
  /// branch. If so, its operands at the indices given by
  /// `blockparam_arg_offset()` below *must* be the block
  /// parameters for each of its block's `block_succs` successor
  /// blocks, in order.
  fn is_branch(&self) -> bool;

  /// Returns the outgoing blockparam arguments for the given successor. The
  /// number of arguments must match the number incoming blockparams
  /// for each respective successor block.
  fn branch_blockparams(&self, succ_idx: usize) -> &[regalloc2::VReg];

  /// Determine whether an instruction is a move; if so, return the
  /// Operands for (src, dst).
  fn is_move(&self) -> Option<(Operand, Operand)>;

  /// Get the Operands for an instruction.
  fn collect_operands(&self, _: &mut Vec<Operand>);

  /// Get the clobbers for an instruction.
  fn clobbers(&self) -> &[PReg];
}

/// Conceptually the same as `IdxVec<I, Vec<T>>`, but shares allocations between the vectors.
/// Best used for append-only use, since only the last added element can be pushed to.
pub struct ChunkVec<I, T> {
  data: Vec<T>,
  idxs: IdxVec<I, u32>,
}

impl<I, T> Default for ChunkVec<I, T> {
  fn default() -> Self { Self { data: vec![], idxs: Default::default() } }
}

impl<I, T: Clone> Clone for ChunkVec<I, T> {
  fn clone(&self) -> Self {
    Self { data: self.data.clone(), idxs: self.idxs.clone() }
  }
}

impl<I: Idx, T: Debug> Debug for ChunkVec<I, T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_list()
      .entries(self.idxs.enum_iter().map(|(i, _)| &self[i]))
      .finish()
  }
}

impl<I: Idx, T> ChunkVec<I, T> {
  /// Push a new `[T]` to the list of lists. The value to be inserted is represented in
  /// continuation passing style; the function `f` is passed a vector and should extend the vector
  /// with the list of values.
  /// Behavior is unspecified if `f` clears or otherwise mishandles the vector.
  pub fn push_into(&mut self, f: impl FnOnce(&mut Vec<T>)) -> I {
    let i = self.idxs.push(self.data.len().try_into().expect("overflow"));
    f(&mut self.data);
    i
  }

  /// Push a new `[T]` to the list of lists. The value to be inserted is represented as
  /// an iterator.
  pub fn push(&mut self, it: impl IntoIterator<Item=T>) -> I {
    self.push_into(|v| v.extend(it))
  }

  /// Push a new empty list to the list of lists.
  pub fn push_new(&mut self) -> I { self.push_into(|_| ()) }

  /// Push a `T` to the last element of the list. The list must be nonempty.
  pub fn extend_last(&mut self, val: T) {
    assert!(!self.idxs.is_empty());
    self.data.push(val);
  }

  /// The starting index for the given value in the `data` array.
  fn start(&self, i: I) -> usize { u32_as_usize(self.idxs[i]) }

  /// The end index for the given value in the `data` array.
  fn end(&self, i: I) -> usize {
    match self.idxs.0.get(i.into_usize() + 1) {
      None => self.data.len(),
      Some(&b) => u32_as_usize(b)
    }
  }

  /// The start and end index for the given value in the `data` array.
  fn extent(&self, i: I) -> std::ops::Range<usize> { self.start(i)..self.end(i) }
}

impl<I: Idx, T> std::ops::Index<I> for ChunkVec<I, T> {
  type Output = [T];
  fn index(&self, i: I) -> &[T] { &self.data[self.extent(i)] }
}

impl<I: Idx, T, A: IntoIterator<Item = T>> FromIterator<A> for ChunkVec<I, T> {
  fn from_iter<J: IntoIterator<Item = A>>(iter: J) -> Self {
    let mut out = Self::default();
    for it in iter { out.push(it); }
    out
  }
}

/// The calling convention of a single argument.
#[allow(variant_size_differences)]
#[derive(Clone, Copy, Debug)]
pub enum ArgAbi {
  /// The value is not passed.
  Ghost,
  /// The value is passed in the given physical register.
  Reg(PReg, Size),
  /// The value is passed in a memory location.
  Mem {
    /// The offset in the `OUTGOING` slot to find the data.
    off: u32,
    /// The size of the data in bytes.
    sz: u32
  },
  /// A pointer to a value of the given size is passed in a physical register.
  /// Note: For return values with this ABI, this is an additional argument *to* the function:
  /// the caller passes a pointer to the return slot.
  Boxed {
    /// The register carrying the pointer.
    reg: PReg,
    /// The size of the pointed-to data in bytes.
    sz: u32
  },
  /// A pointer to the value is passed in memory. This is like `Boxed`,
  /// but for the case that we have run out of physical registers.
  /// (The pointer is at `off..off+8`, and the actual value is at `[off]..[off]+sz`.)
  /// Note: For return values with this ABI, this is an additional argument *to* the function:
  /// the caller puts a pointer to the return slot at this location in the outgoing slot.
  BoxedMem {
    /// The offset in the `OUTGOING` slot to find the pointer. (It has a fixed size of 8.)
    off: u32,
    /// The size of the data starting at the pointer location.
    sz: u32
  },
}

/// The representation of a monomorphized function's calling convention.
#[derive(Default, Debug)]
pub struct ProcAbi {
  /// The arguments of the procedure.
  pub args: Box<[ArgAbi]>,
  /// The return values of the procedure. (Functions and procedures return multiple values in MMC.)
  /// If None, then the function does not return.
  pub rets: Option<Box<[ArgAbi]>>,
  /// The total size of the stack-allocated incoming arguments in bytes
  pub args_space: u32,
  /// The registers that are clobbered by the call.
  pub clobbers: Box<[PReg]>,
}

/// A low level representation of a function, after instruction selection but before
/// register allocation.
#[derive(Debug)]
pub struct VCode<I> {
  pub(crate) abi: ProcAbi,
  pub(crate) insts: IdxVec<InstId, I>,
  pub(crate) block_map: HashMap<mir::BlockId, BlockId>,
  pub(crate) blocks: IdxVec<BlockId, (InstId, InstId)>,
  pub(crate) block_preds: IdxVec<BlockId, Vec<BlockId>>,
  pub(crate) block_succs: IdxVec<BlockId, Vec<BlockId>>,
  pub(crate) block_params: ChunkVec<BlockId, VReg>,
  pub(crate) operands: ChunkVec<InstId, Operand>,
  pub(crate) trace: Trace,
  pub(crate) num_vregs: usize,
  pub(crate) spills: IdxVec<SpillId, u32>,
}

impl<I> Default for VCode<I> {
  fn default() -> Self {
    Self {
      abi: Default::default(),
      insts: Default::default(),
      block_map: HashMap::new(),
      blocks: Default::default(),
      block_preds: Default::default(),
      block_succs: Default::default(),
      block_params: Default::default(),
      operands: Default::default(),
      trace: Default::default(),
      num_vregs: 0,
      spills: vec![0, 0].into(), // INCOMING, OUTGOING
    }
  }
}

impl<I> VCode<I> {
  /// Create a new unused `VReg`.
  #[must_use] pub fn fresh_vreg(&mut self) -> VReg {
    let v = VReg::new(self.num_vregs);
    self.num_vregs += 1;
    v
  }

  /// Create a new unused `SpillId`. (It is allowable to use size 0 here and grow it later with
  /// `grow_spill`.)
  pub fn fresh_spill(&mut self, sz: u32) -> SpillId { self.spills.push(sz) }

  /// Ensure that the given spill is at least the specified size.
  pub fn grow_spill(&mut self, n: SpillId, sz: u32) {
    let old = &mut self.spills[n];
    *old = (*old).max(sz)
  }

  /// Finalize a block. Must be called after each call to `new_block`,
  /// once all instructions of the block are emitted.
  pub fn finish_block(&mut self) {
    self.blocks.0.last_mut().expect("no blocks").1 = InstId::new(self.insts.len());
  }

  /// Make space in the outgoing argument stack region.
  pub fn mk_outgoing_spill(&mut self, sz: u32) {
    self.grow_spill(SpillId::OUTGOING, sz)
  }

  /// Add an edge in the CFG, from `from` to `to`.
  pub fn add_edge(&mut self, from: BlockId, to: BlockId) {
    self.block_succs[from].push(to);
    self.block_preds[to].push(from);
  }

  /// Start a new block, giving the list of block parameters.
  pub fn new_block(&mut self, params: impl IntoIterator<Item=VReg>) -> BlockId {
    let inst = InstId::new(self.insts.len());
    let bl = self.blocks.push((inst, inst));
    self.block_preds.push(vec![]);
    self.block_succs.push(vec![]);
    self.block_params.push(params.into_iter());
    bl
  }
}

impl<I: Inst> VCode<I> {
  /// Emit an instruction into the current block.
  pub fn emit(&mut self, inst: I) -> InstId {
    self.operands.push_into(|v| inst.collect_operands(v));
    self.insts.push(inst)
  }
}

impl<I> std::ops::Index<InstId> for VCode<I> {
  type Output = I;
  fn index(&self, i: InstId) -> &Self::Output { &self.insts[i] }
}
impl<I> std::ops::IndexMut<InstId> for VCode<I> {
  fn index_mut(&mut self, i: InstId) -> &mut Self::Output { &mut self.insts[i] }
}

impl<I: Inst> regalloc2::Function for VCode<I> {
  fn num_insts(&self) -> usize { self.insts.len() }
  fn num_blocks(&self) -> usize { self.blocks.len() }
  fn entry_block(&self) -> BlockId { BlockId::new(0) }

  fn block_insns(&self, block: BlockId) -> InstRange {
    let (from, to) = self.blocks[block];
    InstRange::forward(from, to)
  }

  fn block_succs(&self, block: BlockId) -> &[BlockId] { &self.block_succs[block] }
  fn block_preds(&self, block: BlockId) -> &[BlockId] { &self.block_preds[block] }
  fn block_params(&self, block: BlockId) -> &[regalloc2::VReg] {
    let ret = &self.block_params[block];
    // Safety: `VReg` is repr(transparent)
    unsafe { std::mem::transmute::<&[VReg], &[regalloc2::VReg]>(ret) }
  }

  fn is_ret(&self, insn: InstId) -> bool { self.insts[insn].is_ret() }
  fn is_branch(&self, insn: InstId) -> bool { self.insts[insn].is_branch() }

  fn branch_blockparams(&self, _: BlockId, insn: InstId, succ_idx: usize) -> &[regalloc2::VReg] {
    self.insts[insn].branch_blockparams(succ_idx)
  }

  fn is_move(&self, insn: InstId) -> Option<(Operand, Operand)> { self.insts[insn].is_move() }
  fn inst_operands(&self, insn: InstId) -> &[Operand] { &self.operands[insn] }
  fn inst_clobbers(&self, insn: InstId) -> &[regalloc2::PReg] {
    let ret = self.insts[insn].clobbers();
    // Safety: `PReg` is repr(transparent)
    unsafe { std::mem::transmute::<&[PReg], &[regalloc2::PReg]>(ret) }
  }
  fn num_vregs(&self) -> usize { self.num_vregs }
  fn spillslot_size(&self, _: regalloc2::RegClass) -> usize { 1 }
}
