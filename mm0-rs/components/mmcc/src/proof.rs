//! The proof objects constructed by the compiler.

use std::collections::HashMap;

use crate::regalloc::PCode;
use crate::types::classify;
use crate::types::vcode::ProcAbi;
use crate::{Idx, IdxVec, LinkedCode, Symbol, TEXT_START};
use crate::codegen::FUNCTION_ALIGN;
use crate::types::{mir::{self, Cfg, BlockTree}, vcode::ConstRef};

pub use mir::BlockId;
pub use crate::types::vcode::{ProcId, BlockId as VBlockId};
pub use crate::arch::{self, PReg, PInst as VInst, PRegMem};

/// If true, we are proving total correctness, so all recursions and loops
/// must come with a variant that decreases on recursive calls.
/// If false, then we are proving partial correctness, so variants are not required.
pub const VERIFY_TERMINATION: bool = true;

/// A constructed ELF file, which contains functions for extracting theorems about
/// the correctness of the parts of the file.
#[derive(Debug)]
pub struct ElfProof<'a> {
  code: &'a LinkedCode,
  /// The full ELF file.
  file: Box<[u8]>,
}

impl std::ops::Deref for ElfProof<'_> {
  type Target = [u8];
  fn deref(&self) -> &Self::Target { &self.file }
}

impl LinkedCode {
  /// Entry point for the proof object associated to the ELF file.
  #[must_use] pub fn proof(&self) -> ElfProof<'_> {
    let mut file = vec![];
    self.write_elf(&mut file).expect("impossible");
    ElfProof { code: self, file: file.into() }
  }
}

impl<'a> ElfProof<'a> {
  /// The ELF header.
  #[must_use] pub fn header(&self) -> &[u8] { &self[..0x40] }

  /// The program header.
  #[must_use] pub fn p_header(&self) -> &[u8] { &self[0x40..0x78] }

  /// The content of the program segment (the main body of the file).
  #[must_use] pub fn content(&self) -> &[u8] { &self[0x78..] }

  /// The entry point address.
  #[allow(clippy::unused_self)]
  #[must_use] pub fn entry(&self) -> u64 { TEXT_START.into() }

  /// The size of the segment in the file image.
  #[must_use] pub fn p_filesz(&self) -> u64 {
    u64::from_le_bytes(self[0x60..0x68].try_into().expect("impossible"))
  }

  /// The size of the segment in memory.
  #[must_use] pub fn p_memsz(&self) -> u64 {
    u64::from_le_bytes(self[0x68..0x70].try_into().expect("impossible"))
  }

  /// The size of the BSS section (zeroed data following the read-only section).
  #[must_use] pub fn bss(&self) -> u64 { self.p_memsz() - self.p_filesz() }

  /// The mapping from IDs to function names.
  #[must_use] pub fn func_names(&self) -> &'a IdxVec<ProcId, Symbol> { &self.code.func_names.1 }

  /// The mapping from IDs to function names.
  #[must_use] pub fn get_func(&self, f: Symbol) -> Option<ProcId> {
    self.code.func_names.0.get(&f).copied()
  }

  /// Get the ABI (calling convention) of a function.
  #[must_use] pub fn proc_abi(&self, id: ProcId) -> &'a ProcAbi { &self.code.func_abi[id] }

  /// An iterator over the assembled items (procedures and constants).
  #[must_use] pub fn assembly(&self) -> AssemblyItemIter<'_> {
    AssemblyItemIter {
      code: self.code,
      pos: TEXT_START,
      content: self.content(),
      state: AssemblyItemState::Init,
    }
  }

  /// An iterator over the functions, in function dependency order.
  #[must_use] pub fn proc_proofs(&self) -> ProcIter<'_> {
    ProcIter {
      code: self.code,
      content: self.content(),
      order: Some(self.code.postorder.iter()),
    }
  }

  /// Construct a proof item directly for a given function, or the init function.
  #[must_use] pub fn proof_item(&self, func: Option<ProcId>) -> Proc<'_> {
    self.code.proc_proof(self.content(), func)
  }
}

/// A decomposition of assembled results of the top level program items.
#[derive(Debug)]
pub enum AssemblyItem<'a> {
  /// Insert a block of bytes corresponding to a function.
  Proc(Proc<'a>),
  /// Insert a block of bytes corresponding to a constant.
  Const(Const<'a>),
}

impl<'a> AssemblyItem<'a> {
  /// The starting virtual address of the item being assembled.
  #[must_use] pub fn start(&self) -> u32 {
    match *self {
      AssemblyItem::Proc(ref proc) => proc.start,
      AssemblyItem::Const(ref data) => data.start,
    }
  }

  /// The byte slice in the file corresponding to the item being assembled.
  #[must_use] pub fn content(&self) -> &'a [u8] {
    match *self {
      AssemblyItem::Proc(ref proc) => proc.content,
      AssemblyItem::Const(ref data) => data.content,
    }
  }
}

#[derive(Debug)]
#[allow(variant_size_differences)]
enum AssemblyItemState<'a> {
  Init,
  Proc(ProcId),
  Const(std::slice::Iter<'a, Symbol>),
}

/// An iterator over the top level program items in assembly order (order in the file).
#[derive(Debug)]
pub struct AssemblyItemIter<'a> {
  code: &'a LinkedCode,
  pos: u32,
  content: &'a [u8],
  state: AssemblyItemState<'a>,
}

impl<'a> AssemblyItemIter<'a> {
  /// The virtual address at which the next item will start.
  #[must_use] pub fn pos(&self) -> u32 { self.pos }
  fn advance(&mut self, n: u32) -> &'a [u8] {
    let (left, right) = self.content.split_at(n.try_into().expect("impossible"));
    self.pos += n;
    self.content = right;
    left
  }

  fn padded_content(&mut self, len: u32) -> &'a [u8] {
    let aligned = (self.pos + len + FUNCTION_ALIGN - 1) & !(FUNCTION_ALIGN - 1);
    self.advance(aligned - self.pos)
  }
}

impl<'a> Iterator for AssemblyItemIter<'a> {
  type Item = AssemblyItem<'a>;
  fn next(&mut self) -> Option<Self::Item> {
    let start = self.pos;
    loop {
      match self.state {
        AssemblyItemState::Init => {
          self.state = AssemblyItemState::Proc(ProcId(0));
          return Some(AssemblyItem::Proc(Proc {
            code: self.code, cfg: &self.code.init.0, proc: &self.code.init.1,
            id: None,
            start,
            content: self.padded_content(self.code.init.1.len),
          }))
        }
        AssemblyItemState::Proc(n) => {
          if let Some((_, proc)) = self.code.funcs.get(n) {
            self.state = AssemblyItemState::Proc(ProcId(n.0 + 1));
            return Some(AssemblyItem::Proc(Proc {
              code: self.code,
              cfg: &self.code.mir[&self.code.func_names.1[n]].body,
              proc,
              id: Some(n),
              start,
              content: self.padded_content(proc.len),
            }))
          }
          self.state = AssemblyItemState::Const(self.code.consts.ordered.iter())
        }
        AssemblyItemState::Const(ref mut iter) => {
          let name = *iter.next()?;
          if let (size, ConstRef::Ptr(addr)) = self.code.consts.map[&name] {
            assert_eq!(TEXT_START + self.code.text_size + addr, self.pos);
            return Some(AssemblyItem::Const(Const {
              name,
              start,
              content: self.advance(size)
            }))
          }
          unreachable!()
        }
      }
    }
  }
  fn size_hint(&self) -> (usize, Option<usize>) { let n = self.len(); (n, Some(n)) }
}

impl ExactSizeIterator for AssemblyItemIter<'_> {
  fn len(&self) -> usize {
    match &self.state {
      AssemblyItemState::Init => self.code.funcs.len() + self.code.consts.ordered.len() + 1,
      AssemblyItemState::Proc(n) =>
        (self.code.funcs.len() - n.into_usize()) + self.code.consts.ordered.len(),
      AssemblyItemState::Const(it) => it.len(),
    }
  }
}

/// A constant that has been written to the read-only section.
#[derive(Debug)]
#[non_exhaustive]
pub struct Const<'a> {
  /// The name of this constant.
  pub name: Symbol,
  /// The starting virtual address of this constant.
  pub start: u32,
  /// The byte data stored for this constant.
  pub content: &'a [u8],
}

/// An iterator over the top level program items in proof order (function dependency order,
/// the order in which correctness theorems should be proved).
#[derive(Debug)]
pub struct ProcIter<'a> {
  code: &'a LinkedCode,
  content: &'a [u8],
  order: Option<std::slice::Iter<'a, ProcId>>,
}

impl<'a> Iterator for ProcIter<'a> {
  type Item = Proc<'a>;
  fn next(&mut self) -> Option<Self::Item> {
    let func = self.order.as_mut()?.next().copied();
    if func.is_none() { self.order = None }
    Some(self.code.proc_proof(self.content, func))
  }
  fn size_hint(&self) -> (usize, Option<usize>) { let n = self.len(); (n, Some(n)) }
}

impl ExactSizeIterator for ProcIter<'_> {
  fn len(&self) -> usize {
    match &self.order {
      Some(it) => it.len() + 1,
      None => 0
    }
  }
}

/// A correctness theorem for a function, or the init function.
#[derive(Clone, Copy, Debug)]
pub struct Proc<'a> {
  code: &'a LinkedCode,
  /// The corresponding CFG object in the MIR.
  pub cfg: &'a Cfg,
  proc: &'a PCode,
  /// The function being proven, or `None` for the init function.
  pub id: Option<ProcId>,
  /// The starting virtual address for the function.
  pub start: u32,
  /// The code of the function as a byte slice. Includes trailing padding.
  pub content: &'a [u8],
}

impl LinkedCode {
  fn proc_proof<'a>(&'a self, content: &'a [u8], id: Option<ProcId>) -> Proc<'a> {
    let (start, cfg, proc) = match id {
      Some(f) => {
        let (start, ref pc) = self.funcs[f];
        (start, &self.mir[&self.func_names.1[f]].body, pc)
      }
      None => (TEXT_START, &self.init.0, &self.init.1)
    };
    Proc {
      code: self, cfg, proc, id, start,
      content: &content[(start - TEXT_START) as usize..][..proc.len as usize],
    }
  }
}

impl<'a> Proc<'a> {
  /// The name of the function, or `None` for the init function.
  #[must_use] pub fn name(&self) -> Option<Symbol> {
    self.id.map(|id| self.code.func_names.1[id])
  }

  /// The size of the procedure with padding omitted.
  #[must_use] pub fn len_no_padding(&self) -> u32 { self.proc.len }

  /// The trailing padding of the procedure.
  #[must_use] pub fn trailing_padding(&self) -> &'a [u8] {
    &self.content[self.len_no_padding() as usize..]
  }

  /// The list of callee-saved regs that were pushed in the function prologue,
  /// and popped in the epilogue in reverse order.
  #[must_use] pub fn saved_regs(&self) -> &'a [PReg] {
    &self.proc.saved_regs
  }

  /// The stack size for the function, i.e. the number of bytes allocated for the local variables.
  /// Does not include the stack space for the return or the callee-saved regs.
  #[must_use] pub fn stack_size(&self) -> u32 {
    self.proc.stack_size
  }

  /// An iterator over the blocks of the procedure in assembly order.
  #[must_use] pub fn assembly_blocks(&self) -> AssemblyBlocks<'_> {
    AssemblyBlocks {
      ctx: self,
      iter: 0..self.proc.blocks.len(),
    }
  }
  /// Get the block by ID.
  #[must_use] pub fn block(&self, id: BlockId) -> BlockProof<'_> {
    BlockProof { ctx: self, id }
  }

  /// Get the physical block ID for a virtual block, or `None` for a pure virtual block.
  #[must_use] pub fn vblock_id(&self, id: BlockId) -> Option<VBlockId> {
    self.proc.block_map.get(&id).copied()
  }

  /// Get a (physical) block by block ID.
  #[must_use] pub fn vblock(&self, id: VBlockId) -> VBlock<'_> {
    VBlock::new(self, id.index())
  }

  /// The proof tree for the entry block.
  #[must_use] pub fn proof_tree(&self) -> BlockProofTree<'_> {
    BlockProofTree::new(self, &self.cfg.tree)
  }
}

/// An iterator over the blocks in a procedure in assembly order.
#[derive(Debug)]
pub struct AssemblyBlocks<'a> {
  ctx: &'a Proc<'a>,
  iter: std::ops::Range<usize>,
}

impl<'a> Iterator for AssemblyBlocks<'a> {
  type Item = VBlock<'a>;
  fn next(&mut self) -> Option<Self::Item> {
    Some(VBlock::new(self.ctx, self.iter.next()?))
  }
  fn size_hint(&self) -> (usize, Option<usize>) { let n = self.len(); (n, Some(n)) }
}

impl ExactSizeIterator for AssemblyBlocks<'_> {
  fn len(&self) -> usize { self.iter.len() }
}

/// A handle to an individual block in a procedure.
#[derive(Debug)]
pub struct VBlock<'a> {
  ctx: &'a Proc<'a>,
  /// The block ID of the block.
  pub id: VBlockId,
  /// The block ID of the corresponding logical block.
  pub mir_id: BlockId,
  /// The start of this block relative to the function start.
  pub start: u32,
  /// The byte data for this block.
  pub content: &'a [u8],
  /// The memory locations of variables that have been mapped.
  pub block_params: &'a [(mir::VarId, PRegMem)],
  /// The sequence of (physical) instructions in the block.
  pub insts: &'a [VInst],
}

impl<'a> VBlock<'a> {
  fn new(ctx: &'a Proc<'a>, id: usize) -> Self {
    let start = ctx.proc.block_addr.0[id];
    let end = ctx.proc.block_addr.0.get(id+1).copied().unwrap_or(ctx.proc.len);
    let id = VBlockId::from_usize(id);
    Self {
      ctx,
      mir_id: ctx.proc.blocks[id].0,
      id,
      start,
      content: &ctx.content[start as usize..end as usize],
      block_params: &ctx.proc.block_params[id],
      insts: ctx.proc.block_insts(id),
    }
  }

  /// An iterator over the instructions in the block.
  #[must_use] pub fn insts(&self) -> InstIter<'a> {
    InstIter {
      ctx: self.ctx,
      start: self.start,
      insts: self.insts.iter(),
    }
  }

  /// The underlying MIR block object.
  #[must_use] pub fn mir_block(&self) -> &'a mir::BasicBlock { &self.ctx.cfg.blocks[self.mir_id] }

  /// Calls a visitor on the MIR block and its physical counterpart.
  pub fn visit(&self, v: &mut impl classify::Visitor<'a>) {
    let funcs = &self.ctx.code.func_abi;
    let abi_rets = self.ctx.id.and_then(|id| funcs[id].rets.as_deref());
    let (mut iter, term) = self.ctx.proc.trace.iter(self.id, self.insts());
    let bl = self.mir_block();
    for (stmt, cl) in bl.stmts.iter().zip(&self.ctx.proc.trace.stmts[self.id]) {
      v.do_stmt(stmt, cl, &mut iter);
    }
    v.do_terminator(funcs, abi_rets, bl.terminator(), term, &mut iter);
  }
}

/// An iterator over the instructions in the block.
#[derive(Clone, Debug)]
pub struct InstIter<'a> {
  ctx: &'a Proc<'a>,
  start: u32,
  insts: std::slice::Iter<'a, VInst>,
}

impl<'a> Iterator for InstIter<'a> {
  type Item = Inst<'a>;
  fn next(&mut self) -> Option<Self::Item> {
    let inst = self.insts.next()?;
    let layout = inst.layout_inst();
    let start = self.start;
    self.start += u32::from(layout.len());
    Some(Inst { ctx: self.ctx, start, layout, inst })
  }
  fn size_hint(&self) -> (usize, Option<usize>) { let n = self.len(); (n, Some(n)) }
}
impl ExactSizeIterator for InstIter<'_> {
  fn len(&self) -> usize { self.insts.len() }
}

/// A reference to a physical instruction.
#[derive(Clone, Copy, Debug)]
pub struct Inst<'a> {
  ctx: &'a Proc<'a>,
  /// The address of the instruction relative to the function start.
  pub start: u32,
  /// The layout of the instruction.
  pub layout: arch::InstLayout,
  /// The physical instruction
  pub inst: &'a VInst,
}

impl<'a> Inst<'a> {
  /// The byte data for this instruction.
  #[must_use] pub fn content(&self) -> &'a [u8] {
    &self.ctx.content[self.start as usize..][..self.layout.len() as usize]
  }
}

/// A tree-structured proof of correctness of a block.
///
/// The idea here is that most blocks only jump downward, so we can prove
/// the correctness of blocks from the bottom up, i.e. if a later block
/// terminates successfully then a block that does something and then goes to
/// the later block also terminates successfully, but some blocks,
/// in particular loops and labels, participate in cycles, and the front end
/// associates decreasing variants to back edges in these cycles.
/// This enables a proof strategy where we perform an induction proof at each
/// cycle, with the inductive hypothesis acting as a label that we can later
/// jump to.
///
/// For example, suppose we have a CFG like so:
/// ```text
///  .>...  .-> C---\     __
/// |      /        v    v  \
/// A --> B -> D -> E -> F -^
/// ^                    v
///  \------------------ G
/// ```
/// An example of code that would cause a CFG like this is:
/// ```text
/// while A variant v1 {
///   if B { C } else { D }
///   E;
///   while F variant v2 {
///     continue (h: v2' < v2)
///   }
///   G;
///   continue (h: v1' < v1)
/// }
/// ```
/// The back-edges are `F -> F` and `G -> A` here, marked in the code using
/// explicit `continue` calls. In MMC, these `continue` calls carry variants,
/// so we can be sure that the variant decreases each time around the loop.
/// Thus we obtain the following proof sketch:
///
/// ```text
/// 0.  running ... is ok
/// 1.  | Assume: running A with v1 < n is ok
/// 2.  | running G is ok, by (1)
/// 3.  | | Assume: running F with v2 < m is ok
/// 4.  | | running F with v2 = m is ok by (3)
/// 5.  | running F is ok by (4) and induction on m
/// 6.  | running E is ok by (5)
/// 7.  | running D is ok by (6)
/// 8.  | running C is ok by (6)
/// 9.  | running B is ok by (7, 8)
/// 10. | running A is ok with v1 = n by (0, 9)
/// 11. running A is ok by (10) and induction on n
/// ```
///
/// In general, we either prove that a block is ok because all its successors
/// are ok (and the code in the block itself is ok), or we do an induction
/// on the variant value in the case where this node has a back-edge pointing
/// to it. Inductions can be nested, like in this case, and they can also be
/// mutual inductions, where we assume that calling multiple blocks is okay for
/// some shared variant value (this comes up when proving programs using a
/// label group with multiple labels).
#[derive(Clone, Debug)]
pub enum BlockProofTree<'a> {
  /// A proof by induction.
  Induction(&'a [BlockId], BlockTreeSeq<'a>),
  /// A sequence of block proofs in dependency order.
  Seq(BlockTreeSeq<'a>),
  /// A single block proof.
  One(BlockProof<'a>),
}

impl<'a> BlockProofTree<'a> {
  fn new(ctx: &'a Proc<'a>, bt: &'a BlockTree) -> Self {
    match bt {
      BlockTree::LabelGroup(data) => Self::Induction(&data.0, BlockTreeSeq {
        ctx,
        args: &data.1,
      }),
      BlockTree::Many(args) => Self::Seq(BlockTreeSeq { ctx, args }),
      &BlockTree::One(id) => Self::One(ctx.block(id)),
    }
  }

  fn develop(ctx: &'a Proc<'a>, mut id: BlockId, stack: &mut Vec<(bool, BlockId)>) -> BlockId {
    loop {
      match *ctx.cfg[id].terminator() {
        mir::Terminator::Jump(..) |
        mir::Terminator::Return(..) |
        mir::Terminator::Unreachable(_) |
        mir::Terminator::Exit(_) |
        mir::Terminator::Dead |
        mir::Terminator::Call { reach: false, .. } |
        mir::Terminator::Assert(_, _, false, _) => return id,
        mir::Terminator::Jump1(tgt) |
        mir::Terminator::Assert(_, _, _, tgt) |
        mir::Terminator::Call { tgt, .. } => stack.push((true, std::mem::replace(&mut id, tgt))),
        mir::Terminator::If(_, [(_, bl1), (_, bl2)]) => {
          stack.push((true, std::mem::replace(&mut id, bl1)));
          stack.push((false, std::mem::replace(&mut id, bl2)));
        }
      }
    }
  }

  // fn one(ctx: &'a Proc<'a>, id: BlockId) -> Self {
  //   let mut stack = vec![];
  //   let id = Self::develop(ctx, id, &mut stack);
  //   if stack.is_empty() {
  //     Self::One(BlockProof { ctx, id })
  //   } else {
  //     stack.push((true, id));
  //     Self::Seq(BlockTreeIter { ctx, seq: [].iter(), stack })
  //   }
  // }
}

/// An iterator over block tree proofs, in forward dependency order
/// (i.e. working backward from the end of the function).
#[derive(Clone, Copy, Debug)]
pub struct BlockTreeSeq<'a> {
  ctx: &'a Proc<'a>,
  args: &'a [mir::BlockTree],
}

impl<'a> BlockTreeSeq<'a> {
  /// Get the root block of the proof tree.
  #[must_use] pub fn main(&self) -> BlockProofTree<'a> {
    BlockProofTree::new(self.ctx, &self.args[0])
  }

  /// Get the sequence of dependencies, in dependency order.
  #[must_use] pub fn deps(&self) -> BlockTreeIter<'a> {
    BlockTreeIter {
      ctx: self.ctx,
      seq: self.args[1..].iter(),
      stack: vec![],
    }
  }

  /// Get the sequence of dependencies, including the root, in dependency order.
  #[must_use] pub fn deps_full(&self) -> BlockTreeIter<'a> {
    BlockTreeIter {
      ctx: self.ctx,
      seq: self.args.iter(),
      stack: vec![],
    }
  }
}

/// An iterator over block tree proofs, in forward dependency order
/// (i.e. working backward from the end of the function).
#[derive(Clone, Debug)]
pub struct BlockTreeIter<'a> {
  ctx: &'a Proc<'a>,
  seq: std::slice::Iter<'a, mir::BlockTree>,
  stack: Vec<(bool, BlockId)>,
}

impl<'a> Iterator for BlockTreeIter<'a> {
  type Item = BlockProofTree<'a>;
  fn next(&mut self) -> Option<Self::Item> {
    if let Some((developed, bl)) = self.stack.pop() {
      Some(BlockProofTree::One(self.ctx.block(
        if developed { bl } else { BlockProofTree::develop(self.ctx, bl, &mut self.stack) }
      )))
    } else {
      Some(BlockProofTree::new(self.ctx, self.seq.next_back()?))
    }
  }
}

/// A proof for an individual block.
#[derive(Copy, Clone, Debug)]
pub struct BlockProof<'a> {
  ctx: &'a Proc<'a>,
  /// The block ID.
  pub id: BlockId,
}

impl<'a> BlockProof<'a> {
  /// The underlying MIR block object.
  #[must_use] pub fn block(&self) -> &'a mir::BasicBlock { &self.ctx.cfg.blocks[self.id] }

  /// The physical block associated to this proof, or `None` if this is a virtual-only block.
  #[must_use] pub fn vblock(&self) -> Option<VBlock<'a>> {
    Some(self.ctx.vblock(self.ctx.vblock_id(self.id)?))
  }
}

impl ElfProof<'_> {
  /// Check that an `ElfProof` object is valid.
  #[allow(clippy::unwrap_used)]
  pub fn validate(&self) {
    // basicElf_ok
    assert!(self.p_filesz() <= self.p_memsz());
    assert!(self.p_filesz() == u64::try_from(self.content().len()).unwrap());
    assert!(!self.content().is_empty());

    // assemble
    let mut init = None;
    let mut procs = IdxVec::<ProcId, _>::new();
    let mut consts = HashMap::new();
    let mut pos = TEXT_START;
    for item in self.assembly() {
      assert!(pos == item.start() && !item.content().is_empty());
      pos += u32::try_from(item.content().len()).unwrap();
      match item {
        AssemblyItem::Proc(code) => {
          match code.id {
            None => { assert!(init.is_none()); init = Some(code) }
            Some(p) => assert!(procs.push(code) == p),
          }
          assert!(!code.trailing_padding().len() < 16)
        }
        AssemblyItem::Const(data) =>
          assert!(consts.insert(data.start, data.content).is_none()),
      }
    }
    assert!(u64::from(pos) == self.p_filesz());
    let _init = init.unwrap();

    for item in self.proc_proofs() {
      item.proof_tree().validate(&mut Default::default());
      // assert!(start == item.start() && std::ptr::eq(code, item.content()));
    }
  }
}

impl BlockTreeSeq<'_> {
  #[allow(clippy::unwrap_used)]
  fn validate(self, ctx: &mut im::HashMap<BlockId, bool>) {
    for tr in self.deps() { tr.validate(ctx) }
    self.main().validate(ctx)
  }
}

impl BlockProofTree<'_> {
  #[allow(clippy::unwrap_used)]
  fn validate(self, ctx: &mut im::HashMap<BlockId, bool>) {
    match self {
      BlockProofTree::Induction(labs, seq) => {
        let mut iter = seq.deps_full();
        let mut ctx2 = ctx.clone();
        for &l in labs { assert!(ctx2.insert(l, true).is_none()) }
        'todo: for &tgt in labs.iter().rev() {
          loop {
            let tr = iter.next().unwrap();
            let ok = matches!(tr, BlockProofTree::One(bl) if bl.id == tgt);
            tr.validate(&mut ctx2);
            if ok { continue 'todo }
          }
        }
        assert!(iter.next().is_none());
        for &l in labs { assert!(ctx.insert(l, false).is_none()) }
      }
      BlockProofTree::Seq(seq) => seq.validate(ctx),
      BlockProofTree::One(bl) => {
        bl.validate(ctx);
        assert!(ctx.insert(bl.id, false).is_none());
      }
    }
  }
}

impl<'a> BlockProof<'a> {
  fn validate(&self, ctx: &im::HashMap<BlockId, bool>) {
    loop {
      match *self.ctx.cfg[self.id].terminator() {
        mir::Terminator::Jump(bl, _, ref var) => assert!(ctx[&bl] == var.is_some()),
        mir::Terminator::Return(..) |
        mir::Terminator::Unreachable(_) |
        mir::Terminator::Exit(_) |
        mir::Terminator::Dead |
        mir::Terminator::Call { reach: false, .. } |
        mir::Terminator::Assert(_, _, false, _) => {}
        mir::Terminator::Jump1(tgt) |
        mir::Terminator::Assert(_, _, _, tgt) |
        mir::Terminator::Call { tgt, .. } => self.ctx.block(tgt).validate(ctx),
        mir::Terminator::If(_, [(_, bl1), (_, bl2)]) => {
          self.ctx.block(bl1).validate(ctx);
          self.ctx.block(bl2).validate(ctx);
        }
      }
    }
  }
}
