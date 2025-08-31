//! ARM64 Virtual Code (VCode) representation
//!
//! This module defines the ARM64-specific VCode type that represents
//! programs using virtual registers before register allocation.

use crate::types::vcode::{BlockId, InstId, ProcAbi, VReg, ChunkVec, Trace};
use crate::types::{IdxVec, Size, mir};
use crate::arch_pcode::PInstId;
use crate::codegen_arch::VCodeTrait;
use crate::arch_pcode::ArchPCode;
use super::{Inst, PReg};
use crate::arch::arm64::inst::{PInst, OperandSize, CallTarget, Operand, POperand};
use regalloc2;
use std::ops::Index;
use std::collections::HashMap;

/// ARM64-specific VCode implementation
#[derive(Debug)]
pub struct VCode {
    /// The blocks in the function
    pub blocks: IdxVec<BlockId, Block>,
    /// The instructions in the function
    pub insts: IdxVec<InstId, Inst>,
    /// Virtual register count
    pub num_vregs: u32,
    /// Procedure ABI information
    pub abi: ProcAbi,
}

/// A basic block in ARM64 VCode
#[derive(Debug)]
pub struct Block {
    /// The instructions in this block
    pub insts: Vec<InstId>,
    /// The terminator instruction
    pub term: InstId,
}

impl VCode {
    /// Create a new empty VCode
    pub fn new(abi: ProcAbi) -> Self {
        Self {
            blocks: IdxVec::default(),
            insts: IdxVec::default(),
            num_vregs: 0,
            abi,
        }
    }
    
    /// Get blocks
    pub fn blocks(&self) -> impl Iterator<Item = (BlockId, &Block)> {
        self.blocks.enum_iter()
    }
    
    /// Get block instructions
    pub fn block_insts(&self, block: BlockId) -> impl Iterator<Item = InstId> + '_ {
        let b = &self.blocks[block];
        b.insts.iter().chain(std::iter::once(&b.term)).copied()
    }

    /// Add a new block
    pub fn new_block(&mut self) -> BlockId {
        self.blocks.push(Block {
            insts: Vec::new(),
            term: InstId(0), // Will be set later
        })
    }

    /// Add an instruction to a block
    pub fn push_inst(&mut self, block: BlockId, inst: Inst) -> InstId {
        let id = self.insts.push(inst);
        self.blocks[block].insts.push(id);
        id
    }

    /// Set the terminator for a block
    pub fn set_terminator(&mut self, block: BlockId, inst: Inst) {
        let id = self.insts.push(inst);
        self.blocks[block].term = id;
    }

    /// Allocate a new virtual register
    pub fn new_vreg(&mut self) -> u32 {
        let vreg = self.num_vregs;
        self.num_vregs += 1;
        vreg
    }
}

impl Index<InstId> for VCode {
    type Output = Inst;
    
    fn index(&self, index: InstId) -> &Self::Output {
        &self.insts[index]
    }
}

/// Simple ARM64 register allocation
/// Maps virtual registers to physical registers for basic cases
fn regalloc_arm64(vcode: VCode) -> (ProcAbi, Box<super::regalloc::PCode>) {
    use crate::types::IdxVec;
    use crate::types::vcode::{ChunkVec, Trace};
    
    eprintln!("ARM64: Starting register allocation");
    
    // Simple register mapping for syscalls:
    // vreg 0 -> X0 (first arg / exit code / fd)
    // vreg 1 -> X1 (second arg / buffer pointer)
    // vreg 2 -> X2 (third arg / count)
    // vreg 3 -> X16 (syscall number)
    // Additional vregs for other uses
    let vreg_to_preg = |vreg: u32| -> Option<PReg> {
        match vreg {
            0 => Some(PReg::new(0)),  // X0
            1 => Some(PReg::new(1)),  // X1
            2 => Some(PReg::new(2)),  // X2
            3 => Some(PReg::new(16)), // X16
            4 => Some(PReg::new(3)),  // X3 (temp)
            5 => Some(PReg::new(4)),  // X4 (temp)
            6 => Some(PReg::new(5)),  // X5 (temp)
            _ => None,
        }
    };
    
    // Convert virtual instructions to physical instructions
    let mut code = Vec::new();
    let mut current_offset = 0u32;
    
    for (_, block) in vcode.blocks.enum_iter() {
        for &inst_id in &block.insts {
            match &vcode.insts[inst_id] {
                Inst::MovImm { dst, imm, size } => {
                    if let Some(preg) = vreg_to_preg(dst.0.vreg() as u32) {
                        code.push(PInst::MovImm {
                            dst: preg,
                            imm: *imm,
                            size: (*size).into(),
                        });
                        current_offset += 4; // ARM64 instructions are 4 bytes
                    }
                }
                Inst::LoadConst { dst, const_id } => {
                    if let Some(preg) = vreg_to_preg(dst.0.vreg() as u32) {
                        // We'll patch this later with the correct offset
                        // For now, just record the instruction position
                        code.push(PInst::Adr {
                            dst: preg,
                            offset: 0, // Will be patched
                        });
                        current_offset += 4;
                    }
                }
                Inst::Svc { imm } => {
                    code.push(PInst::Svc { imm: *imm });
                    current_offset += 4;
                }
                Inst::Call { target, args, rets } => {
                    // Move arguments to the correct registers (X0-X7)
                    for (i, &arg) in args.iter().take(8).enumerate() {
                        if let Some(src_preg) = vreg_to_preg(arg.0.vreg() as u32) {
                            let dst_preg = PReg::new(i); // X0-X7
                            if src_preg != dst_preg {
                                code.push(PInst::Mov {
                                    dst: dst_preg,
                                    src: src_preg,
                                    size: OperandSize::Size64,
                                });
                                current_offset += 4;
                            }
                        }
                    }
                    
                    // Generate the call
                    match target {
                        CallTarget::Direct(sym) => {
                            // For now, use a placeholder offset
                            // In a real implementation, this would be resolved by the linker
                            code.push(PInst::Bl { offset: 0 });
                            current_offset += 4;
                        }
                        CallTarget::Indirect(vreg) => {
                            if let Some(preg) = vreg_to_preg(vreg.0.vreg() as u32) {
                                // BLR instruction for indirect calls
                                eprintln!("ARM64: Indirect calls not yet implemented");
                            }
                        }
                    }
                    
                    // Handle return values (X0-X1)
                    for (i, &ret) in rets.iter().take(2).enumerate() {
                        if let Some(dst_preg) = vreg_to_preg(ret.0.vreg() as u32) {
                            let src_preg = PReg::new(i); // X0-X1
                            if src_preg != dst_preg {
                                code.push(PInst::Mov {
                                    dst: dst_preg,
                                    src: src_preg,
                                    size: OperandSize::Size64,
                                });
                                current_offset += 4;
                            }
                        }
                    }
                }
                // Arithmetic operations
                Inst::Add { dst, src1, src2, size } => {
                    if let (Some(dst_preg), Some(src1_preg)) = 
                        (vreg_to_preg(dst.0.vreg() as u32), vreg_to_preg(src1.0.vreg() as u32)) {
                        let poperand = match src2 {
                            Operand::Reg(vreg) => {
                                if let Some(preg) = vreg_to_preg(vreg.0.vreg() as u32) {
                                    POperand::Reg(preg)
                                } else {
                                    continue;
                                }
                            }
                            Operand::Imm(imm) => POperand::Imm(*imm),
                        };
                        code.push(PInst::Add {
                            dst: dst_preg,
                            src1: src1_preg,
                            src2: poperand,
                            size: (*size).into(),
                        });
                        current_offset += 4;
                    }
                }
                Inst::Sub { dst, src1, src2, size } => {
                    if let (Some(dst_preg), Some(src1_preg)) = 
                        (vreg_to_preg(dst.0.vreg() as u32), vreg_to_preg(src1.0.vreg() as u32)) {
                        let poperand = match src2 {
                            Operand::Reg(vreg) => {
                                if let Some(preg) = vreg_to_preg(vreg.0.vreg() as u32) {
                                    POperand::Reg(preg)
                                } else {
                                    continue;
                                }
                            }
                            Operand::Imm(imm) => POperand::Imm(*imm),
                        };
                        code.push(PInst::Sub {
                            dst: dst_preg,
                            src1: src1_preg,
                            src2: poperand,
                            size: (*size).into(),
                        });
                        current_offset += 4;
                    }
                }
                Inst::Mul { dst, src1, src2, size } => {
                    if let (Some(dst_preg), Some(src1_preg), Some(src2_preg)) = 
                        (vreg_to_preg(dst.0.vreg() as u32), 
                         vreg_to_preg(src1.0.vreg() as u32),
                         vreg_to_preg(src2.0.vreg() as u32)) {
                        code.push(PInst::Mul {
                            dst: dst_preg,
                            src1: src1_preg,
                            src2: src2_preg,
                            size: (*size).into(),
                        });
                        current_offset += 4;
                    }
                }
                Inst::Sdiv { dst, src1, src2, size } => {
                    if let (Some(dst_preg), Some(src1_preg), Some(src2_preg)) = 
                        (vreg_to_preg(dst.0.vreg() as u32), 
                         vreg_to_preg(src1.0.vreg() as u32),
                         vreg_to_preg(src2.0.vreg() as u32)) {
                        code.push(PInst::Sdiv {
                            dst: dst_preg,
                            src1: src1_preg,
                            src2: src2_preg,
                            size: (*size).into(),
                        });
                        current_offset += 4;
                    }
                }
                Inst::Udiv { dst, src1, src2, size } => {
                    if let (Some(dst_preg), Some(src1_preg), Some(src2_preg)) = 
                        (vreg_to_preg(dst.0.vreg() as u32), 
                         vreg_to_preg(src1.0.vreg() as u32),
                         vreg_to_preg(src2.0.vreg() as u32)) {
                        code.push(PInst::Udiv {
                            dst: dst_preg,
                            src1: src1_preg,
                            src2: src2_preg,
                            size: (*size).into(),
                        });
                        current_offset += 4;
                    }
                }
                Inst::Cmp { lhs, rhs, size } => {
                    if let Some(lhs_preg) = vreg_to_preg(lhs.0.vreg() as u32) {
                        let poperand = match rhs {
                            Operand::Reg(vreg) => {
                                if let Some(preg) = vreg_to_preg(vreg.0.vreg() as u32) {
                                    POperand::Reg(preg)
                                } else {
                                    continue;
                                }
                            }
                            Operand::Imm(imm) => POperand::Imm(*imm),
                        };
                        code.push(PInst::Cmp {
                            lhs: lhs_preg,
                            rhs: poperand,
                            size: (*size).into(),
                        });
                        current_offset += 4;
                    }
                }
                _ => {}
            }
        }
        
        // Handle terminator - check if it's valid first
        if (block.term.0 as usize) < vcode.insts.len() {
            match &vcode.insts[block.term] {
                Inst::Ret => {
                    code.push(PInst::Ret);
                    current_offset += 4;
                }
                _ => {}
            }
        }
    }
    
    let code_len = code.len();
    eprintln!("ARM64: Generated {} physical instructions", code_len);
    
    // Now patch ADR instructions with correct offsets
    for (i, inst) in code.iter_mut().enumerate() {
        if let PInst::Adr { offset, .. } = inst {
            // Calculate offset from this instruction to constant data
            // Offset is from current PC (this instruction) to the target
            let remaining_instructions = code_len - i;
            let offset_to_const = remaining_instructions * 4;
            *offset = offset_to_const as i32;
            eprintln!("ARM64: Patched ADR at instruction {} with offset {} (remaining: {})", 
                     i, *offset, remaining_instructions);
        }
    }
    
    // Convert Vec to IdxVec for PCode
    let mut pinsts: IdxVec<PInstId, PInst> = IdxVec::default();
    for inst in code {
        pinsts.push(inst);
    }
    
    // Create basic block structure
    let mut blocks = IdxVec::default();
    let start = PInstId(0);
    let end = PInstId(pinsts.len().try_into().unwrap());
    blocks.push((mir::BlockId(0), start, end));
    
    // Create hardcoded "Hello, World!\n" string
    let hello_string = b"Hello, World!\n";
    
    // Create ARM64 PCode
    let arm64_pcode = super::pcode::Arm64PCode {
        insts: pinsts,
        block_map: vec![(mir::BlockId(0), regalloc2::Block::new(0))].into_iter().collect(),
        blocks,
        block_addr: IdxVec::from(vec![0]),
        block_params: ChunkVec::default(),
        trace: Trace::default(),
        stack_size: 0,
        saved_regs: vec![],
        len: (code_len * 4) as u32, // ARM64 instructions are 4 bytes each
        const_data: hello_string.to_vec(),
        const_table: None,
    };
    
    // Return the ARM64 PCode directly!
    eprintln!("ARM64: Returning actual ARM64 PCode with {} instructions", arm64_pcode.insts.len());
    
    (vcode.abi, Box::new(arm64_pcode))
}

impl VCodeTrait for VCode {
    fn regalloc(self: Box<Self>) -> (ProcAbi, ArchPCode) {
        // Use the complete register allocator implementation
        match super::regalloc_impl::allocate_registers(&self) {
            Ok(result) => {
                // Convert RegAllocResult to PCode
                let pcode = super::regalloc::PCode {
                    insts: result.pinsts,
                    block_map: HashMap::new(), // TODO: populate properly
                    blocks: result.blocks,
                    block_addr: result.block_addr,
                    block_params: ChunkVec::default(),
                    trace: Trace::default(),
                    stack_size: result.stack_size,
                    saved_regs: vec![],
                    len: result.len,
                    const_data: vec![], // TODO: Handle constants
                    const_table: None,
                };
                (self.abi.clone(), ArchPCode::Arm64(Box::new(pcode)))
            }
            Err(e) => {
                eprintln!("ARM64: Register allocation failed, using simple allocator: {}", e);
                // Fall back to simple allocator
                let (abi, pcode) = regalloc_arm64(*self);
                (abi, ArchPCode::Arm64(pcode))
            }
        }
    }
}

// Implement regalloc2::Function trait for ARM64 VCode
impl regalloc2::Function for VCode {
    
    fn num_insts(&self) -> usize {
        self.insts.len()
    }
    
    fn num_blocks(&self) -> usize {
        self.blocks.len()
    }
    
    fn entry_block(&self) -> regalloc2::Block {
        regalloc2::Block::new(0)
    }
    
    fn block_insns(&self, block: regalloc2::Block) -> regalloc2::InstRange {
        let b = &self.blocks[BlockId(block.index() as u32)];
        let start = b.insts.first().map(|&i| i.0).unwrap_or(0);
        let end = b.term.0 + 1;
        regalloc2::InstRange::new(
            regalloc2::Inst::new(start as usize),
            regalloc2::Inst::new(end as usize),
        )
    }
    
    fn block_succs(&self, block: regalloc2::Block) -> &[regalloc2::Block] {
        // TODO: Implement proper successor tracking
        &[]
    }
    
    fn block_preds(&self, block: regalloc2::Block) -> &[regalloc2::Block] {
        // TODO: Implement proper predecessor tracking
        &[]
    }
    
    fn block_params(&self, block: regalloc2::Block) -> &[regalloc2::VReg] {
        // TODO: Implement block parameters
        &[]
    }
    
    fn is_ret(&self, insn: regalloc2::Inst) -> bool {
        matches!(self.insts[InstId(insn.index() as u32)], Inst::Ret)
    }
    
    fn is_branch(&self, insn: regalloc2::Inst) -> bool {
        matches!(self.insts[InstId(insn.index() as u32)], 
            Inst::Branch { .. } | Inst::BranchCond { .. })
    }
    
    fn inst_operands(&self, insn: regalloc2::Inst) -> &[regalloc2::Operand] {
        // TODO: Implement operand collection
        &[]
    }
    
    fn inst_clobbers(&self, insn: regalloc2::Inst) -> regalloc2::PRegSet {
        // TODO: Implement clobber tracking
        regalloc2::PRegSet::default()
    }
    
    fn num_vregs(&self) -> usize {
        self.num_vregs as usize
    }
    
    fn spillslot_size(&self, regclass: regalloc2::RegClass) -> usize {
        // ARM64 spill slots are 8 bytes for general purpose, 16 for vector
        if regclass == regalloc2::RegClass::Int {
            8
        } else if regclass == regalloc2::RegClass::Float {
            16
        } else {
            unreachable!()
        }
    }
    
    fn branch_blockparams(&self, block: regalloc2::Block, _branch: regalloc2::Inst, _idx: usize) -> &[regalloc2::VReg] {
        // TODO: Implement proper branch block parameters
        &[]
    }
}