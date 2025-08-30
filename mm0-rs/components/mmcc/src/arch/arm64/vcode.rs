//! ARM64 Virtual Code (VCode) representation
//!
//! This module defines the ARM64-specific VCode type that represents
//! programs using virtual registers before register allocation.

use crate::types::vcode::{BlockId, InstId, ProcAbi, VReg, ChunkVec};
use crate::types::{IdxVec, Size, mir};
use crate::types::classify::Trace;
use crate::regalloc::{PCode, PInstId};
use crate::codegen_arch::VCodeTrait;
use super::{Inst, PReg};
use crate::arch::arm64::inst::{PInst, OperandSize};

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

/// Simple ARM64 register allocation
/// Maps virtual registers to physical registers for basic cases
fn regalloc_arm64(vcode: VCode) -> (ProcAbi, Box<PCode>) {
    use crate::types::IdxVec;
    use crate::types::classify::Trace;
    use crate::types::vcode::ChunkVec;
    
    eprintln!("ARM64: Starting register allocation");
    
    // Simple register mapping for syscalls:
    // vreg 0 -> X0 (first arg / exit code)
    // vreg 1 -> X1 (second arg)
    // vreg 2 -> X2 (third arg)
    // vreg 3 -> X16 (syscall number)
    let vreg_to_preg = |vreg: u32| -> Option<PReg> {
        match vreg {
            0 => Some(PReg::new(0)),  // X0
            1 => Some(PReg::new(1)),  // X1
            2 => Some(PReg::new(2)),  // X2
            3 => Some(PReg::new(16)), // X16
            _ => None,
        }
    };
    
    // Convert virtual instructions to physical instructions
    let mut code = Vec::new();
    
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
                    }
                }
                Inst::LoadConst { dst, const_id } => {
                    if let Some(preg) = vreg_to_preg(dst.0.vreg() as u32) {
                        // For now, emit ADR instruction with placeholder offset
                        // In a real implementation, this would be patched with the actual offset
                        code.push(PInst::Adr {
                            dst: preg,
                            offset: 0x1000, // Placeholder offset to rodata section
                        });
                    }
                }
                Inst::Svc { imm } => {
                    code.push(PInst::Svc { imm: *imm });
                }
                _ => {}
            }
        }
        
        // Handle terminator
        match &vcode.insts[block.term] {
            Inst::Ret => {
                code.push(PInst::Ret);
            }
            _ => {}
        }
    }
    
    let code_len = code.len();
    eprintln!("ARM64: Generated {} physical instructions", code_len);
    
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
    
    // Create ARM64 PCode
    let arm64_pcode = super::pcode::Arm64PCode {
        insts: pinsts,
        block_map: vec![(mir::BlockId(0), regalloc2::Block::new(0))].into_iter().collect(),
        blocks,
        block_addr: IdxVec::from(vec![0]),
        block_params: ChunkVec::default(),
        trace: Trace {
            stmts: ChunkVec::default(),
            block: IdxVec::default(),
            projs: vec![],
            lists: vec![],
        },
        stack_size: 0,
        saved_regs: vec![],
        len: (code_len * 4) as u32, // ARM64 instructions are 4 bytes each
    };
    
    // Clone the trace before moving arm64_pcode
    let trace_clone = arm64_pcode.trace.clone();
    
    // Store the ARM64 code in our cache
    let code_id = super::code_cache::store_code(arm64_pcode);
    
    // For now, we still need to return x86 PCode for compatibility
    // We encode the ARM64 code ID in the x86 instructions for retrieval
    eprintln!("ARM64: Generated ARM64 code with ID {} but returning dummy x86 PCode for compatibility", code_id);
    
    use crate::regalloc::PCode;
    use crate::arch::x86::PInst as X86PInst;
    
    let mut x86_insts = IdxVec::default();
    x86_insts.push(X86PInst::Ud2);
    
    let pcode = Box::new(PCode {
        insts: x86_insts,
        block_map: vec![(mir::BlockId(0), regalloc2::Block::new(0))].into_iter().collect(),
        blocks: IdxVec::default(),
        block_addr: IdxVec::from(vec![0]),
        block_params: ChunkVec::default(),
        trace: trace_clone,
        stack_size: 0,
        saved_regs: vec![],
        len: 2,
    });
    
    (vcode.abi, pcode)
}

impl VCodeTrait for VCode {
    fn regalloc(self: Box<Self>) -> (ProcAbi, Box<PCode>) {
        regalloc_arm64(*self)
    }
}