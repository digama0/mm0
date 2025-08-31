//! WASM VCode trait implementations
//!
//! This module implements the necessary traits for WASM VCode to integrate
//! with the compiler pipeline, particularly the regalloc2::Function trait.

use super::vcode::VCode;
use super::WasmInst;
use crate::types::vcode::{BlockId, InstId};
use regalloc2;

// Implement regalloc2::Function trait for WASM VCode
// Note: WASM doesn't actually need register allocation since it's a stack machine,
// but we need this trait to integrate with the compiler pipeline
impl regalloc2::Function for VCode {
    fn num_insts(&self) -> usize {
        self.insts.len()
    }
    
    fn num_blocks(&self) -> usize {
        self.blocks.len()
    }
    
    fn entry_block(&self) -> regalloc2::Block {
        regalloc2::Block(0)
    }
    
    fn block_insns(&self, block: regalloc2::Block) -> regalloc2::InstRange {
        let b = &self.blocks[BlockId(block.0 as u32)];
        regalloc2::InstRange::new(
            regalloc2::Inst(b.start.0 as usize),
            regalloc2::Inst(b.end.0 as usize),
        )
    }
    
    fn block_succs(&self, block: regalloc2::Block) -> &[regalloc2::Block] {
        // Extract successors from the last instruction of the block
        let b = &self.blocks[BlockId(block.0 as u32)];
        if b.start == b.end {
            return &[];
        }
        
        let last_inst = InstId(b.end.0 - 1);
        match &self.insts[last_inst] {
            WasmInst::Branch { target } => {
                // This is a hack - we need to store successors properly
                // For now, assume sequential blocks
                &[]
            }
            WasmInst::BranchIf { target } => {
                // Conditional branch has two successors
                &[]
            }
            _ => &[],
        }
    }
    
    fn block_preds(&self, block: regalloc2::Block) -> &[regalloc2::Block] {
        // WASM doesn't track predecessors explicitly
        // This would need to be computed during lowering
        &[]
    }
    
    fn block_params(&self, block: regalloc2::Block) -> &[regalloc2::VReg] {
        // WASM blocks can have parameters in the typed extension
        // but our current implementation doesn't use them
        &[]
    }
    
    fn is_ret(&self, insn: regalloc2::Inst) -> bool {
        matches!(self.insts[InstId(insn.0 as u32)], WasmInst::Return)
    }
    
    fn is_branch(&self, insn: regalloc2::Inst) -> bool {
        matches!(
            self.insts[InstId(insn.0 as u32)],
            WasmInst::Branch { .. } | WasmInst::BranchIf { .. }
        )
    }
    
    fn branch_blockparams(&self, block: regalloc2::Block, _branch: regalloc2::Inst, _idx: usize) -> &[regalloc2::VReg] {
        // WASM doesn't have block parameters in our implementation
        &[]
    }
    
    fn inst_operands(&self, insn: regalloc2::Inst) -> &[regalloc2::Operand] {
        // WASM is a stack machine, so we don't have explicit operands
        // However, local.get/set instructions do reference locals
        // For now, return empty - proper implementation would track stack/local usage
        &[]
    }
    
    fn inst_clobbers(&self, insn: regalloc2::Inst) -> regalloc2::PRegSet {
        // WASM doesn't have physical registers to clobber
        regalloc2::PRegSet::empty()
    }
    
    fn num_vregs(&self) -> usize {
        self.num_vregs as usize
    }
    
    fn spillslot_size(&self, _class: regalloc2::RegClass) -> usize {
        // WASM locals are effectively spill slots
        // All values are either 32-bit or 64-bit
        8 // Conservative estimate
    }
}

