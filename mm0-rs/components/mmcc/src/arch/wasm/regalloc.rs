//! WASM "register allocation" implementation
//!
//! WebAssembly is a stack machine, so it doesn't need traditional register
//! allocation. This module provides a minimal implementation to satisfy
//! the compiler interface.

use crate::types::{IdxVec, mir, vcode::*};
// WASM doesn't have a VCode type yet, we'll create a placeholder
use crate::types::classify::Trace;
use crate::Idx;
use super::{WasmReg, WasmRegSet, WasmInst};

/// WASM doesn't need register allocation, but we need a PCode type
#[derive(Clone, Debug)]
pub struct PCode {
    /// The instructions (same as VCode for WASM)
    pub insts: IdxVec<PInstId, WasmInst>,
    /// Map from VCode block to instruction range
    pub blocks: IdxVec<regalloc2::Block, (mir::BlockId, PInstId, PInstId)>,
    /// Start address of each block
    pub block_addr: IdxVec<regalloc2::Block, u32>,
    /// Trace information for debugging
    pub trace: Trace,
    /// Stack size needed (for locals)
    pub stack_size: u32,
    /// Total code size (in WASM bytes)
    pub len: u32,
}

impl PCode {
    /// Get the instructions
    pub fn insts(&self) -> &IdxVec<PInstId, WasmInst> {
        &self.insts
    }
    
    /// Get block addresses
    pub fn block_addrs(&self) -> &IdxVec<regalloc2::Block, u32> {
        &self.block_addr
    }
}

/// Identifier for physical instructions
mk_id! { PInstId }

/// "Register allocation" for WASM (no-op since it's a stack machine)
pub fn regalloc_wasm(vcode: &super::vcode::VCode) -> Result<PCode, String> {
    let mut pinsts = IdxVec::default();
    let mut blocks = IdxVec::default();
    let mut block_addr = IdxVec::default();
    let mut addr = 0u32;
    
    // Copy instructions directly (no register allocation needed)
    for (block_idx, block) in vcode.blocks() {
        let start = PInstId(pinsts.len() as u32);
        block_addr.push(addr);
        
        let inst_range = vcode.block_insts(block);
        for inst_idx in inst_range {
            let vinst = &vcode[inst_idx];
            pinsts.push(vinst.clone());
            
            // Estimate instruction size (varies in WASM)
            addr += estimate_wasm_inst_size(vinst);
        }
        
        let end = PInstId(pinsts.len() as u32);
        blocks.push((mir::BlockId(block_idx.index() as u32), start, end));
    }
    
    // Count locals needed
    let stack_size = count_locals(vcode);
    
    Ok(PCode {
        insts: pinsts,
        blocks,
        block_addr,
        trace: vcode.trace().clone(),
        stack_size,
        len: addr,
    })
}

/// Estimate the encoded size of a WASM instruction
fn estimate_wasm_inst_size(inst: &WasmInst) -> u32 {
    use WasmInst::*;
    match inst {
        Const { .. } => 5, // opcode + LEB128 value
        LocalGet { .. } | LocalSet { .. } | LocalTee { .. } => 2, // opcode + local idx
        Load { .. } | Store { .. } => 3, // opcode + alignment + offset
        Add { .. } | Sub { .. } | Mul { .. } => 1, // single opcode
        Call { .. } => 2, // opcode + function idx
        Return => 1, // single opcode
        Branch { .. } | BranchIf { .. } => 2, // opcode + label idx
        Drop => 1, // single opcode
        Unreachable => 1, // single opcode
    }
}

/// Count the number of locals needed
fn count_locals(vcode: &VCode<WasmInst>) -> u32 {
    // For now, estimate based on the number of virtual registers
    // In a real implementation, this would analyze local usage
    16 // Default to 16 locals
}