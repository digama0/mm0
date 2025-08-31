//! WASM "register allocation" implementation
//!
//! WebAssembly is a stack machine, so it doesn't need traditional register
//! allocation. This module provides a minimal implementation to satisfy
//! the compiler interface.

use crate::types::{IdxVec, mir, vcode::*};
// WASM doesn't have a VCode type yet, we'll create a placeholder
// Simple Trace type for WASM (since we don't have the full classify module)
#[derive(Clone, Debug, Default)]
pub struct Trace;
use crate::Idx;
use super::{WasmReg, WasmRegSet, WasmInst};

/// WASM doesn't need register allocation, but we need a PCode type
#[derive(Clone, Debug)]
pub struct PCode {
    /// Function ABI
    pub abi: ProcAbi,
    /// The instructions (same as VCode for WASM)
    pub insts: IdxVec<PInstId, super::WasmInst>,
    /// Map from VCode block to instruction range
    pub blocks: IdxVec<regalloc2::Block, (mir::BlockId, PInstId, PInstId)>,
    /// Start address of each block
    pub block_addr: IdxVec<regalloc2::Block, u32>,
    /// Block parameters (unused in WASM)
    pub block_params: ChunkVec<regalloc2::Block, VReg>,
    /// Trace information for debugging
    pub trace: Trace,
    /// Stack size needed (for locals)
    pub stack_size: u32,
    /// Total code size (in WASM bytes)
    pub len: u32,
    /// Local variable types
    pub local_types: Vec<super::WasmType>,
}

impl PCode {
    /// Get the instructions
    pub fn insts(&self) -> &IdxVec<PInstId, super::WasmInst> {
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
    let mut block_params = ChunkVec::default();
    let mut addr = 0u32;
    
    // Copy instructions directly (no register allocation needed)
    for (block_idx, block) in vcode.blocks() {
        let start = PInstId(pinsts.len() as u32);
        block_addr.push(addr);
        
        let inst_range = vcode.block_insts(block_idx);
        for inst_idx in inst_range {
            let vinst = &vcode[inst_idx];
            pinsts.push(vinst.clone());
            
            // Estimate instruction size (varies in WASM)
            addr += estimate_wasm_inst_size(vinst);
        }
        
        let end = PInstId(pinsts.len() as u32);
        blocks.push((block.mir_block, start, end));
    }
    
    // Count locals needed
    let stack_size = count_locals(vcode);
    
    Ok(PCode {
        abi: vcode.abi.clone(),
        insts: pinsts,
        blocks,
        block_addr,
        block_params,
        trace: vcode.trace.clone(),
        stack_size,
        len: addr,
        local_types: vec![super::WasmType::I64; stack_size as usize],
    })
}

/// Estimate the encoded size of a WASM instruction
fn estimate_wasm_inst_size(inst: &super::WasmInst) -> u32 {
    use super::WasmInst::*;
    match inst {
        Const { .. } => 5, // opcode + LEB128 value
        LocalGet { .. } | LocalSet { .. } | LocalTee { .. } => 2, // opcode + local idx
        Load { .. } | Store { .. } => 3, // opcode + alignment + offset
        Add { .. } | Sub { .. } | Mul { .. } => 1, // single opcode
        Call { .. } => 2, // opcode + function idx
        Return => 1, // single opcode
        Branch { .. } | BranchIf { .. } => 2, // opcode + label idx
        Drop => 1, // single opcode
        Block { .. } | Loop { .. } | If { .. } => 2, // opcode + block type
        Else | End => 1, // single opcode
        I32Eq | I32Ne | I32LtS | I32LtU | I32GtS | I32GtU => 1, // single opcode
        I32LeS | I32LeU | I32GeS | I32GeU | I32Eqz => 1, // single opcode
        Select => 1,
        BranchTable { .. } => 5, // conservative estimate
        // SIMD instructions
        V128Const { .. } => 18, // opcode + 16 bytes
        V128Load { .. } | V128Store { .. } => 6, // opcode + align + offset
        F32x4Add | F32x4Sub | F32x4Mul | F32x4Div | F32x4Sqrt | F32x4Min | F32x4Max => 2,
        I32x4Add | I32x4Sub | I32x4Mul => 2,
        I16x8Add | I16x8Sub | I16x8Mul => 2,
        I8x16Add | I8x16Sub => 2,
        F32x4Eq | F32x4Ne | F32x4Lt | F32x4Gt | F32x4Le | F32x4Ge => 2,
        I32x4Eq | I32x4Ne | I32x4LtS | I32x4LtU | I32x4GtS | I32x4GtU => 2,
        I32x4LeS | I32x4LeU | I32x4GeS | I32x4GeU => 2,
        I32x4TruncSatF32x4S | I32x4TruncSatF32x4U => 2,
        F32x4ConvertI32x4S | F32x4ConvertI32x4U => 2,
        I8x16Shuffle { .. } => 18, // opcode + 16 lane bytes
        I8x16Swizzle => 2,
        I32x4Splat | I16x8Splat | I8x16Splat | F32x4Splat | F64x2Splat => 2,
        I32x4ExtractLane { .. } | I16x8ExtractLane { .. } | I8x16ExtractLane { .. } => 3,
        F32x4ExtractLane { .. } | F64x2ExtractLane { .. } => 3,
        I32x4ReplaceLane { .. } | I16x8ReplaceLane { .. } | I8x16ReplaceLane { .. } => 3,
        F32x4ReplaceLane { .. } | F64x2ReplaceLane { .. } => 3,
        V128And | V128Or | V128Xor | V128Not | V128Andnot | V128Bitselect => 2,
        V128AnyTrue | I32x4AllTrue | I16x8AllTrue | I8x16AllTrue => 2,
    }
}

/// Count the number of locals needed
fn count_locals(vcode: &super::vcode::VCode) -> u32 {
    // For now, estimate based on the number of virtual registers
    // In a real implementation, this would analyze local usage
    vcode.num_vregs.max(16) // At least 16 locals
}