//! WASM virtual code representation
//!
//! This module defines the VCode type for WebAssembly, which represents
//! code in a form close to WASM instructions but using virtual registers.

use crate::types::{IdxVec, mir, vcode::*};
use super::regalloc::Trace;
use crate::types::mir::Constant;
use crate::Idx;
use super::WasmInst;
use std::ops::Index;
use crate::codegen_arch::VCodeTrait;
use crate::arch_pcode::ArchPCode;

/// WASM virtual code
#[derive(Debug)]
pub struct VCode {
    /// The function ABI
    pub abi: ProcAbi,
    /// The instructions
    pub insts: IdxVec<InstId, WasmInst>,
    /// Basic blocks
    pub blocks: IdxVec<BlockId, Block>,
    /// Map from MIR blocks to VCode blocks
    pub block_map: Vec<(mir::BlockId, BlockId)>,
    /// Block parameters (empty for WASM)
    pub block_params: ChunkVec<BlockId, VReg>,
    /// Spill slots (not used in WASM)
    pub spills: IdxVec<SpillId, u32>,
    /// Number of virtual registers
    pub num_vregs: u32,
    /// Constants
    pub consts: Vec<Constant>,
    /// Trace information
    pub trace: Trace,
}

/// Basic block information
#[derive(Debug, Clone)]
pub struct Block {
    /// MIR block ID
    pub mir_block: mir::BlockId,
    /// Start instruction
    pub start: InstId,
    /// End instruction (exclusive)
    pub end: InstId,
}

impl VCode {
    /// Iterate over blocks
    pub fn blocks(&self) -> impl Iterator<Item = (BlockId, &Block)> {
        self.blocks.enum_iter()
    }
    
    /// Get instructions for a block
    pub fn block_insts(&self, block: BlockId) -> std::ops::Range<InstId> {
        let block = &self.blocks[block];
        block.start..block.end
    }
    
    /// Emit an instruction
    pub fn emit(&mut self, inst: Inst) -> InstId {
        let id = InstId(self.insts.len() as u32);
        self.insts.push(inst);
        id
    }
}

impl Index<InstId> for VCode {
    type Output = WasmInst;
    
    fn index(&self, idx: InstId) -> &Self::Output {
        &self.insts[idx]
    }
}

impl VCodeTrait for VCode {
    fn regalloc(self: Box<Self>) -> (ProcAbi, ArchPCode) {
        // WASM doesn't need register allocation - it's a stack machine
        // We just convert VCode directly to PCode
        let pcode = super::regalloc_impl::wasm_simple_alloc(*self);
        let abi = pcode.abi.clone();
        (abi, ArchPCode::Wasm(Box::new(pcode)))
    }
}