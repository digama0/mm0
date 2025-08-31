//! WASM virtual code representation
//!
//! This module defines the VCode type for WebAssembly, which represents
//! code in a form close to WASM instructions but using virtual registers.

use crate::types::{IdxVec, mir, vcode::*};
use crate::types::classify::Trace;
use crate::types::mir::Constant;
use crate::Idx;
use super::inst::Inst;
use std::ops::Index;

/// WASM virtual code
#[derive(Debug)]
pub struct VCode {
    /// The function ABI
    pub abi: ProcAbi,
    /// The instructions
    pub insts: IdxVec<InstId, Inst>,
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
}

impl Index<InstId> for VCode {
    type Output = Inst;
    
    fn index(&self, idx: InstId) -> &Self::Output {
        &self.insts[idx]
    }
}