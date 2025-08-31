//! Generic VCode types that don't depend on specific architectures
//!
//! This module provides the core VCode types without importing any
//! architecture-specific register types. Each architecture provides
//! its own concrete implementations.

use std::{collections::HashMap, fmt::{Debug, Display}, iter::FromIterator};
use crate::{types::{mir, IdxVec}, Idx};
use mm0_util::u32_as_usize;
pub(crate) use regalloc2::{RegClass, InstRange, Operand, Inst as InstId};
pub use regalloc2::Block as BlockId;
use super::Size;
#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
use super::classify::Trace;
#[cfg(any(feature = "arm64-backend", feature = "wasm-backend"))]
use super::vcode::Trace;

/// Re-export common types
pub use super::vcode::{
    IsReg, VReg, VRegRename, GlobalId, ProcId, SpillId, 
    ConstRef, ChunkVec
};
pub use super::mir::Constant;

/// Generic instruction trait without architecture-specific types
pub trait GenericInst: Sized + Debug {
    /// Determine whether an instruction is a call instruction
    fn is_call(&self) -> bool;
    
    /// Determine whether an instruction is a return instruction
    fn is_ret(&self) -> bool;
    
    /// Determine whether an instruction is a branch instruction
    fn is_branch(&self) -> bool;
    
    /// Get the blockparam arguments for a successor
    fn branch_blockparams(&self, succ_idx: usize) -> &[regalloc2::VReg];
    
    /// Collect operands for register allocation
    fn collect_operands(&self, ops: &mut Vec<Operand>);
}

/// Generic VCode without architecture-specific types
#[derive(Debug)]
pub struct GenericVCode<I: GenericInst> {
    /// The instructions
    pub insts: IdxVec<InstId, I>,
    /// Basic blocks
    pub blocks: IdxVec<BlockId, (mir::BlockId, InstId, InstId)>,
    /// Block parameters
    pub block_params: ChunkVec<BlockId, VReg>,
    /// Number of virtual registers
    pub num_vregs: u32,
    /// Spill slots
    pub spills: IdxVec<SpillId, u32>,
    /// Constants
    pub consts: Vec<Constant>,
    /// Trace information
    pub trace: Trace,
}

impl<I: GenericInst> GenericVCode<I> {
    /// Get a fresh virtual register
    pub fn fresh_vreg(&mut self) -> VReg {
        let vreg = VReg::new(self.num_vregs as usize);
        self.num_vregs += 1;
        vreg
    }
    
    /// Emit an instruction
    pub fn emit(&mut self, inst: I) -> InstId {
        self.insts.push(inst)
    }
    
    /// Get the current block
    pub fn cur_block(&self) -> BlockId {
        BlockId::new(self.blocks.len().saturating_sub(1))
    }
}

/// Generic procedure ABI without architecture-specific register types
#[derive(Clone, Debug)]
pub struct GenericProcAbi {
    /// Whether the function is reachable
    pub reach: bool,
    /// Space needed for outgoing arguments
    pub args_space: u32,
    /// Number of arguments
    pub num_args: usize,
    /// Number of return values
    pub num_rets: usize,
}