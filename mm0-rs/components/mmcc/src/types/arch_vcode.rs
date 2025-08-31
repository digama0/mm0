//! Architecture-specific VCode types
//!
//! This module provides architecture-agnostic traits and types for VCode,
//! allowing each architecture to define its own register and instruction types
//! without global type conflicts.

use super::{Size, mir, IdxVec};
#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
use super::classify::Trace;
#[cfg(any(feature = "arm64-backend", feature = "wasm-backend"))]
use super::vcode::Trace;
use crate::Idx;
use std::fmt::Debug;
pub use regalloc2::{RegClass, InstRange, Operand, Inst as InstId, Block as BlockId};

/// Architecture-specific types for VCode
pub trait ArchVCode: Sized + 'static {
    /// Physical register type for this architecture
    type PReg: Copy + Clone + Debug + PartialEq + Eq;
    
    /// Physical register set type for this architecture
    type PRegSet: Copy + Clone + Debug + Default;
    
    /// Instruction type for this architecture
    type Inst: ArchInst<PReg = Self::PReg, PRegSet = Self::PRegSet>;
    
    /// Physical instruction type after register allocation
    type PInst: Debug;
    
    /// Get the architecture name
    fn name() -> &'static str;
}

/// Architecture-specific instruction trait
pub trait ArchInst: Sized + Debug {
    /// Physical register type
    type PReg: Copy + Clone + Debug;
    
    /// Physical register set type
    type PRegSet: Copy + Clone + Debug;
    
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
    
    /// Get clobbered registers
    fn clobbers(&self) -> Self::PRegSet;
}

/// Architecture-specific argument ABI
#[derive(Clone, Copy, Debug)]
pub enum ArchArgAbi<PReg> {
    /// The value is not passed
    Ghost,
    /// The value is passed in the given physical register
    Reg(PReg, Size),
    /// The value is passed in a memory location
    Mem { off: u32, sz: u32 },
    /// A pointer to a value is passed in a physical register
    Boxed { reg: PReg, sz: u32 },
    /// A pointer to the value is passed in memory
    BoxedMem { off: u32, sz: u32 },
}

/// Architecture-specific procedure ABI
#[derive(Clone, Debug)]
pub struct ArchProcAbi<A: ArchVCode> {
    /// Arguments to the function
    pub args: Box<[ArchArgAbi<A::PReg>]>,
    /// Return values from the function
    pub rets: Box<[ArchArgAbi<A::PReg>]>,
    /// Whether the function is reachable
    pub reach: bool,
    /// Space needed for outgoing arguments
    pub args_space: u32,
    /// Registers clobbered by calls
    pub clobbers: A::PRegSet,
}

/// Trait for converting architecture-specific types to generic ones
pub trait ToGeneric {
    /// The generic type this converts to
    type Generic;
    
    /// Convert to the generic representation
    fn to_generic(self) -> Self::Generic;
}

/// Architecture-specific VCode
#[derive(Debug)]
pub struct ArchVCodeData<A: ArchVCode> {
    /// The function ABI
    pub abi: ArchProcAbi<A>,
    /// The instructions
    pub insts: IdxVec<InstId, A::Inst>,
    /// Basic blocks
    pub blocks: IdxVec<BlockId, (mir::BlockId, InstId, InstId)>,
    /// Block parameters
    pub block_params: super::vcode::ChunkVec<BlockId, super::vcode::VReg>,
    /// Number of virtual registers
    pub num_vregs: u32,
    /// Spill slots
    pub spills: IdxVec<super::vcode::SpillId, u32>,
    /// Constants
    pub consts: Vec<mir::Constant>,
    /// Trace information
    pub trace: Trace,
}