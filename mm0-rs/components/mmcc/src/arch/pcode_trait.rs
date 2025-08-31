//! Architecture-agnostic traits for cross-platform code generation
//!
//! This module defines traits that allow LinkedCode and other high-level
//! structures to work with any architecture's instruction format.

use std::collections::HashMap;
use crate::types::{IdxVec, mir, vcode::{ProcAbi, BlockId, ChunkVec}};
use crate::types::classify::Trace;
use crate::{Symbol, FileSpan};

/// Unique identifier for physical instructions (after register allocation)
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "memory", derive(mm0_deepsize::DeepSizeOf))]
pub struct PInstId(pub u32);

impl crate::Idx for PInstId {
    fn into_usize(self) -> usize { self.0 as usize }
    fn from_usize(n: usize) -> Self { Self(n as u32) }
}

/// Architecture-agnostic trait for physical code after register allocation
pub trait ArchPCode: Send + Sync + std::fmt::Debug {
    /// The architecture-specific physical instruction type
    type PInst: PhysicalInstruction;
    
    /// Get the instructions
    fn insts(&self) -> &IdxVec<PInstId, Self::PInst>;
    
    /// Get mutable access to instructions
    fn insts_mut(&mut self) -> &mut IdxVec<PInstId, Self::PInst>;
    
    /// Get the block map from MIR blocks to regalloc blocks
    fn block_map(&self) -> &HashMap<mir::BlockId, BlockId>;
    
    /// Get the blocks with their instruction ranges
    fn blocks(&self) -> &IdxVec<BlockId, (mir::BlockId, PInstId, PInstId)>;
    
    /// Get the starting address of each block
    fn block_addr(&self) -> &IdxVec<BlockId, u32>;
    
    /// Get block parameters
    fn block_params(&self) -> &ChunkVec<BlockId, (mir::VarId, Self::PRegMem)>
    where Self::PRegMem: Sized;
    
    /// Get trace information
    fn trace(&self) -> &Trace;
    
    /// Get the stack size
    fn stack_size(&self) -> u32;
    
    /// Get saved registers (architecture-specific)
    fn saved_regs(&self) -> &[Self::PReg]
    where Self::PReg: PhysicalReg;
    
    /// Get the total code length
    fn len(&self) -> u32;
    
    /// Architecture name for debugging
    fn arch_name(&self) -> &'static str;
    
    /// Associated types that architectures must define
    type PReg: PhysicalReg;
    type PRegMem: Send + Sync + std::fmt::Debug;
}

/// Trait for architecture-specific physical registers
pub trait PhysicalReg: Copy + Send + Sync + std::fmt::Debug + std::fmt::Display {
    /// Create a new physical register from an index
    fn new(index: usize) -> Self;
    
    /// Get the register index
    fn index(self) -> u8;
    
    /// Check if this is a valid register
    fn is_valid(self) -> bool;
    
    /// Get an invalid register sentinel
    fn invalid() -> Self;
    
    /// Convert to regalloc2 PReg
    fn to_regalloc(self) -> regalloc2::PReg;
}

/// Trait for physical instructions (after register allocation)
pub trait PhysicalInstruction: Clone + Send + Sync + std::fmt::Debug {
    /// Encode the instruction to bytes
    fn encode(&self, sink: &mut impl InstructionSink) -> Result<(), EncodeError>;
    
    /// Get the size hint for this instruction (if known)
    fn size_hint(&self) -> Option<usize>;
    
    /// Check if this is a spill instruction added by regalloc
    fn is_spill(&self) -> bool { false }
}

/// Trait for collecting encoded instructions
pub trait InstructionSink {
    /// Emit raw bytes
    fn emit_bytes(&mut self, bytes: &[u8]);
    
    /// Emit a single byte
    fn emit_u8(&mut self, byte: u8) {
        self.emit_bytes(&[byte]);
    }
    
    /// Emit a 32-bit value (little-endian)
    fn emit_u32(&mut self, value: u32) {
        self.emit_bytes(&value.to_le_bytes());
    }
}

/// Errors that can occur during instruction encoding
#[derive(Debug, thiserror::Error)]
pub enum EncodeError {
    /// Feature not implemented
    #[error("not implemented: {0}")]
    NotImplemented(&'static str),
    
    /// Invalid instruction configuration
    #[error("invalid instruction: {0}")]
    InvalidInstruction(String),
}

/// Extension trait to convert architecture-specific PCode to trait object
pub trait IntoPCodeBox {
    /// Convert to boxed trait object
    fn into_pcode_box(self: Box<Self>) -> Box<dyn ArchPCode<
        PInst = Self::PInst,
        PReg = Self::PReg,
        PRegMem = Self::PRegMem,
    >>;
}

// Blanket implementation for all types that implement ArchPCode
impl<T> IntoPCodeBox for T 
where 
    T: ArchPCode + 'static,
    T::PInst: 'static,
    T::PReg: 'static,
    T::PRegMem: 'static,
{
    fn into_pcode_box(self: Box<Self>) -> Box<dyn ArchPCode<
        PInst = Self::PInst,
        PReg = Self::PReg,
        PRegMem = Self::PRegMem,
    >> {
        self
    }
}