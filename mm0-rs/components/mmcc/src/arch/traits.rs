//! Architecture-independent traits for the compiler
//!
//! This module defines traits that allow the compiler to work with
//! multiple target architectures without hardcoding architecture-specific types.

use crate::types::{Size, vcode::{BlockId, VReg}};
use crate::types::vcode::ProcAbi;
use super::target::{Target, SyscallConvention};
use regalloc2::MachineEnv;
use std::io::{self, Write};

/// Architecture kind (register-based or stack-based)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArchKind {
    /// Traditional register-based architecture (x86, ARM, etc.)
    RegisterMachine,
    /// Stack-based architecture (WASM, JVM, etc.)
    StackMachine,
}

/// Core architecture trait
pub trait Architecture: 'static {
    /// What kind of architecture is this?
    const KIND: ArchKind;
    
    /// Architecture name for display/debugging
    const NAME: &'static str;
    
    /// Physical register type for this architecture
    /// (For stack machines, this might be a dummy type)
    type PReg: PhysicalReg;
    
    /// Register set type (bitset of physical registers)
    type PRegSet: RegisterSet<Self::PReg>;
    
    /// Instruction type (with virtual registers)
    type Inst: Instruction;
    
    /// Physical instruction type (after register allocation)
    type PInst: PhysicalInstruction;
    
    /// Get the machine environment for register allocation
    /// Stack machines may return a dummy environment
    fn machine_env() -> &'static MachineEnv;
    
    /// Get the stack pointer register (if applicable)
    fn stack_pointer() -> Option<Self::PReg> {
        // Default: architectures with registers have a stack pointer
        match Self::KIND {
            ArchKind::RegisterMachine => panic!("{} must implement stack_pointer()", Self::NAME),
            ArchKind::StackMachine => None,
        }
    }
    
    /// Get callee-saved registers
    fn callee_saved() -> &'static [Self::PReg] {
        match Self::KIND {
            ArchKind::RegisterMachine => panic!("{} must implement callee_saved()", Self::NAME),
            ArchKind::StackMachine => &[],
        }
    }
    
    /// Get caller-saved registers
    fn caller_saved() -> &'static [Self::PReg] {
        match Self::KIND {
            ArchKind::RegisterMachine => panic!("{} must implement caller_saved()", Self::NAME),
            ArchKind::StackMachine => &[],
        }
    }
    
    /// Get argument registers
    fn arg_regs() -> &'static [Self::PReg] {
        match Self::KIND {
            ArchKind::RegisterMachine => panic!("{} must implement arg_regs()", Self::NAME),
            ArchKind::StackMachine => &[],
        }
    }
    
    /// Check if this target supports system calls
    fn has_syscalls(target: Target) -> bool {
        let _ = target;
        false
    }
    
    /// Get syscall argument registers
    fn syscall_arg_regs(_target: Target) -> Option<(Self::PReg, &'static [Self::PReg])> {
        None
    }
}

/// Trait for physical registers
pub trait PhysicalReg: Copy + Clone + Eq + std::fmt::Debug + std::fmt::Display {
    /// Create a register from an index
    fn new(index: usize) -> Self;
    
    /// Get the index of this register
    fn index(self) -> u8;
    
    /// Check if this register is valid
    fn is_valid(self) -> bool;
    
    /// Get the invalid register value
    fn invalid() -> Self;
    
    /// Convert to regalloc2 representation
    fn to_regalloc(self) -> regalloc2::PReg;
}

/// Trait for register sets
pub trait RegisterSet<R: PhysicalReg>: Default + Clone {
    /// Insert a register into the set
    fn insert(&mut self, reg: R);
    
    /// Check if the set contains a register
    fn contains(&self, reg: R) -> bool;
    
    /// Remove a register from the set
    fn remove(&mut self, reg: R);
    
    /// Iterate over registers in the set
    fn iter(&self) -> impl Iterator<Item = R>;
    
    /// Convert to regalloc2 representation
    fn to_regalloc(self) -> regalloc2::PRegSet;
}

/// Trait for instructions (with virtual registers)
pub trait Instruction {
    /// Check if this is a move instruction
    fn is_move(&self) -> bool {
        false
    }
    
    /// Get a size hint for this instruction
    fn size_hint(&self) -> Option<usize> {
        None
    }
}

/// Trait for physical instructions (after register allocation)
pub trait PhysicalInstruction: Clone + std::fmt::Debug {
    /// Encode this instruction to bytes
    fn encode(&self, sink: &mut impl InstructionSink) -> Result<(), EncodeError>;
}

/// Trait for collecting encoded instructions
pub trait InstructionSink {
    /// Emit raw bytes
    fn emit_bytes(&mut self, bytes: &[u8]);
    
    /// Get current offset
    fn offset(&self) -> usize;
}

/// Errors that can occur during encoding
#[derive(Debug)]
pub enum EncodeError {
    /// Feature not implemented
    NotImplemented(&'static str),
    /// Invalid instruction format
    InvalidFormat(String),
}

/// Architecture-independent physical code trait
pub trait ArchPCode: std::fmt::Debug + Send + Sync {
    /// Get the total code size in bytes
    fn len(&self) -> u32;
    
    /// Check if the code is empty
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    
    /// Write the code bytes to a writer
    fn write_bytes(&self, w: &mut dyn Write) -> io::Result<()>;
    
    /// Get the procedure ABI
    fn abi(&self) -> &ProcAbi;
}