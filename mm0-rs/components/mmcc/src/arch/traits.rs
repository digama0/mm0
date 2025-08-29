//! Architecture abstraction traits
//!
//! This module defines traits that architecture-specific modules must implement
//! to support code generation for different targets.
//!
//! The abstraction is designed to support diverse architectures including:
//! - Register machines (x86-64, ARM64)  
//! - Stack machines (WebAssembly)
//! - Future targets (RISC-V, etc.)

use std::fmt::{Debug, Display};
use regalloc2::MachineEnv;
use crate::types::{Size, vcode::{BlockId, VReg}};
use super::target::{Target, SyscallConvention};

/// Architecture categories
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArchKind {
    /// Traditional register-based architecture (x86, ARM, RISC-V)
    RegisterMachine,
    /// Stack-based architecture (WebAssembly, JVM bytecode)
    StackMachine,
}

/// Core trait that defines an architecture's interface
pub trait Architecture: Sized {
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
        &[]  // Default: no callee-saved registers (e.g., WASM)
    }
    
    /// Get caller-saved registers  
    fn caller_saved() -> &'static [Self::PReg] {
        &[]  // Default: no caller-saved registers
    }
    
    /// Get registers used for function arguments and return values
    fn arg_regs() -> &'static [Self::PReg] {
        &[]  // Default: no argument registers (stack passing)
    }
    
    /// Check if this architecture supports direct system calls
    fn has_syscalls(target: Target) -> bool {
        target.syscall_convention().is_some()
    }
    
    /// Get registers used for system call arguments (platform-specific)
    fn syscall_arg_regs(target: Target) -> Option<(Self::PReg, &'static [Self::PReg])> {
        None  // Default: no syscall support
    }
}

/// Trait for physical registers
pub trait PhysicalReg: Copy + Clone + PartialEq + Eq + Debug + Display {
    /// Create a new register from index
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

/// Trait for register sets
pub trait RegisterSet<R: PhysicalReg>: Default + Clone + Copy + Debug {
    /// Insert a register into the set
    fn insert(&mut self, reg: R);
    
    /// Check if a register is in the set
    fn contains(&self, reg: R) -> bool;
    
    /// Remove a register from the set
    fn remove(&mut self, reg: R);
    
    /// Iterate over registers in the set
    fn iter(&self) -> impl Iterator<Item = R>;
    
    /// Convert to regalloc2 PRegSet
    fn to_regalloc(self) -> regalloc2::PRegSet;
}

/// Base instruction trait
pub trait Instruction: Clone + Debug {
    /// Check if this is a move instruction
    fn is_move(&self) -> bool;
    
    /// Get the instruction size in bytes (if known)
    fn size_hint(&self) -> Option<usize>;
}

/// Physical instruction trait (after register allocation)
pub trait PhysicalInstruction: Clone + Debug {
    /// Encode the instruction to bytes
    fn encode(&self, sink: &mut impl InstructionSink) -> Result<(), EncodeError>;
}

/// Trait for emitting encoded instructions
pub trait InstructionSink {
    /// Emit raw bytes
    fn emit_bytes(&mut self, bytes: &[u8]);
    
    /// Get current offset
    fn offset(&self) -> usize;
}

/// Errors that can occur during instruction encoding
#[derive(Debug, Clone)]
pub enum EncodeError {
    /// Instruction encoding not implemented
    NotImplemented(&'static str),
    /// Invalid instruction format
    InvalidFormat(String),
}

/// Common binary operations across architectures
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Binop {
    Add,
    Sub,
    And,
    Or,
    Xor,
    Mul,
    // Architecture-specific ops can be added via extension
}

/// Common unary operations
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unop {
    Not,
    Neg,
}

/// Common condition codes
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConditionCode {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Below,      // Unsigned less
    BelowEqual, // Unsigned less-equal
    Above,      // Unsigned greater
    AboveEqual, // Unsigned greater-equal
    Overflow,
    NotOverflow,
    Sign,       // Negative
    NotSign,    // Non-negative
}