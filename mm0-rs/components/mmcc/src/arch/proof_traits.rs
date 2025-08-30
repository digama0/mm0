//! Architecture-agnostic proof generation traits
//!
//! This module defines traits that allow each architecture to generate
//! proofs about the correctness of its code generation, without coupling
//! the proof system to any specific architecture.

use crate::proof::{ProcId, VBlockId};
use crate::types::{mir, Size};
use crate::Symbol;

/// Abstract representation of a register for proof purposes
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbstractReg {
    /// A general-purpose register
    Gpr(u8),
    /// Stack pointer
    StackPointer,
    /// Frame pointer
    FramePointer,
    /// Return value register
    ReturnValue,
    /// Argument register
    Argument(u8),
    /// Syscall number register
    SyscallNum,
}

/// Abstract representation of an operand
#[derive(Debug, Clone)]
pub enum AbstractOperand {
    /// Register operand
    Reg(AbstractReg),
    /// Immediate value
    Imm(i64),
    /// Memory location
    Mem(AbstractReg, i64),
}

/// Abstract instruction for proof generation
#[derive(Debug, Clone)]
pub enum AbstractInst {
    /// Move data between locations
    Move {
        dst: AbstractOperand,
        src: AbstractOperand,
        size: Size,
    },
    /// Arithmetic operation
    Arith {
        op: ArithOp,
        dst: AbstractReg,
        src1: AbstractOperand,
        src2: AbstractOperand,
    },
    /// Function call
    Call {
        target: CallTarget,
        args: Vec<AbstractOperand>,
        ret: Option<AbstractReg>,
    },
    /// System call
    Syscall {
        num: u32,
        args: Vec<AbstractOperand>,
        ret: Option<AbstractReg>,
    },
    /// Conditional branch
    Branch {
        cond: BranchCond,
        target: VBlockId,
    },
    /// Unconditional jump
    Jump {
        target: VBlockId,
    },
    /// Return from function
    Return {
        value: Option<AbstractOperand>,
    },
}

/// Arithmetic operations
#[derive(Debug, Clone, Copy)]
pub enum ArithOp {
    Add, Sub, Mul, Div, Mod,
    And, Or, Xor, Not,
    Shl, Shr, Sar,
}

/// Branch conditions
#[derive(Debug, Clone, Copy)]
pub enum BranchCond {
    Eq, Ne, Lt, Le, Gt, Ge,
    Above, Below, AboveEq, BelowEq,
}

/// Call targets
#[derive(Debug, Clone)]
pub enum CallTarget {
    /// Direct call to known procedure
    Direct(ProcId),
    /// Indirect call through register
    Indirect(AbstractReg),
    /// External function call
    External(Symbol),
}

/// Proof obligations that must be satisfied
#[derive(Debug)]
pub struct ProofObligation {
    /// What property must be proven
    pub property: ProofProperty,
    /// Why this proof is needed
    pub reason: String,
}

/// Properties that can be proven about instructions
#[derive(Debug)]
pub enum ProofProperty {
    /// Register contains expected value
    RegisterValue {
        reg: AbstractReg,
        // TODO: Fix mir::Operand usage
        value: Option<()>, // Temporarily replaced
    },
    /// Memory location contains expected value
    MemoryValue {
        addr: AbstractOperand,
        // TODO: Fix mir::Operand usage
        value: Option<()>, // Temporarily replaced
        size: Size,
    },
    /// Stack is properly aligned
    StackAlignment {
        alignment: u32,
    },
    /// Calling convention is satisfied
    CallingConvention {
        target: CallTarget,
        convention: CallingConvention,
    },
}

/// Calling conventions
#[derive(Debug, Clone, Copy)]
pub enum CallingConvention {
    /// System V AMD64 ABI (Linux x86-64)
    SystemV,
    /// Microsoft x64 ABI (Windows)
    Win64,
    /// ARM64 AAPCS64 (ARM64 Linux/BSD)
    Aapcs64,
    /// Apple ARM64 ABI (macOS/iOS)
    AppleArm64,
}

/// Main trait for architecture-specific proof generation
pub trait ArchProof {
    /// The concrete instruction type for this architecture
    type Inst;
    
    /// The concrete register type for this architecture
    type Reg;
    
    /// Convert a concrete instruction to abstract representation
    fn abstract_inst(&self, inst: &Self::Inst) -> AbstractInst;
    
    /// Convert a concrete register to abstract representation
    fn abstract_reg(&self, reg: &Self::Reg) -> AbstractReg;
    
    /// Get the calling convention for this architecture
    fn calling_convention(&self) -> CallingConvention;
    
    /// Generate proof obligations for an instruction
    fn proof_obligations(&self, inst: &Self::Inst) -> Vec<ProofObligation>;
    
    /// Verify that an instruction sequence preserves a property
    fn verify_property(
        &self,
        pre: &ProofProperty,
        insts: &[Self::Inst],
        post: &ProofProperty,
    ) -> Result<(), String>;
}

/// Trait for generating architecture-specific proof terms
pub trait ProofGen: ArchProof {
    /// Generate proof that a move instruction preserves values
    fn prove_move(
        &self,
        dst: &Self::Reg,
        src: &AbstractOperand,
        size: Size,
    ) -> ProofTerm;
    
    /// Generate proof that a syscall follows conventions
    fn prove_syscall(
        &self,
        num: u32,
        args: &[Self::Reg],
    ) -> ProofTerm;
    
    /// Generate proof that a call follows conventions
    fn prove_call(
        &self,
        target: &CallTarget,
        args: &[Self::Reg],
    ) -> ProofTerm;
    
    /// Generate proof that stack operations are safe
    fn prove_stack_op(
        &self,
        op: StackOp,
        size: u32,
    ) -> ProofTerm;
}

/// Stack operations that need proofs
#[derive(Debug)]
pub enum StackOp {
    /// Allocate stack space
    Alloc(u32),
    /// Deallocate stack space
    Dealloc(u32),
    /// Push value onto stack
    Push(AbstractOperand),
    /// Pop value from stack
    Pop(AbstractReg),
}

/// A proof term (placeholder - would be actual MM0 proof term)
#[derive(Debug)]
pub struct ProofTerm {
    /// The conclusion of this proof
    pub conclusion: ProofProperty,
    /// Steps in the proof
    pub steps: Vec<ProofStep>,
}

/// A single step in a proof
#[derive(Debug)]
pub struct ProofStep {
    /// What this step proves
    pub claim: String,
    /// Justification for this step
    pub reason: ProofReason,
}

/// Reasons that justify proof steps
#[derive(Debug)]
pub enum ProofReason {
    /// By definition of instruction semantics
    InstructionSemantics,
    /// By calling convention rules
    CallingConvention,
    /// By memory model rules
    MemoryModel,
    /// By previous proof steps
    BySteps(Vec<usize>),
}