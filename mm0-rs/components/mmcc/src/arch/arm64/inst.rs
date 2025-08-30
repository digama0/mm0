//! ARM64 instruction definitions

use crate::arch::traits::{Instruction, PhysicalInstruction, InstructionSink, EncodeError};
use crate::types::{Size, vcode::{BlockId, VReg}};
use super::regs::PReg;

/// ARM64 instructions (with virtual registers)
#[derive(Clone, Debug)]
pub enum Inst {
    /// Fallthrough to next block (no code emitted)
    Fallthrough { dst: BlockId },
    
    /// Move between registers
    Mov { dst: VReg, src: VReg },
    
    /// Load immediate
    MovImm { dst: VReg, imm: u64, size: Size },
    
    /// Arithmetic operations
    Add { dst: VReg, src1: VReg, src2: Operand, size: Size },
    Sub { dst: VReg, src1: VReg, src2: Operand, size: Size },
    
    /// Logical operations
    And { dst: VReg, src1: VReg, src2: Operand, size: Size },
    Orr { dst: VReg, src1: VReg, src2: Operand, size: Size },
    Eor { dst: VReg, src1: VReg, src2: Operand, size: Size },
    
    /// Memory operations
    Load { dst: VReg, addr: AMode, size: Size },
    Store { src: VReg, addr: AMode, size: Size },
    
    /// Load address of a constant (will be resolved later)
    LoadConst { dst: VReg, const_id: u32 },
    
    /// Branch operations
    Branch { target: BlockId },
    BranchCond { cond: Cond, target: BlockId },
    
    /// Function calls
    Call { target: CallTarget },
    Ret,
    
    /// System call
    Svc { imm: u16 }, // Supervisor call
}

/// Physical instructions (after register allocation)
#[derive(Clone, Debug)]
pub enum PInst {
    /// Fallthrough (no code)
    Fallthrough { dst: BlockId },
    
    /// Move between registers
    Mov { dst: PReg, src: PReg, size: OperandSize },
    
    /// Load immediate
    MovImm { dst: PReg, imm: u64, size: OperandSize },
    
    /// Arithmetic
    Add { dst: PReg, src1: PReg, src2: POperand, size: OperandSize },
    Sub { dst: PReg, src1: PReg, src2: POperand, size: OperandSize },
    
    /// Logical
    And { dst: PReg, src1: PReg, src2: POperand, size: OperandSize },
    Orr { dst: PReg, src1: PReg, src2: POperand, size: OperandSize },
    Eor { dst: PReg, src1: PReg, src2: POperand, size: OperandSize },
    
    /// Memory
    Ldr { dst: PReg, addr: PAMode, size: OperandSize },
    Str { src: PReg, addr: PAMode, size: OperandSize },
    
    /// Load address (PC-relative)
    Adr { dst: PReg, offset: i32 },
    
    /// Branches
    B { offset: i32 },
    Bcond { cond: Cond, offset: i32 },
    
    /// Calls
    Bl { offset: i32 },
    Ret,
    
    /// System
    Svc { imm: u16 },
}

/// Operand (register or immediate)
#[derive(Clone, Debug)]
pub enum Operand {
    Reg(VReg),
    Imm(u64),
}

/// Physical operand
#[derive(Clone, Debug)]
pub enum POperand {
    Reg(PReg),
    Imm(u64),
}

/// Addressing modes
#[derive(Clone, Debug)]
pub enum AMode {
    /// Register indirect: [Xn]
    Reg(VReg),
    /// Register + immediate offset: [Xn, #imm]
    RegImm(VReg, i64),
    /// Pre-indexed: [Xn, #imm]!
    PreIndex(VReg, i64),
    /// Post-indexed: [Xn], #imm
    PostIndex(VReg, i64),
}

/// Physical addressing modes
#[derive(Clone, Debug)]
pub enum PAMode {
    Reg(PReg),
    RegImm(PReg, i64),
    PreIndex(PReg, i64),
    PostIndex(PReg, i64),
}

/// Condition codes
#[derive(Clone, Copy, Debug)]
pub enum Cond {
    Eq,  // Equal (Z == 1)
    Ne,  // Not equal (Z == 0)
    Cs,  // Carry set (C == 1) - unsigned >=
    Cc,  // Carry clear (C == 0) - unsigned <
    Mi,  // Minus (N == 1)
    Pl,  // Plus (N == 0)
    Vs,  // Overflow set (V == 1)
    Vc,  // Overflow clear (V == 0)
    Hi,  // Unsigned higher (C == 1 && Z == 0)
    Ls,  // Unsigned lower or same (!(C == 1 && Z == 0))
    Ge,  // Signed >= (N == V)
    Lt,  // Signed < (N != V)
    Gt,  // Signed > (Z == 0 && N == V)
    Le,  // Signed <= (!(Z == 0 && N == V))
    Al,  // Always
    Nv,  // Never
}

impl Cond {
    /// Get the encoding for this condition
    fn encode(self) -> u8 {
        match self {
            Cond::Eq => 0b0000,
            Cond::Ne => 0b0001,
            Cond::Cs => 0b0010,
            Cond::Cc => 0b0011,
            Cond::Mi => 0b0100,
            Cond::Pl => 0b0101,
            Cond::Vs => 0b0110,
            Cond::Vc => 0b0111,
            Cond::Hi => 0b1000,
            Cond::Ls => 0b1001,
            Cond::Ge => 0b1010,
            Cond::Lt => 0b1011,
            Cond::Gt => 0b1100,
            Cond::Le => 0b1101,
            Cond::Al => 0b1110,
            Cond::Nv => 0b1111,
        }
    }
}

/// Call targets
#[derive(Clone, Debug)]
pub enum CallTarget {
    Direct(String),
    Indirect(VReg),
}

/// Operand size (32 or 64 bit)
#[derive(Clone, Copy, Debug)]
pub enum OperandSize {
    Size32,
    Size64,
}

impl From<Size> for OperandSize {
    fn from(size: Size) -> Self {
        match size.bytes() {
            Some(1) | Some(2) | Some(4) => OperandSize::Size32,
            Some(8) => OperandSize::Size64,
            _ => panic!("Invalid size for ARM64: {:?}", size),
        }
    }
}

impl Instruction for Inst {
    fn is_move(&self) -> bool {
        matches!(self, Inst::Mov { .. })
    }
    
    fn size_hint(&self) -> Option<usize> {
        // Most ARM64 instructions are 4 bytes
        Some(match self {
            Inst::Fallthrough { .. } => 0,
            _ => 4,
        })
    }
}

// Implementation moved to encode.rs