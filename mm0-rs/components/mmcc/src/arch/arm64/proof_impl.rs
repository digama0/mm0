//! ARM64 implementation of architecture-agnostic proof traits
//!
//! This demonstrates how ARM64 proof generation would work with the new
//! trait-based system, properly handling ARM64-specific conventions.

use super::{PReg, PInst};
use crate::arch::proof_traits::*;
use crate::types::{mir, Size};

/// ARM64-specific proof generator
pub struct Arm64ProofGen {
    /// Target OS (affects syscall conventions)
    os: crate::arch::target::OperatingSystem,
}

impl Arm64ProofGen {
    pub fn new(os: crate::arch::target::OperatingSystem) -> Self {
        Self { os }
    }
}

impl ArchProof for Arm64ProofGen {
    type Inst = PInst;
    type Reg = PReg;
    
    fn abstract_inst(&self, inst: &Self::Inst) -> AbstractInst {
        use super::OperandSize;
        
        match inst {
            PInst::MovReg { dst, src, size } => AbstractInst::Move {
                dst: AbstractOperand::Reg(self.abstract_reg(dst)),
                src: AbstractOperand::Reg(self.abstract_reg(src)),
                size: match size {
                    OperandSize::Size32 => Size::S32,
                    OperandSize::Size64 => Size::S64,
                },
            },
            PInst::MovImm { dst, imm, size } => AbstractInst::Move {
                dst: AbstractOperand::Reg(self.abstract_reg(dst)),
                src: AbstractOperand::Imm(*imm as i64),
                size: match size {
                    OperandSize::Size32 => Size::S32,
                    OperandSize::Size64 => Size::S64,
                },
            },
            PInst::Svc { imm } => {
                // ARM64 syscall convention varies by OS
                match self.os {
                    crate::arch::target::OperatingSystem::Linux => {
                        // Linux: syscall number in X8, args in X0-X5
                        AbstractInst::Syscall {
                            num: 0, // Would need to track X8 value
                            args: vec![
                                AbstractOperand::Reg(AbstractReg::Gpr(0)),  // X0
                                AbstractOperand::Reg(AbstractReg::Gpr(1)),  // X1
                                AbstractOperand::Reg(AbstractReg::Gpr(2)),  // X2
                                AbstractOperand::Reg(AbstractReg::Gpr(3)),  // X3
                                AbstractOperand::Reg(AbstractReg::Gpr(4)),  // X4
                                AbstractOperand::Reg(AbstractReg::Gpr(5)),  // X5
                            ],
                            ret: Some(AbstractReg::Gpr(0)), // X0
                        }
                    },
                    crate::arch::target::OperatingSystem::MacOS => {
                        // macOS: syscall number in X16, args in X0-X5
                        AbstractInst::Syscall {
                            num: 0, // Would need to track X16 value
                            args: vec![
                                AbstractOperand::Reg(AbstractReg::Gpr(0)),  // X0
                                AbstractOperand::Reg(AbstractReg::Gpr(1)),  // X1
                                AbstractOperand::Reg(AbstractReg::Gpr(2)),  // X2
                                AbstractOperand::Reg(AbstractReg::Gpr(3)),  // X3
                                AbstractOperand::Reg(AbstractReg::Gpr(4)),  // X4
                                AbstractOperand::Reg(AbstractReg::Gpr(5)),  // X5
                            ],
                            ret: Some(AbstractReg::Gpr(0)), // X0
                        }
                    },
                    _ => panic!("Unsupported OS for ARM64 syscalls"),
                }
            },
            PInst::Ret => AbstractInst::Return {
                value: Some(AbstractOperand::Reg(AbstractReg::Gpr(0))), // X0
            },
            PInst::Adr { dst, offset } => {
                // ADR loads PC-relative address
                // This is ARM64-specific and doesn't map cleanly to abstract
                // We'd need to extend AbstractInst for this
                AbstractInst::Move {
                    dst: AbstractOperand::Reg(self.abstract_reg(dst)),
                    src: AbstractOperand::Imm(*offset as i64), // Simplified
                    size: Size::S64,
                }
            },
            _ => todo!("abstract other ARM64 instructions"),
        }
    }
    
    fn abstract_reg(&self, reg: &Self::Reg) -> AbstractReg {
        match reg.index() {
            0..=7 => AbstractReg::Argument(reg.index()), // X0-X7 are args
            8..=15 => AbstractReg::Gpr(reg.index()),     // X8-X15 are temp
            16 => AbstractReg::SyscallNum,                // X16 (macOS)
            29 => AbstractReg::FramePointer,              // X29/FP
            30 => AbstractReg::Gpr(30),                   // X30/LR
            31 => AbstractReg::StackPointer,              // X31/SP
            _ => AbstractReg::Gpr(reg.index()),
        }
    }
    
    fn calling_convention(&self) -> CallingConvention {
        match self.os {
            crate::arch::target::OperatingSystem::MacOS => CallingConvention::AppleArm64,
            _ => CallingConvention::Aapcs64,
        }
    }
    
    fn proof_obligations(&self, inst: &Self::Inst) -> Vec<ProofObligation> {
        match inst {
            PInst::Svc { imm } => {
                let syscall_reg = match self.os {
                    crate::arch::target::OperatingSystem::Linux => AbstractReg::Gpr(8),   // X8
                    crate::arch::target::OperatingSystem::MacOS => AbstractReg::Gpr(16),  // X16
                    _ => panic!("Unsupported OS"),
                };
                
                vec![
                    ProofObligation {
                        property: ProofProperty::RegisterValue {
                            reg: syscall_reg,
                            value: mir::Operand::Const(mir::Const {
                                k: mir::ConstKind::Int,
                                val: None,
                            }),
                        },
                        reason: format!("Syscall number must be in {:?}", syscall_reg),
                    },
                    ProofObligation {
                        property: ProofProperty::StackAlignment {
                            alignment: 16,
                        },
                        reason: "Stack must be 16-byte aligned for syscall".to_string(),
                    },
                ]
            },
            PInst::Bl { .. } => vec![
                ProofObligation {
                    property: ProofProperty::StackAlignment {
                        alignment: 16,
                    },
                    reason: "Stack must be 16-byte aligned before BL".to_string(),
                },
                ProofObligation {
                    property: ProofProperty::RegisterValue {
                        reg: AbstractReg::Gpr(30), // LR
                        value: mir::Operand::Var(0), // Return address
                    },
                    reason: "BL sets LR to return address".to_string(),
                },
            ],
            _ => vec![],
        }
    }
    
    fn verify_property(
        &self,
        pre: &ProofProperty,
        insts: &[Self::Inst],
        post: &ProofProperty,
    ) -> Result<(), String> {
        // Placeholder for actual verification
        Ok(())
    }
}

impl ProofGen for Arm64ProofGen {
    fn prove_move(
        &self,
        dst: &Self::Reg,
        src: &AbstractOperand,
        size: Size,
    ) -> ProofTerm {
        ProofTerm {
            conclusion: ProofProperty::RegisterValue {
                reg: self.abstract_reg(dst),
                value: mir::Operand::Var(0), // Placeholder
            },
            steps: vec![
                ProofStep {
                    claim: format!("MOV {:?}, {:?} transfers value", dst, src),
                    reason: ProofReason::InstructionSemantics,
                },
            ],
        }
    }
    
    fn prove_syscall(
        &self,
        num: u32,
        args: &[Self::Reg],
    ) -> ProofTerm {
        let (syscall_reg, convention) = match self.os {
            crate::arch::target::OperatingSystem::Linux => ("X8", "Linux ARM64 ABI"),
            crate::arch::target::OperatingSystem::MacOS => ("X16", "macOS ARM64 ABI"),
            _ => panic!("Unsupported OS"),
        };
        
        ProofTerm {
            conclusion: ProofProperty::CallingConvention {
                target: CallTarget::External(Symbol::new("syscall")),
                convention: self.calling_convention(),
            },
            steps: vec![
                ProofStep {
                    claim: format!("SVC follows {}", convention),
                    reason: ProofReason::CallingConvention,
                },
                ProofStep {
                    claim: format!("Syscall number {} in {}", num, syscall_reg),
                    reason: ProofReason::CallingConvention,
                },
                ProofStep {
                    claim: "Arguments in X0-X5, return in X0".to_string(),
                    reason: ProofReason::CallingConvention,
                },
            ],
        }
    }
    
    fn prove_call(
        &self,
        target: &CallTarget,
        args: &[Self::Reg],
    ) -> ProofTerm {
        ProofTerm {
            conclusion: ProofProperty::CallingConvention {
                target: target.clone(),
                convention: self.calling_convention(),
            },
            steps: vec![
                ProofStep {
                    claim: "BL follows ARM64 AAPCS".to_string(),
                    reason: ProofReason::CallingConvention,
                },
                ProofStep {
                    claim: "First 8 args in X0-X7".to_string(),
                    reason: ProofReason::CallingConvention,
                },
                ProofStep {
                    claim: "Return address saved in X30/LR".to_string(),
                    reason: ProofReason::InstructionSemantics,
                },
                ProofStep {
                    claim: "Additional args on stack".to_string(),
                    reason: ProofReason::CallingConvention,
                },
            ],
        }
    }
    
    fn prove_stack_op(
        &self,
        op: StackOp,
        size: u32,
    ) -> ProofTerm {
        match op {
            StackOp::Alloc(n) => ProofTerm {
                conclusion: ProofProperty::StackAlignment { alignment: 16 },
                steps: vec![
                    ProofStep {
                        claim: format!("SUB SP, SP, #{} maintains alignment", n),
                        reason: ProofReason::InstructionSemantics,
                    },
                ],
            },
            StackOp::Push(val) => ProofTerm {
                conclusion: ProofProperty::MemoryValue {
                    addr: AbstractOperand::Mem(AbstractReg::StackPointer, -16),
                    value: mir::Operand::Var(0), // Placeholder
                    size: Size::S64,
                },
                steps: vec![
                    ProofStep {
                        claim: "STR X, [SP, #-16]! pre-decrements SP".to_string(),
                        reason: ProofReason::InstructionSemantics,
                    },
                    ProofStep {
                        claim: "Value stored at new SP location".to_string(),
                        reason: ProofReason::MemoryModel,
                    },
                ],
            },
            _ => todo!("prove other stack operations"),
        }
    }
}

/// ARM64-specific proof properties
pub mod arm64_properties {
    use super::*;
    
    /// Verify that PSTATE flags are preserved across calls
    pub fn preserves_flags(insts: &[PInst]) -> ProofProperty {
        ProofProperty::RegisterValue {
            reg: AbstractReg::Gpr(32), // Fictional PSTATE register
            value: mir::Operand::Var(0),
        }
    }
    
    /// Verify that stack red zone is respected (macOS specific)
    pub fn respects_red_zone(insts: &[PInst]) -> ProofProperty {
        ProofProperty::MemoryValue {
            addr: AbstractOperand::Mem(AbstractReg::StackPointer, -128),
            value: mir::Operand::Var(0),
            size: mir::Size::S8,
        }
    }
}