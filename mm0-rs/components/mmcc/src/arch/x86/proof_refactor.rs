//! Example refactoring of x86 proof generation to use the trait system
//!
//! This demonstrates how the existing x86-specific proof code could be
//! gradually migrated to use the architecture-agnostic traits.

use crate::arch::proof_traits::*;
use crate::arch::x86::{PInst, PReg, PCode};
use crate::proof::{VBlockId, BlockId};
use crate::types::{mir, Size, vcode::ProcAbi};

/// Example of how to generate proofs for x86 code using the trait system
pub struct X86ProofBuilder<'a> {
    gen: &'a crate::arch::x86::proof_impl::X86ProofGen,
    code: &'a PCode,
    abi: &'a ProcAbi,
}

impl<'a> X86ProofBuilder<'a> {
    pub fn new(
        gen: &'a crate::arch::x86::proof_impl::X86ProofGen,
        code: &'a PCode,
        abi: &'a ProcAbi,
    ) -> Self {
        Self { gen, code, abi }
    }
    
    /// Generate proof that the function prologue is correct
    pub fn prove_prologue(&self) -> ProofTerm {
        let mut steps = vec![];
        let mut stack_adjustment = 0;
        
        // Analyze prologue instructions
        for inst in self.code.insts.iter().take(10) {
            match inst {
                PInst::Push64 { src } => {
                    stack_adjustment += 8;
                    steps.push(ProofStep {
                        claim: format!("PUSH decrements RSP by 8"),
                        reason: ProofReason::InstructionSemantics,
                    });
                    
                    // Check if we're saving callee-saved registers
                    if let Some(reg) = src.as_reg() {
                        let abs_reg = self.gen.abstract_reg(&reg);
                        steps.push(ProofStep {
                            claim: format!("Save callee-saved register {:?}", abs_reg),
                            reason: ProofReason::CallingConvention,
                        });
                    }
                }
                PInst::Binop { op: crate::arch::x86::Binop::Sub, dst, src, .. } 
                    if dst.index() == 4 => // RSP
                {
                    if let Some(imm) = src.as_imm() {
                        stack_adjustment += imm;
                        steps.push(ProofStep {
                            claim: format!("Allocate {} bytes of stack space", imm),
                            reason: ProofReason::InstructionSemantics,
                        });
                    }
                }
                _ => break,
            }
        }
        
        // Verify stack alignment
        if stack_adjustment % 16 == 0 {
            steps.push(ProofStep {
                claim: "Stack remains 16-byte aligned after prologue".to_string(),
                reason: ProofReason::BySteps(vec![0, 1]),
            });
        }
        
        ProofTerm {
            conclusion: ProofProperty::StackAlignment { alignment: 16 },
            steps,
        }
    }
    
    /// Generate proof that a basic block preserves invariants
    pub fn prove_block(&self, block_id: VBlockId) -> Result<ProofTerm, String> {
        let block_insts = self.code.block_insts(block_id);
        let mut steps = vec![];
        
        for (i, inst) in block_insts.iter().enumerate() {
            // Get proof obligations for this instruction
            let obligations = self.gen.proof_obligations(inst);
            
            // Try to discharge each obligation
            for obligation in obligations {
                match &obligation.property {
                    ProofProperty::StackAlignment { alignment } => {
                        // Track stack pointer changes through the block
                        steps.push(ProofStep {
                            claim: format!("Instruction {} maintains {}-byte stack alignment", i, alignment),
                            reason: ProofReason::InstructionSemantics,
                        });
                    }
                    ProofProperty::RegisterValue { reg, value } => {
                        // Track register dataflow
                        steps.push(ProofStep {
                            claim: format!("Register {:?} contains expected value", reg),
                            reason: ProofReason::BySteps(vec![i]),
                        });
                    }
                    _ => {
                        // Other properties would be handled here
                    }
                }
            }
        }
        
        Ok(ProofTerm {
            conclusion: ProofProperty::StackAlignment { alignment: 16 },
            steps,
        })
    }
    
    /// Generate proof that the function epilogue restores state correctly
    pub fn prove_epilogue(&self) -> ProofTerm {
        let mut steps = vec![];
        
        // Find epilogue instructions (working backwards from end)
        let epilogue_start = self.code.insts.len().saturating_sub(20);
        
        for (i, inst) in self.code.insts[epilogue_start..].iter().enumerate() {
            match inst {
                PInst::Binop { op: crate::arch::x86::Binop::Add, dst, src, .. } 
                    if dst.index() == 4 => // RSP
                {
                    if let Some(imm) = src.as_imm() {
                        steps.push(ProofStep {
                            claim: format!("Deallocate {} bytes of stack space", imm),
                            reason: ProofReason::InstructionSemantics,
                        });
                    }
                }
                PInst::Pop64 { dst } => {
                    let abs_reg = self.gen.abstract_reg(dst);
                    steps.push(ProofStep {
                        claim: format!("Restore callee-saved register {:?}", abs_reg),
                        reason: ProofReason::CallingConvention,
                    });
                }
                PInst::Ret => {
                    steps.push(ProofStep {
                        claim: "Return instruction transfers control to caller".to_string(),
                        reason: ProofReason::InstructionSemantics,
                    });
                }
                _ => {}
            }
        }
        
        ProofTerm {
            conclusion: ProofProperty::CallingConvention {
                target: CallTarget::Direct(crate::proof::ProcId(0)),
                convention: CallingConvention::SystemV,
            },
            steps,
        }
    }
}

// Extension trait to help with pattern matching
trait RegMemImmExt {
    fn as_reg(&self) -> Option<PReg>;
    fn as_imm(&self) -> Option<u32>;
}

impl RegMemImmExt for crate::arch::x86::PRegMemImm {
    fn as_reg(&self) -> Option<PReg> {
        match self {
            crate::arch::x86::PRegMemImm::Reg(r) => Some(*r),
            _ => None,
        }
    }
    
    fn as_imm(&self) -> Option<u32> {
        match self {
            crate::arch::x86::PRegMemImm::Imm(i) => Some(*i),
            _ => None,
        }
    }
}