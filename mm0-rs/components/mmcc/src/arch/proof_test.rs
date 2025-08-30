//! Test demonstrating architecture-agnostic proof generation
//!
//! This shows how the same high-level program can generate different
//! proofs for different architectures while maintaining correctness.

#[cfg(test)]
mod tests {
    use crate::arch::proof_traits::*;
    use crate::arch::target::{OperatingSystem, TargetArch};
    
    /// Test that exit syscall proofs work for both architectures
    #[test]
    fn test_exit_syscall_proof() {
        // Create proof generators for both architectures
        let x86_gen = crate::arch::x86::proof_impl::X86ProofGen;
        let arm64_gen = crate::arch::arm64::proof_impl::Arm64ProofGen::new(
            OperatingSystem::MacOS
        );
        
        // Test x86 exit syscall
        {
            use crate::arch::x86::{PReg, PInst};
            
            // MOV RAX, 60  ; exit syscall number on Linux x86-64
            let mov_rax = PInst::MovRI {
                dst: PReg::new(0), // RAX
                src: 60,
            };
            
            // MOV RDI, 0   ; exit code
            let mov_rdi = PInst::MovRI {
                dst: PReg::new(7), // RDI
                src: 0,
            };
            
            // SYSCALL
            let syscall = PInst::Syscall;
            
            // Generate proof obligations
            let obligations = x86_gen.proof_obligations(&syscall);
            assert!(!obligations.is_empty());
            
            // Generate syscall proof
            let proof = ProofGen::prove_syscall(&x86_gen, 60, &[PReg::new(7)]);
            assert_eq!(proof.steps.len(), 2);
        }
        
        // Test ARM64 exit syscall
        {
            use crate::arch::arm64::{PReg, PInst, OperandSize};
            
            // MOV X0, #0    ; exit code
            let mov_x0 = PInst::MovImm {
                dst: PReg::new(0), // X0
                imm: 0,
                size: OperandSize::Size64,
            };
            
            // MOV X16, #1   ; exit syscall number on macOS
            let mov_x16 = PInst::MovImm {
                dst: PReg::new(16), // X16
                imm: 1,
                size: OperandSize::Size64,
            };
            
            // SVC #0x80     ; macOS syscall
            let svc = PInst::Svc { imm: 0x80 };
            
            // Generate proof obligations
            let obligations = arm64_gen.proof_obligations(&svc);
            assert!(!obligations.is_empty());
            
            // Generate syscall proof
            let proof = ProofGen::prove_syscall(&arm64_gen, 1, &[PReg::new(0)]);
            assert_eq!(proof.steps.len(), 3);
            
            // Verify the proof mentions the correct register
            assert!(proof.steps[1].claim.contains("X16"));
        }
    }
    
    /// Test that calling conventions are architecture-specific
    #[test]
    fn test_calling_conventions() {
        let x86_gen = crate::arch::x86::proof_impl::X86ProofGen;
        let arm64_gen = crate::arch::arm64::proof_impl::Arm64ProofGen::new(
            OperatingSystem::Linux
        );
        
        assert_eq!(x86_gen.calling_convention(), CallingConvention::SystemV);
        assert_eq!(arm64_gen.calling_convention(), CallingConvention::Aapcs64);
        
        // macOS has different convention
        let arm64_macos = crate::arch::arm64::proof_impl::Arm64ProofGen::new(
            OperatingSystem::MacOS
        );
        assert_eq!(arm64_macos.calling_convention(), CallingConvention::AppleArm64);
    }
    
    /// Test abstract instruction conversion
    #[test]
    fn test_abstract_inst() {
        use crate::arch::arm64::{PReg, PInst, OperandSize};
        
        let arm64_gen = crate::arch::arm64::proof_impl::Arm64ProofGen::new(
            OperatingSystem::MacOS
        );
        
        // Test move instruction abstraction
        let mov = PInst::MovReg {
            dst: PReg::new(1),
            src: PReg::new(0),
            size: OperandSize::Size64,
        };
        
        match arm64_gen.abstract_inst(&mov) {
            AbstractInst::Move { dst, src, size } => {
                assert_eq!(dst, AbstractOperand::Reg(AbstractReg::Argument(1)));
                assert_eq!(src, AbstractOperand::Reg(AbstractReg::Argument(0)));
                assert_eq!(size, crate::types::mir::Size::S64);
            }
            _ => panic!("Expected Move instruction"),
        }
    }
    
    /// Test that proof generation doesn't panic for basic instructions
    #[test]
    fn test_proof_generation_smoke() {
        use crate::arch::arm64::{PReg, PInst, OperandSize};
        
        let arm64_gen = crate::arch::arm64::proof_impl::Arm64ProofGen::new(
            OperatingSystem::MacOS
        );
        
        // Test various proof generations don't panic
        let _ = ProofGen::prove_move(
            &arm64_gen,
            &PReg::new(0),
            &AbstractOperand::Imm(42),
            crate::types::mir::Size::S64,
        );
        
        let _ = ProofGen::prove_stack_op(
            &arm64_gen,
            StackOp::Alloc(16),
            16,
        );
        
        let _ = ProofGen::prove_call(
            &arm64_gen,
            &CallTarget::External(crate::Symbol::new("printf")),
            &[PReg::new(0), PReg::new(1)],
        );
    }
}