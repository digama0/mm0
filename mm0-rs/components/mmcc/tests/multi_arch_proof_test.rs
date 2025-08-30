//! Integration tests for multi-architecture proof generation
//!
//! These tests verify that the trait-based proof system works correctly
//! across different architectures.

use mmcc::arch::proof_traits::*;
use mmcc::arch::target::{Target, TargetArch, OperatingSystem};
use mmcc::proof_gen::ProofGenFactory;

#[test]
fn test_proof_gen_factory_all_architectures() {
    // Test all supported architectures
    let architectures = vec![
        (TargetArch::X86_64, OperatingSystem::Linux, true),
        (TargetArch::X86_64, OperatingSystem::MacOS, true),
        (TargetArch::X86_64, OperatingSystem::Windows, true),
        (TargetArch::Aarch64, OperatingSystem::Linux, false),
        (TargetArch::Aarch64, OperatingSystem::MacOS, false),
        (TargetArch::Wasm32, OperatingSystem::Wasi, false),
    ];
    
    for (arch, os, expected_support) in architectures {
        let target = Target { arch, os };
        let adapter = ProofGenFactory::create(target);
        assert_eq!(
            adapter.supports_proofs(),
            expected_support,
            "Unexpected proof support for {:?}/{:?}",
            arch, os
        );
    }
}

#[test]
fn test_abstract_instruction_consistency() {
    use mmcc::arch::x86::proof_impl::X86ProofGen;
    use mmcc::arch::arm64::proof_impl::Arm64ProofGen;
    
    let x86_gen = X86ProofGen;
    let arm64_gen = Arm64ProofGen::new(OperatingSystem::MacOS);
    
    // Both architectures should abstract return instructions similarly
    let x86_ret = mmcc::arch::x86::PInst::Ret;
    let arm64_ret = mmcc::arch::arm64::PInst::Ret;
    
    let x86_abstract = x86_gen.abstract_inst(&x86_ret);
    let arm64_abstract = arm64_gen.abstract_inst(&arm64_ret);
    
    match (x86_abstract, arm64_abstract) {
        (AbstractInst::Return { .. }, AbstractInst::Return { .. }) => {
            // Both correctly abstract to Return
        }
        _ => panic!("Return instructions should abstract consistently"),
    }
}

#[test]
fn test_calling_convention_mapping() {
    use mmcc::arch::x86::proof_impl::X86ProofGen;
    use mmcc::arch::arm64::proof_impl::Arm64ProofGen;
    
    // x86-64 Linux uses System V
    let x86_linux_gen = X86ProofGen;
    assert!(matches!(
        x86_linux_gen.calling_convention(),
        CallingConvention::SystemV
    ));
    
    // ARM64 macOS uses Apple ARM64 ABI
    let arm64_macos_gen = Arm64ProofGen::new(OperatingSystem::MacOS);
    assert!(matches!(
        arm64_macos_gen.calling_convention(),
        CallingConvention::AppleArm64
    ));
    
    // ARM64 Linux uses AAPCS64
    let arm64_linux_gen = Arm64ProofGen::new(OperatingSystem::Linux);
    assert!(matches!(
        arm64_linux_gen.calling_convention(),
        CallingConvention::Aapcs64
    ));
}

#[test]
fn test_syscall_abstraction() {
    use mmcc::arch::x86::proof_impl::X86ProofGen;
    use mmcc::arch::arm64::proof_impl::Arm64ProofGen;
    
    let x86_gen = X86ProofGen;
    let arm64_gen = Arm64ProofGen::new(OperatingSystem::MacOS);
    
    // Test syscall abstraction
    let x86_syscall = mmcc::arch::x86::PInst::SysCall;
    let arm64_syscall = mmcc::arch::arm64::PInst::Svc { imm: 0x80 };
    
    let x86_abstract = x86_gen.abstract_inst(&x86_syscall);
    let arm64_abstract = arm64_gen.abstract_inst(&arm64_syscall);
    
    // Both should abstract to Syscall variant
    match (x86_abstract, arm64_abstract) {
        (
            AbstractInst::Syscall { args: x86_args, .. },
            AbstractInst::Syscall { args: arm64_args, .. }
        ) => {
            // x86-64 uses 6 syscall argument registers
            assert_eq!(x86_args.len(), 6);
            // ARM64 macOS uses 8 syscall argument registers
            assert_eq!(arm64_args.len(), 8);
        }
        _ => panic!("Syscalls should abstract to Syscall variant"),
    }
}

#[test]
fn test_proof_obligations_consistency() {
    use mmcc::arch::x86::proof_impl::X86ProofGen;
    use mmcc::arch::arm64::proof_impl::Arm64ProofGen;
    
    let x86_gen = X86ProofGen;
    let arm64_gen = Arm64ProofGen::new(OperatingSystem::MacOS);
    
    // Test that similar instructions generate similar obligations
    let x86_call = mmcc::arch::x86::PInst::Call { 
        dst: mmcc::arch::x86::RegMemImm::Imm(0x1000) 
    };
    let arm64_call = mmcc::arch::arm64::PInst::Bl { offset: 0x1000 };
    
    let x86_obligations = x86_gen.proof_obligations(&x86_call);
    let arm64_obligations = arm64_gen.proof_obligations(&arm64_call);
    
    // Both should require stack alignment
    assert!(x86_obligations.iter().any(|o| matches!(
        &o.property,
        ProofProperty::StackAlignment { .. }
    )));
    assert!(arm64_obligations.iter().any(|o| matches!(
        &o.property,
        ProofProperty::StackAlignment { .. }
    )));
}

#[test]
fn test_abstract_register_mapping() {
    use mmcc::arch::x86::proof_impl::X86ProofGen;
    use mmcc::arch::arm64::proof_impl::Arm64ProofGen;
    
    let x86_gen = X86ProofGen;
    let arm64_gen = Arm64ProofGen::new(OperatingSystem::Linux);
    
    // Test special register mappings
    let x86_sp = mmcc::arch::x86::PReg::new(4); // RSP
    let arm64_sp = mmcc::arch::arm64::PReg::new(31); // SP
    
    assert_eq!(
        x86_gen.abstract_reg(&x86_sp),
        AbstractReg::StackPointer
    );
    assert_eq!(
        arm64_gen.abstract_reg(&arm64_sp),
        AbstractReg::StackPointer
    );
    
    // Test return value register
    let x86_ret = mmcc::arch::x86::PReg::new(0); // RAX
    let arm64_ret = mmcc::arch::arm64::PReg::new(0); // X0
    
    // Note: The current implementation maps these as Gpr(0)
    // In a full implementation, we might want to distinguish return value registers
    assert_eq!(
        x86_gen.abstract_reg(&x86_ret),
        AbstractReg::Gpr(0)
    );
    assert_eq!(
        arm64_gen.abstract_reg(&arm64_ret),
        AbstractReg::Gpr(0)
    );
}