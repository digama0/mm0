//! ARM64 (AArch64) architecture support
//!
//! This module implements code generation for ARM64/AArch64 processors,
//! initially targeting Apple Silicon (M1/M2) for testing MM0 on macOS.

use std::fmt::{Debug, Display};
use crate::arch::{traits::*, target::Target};

mod regs;
mod inst;
// mod encode;  // TODO: implement encoding

pub use regs::*;
pub use inst::*;

/// ARM64 architecture implementation
pub struct Arm64;

impl Architecture for Arm64 {
    const KIND: ArchKind = ArchKind::RegisterMachine;
    const NAME: &'static str = "arm64";
    
    type PReg = PReg;
    type PRegSet = PRegSet;
    type Inst = Inst;
    type PInst = PInst;
    
    fn machine_env() -> &'static regalloc2::MachineEnv {
        &MACHINE_ENV
    }
    
    fn stack_pointer() -> Option<Self::PReg> {
        Some(SP)
    }
    
    fn callee_saved() -> &'static [Self::PReg] {
        &CALLEE_SAVED
    }
    
    fn caller_saved() -> &'static [Self::PReg] {
        &CALLER_SAVED
    }
    
    fn arg_regs() -> &'static [Self::PReg] {
        &ARG_REGS[..]
    }
    
    fn has_syscalls(target: Target) -> bool {
        matches!(target.os, crate::arch::target::OperatingSystem::Linux | 
                           crate::arch::target::OperatingSystem::MacOS)
    }
    
    fn syscall_arg_regs(target: Target) -> Option<(Self::PReg, &'static [Self::PReg])> {
        use crate::arch::target::OperatingSystem;
        
        match target.os {
            OperatingSystem::Linux => Some((X8, &SYSCALL_ARG_REGS[..])),
            OperatingSystem::MacOS => Some((X16, &SYSCALL_ARG_REGS[..])),
            _ => None,
        }
    }
}

// Machine environment for register allocation
use std::sync::LazyLock;
pub(crate) static MACHINE_ENV: LazyLock<regalloc2::MachineEnv> = LazyLock::new(|| {
    // ARM64 has 31 general-purpose registers (X0-X30)
    // X31 is either SP or ZR depending on context
    let caller_saved_regs: Vec<_> = CALLER_SAVED.iter().map(|r| r.to_regalloc()).collect();
    let callee_saved_regs: Vec<_> = CALLEE_SAVED.iter().map(|r| r.to_regalloc()).collect();
    
    regalloc2::MachineEnv {
        // Prefer caller-saved registers first
        preferred_regs_by_class: [caller_saved_regs, vec![], vec![]],
        // Then use callee-saved if needed
        non_preferred_regs_by_class: [callee_saved_regs, vec![], vec![]],
        // No scratch registers needed
        scratch_by_class: [None; 3],
        // No fixed stack slots
        fixed_stack_slots: vec![],
    }
});