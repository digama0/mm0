//! Compatibility layer for ARM64 to work with x86-centric vcode types
//!
//! This is a temporary solution until vcode is properly abstracted

use crate::types::vcode::ArgAbi;
use crate::types::Size;
use super::PReg as Arm64PReg;

/// Convert ARM64 PReg to x86 PReg for ArgAbi compatibility
pub fn convert_arg_abi(arm64_reg: Arm64PReg, size: Size) -> ArgAbi {
    // Map ARM64 register to equivalent x86 register number
    // This is a hack but allows us to test ARM64 code generation
    let x86_preg = crate::arch::x86::PReg::new(arm64_reg.index() as usize);
    ArgAbi::Reg(x86_preg, size)
}

/// Convert stack argument to ArgAbi
pub fn stack_arg_abi(offset: u32, size: u32) -> ArgAbi {
    ArgAbi::Mem { off: offset, sz: size }
}