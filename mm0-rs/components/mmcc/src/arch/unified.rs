//! Unified architecture types
//!
//! This module provides architecture-agnostic types that can represent
//! registers and other architecture-specific values from any supported
//! architecture. This allows vcode to work with multiple architectures
//! without needing to be parameterized.

use std::fmt::{Debug, Display};

/// A unified physical register that can be from any architecture
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum UnifiedPReg {
    X86(crate::arch::x86::PReg),
    Arm64(crate::arch::arm64::PReg),
    Wasm(crate::arch::wasm::WasmReg),
}

impl Debug for UnifiedPReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnifiedPReg::X86(r) => write!(f, "x86:{:?}", r),
            UnifiedPReg::Arm64(r) => write!(f, "arm64:{:?}", r),
            UnifiedPReg::Wasm(r) => write!(f, "wasm:{:?}", r),
        }
    }
}

impl Display for UnifiedPReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnifiedPReg::X86(r) => Display::fmt(r, f),
            UnifiedPReg::Arm64(r) => Display::fmt(r, f),
            UnifiedPReg::Wasm(r) => Display::fmt(r, f),
        }
    }
}

impl crate::types::vcode::IsReg for UnifiedPReg {
    fn invalid() -> Self {
        // Default to x86 for compatibility
        UnifiedPReg::X86(crate::types::vcode::IsReg::invalid())
    }
    
    fn is_valid(&self) -> bool {
        match self {
            UnifiedPReg::X86(r) => crate::types::vcode::IsReg::is_valid(r),
            UnifiedPReg::Arm64(r) => {
                use crate::arch::traits::PhysicalReg;
                r.is_valid()
            },
            UnifiedPReg::Wasm(r) => {
                use crate::arch::traits::PhysicalReg;
                r.is_valid()
            },
        }
    }
}

/// A unified register set that can contain registers from any architecture
#[derive(Copy, Clone, Debug, Default)]
pub struct UnifiedPRegSet {
    x86: Option<crate::arch::x86::PRegSet>,
    arm64: Option<crate::arch::arm64::regs::PRegSet>,
    wasm: Option<crate::arch::wasm::WasmRegSet>,
}

impl UnifiedPRegSet {
    pub fn new_x86(set: crate::arch::x86::PRegSet) -> Self {
        Self { x86: Some(set), arm64: None, wasm: None }
    }
    
    pub fn new_arm64(set: crate::arch::arm64::regs::PRegSet) -> Self {
        Self { x86: None, arm64: Some(set), wasm: None }
    }
    
    pub fn new_wasm(set: crate::arch::wasm::WasmRegSet) -> Self {
        Self { x86: None, arm64: None, wasm: Some(set) }
    }
    
    pub fn insert(&mut self, reg: UnifiedPReg) {
        match (reg, &mut self.x86, &mut self.arm64, &mut self.wasm) {
            (UnifiedPReg::X86(r), Some(ref mut set), _, _) => {
                use crate::arch::x86::PRegSet as X86Set;
                X86Set::insert(set, r);
            },
            (UnifiedPReg::Arm64(r), _, Some(ref mut set), _) => {
                set.insert(r);
            },
            (UnifiedPReg::Wasm(r), _, _, Some(ref mut set)) => {
                use crate::arch::traits::RegisterSet;
                set.insert(r);
            },
            _ => panic!("Register type mismatch with set type"),
        }
    }
}

// Conversion implementations for seamless integration

impl From<crate::arch::x86::PReg> for UnifiedPReg {
    fn from(r: crate::arch::x86::PReg) -> Self {
        UnifiedPReg::X86(r)
    }
}

impl From<crate::arch::arm64::PReg> for UnifiedPReg {
    fn from(r: crate::arch::arm64::PReg) -> Self {
        UnifiedPReg::Arm64(r)
    }
}

impl From<crate::arch::wasm::WasmReg> for UnifiedPReg {
    fn from(r: crate::arch::wasm::WasmReg) -> Self {
        UnifiedPReg::Wasm(r)
    }
}

impl From<crate::arch::x86::PRegSet> for UnifiedPRegSet {
    fn from(s: crate::arch::x86::PRegSet) -> Self {
        Self::new_x86(s)
    }
}

impl From<crate::arch::arm64::regs::PRegSet> for UnifiedPRegSet {
    fn from(s: crate::arch::arm64::regs::PRegSet) -> Self {
        Self::new_arm64(s)
    }
}

impl From<crate::arch::wasm::WasmRegSet> for UnifiedPRegSet {
    fn from(s: crate::arch::wasm::WasmRegSet) -> Self {
        Self::new_wasm(s)
    }
}