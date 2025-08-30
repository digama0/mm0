//! Architecture type abstraction layer
//!
//! This module provides a bridge between architecture-specific types and
//! the generic vcode infrastructure. It allows gradual migration from
//! x86-specific code to architecture-agnostic code.

use crate::types::Size;
use std::fmt::Debug;

// Select architecture types based on compile-time features
// Default to x86 for compatibility

#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
pub use crate::arch::x86::{PReg, PRegSet};

#[cfg(feature = "arm64-backend")]
pub use crate::arch::arm64::{PReg, regs::PRegSet};

#[cfg(feature = "wasm-backend")]
pub use crate::arch::wasm::{WasmReg as PReg, WasmRegSet as PRegSet};

/// Trait for architecture-specific types
/// This will eventually replace the direct x86 imports
pub trait ArchitectureTypes: Sized {
    /// Physical register type
    type PReg: Copy + Clone + Debug + PartialEq + Eq;
    
    /// Physical register set type  
    type PRegSet: Copy + Clone + Debug + Default;
    
    /// Get the name of this architecture
    fn name() -> &'static str;
}

/// Marker type for x86 architecture
#[derive(Debug, Clone, Copy)]
pub struct X86Arch;

impl ArchitectureTypes for X86Arch {
    type PReg = crate::arch::x86::PReg;
    type PRegSet = crate::arch::x86::PRegSet;
    
    fn name() -> &'static str { "x86-64" }
}

/// Marker type for ARM64 architecture
#[derive(Debug, Clone, Copy)]
pub struct Arm64Arch;

impl ArchitectureTypes for Arm64Arch {
    type PReg = crate::arch::arm64::PReg;
    type PRegSet = crate::arch::arm64::regs::PRegSet;
    
    fn name() -> &'static str { "arm64" }
}

/// Marker type for WASM architecture
#[derive(Debug, Clone, Copy)]
pub struct WasmArch;

impl ArchitectureTypes for WasmArch {
    type PReg = crate::arch::wasm::WasmReg;
    type PRegSet = crate::arch::wasm::WasmRegSet;
    
    fn name() -> &'static str { "wasm32" }
}

/// Architecture-agnostic register trait
pub trait ArchReg: Copy + Clone + Debug + PartialEq + Eq {
    /// Check if this register is valid
    fn is_valid(&self) -> bool;
    
    /// Get an invalid register value
    fn invalid() -> Self;
}

impl ArchReg for crate::arch::x86::PReg {
    fn is_valid(&self) -> bool {
        crate::types::vcode::IsReg::is_valid(self)
    }
    
    fn invalid() -> Self {
        crate::types::vcode::IsReg::invalid()
    }
}

impl ArchReg for crate::arch::arm64::PReg {
    fn is_valid(&self) -> bool {
        use crate::arch::traits::PhysicalReg;
        PhysicalReg::is_valid(*self)
    }
    
    fn invalid() -> Self {
        use crate::arch::traits::PhysicalReg;
        PhysicalReg::invalid()
    }
}

impl ArchReg for crate::arch::wasm::WasmReg {
    fn is_valid(&self) -> bool {
        use crate::arch::traits::PhysicalReg;
        PhysicalReg::is_valid(*self)
    }
    
    fn invalid() -> Self {
        use crate::arch::traits::PhysicalReg;
        PhysicalReg::invalid()
    }
}

/// Architecture-agnostic register set trait
pub trait ArchRegSet<R: ArchReg>: Copy + Clone + Debug + Default {
    /// Insert a register into the set
    fn insert(&mut self, reg: R);
    
    /// Check if a register is in the set
    fn contains(&self, reg: R) -> bool;
    
    /// Remove a register from the set
    fn remove(&mut self, reg: R);
}

// Note: We'll implement these traits for the concrete types once we
// update the register set implementations to have consistent interfaces