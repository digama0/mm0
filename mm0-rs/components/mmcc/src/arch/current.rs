//! Current architecture selection
//!
//! This module provides a way to select the current compilation target
//! architecture at compile time, allowing the vcode module to work with
//! different architectures without being parameterized everywhere.

use super::arch_types::*;

/// The currently selected architecture for compilation
/// 
/// This can be controlled by features or configuration in the future.
#[cfg(all(not(feature = "arm64-backend"), not(feature = "wasm-backend")))]
pub type CurrentArch = X86Arch;

#[cfg(feature = "arm64-backend")]
pub type CurrentArch = Arm64Arch;

#[cfg(feature = "wasm-backend")]
pub type CurrentArch = WasmArch;

/// Physical register type for the current architecture
pub type PReg = <CurrentArch as ArchitectureTypes>::PReg;

/// Physical register set type for the current architecture  
pub type PRegSet = <CurrentArch as ArchitectureTypes>::PRegSet;

/// Get the name of the current architecture
pub fn arch_name() -> &'static str {
    CurrentArch::name()
}

/// Check if we're compiling for x86
pub fn is_x86() -> bool {
    CurrentArch::name() == "x86-64"
}

/// Check if we're compiling for ARM64
pub fn is_arm64() -> bool {
    CurrentArch::name() == "arm64"
}

/// Check if we're compiling for WASM
pub fn is_wasm() -> bool {
    CurrentArch::name() == "wasm32"
}