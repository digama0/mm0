//! Architecture-specific parts of the compiler.
//!
//! This module provides abstractions for different target architectures,
//! including register machines (x86-64, ARM64) and stack machines (WebAssembly).

pub mod traits;
pub mod target;

// Architecture implementations
pub mod x86;
pub mod arm64;
pub mod wasm;

use target::Target;
use traits::Architecture;

/// Select architecture based on target
pub fn select_arch(target: Target) -> Box<dyn ArchitectureImpl> {
    use target::TargetArch;
    
    match target.arch {
        TargetArch::X86_64 => Box::new(X86_64Arch { target }),
        TargetArch::Arm64 => Box::new(Arm64Arch { target }),
        TargetArch::Wasm32 | TargetArch::Wasm64 => Box::new(WasmArch { target }),
    }
}

/// Dynamic architecture implementation
pub trait ArchitectureImpl {
    fn target(&self) -> Target;
    
    // Add methods that need dynamic dispatch here
    // Most of the Architecture trait methods are static, so we need
    // a different approach for runtime selection
}

struct X86_64Arch {
    target: Target,
}

impl ArchitectureImpl for X86_64Arch {
    fn target(&self) -> Target {
        self.target
    }
}

struct Arm64Arch {
    target: Target,
}

impl ArchitectureImpl for Arm64Arch {
    fn target(&self) -> Target {
        self.target
    }
}

struct WasmArch {
    target: Target,
}

impl ArchitectureImpl for WasmArch {
    fn target(&self) -> Target {
        self.target
    }
}

// For now, continue to export x86 as the default
// This allows gradual migration
pub use x86::*;