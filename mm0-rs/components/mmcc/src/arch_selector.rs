//! Architecture selection and configuration
//!
//! This module provides the mechanism to select which architecture to compile for.

use crate::arch::target::{Target, TargetArch};

/// Architecture configuration
#[derive(Debug, Clone)]
pub struct ArchConfig {
    pub target: Target,
}

impl Default for ArchConfig {
    fn default() -> Self {
        Self {
            target: Target::current(),
        }
    }
}

impl ArchConfig {
    /// Create config for a specific target triple
    pub fn from_triple(triple: &str) -> Result<Self, String> {
        Ok(Self {
            target: Target::from_triple(triple)?,
        })
    }
    
    /// Check if this is an x86-64 target
    pub fn is_x86_64(&self) -> bool {
        matches!(self.target.arch, TargetArch::X86_64)
    }
    
    /// Check if this is an ARM64 target
    pub fn is_arm64(&self) -> bool {
        matches!(self.target.arch, TargetArch::Arm64)
    }
    
    /// Check if this is a WebAssembly target
    pub fn is_wasm(&self) -> bool {
        matches!(self.target.arch, TargetArch::Wasm32 | TargetArch::Wasm64)
    }
}

/// Global architecture configuration
/// This will be replaced with proper configuration once we refactor the compiler
pub static ARCH_CONFIG: std::sync::LazyLock<ArchConfig> = std::sync::LazyLock::new(|| {
    // For now, default to current platform
    // TODO: Add command-line option to override
    ArchConfig::default()
});