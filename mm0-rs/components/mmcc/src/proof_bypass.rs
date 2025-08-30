//! Proof system bypass for non-x86 architectures
//!
//! This module provides a way to bypass proof generation for architectures
//! that don't yet have proof support, while maintaining the compilation pipeline.

use crate::arch::target::Target;
use std::sync::atomic::{AtomicBool, Ordering};

/// Global flag to control proof generation
static PROOF_GENERATION_ENABLED: AtomicBool = AtomicBool::new(true);

/// Check if proof generation is enabled
pub fn is_proof_enabled() -> bool {
    PROOF_GENERATION_ENABLED.load(Ordering::Relaxed)
}

/// Temporarily disable proof generation
pub fn disable_proofs() {
    PROOF_GENERATION_ENABLED.store(false, Ordering::Relaxed);
}

/// Re-enable proof generation
pub fn enable_proofs() {
    PROOF_GENERATION_ENABLED.store(true, Ordering::Relaxed);
}

/// Guard that disables proofs in its scope and re-enables on drop
pub struct ProofBypassGuard {
    was_enabled: bool,
}

impl ProofBypassGuard {
    /// Create a new proof bypass guard
    pub fn new() -> Self {
        let was_enabled = is_proof_enabled();
        disable_proofs();
        Self { was_enabled }
    }
}

impl Drop for ProofBypassGuard {
    fn drop(&mut self) {
        if self.was_enabled {
            enable_proofs();
        }
    }
}

/// Check if proofs should be generated for a target
pub fn should_generate_proofs(target: &Target) -> bool {
    use crate::arch::target::TargetArch;
    
    // Only x86_64 has proof support currently
    match target.arch {
        TargetArch::X86_64 => is_proof_enabled(),
        TargetArch::Arm64 => {
            // ARM64 doesn't have proof support yet
            if is_proof_enabled() {
                eprintln!("WARNING: Proof generation not yet supported for ARM64, bypassing proofs");
            }
            false
        }
        TargetArch::Wasm32 | TargetArch::Wasm64 => {
            if is_proof_enabled() {
                eprintln!("WARNING: Proof generation not yet supported for WASM, bypassing proofs");
            }
            false
        }
    }
}

/// Macro to conditionally execute code only when proofs are enabled
#[macro_export]
macro_rules! with_proofs {
    ($body:expr) => {
        if $crate::proof_bypass::is_proof_enabled() {
            $body
        }
    };
}

/// Macro to conditionally execute code based on target architecture
#[macro_export]
macro_rules! with_target_proofs {
    ($target:expr, $body:expr) => {
        if $crate::proof_bypass::should_generate_proofs($target) {
            $body
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_proof_bypass_guard() {
        assert!(is_proof_enabled());
        
        {
            let _guard = ProofBypassGuard::new();
            assert!(!is_proof_enabled());
        }
        
        assert!(is_proof_enabled());
    }
    
    #[test]
    fn test_should_generate_proofs() {
        use crate::arch::target::{Target, TargetArch, OperatingSystem};
        
        let x86_target = Target {
            arch: TargetArch::X86_64,
            os: OperatingSystem::Linux,
        };
        assert!(should_generate_proofs(&x86_target));
        
        let arm64_target = Target {
            arch: TargetArch::Arm64,
            os: OperatingSystem::MacOS,
        };
        assert!(!should_generate_proofs(&arm64_target));
    }
}