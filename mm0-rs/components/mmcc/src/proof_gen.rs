//! Bridge between trait-based proof generation and the existing proof system
//!
//! This module provides utilities to generate proofs using the architecture-agnostic
//! traits while maintaining compatibility with the existing x86-specific proof system.

use crate::arch::proof_traits::{ArchProof, ProofGen};
use crate::arch::target::{Target, TargetArch};
use crate::proof::{ElfProof, VBlockId};
use crate::LinkedCode;

/// Factory for creating architecture-specific proof generators
pub struct ProofGenFactory;

impl ProofGenFactory {
    /// Create a proof generator for the given target
    pub fn create(target: Target) -> Box<dyn ProofGenAdapter> {
        match target.arch {
            TargetArch::X86_64 => {
                use crate::arch::x86::proof_impl::X86ProofGen;
                Box::new(X86ProofGenAdapter {
                    proof_gen: X86ProofGen,
                })
            }
            TargetArch::Arm64 => {
                use crate::arch::arm64::proof_impl::Arm64ProofGen;
                Box::new(Arm64ProofGenAdapter {
                    proof_gen: Arm64ProofGen::new(target.os),
                })
            }
            _ => Box::new(NoOpProofGenAdapter),
        }
    }
}

/// Adapter trait to bridge architecture-specific proof generators with ElfProof
pub trait ProofGenAdapter: Send + Sync {
    /// Generate proof content for the given linked code
    fn generate_proof(&self, code: &LinkedCode) -> Vec<u8>;
    
    /// Check if this architecture supports proof generation
    fn supports_proofs(&self) -> bool;
}

/// Adapter for x86 proof generation
struct X86ProofGenAdapter {
    proof_gen: crate::arch::x86::proof_impl::X86ProofGen,
}

impl ProofGenAdapter for X86ProofGenAdapter {
    fn generate_proof(&self, _code: &LinkedCode) -> Vec<u8> {
        // For now, delegate to the existing x86-specific proof generation
        // This will be refactored to use the trait-based system
        vec![]
    }
    
    fn supports_proofs(&self) -> bool {
        true
    }
}

/// Adapter for ARM64 proof generation
struct Arm64ProofGenAdapter {
    proof_gen: crate::arch::arm64::proof_impl::Arm64ProofGen,
}

impl ProofGenAdapter for Arm64ProofGenAdapter {
    fn generate_proof(&self, _code: &LinkedCode) -> Vec<u8> {
        // ARM64 doesn't generate proofs yet, just returns empty
        vec![]
    }
    
    fn supports_proofs(&self) -> bool {
        false
    }
}

/// No-op adapter for architectures without proof support
struct NoOpProofGenAdapter;

impl ProofGenAdapter for NoOpProofGenAdapter {
    fn generate_proof(&self, _code: &LinkedCode) -> Vec<u8> {
        vec![]
    }
    
    fn supports_proofs(&self) -> bool {
        false
    }
}

/// Extension trait for ElfProof to use trait-based proof generation
pub trait ElfProofExt {
    /// Generate proofs using the trait-based system
    fn generate_with_traits(&mut self, target: Target, code: &LinkedCode);
}

impl<'a> ElfProofExt for ElfProof<'a> {
    fn generate_with_traits(&mut self, target: Target, code: &LinkedCode) {
        let adapter = ProofGenFactory::create(target);
        
        if adapter.supports_proofs() {
            // Generate proof content using the adapter
            let proof_data = adapter.generate_proof(code);
            
            // TODO: Integrate proof_data into the ElfProof structure
            // For now, this is a placeholder showing how the integration would work
        }
    }
}