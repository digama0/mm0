//! Architecture-specific parts of the compiler.

// Architecture modules
pub mod x86;
pub mod arm64;
pub mod wasm;
pub mod target;
pub mod traits;
pub mod proof_traits;

// Re-export common types
pub use target::{Target, TargetArch, OperatingSystem};

// TODO: The following modules currently depend on x86-specific types:
// - regalloc.rs: Assumes x86 architecture for register allocation
// - build_vcode.rs: Uses x86 instruction types
// - proof.rs: References x86 PCode directly
// 
// These dependencies need to be refactored to use the Architecture trait
// or be parameterized by architecture type.
//
// For now, x86 types must be used directly as arch::x86::Type
// This makes the architecture dependency explicit.
