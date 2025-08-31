//! Architecture-specific parts of the compiler.

// Architecture modules
#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
pub mod x86;
#[cfg(feature = "arm64-backend")]
pub mod arm64;
#[cfg(feature = "wasm-backend")]
pub mod wasm;
pub mod target;
pub mod traits;
#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
pub mod proof_traits;
pub mod arch_types;
pub mod current;

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
