//! Architecture-specific parts of the compiler.

// Architecture modules
pub mod x86;
pub mod arm64;
pub mod wasm;
pub mod target;
pub mod traits;

// Re-export common types
pub use target::{Target, TargetArch, OperatingSystem};

// For now, keep x86 as the default architecture for backward compatibility
// We'll parameterize the pipeline instead of removing these exports
pub use x86::*;
