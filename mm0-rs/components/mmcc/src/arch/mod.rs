//! Architecture-specific parts of the compiler.

// Architecture modules
pub mod x86;
pub mod arm64;
pub mod wasm;
pub mod target;
pub mod traits;

// Re-export x86 as default for backward compatibility
pub use x86::*;
