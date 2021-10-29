//! Architecture-specific parts of the compiler.

// We only support x86 at the moment.
mod x86;
pub use x86::*;
