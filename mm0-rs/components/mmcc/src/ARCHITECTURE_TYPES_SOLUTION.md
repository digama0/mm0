# Architecture Types Solution

## The Problem

The core issue is that `types/vcode.rs` imports `PReg` and `PRegSet` from `arch_types.rs`, which uses conditional compilation to select different types based on feature flags:

```rust
// In arch_types.rs
#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
pub use crate::arch::x86::{PReg, PRegSet};

#[cfg(feature = "arm64-backend")]
pub use crate::arch::arm64::{PReg, regs::PRegSet};
```

This means that fundamental types like `ArgAbi` and `ProcAbi` in vcode.rs have different definitions depending on which backend is selected, causing type mismatches.

## Solutions Attempted

### 1. Architecture-Specific Types (Partial Success)
Created `arch_vcode.rs` with architecture-specific traits and types:
- `ArchVCode` trait with associated types for PReg, PRegSet, etc.
- `ArchArgAbi<PReg>` parameterized by register type
- `ArchProcAbi<A: ArchVCode>` using associated types

This works but requires significant refactoring throughout the codebase.

### 2. Remove Global Imports (Failed)
Tried to remove PReg/PRegSet imports from vcode.rs, but these types are deeply embedded:
- `ArgAbi` enum contains PReg directly
- `ProcAbi` contains PRegSet for clobbers
- `VCode` contains ProcAbi
- Many other modules depend on these types

## Recommended Solution

### Short Term (Current Workaround)
1. **Build for one architecture at a time** - Don't mix feature flags
2. **Conditional compilation** - Disable x86 code when building for ARM64
3. **Architecture-specific modules** - Each architecture has its own types

### Long Term (Proper Fix)
The vcode module needs to be parameterized by architecture. Options:

#### Option 1: Generic VCode
```rust
pub struct VCode<A: Architecture> {
    abi: ProcAbi<A::PReg, A::PRegSet>,
    // ...
}
```

#### Option 2: Trait Objects
```rust
pub trait VCodeTrait {
    type PReg;
    type PRegSet;
    // ...
}
```

#### Option 3: Separate Modules
- `x86_vcode` module with x86-specific types
- `arm64_vcode` module with ARM64-specific types
- `wasm_vcode` module with WASM-specific types
- Common traits in a shared module

## Impact Analysis

A proper fix would require changes to:
- All uses of `ArgAbi` throughout the codebase
- All uses of `ProcAbi` throughout the codebase
- The `VCode` type and all its methods
- Register allocation interfaces
- Code generation modules
- The linker (which uses ProcAbi)

## Current Status

We've successfully:
1. ✅ Made LinkedCode architecture-agnostic (uses ArchPCode)
2. ✅ Created architecture-specific lowering infrastructure
3. ✅ Removed x86 hardcoding from many modules

But the fundamental type system issue remains. The compiler works when building for a single architecture but has type conflicts when features are mixed.

## Recommendation

For now, continue with the current approach:
1. Build for one architecture at a time
2. Use conditional compilation where needed
3. Keep architecture-specific code isolated

A full redesign of the vcode type system should be considered for a future major version when breaking changes are acceptable.