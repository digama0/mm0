# Architecture Coupling Issues in MM0 Compiler

## Summary

The MM0 compiler has significant architectural coupling issues that prevent proper multi-architecture support. While trying to add ARM64 support, we discovered that core modules are hardcoded to use x86-specific types.

## Key Problems

### 1. vcode.rs Hardcoded to x86
**File**: `components/mmcc/src/types/vcode.rs`
**Issue**: Line 5 imports x86 types directly:
```rust
use crate::{arch::x86::{PReg, PRegSet}, types::{mir, IdxVec}, Idx};
```

This means:
- `ArgAbi` enum uses x86's `PReg` type
- `ProcAbi` struct uses x86's `PRegSet` type
- Any architecture trying to use `vcode` types must provide x86-compatible types

### 2. regalloc.rs Hardcoded to x86
**File**: `components/mmcc/src/regalloc.rs`
**Issue**: Lines 16-17 import x86 types:
```rust
use crate::arch::x86::{AMode, Inst, callee_saved, caller_saved, MACHINE_ENV, Offset, PAMode, PInst,
  PRegMem, PRegMemImm, PRegSet, PShiftIndex, RSP, PReg, RegMem, RegMemImm};
```

This module is completely x86-specific and can't be used by other architectures.

### 3. Impact on ARM64 Implementation
When trying to implement ARM64 support:
- ARM64's `PReg` type is incompatible with x86's `PReg`
- ARM64 calling convention can't return proper `ArgAbi` values
- ARM64 can't use the common `vcode` infrastructure

## Workarounds Attempted

1. **Proof System**: Successfully created architecture-agnostic traits
2. **x86 Export Removal**: Made x86 imports explicit (but didn't solve the core issue)
3. **ARM64 Parallel Implementation**: Created separate ARM64 modules, but can't integrate

## Recommended Solution

The codebase needs significant refactoring to support multiple architectures:

1. **Create Architecture Traits**: Define traits for `PReg`, `PRegSet`, etc.
2. **Parameterize vcode Types**: Make `ArgAbi`, `ProcAbi` generic over architecture
3. **Architecture-Specific Implementations**: Each architecture provides its own types
4. **Factory Pattern**: Use architecture selection to instantiate correct types

## Current State

- x86 support: Working (as it's the default)
- ARM64 support: Partially implemented but can't compile due to type conflicts
- WASM support: Exists but likely has similar issues

## Next Steps

1. Decide whether to:
   - Accept x86-only compilation for now
   - Undertake major refactoring to support multi-arch
   - Create a compatibility layer for ARM64

2. If refactoring:
   - Start with making `vcode.rs` generic
   - Update `regalloc.rs` to use traits
   - Test x86 still works after changes
   - Then integrate ARM64 properly