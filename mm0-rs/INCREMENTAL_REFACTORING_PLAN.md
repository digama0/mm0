# Incremental Refactoring Plan for Multi-Architecture Support

## Summary

We've implemented the first phase of an incremental, safe approach to address the architecture coupling in the MM0 compiler. This document outlines what we've done and the path forward.

## Phase 1: Architecture Abstraction Layer ✅ COMPLETE

### What We Did
1. **Created `arch/arch_types.rs`**: An abstraction layer that provides a single import point for architecture-specific types
2. **Updated `types/vcode.rs`**: Changed from importing `arch::x86::{PReg, PRegSet}` directly to importing from `arch::arch_types`
3. **Added feature flags**: Created `arm64-backend` and `wasm-backend` features in Cargo.toml
4. **Fixed immediate issues**: Resolved several compilation errors (Clone for Arm64ConstTable, Aarch64 → Arm64, Ok() → Ok(()))

### Result
- The abstraction layer is in place
- x86 still compiles and works (default behavior unchanged)
- Foundation laid for architecture selection via features
- Reduced compilation errors from 7 to 4

## Phase 2: Conditional Architecture Selection (IN PROGRESS)

### Current State
The `arch_types` module conditionally exports the correct types based on feature flags:
```rust
#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
pub use crate::arch::x86::{PReg, PRegSet};

#[cfg(feature = "arm64-backend")]
pub use crate::arch::arm64::{PReg, regs::PRegSet};

#[cfg(feature = "wasm-backend")]
pub use crate::arch::wasm::{WasmReg as PReg, WasmRegSet as PRegSet};
```

### Remaining Issues
1. **Type mismatches**: ARM64 code expects ARM64 types, but vcode structures still expect x86 types
2. **regalloc.rs coupling**: The register allocator is completely x86-specific
3. **Cross-architecture compilation**: Currently can only compile for one architecture at a time

## Phase 3: Architecture-Specific Modules (TODO)

### Plan
1. **Create architecture-specific regalloc modules**:
   - `arch/x86/regalloc.rs`
   - `arch/arm64/regalloc.rs`  
   - `arch/wasm/regalloc.rs` (minimal, as WASM is stack-based)

2. **Update build_vcode to be architecture-aware**:
   - Move x86-specific code to `arch/x86/build_vcode.rs`
   - Create ARM64 and WASM equivalents

3. **Conditional compilation in lib.rs**:
   ```rust
   #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
   mod regalloc {
       pub use crate::arch::x86::regalloc::*;
   }
   
   #[cfg(feature = "arm64-backend")]
   mod regalloc {
       pub use crate::arch::arm64::regalloc::*;
   }
   ```

## Phase 4: Integration Testing (TODO)

### Tests to Run
1. **x86 (default)**: `cargo test`
2. **ARM64**: `cargo test --features arm64-backend`
3. **WASM**: `cargo test --features wasm-backend`

### Expected Behavior
- Each backend compiles and runs independently
- Can generate correct code for the selected architecture
- Existing x86 tests continue to pass

## Phase 5: Multi-Architecture Binary (FUTURE)

### Long-term Goal
Eventually support multiple architectures in a single binary:
1. Replace feature flags with runtime selection
2. Use enum wrappers or trait objects for architecture-specific types
3. Select backend based on Target at runtime

### Example:
```rust
match target.arch {
    TargetArch::X86_64 => x86::codegen(mir),
    TargetArch::Arm64 => arm64::codegen(mir),
    TargetArch::Wasm32 => wasm::codegen(mir),
}
```

## Benefits of This Approach

1. **Incremental**: Each phase can be completed and tested independently
2. **Safe**: Existing x86 functionality is preserved at each step
3. **Reviewable**: Small, focused changes are easier to review
4. **Reversible**: Can back out changes if issues arise
5. **Educational**: Clearly shows the coupling points in the architecture

## Current Status

- ✅ Phase 1: Architecture abstraction layer created
- 🚧 Phase 2: Conditional compilation partially working
- ⏳ Phase 3: Architecture-specific modules needed
- ⏳ Phase 4: Integration testing needed
- 🔮 Phase 5: Future multi-arch support

## Next Steps

1. Fix the remaining type mismatches in ARM64 code
2. Create ARM64-specific regalloc module
3. Test ARM64 backend with feature flag
4. Repeat for WASM backend
5. Document lessons learned

## Conclusion

This incremental approach allows us to gradually migrate from a monolithic x86-only compiler to a multi-architecture compiler without breaking existing functionality. Each phase builds on the previous one, and we can stop at any point with a working system.