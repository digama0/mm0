# X86 Isolation: Learnings from WASM Implementation

## Key Discoveries

### 1. The Pervasiveness of x86 Assumptions

While implementing WASM support, we discovered just how deeply x86 is embedded:

- **classify.rs**: Entirely x86-specific, imports x86 types directly
- **regalloc.rs**: Hardcoded x86 register types and operations  
- **build_vcode.rs**: Assumes x86 instruction patterns
- **proof.rs**: Built around x86 instruction model
- **Type definitions**: PReg, PRegSet change meaning based on features

### 2. Feature Flag Coupling

The current approach uses feature flags to switch between architectures:
```rust
#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
use crate::arch::x86::stuff;
```

This creates a fundamental problem:
- x86 is the implicit default (when no other features)
- Other architectures are "alternatives" not peers
- Can't build with multiple architectures simultaneously

### 3. The Dummy Pattern

We found several places using "dummy" implementations for non-x86:
- `proof_dummy.rs` - Stub types for non-x86 architectures
- Dummy `Trace` type in vcode.rs for non-x86
- `proof_bypass` mechanism to skip proofs

This pattern shows x86 is "first class" while others are "accommodated."

### 4. Success of Incremental Approach

By fixing WASM compilation incrementally (135 → 38 errors), we proved:
- Other architectures CAN work independently
- The coupling is fixable with systematic refactoring
- Each layer of fixes reveals the next set of issues

## Implications for X86 Isolation

### What Works
1. **ArchPCode abstraction** - Successfully decouples LinkedCode
2. **Conditional compilation** - Can exclude x86-specific modules
3. **Trait-based abstractions** - VCode traits work across architectures

### What Needs Fixing
1. **Core type definitions** - PReg, PRegSet must be architecture-agnostic
2. **Module organization** - x86 code scattered in core modules
3. **Default assumptions** - x86 shouldn't be the implicit default
4. **Proof system** - Currently assumes x86 instruction model

## Recommended Approach

Based on WASM implementation experience:

1. **Start with type system** - Fix PReg/PRegSet coupling first
2. **Move obvious modules** - classify.rs is clearly x86-only
3. **Create traits gradually** - Don't over-engineer, build what's needed
4. **Test continuously** - Each change should keep x86 working
5. **Accept temporary inefficiency** - Dummy implementations are OK initially

## The Path Forward

The WASM work proves x86 isolation is achievable. The key is recognizing that x86 being the "only child" wasn't intentional - it's just technical debt from being implemented first. With systematic refactoring, all architectures can truly be peers.