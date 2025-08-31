# X86 Architecture Isolation Insight

## The Core Problem

As you correctly identified, **x86 is not a true peer to ARM64 and WASM** - it's the implicit default baked into core modules.

### Evidence Found

1. **Four core modules have x86-specific TODOs**:
   - `regalloc.rs`: "TODO: This module is currently x86-specific and needs to be refactored"
   - `build_vcode.rs`: "TODO: This module is currently x86-specific and needs to be refactored"  
   - `proof.rs`: "TODO: This module is currently x86-specific and needs to be refactored"
   - `types/classify.rs`: "TODO: This module is currently x86-specific and needs to be refactored"

2. **Direct x86 imports in core modules**:
   ```rust
   // In regalloc.rs - supposed to be generic!
   use crate::arch::x86::{AMode, Inst, callee_saved, caller_saved, MACHINE_ENV, 
                          Offset, PAMode, PInst, PRegMem, PRegMemImm, PRegSet, 
                          PShiftIndex, RSP, PReg, RegMem, RegMemImm};
   ```

3. **Type system coupling** in `types/vcode.rs`:
   ```rust
   use crate::arch::arch_types::{PReg, PRegSet}  // Changes based on feature flags!
   ```

## Why This Matters

### Current State: X86 as the "Only Child"
```
Core Modules
├── regalloc.rs       → hardcoded x86 types
├── build_vcode.rs    → hardcoded x86 instructions  
├── proof.rs          → hardcoded x86 proof types
└── types/
    ├── vcode.rs      → imports change with features
    └── classify.rs   → entirely x86-specific

arch/
├── x86/              ← some x86 code here
├── arm64/            ← properly isolated
└── wasm/             ← properly isolated
```

### Desired State: True Peer Architectures
```
Core Modules (generic only!)
├── regalloc.rs       → uses traits
├── build_vcode.rs    → uses traits
├── proof.rs          → uses traits
└── types/
    └── vcode.rs      → architecture-agnostic

arch/
├── x86/              ← ALL x86 code here
│   ├── regalloc.rs
│   ├── lower.rs
│   ├── proof.rs
│   └── classify.rs
├── arm64/            ← peer architecture
└── wasm/             ← peer architecture
```

## The Fallback Pattern

You identified the key pattern: x86 is the default, others are "fallbacks":

1. **Feature flags create alternatives**, not equals:
   ```rust
   #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
   use crate::arch::x86::stuff;  // x86 is the default
   
   #[cfg(feature = "arm64-backend")]
   use crate::arch::arm64::stuff;  // arm64 is an alternative
   ```

2. **Conditional compilation hides x86 bias**:
   ```rust
   // In lib.rs
   #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
   mod build_vcode;  // Only compiled for x86!
   ```

3. **Type switching creates coupling**:
   ```rust
   // arch_types.rs changes what it exports based on features
   // This ripples through the entire codebase
   ```

## The Solution Direction

As you noted, we need to figure out **"how" to get x86 into its own special folder** so all architectures can be true peers.

The key challenges:
1. **Untangling hardcoded types** - PReg, PRegSet, Inst are baked into core APIs
2. **Extracting lowering logic** - MIR → x86 translation is in generic modules  
3. **Decoupling proof system** - Proof types assume x86 instruction model
4. **Fixing type system** - Need architecture-agnostic core types

## Your Insight Was Correct

This is exactly why ARM64 had to "fake" x86 instructions initially - the core infrastructure wasn't truly generic, it was x86 with escape hatches for other architectures. Now with ArchPCode we've started fixing this, but the root cause remains: **x86 needs to move into its folder and stop being the implicit default**.