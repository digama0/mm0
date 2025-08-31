# X86 Isolation Plan

## Problem Analysis

The MM0 compiler currently has x86 code scattered throughout core modules instead of being properly isolated in the `arch/x86` folder like ARM64 and WASM. This creates several issues:

1. **Type System Coupling**: Core modules depend on x86 types that change based on feature flags
2. **Architecture Asymmetry**: x86 is treated as the "default" architecture, with others as fallbacks
3. **Maintenance Difficulty**: Architecture-specific code is mixed with generic code
4. **Build Complexity**: Feature flags create type mismatches between architectures

## Current X86 Code Distribution

### 1. Core Modules with X86 Dependencies (TODO comments found)
- **`regalloc.rs`** (line 15):
  ```rust
  // TODO: This module is currently x86-specific and needs to be refactored
  use crate::arch::x86::{AMode, Inst, callee_saved, caller_saved, MACHINE_ENV, Offset, PAMode, PInst,
    PRegMem, PRegMemImm, PRegSet, PShiftIndex, RSP, PReg, RegMem, RegMemImm};
  ```

- **`build_vcode.rs`** (line 20):
  ```rust
  // TODO: This module is currently x86-specific and needs to be refactored
  use crate::arch::x86::{AMode, Binop as VBinop, CC, Cmp, ExtMode, Inst, PReg, RegMem, RegMemImm,
    RET_AND_ARG_REGS, SYSCALL_ARG_REGS, ShiftKind, SysCall, Unop as VUnop};
  ```

- **`proof.rs`** (line 16):
  ```rust
  // TODO: This module is currently x86-specific and needs to be refactored
  pub use crate::arch::x86::{self, PReg, PInst as VInst, PRegMem};
  ```

- **`types/classify.rs`** (line 2):
  ```rust
  // TODO: This module is currently x86-specific and needs to be refactored
  use crate::arch::x86::{PInst, SysCall, PReg};
  ```

### 2. Type System Issues
- **`types/vcode.rs`** imports from `arch::arch_types::{PReg, PRegSet}` 
  - These types change based on feature flags (x86 vs arm64 vs wasm)
  - Causes type mismatches when building different architectures

### 3. Already Isolated in arch/x86
- `arch_impl.rs`
- `calling_conv.rs`
- `frame.rs`
- `frame_simple.rs`
- `mod.rs`
- `proof_impl.rs`
- `proof_refactor.rs`

### 4. Additional X86 Dependencies Found
- **`arch/mod_new.rs`** (line 69):
  ```rust
  // For now, continue to export x86 as the default
  // This allows gradual migration
  pub use x86::*;
  ```
  This re-exports ALL x86 types at the architecture module level!

- **`simd/mod.rs`**:
  - Contains x86-specific SIMD implementations
  - Should be moved to `arch/x86/simd.rs`

- **`arch/arm64/compat.rs`**:
  ```rust
  let x86_preg = crate::arch::x86::PReg::new(arm64_reg.index() as usize);
  ```
  ARM64 has compatibility shims that convert to x86 types!

## Proposed Solution

### Phase 1: Create Architecture Traits
1. Define common traits in `arch/traits.rs` for:
   - Register allocation interface
   - Code generation interface
   - Proof generation interface
   - MIR lowering interface

2. Example trait structure:
   ```rust
   // arch/traits.rs
   pub trait ArchRegalloc {
       type PReg: IsReg;
       type PRegSet;
       type PInst;
       type AMode;
       // ... other associated types
       
       fn allocate_registers(vcode: &VCode) -> Result<PCode, Error>;
   }
   
   pub trait ArchLower {
       fn lower_mir(cfg: &Cfg) -> Result<VCode, Error>;
   }
   
   pub trait ArchProof {
       fn generate_proof(pcode: &PCode) -> Option<Proof>;
   }
   ```

### Phase 2: Move X86-Specific Code
1. **Move `regalloc.rs` → `arch/x86/regalloc_core.rs`**
   - Extract x86-specific register allocation logic
   - Implement `ArchRegalloc` trait for x86

2. **Move `build_vcode.rs` → `arch/x86/lower_core.rs`**
   - Extract x86-specific MIR lowering
   - Implement `ArchLower` trait for x86

3. **Move proof generation → `arch/x86/proof_core.rs`**
   - Extract x86-specific proof logic
   - Implement `ArchProof` trait for x86

4. **Move `types/classify.rs` → `arch/x86/classify.rs`**
   - This is entirely x86-specific instruction classification

5. **Move SIMD x86 implementation → `arch/x86/simd.rs`**
   - Extract x86-specific SIMD lowering from `simd/mod.rs`
   - Keep only the trait definition in core

6. **Remove `pub use x86::*` from `arch/mod_new.rs`**
   - Stop re-exporting all x86 types as defaults
   - Force explicit architecture selection

7. **Fix ARM64 compatibility layer**
   - Remove x86 type conversions from `arch/arm64/compat.rs`
   - Use proper architecture-agnostic types

### Phase 3: Create Generic Core Modules
1. **New `regalloc.rs`**:
   ```rust
   use crate::arch::traits::ArchRegalloc;
   
   pub fn allocate_registers<A: ArchRegalloc>(vcode: &VCode) -> Result<A::PCode, Error> {
       A::allocate_registers(vcode)
   }
   ```

2. **New `build_vcode.rs`**:
   ```rust
   use crate::arch::traits::ArchLower;
   
   pub fn lower_mir<A: ArchLower>(cfg: &Cfg) -> Result<VCode, Error> {
       A::lower_mir(cfg)
   }
   ```

### Phase 4: Fix Type System Coupling
1. **Parameterize `types/vcode.rs`**:
   - Remove direct imports of `PReg`, `PRegSet`
   - Use associated types from traits
   - Or create generic type parameters

2. **Update `arch/arch_types.rs`**:
   - Make it a trait provider rather than direct type exports
   - Each architecture implements the trait differently

### Phase 5: Update Build System
1. **Remove feature-flag-based type switching**
2. **Options**:
   - Build separate executables per architecture (as user suggested)
   - Use runtime architecture selection with trait objects
   - Use generics with monomorphization per architecture

## Implementation Order

1. **Start with traits** - Define the architecture interface
2. **Move classify.rs** - It's self-contained and entirely x86-specific
3. **Extract register allocation** - Core functionality but well-defined boundaries
4. **Extract MIR lowering** - More complex but follows similar pattern
5. **Fix type system** - Requires coordination across multiple modules
6. **Update proof system** - Can be done last as it's already partially bypassed

## Benefits

1. **True Architecture Parity**: All architectures become peers, not x86-with-fallbacks
2. **Clean Separation**: Architecture-specific code is properly isolated
3. **Easier Testing**: Can test each architecture independently
4. **Better Maintainability**: Clear boundaries between generic and specific code
5. **Parallel Development**: Teams can work on different architectures without conflicts

## Risks and Mitigations

1. **Risk**: Large refactoring could introduce bugs
   - **Mitigation**: Incremental changes with tests at each step

2. **Risk**: Performance regression from trait indirection
   - **Mitigation**: Use static dispatch (generics) not dynamic dispatch

3. **Risk**: Compilation time increase from monomorphization
   - **Mitigation**: Consider separate executables if needed

## Success Criteria

- [ ] No x86-specific imports in core modules (outside arch/x86)
- [ ] All architectures use the same trait-based interfaces
- [ ] Can build and run with any single architecture feature flag
- [ ] Tests pass for all architectures independently
- [ ] Clear documentation of architecture boundaries