# X86 Isolation: Practical Implementation Layers

## Layer 0: Establish Non-X86 Baseline (Prerequisites)
**Goal**: Prove we can build and run without x86 at all

### Tasks:
1. **Fix remaining WASM compilation errors** (~140 errors)
   - Most are due to classify.rs and proof dependencies
   - Use proof_bypass mechanism more extensively
   - This proves x86 isn't truly required

2. **Create minimal test programs**
   - Exit code test
   - Simple arithmetic 
   - Validates non-x86 architectures work end-to-end

**Why First**: Can't refactor x86 as a "peer" until other architectures actually work independently

## Layer 1: Type System Liberation 
**Goal**: Break the feature-flag-based type coupling

### The Core Problem:
```rust
// This is our enemy - types that change based on features
use crate::arch::arch_types::{PReg, PRegSet};
```

### Approach:
1. **Create `types/arch_agnostic.rs`**:
   ```rust
   // Architecture-agnostic register type
   #[derive(Debug, Clone, Copy)]
   pub enum ArchReg {
       X86(u8),
       Arm64(u8),
       Wasm(u32), // stack slot
   }
   
   // Architecture-agnostic register set
   pub enum ArchRegSet {
       X86([u64; 4]),
       Arm64([u64; 2]),
       Wasm(Vec<u32>),
   }
   ```

2. **Update `types/vcode.rs`** to use agnostic types
3. **Create conversion traits** in each architecture

**Why This Layer**: Everything else is blocked by type coupling

## Layer 2: Classify Extraction (Proof of Concept)
**Goal**: Move the simplest x86-specific module first

### Why classify.rs is perfect:
- Already marked with TODO
- Self-contained (just instruction classification)
- No complex dependencies
- Good test case for the process

### Steps:
1. Move `types/classify.rs` → `arch/x86/classify.rs`
2. Create `types/classify_trait.rs` with generic interface
3. Update imports in proof modules
4. Test x86 still builds and runs

**Success Metric**: One less x86 module in core!

## Layer 3: Minimum Viable Traits
**Goal**: Just enough traits to support current code

### Don't Overengineer - Start Simple:
```rust
// arch/traits.rs
pub trait ArchInst: Clone + Debug {
    type PReg: IsReg;
    type PRegSet;
    type AMode;
    
    fn is_call(&self) -> bool;
    fn is_ret(&self) -> bool;
}

pub trait ArchLower {
    type Inst: ArchInst;
    type Error;
    
    fn lower_block(&mut self, block: &BasicBlock) -> Result<(), Self::Error>;
}
```

### Implementation:
1. Create traits only for what we actively use
2. Implement for x86 using existing code
3. Don't try to be perfect - just functional

**Why Minimal**: Easier to refactor when we understand needs better

## Layer 4: Register Allocator Extraction
**Goal**: Move regalloc.rs to arch/x86

### Challenge: `regalloc.rs` is deeply integrated
- Uses x86 types everywhere
- Called from architecture-agnostic code
- Core part of compilation pipeline

### Approach:
1. **Create `arch/x86/regalloc_impl.rs`**
   - Move the x86-specific parts
   - Keep generic regalloc2 interface in core

2. **Update core `regalloc.rs`**:
   ```rust
   pub fn allocate_registers(
       vcode: VCode,
       arch: &dyn Architecture
   ) -> Result<ArchPCode, Error> {
       arch.allocate_registers(vcode)
   }
   ```

3. **Test incrementally**
   - x86 should work exactly as before
   - ARM64/WASM use their own allocators

## Layer 5: MIR Lowering Extraction  
**Goal**: Move build_vcode.rs to arch/x86

### This is the Big One:
- Largest x86-specific module
- Complex MIR → VCode translation
- Many instruction patterns

### Strategy:
1. **Start with instruction helpers**
   - Move x86-specific instruction builders first
   - Keep MIR traversal generic

2. **Create lowering trait**:
   ```rust
   trait MirLower {
       fn lower_statement(&mut self, stmt: &Statement);
       fn lower_terminator(&mut self, term: &Terminator);
       fn lower_rvalue(&mut self, rv: &RValue);
   }
   ```

3. **Gradual migration**
   - Move one operation type at a time
   - Test after each move

## Layer 6: Architecture Module Cleanup
**Goal**: Remove x86 as the implicit default

### Tasks:
1. **Remove `pub use x86::*`** from arch/mod_new.rs
2. **Fix ARM64 compat layer**
   - Remove x86 type conversions
   - Use architecture-agnostic types
3. **Move SIMD x86 code** to arch/x86/simd.rs
4. **Update all imports** to use explicit paths

## Layer 7: Proof System Decoupling
**Goal**: Make proofs optional per architecture

### Current State:
- Proofs assume x86 instruction model
- Other architectures use proof_bypass
- This is actually fine for now!

### Approach:
1. Make proof generation a capability, not requirement
2. Let each architecture opt-in to proofs
3. x86 keeps full proof support
4. Others can add it later

## Implementation Order & Strategy

### Phase 1: Foundation (Layers 0-2)
- Fix WASM build ← **Do this first**
- Type system decoupling ← **Critical path**
- Move classify.rs ← **Quick win**

### Phase 2: Core Extraction (Layers 3-5)
- Create minimal traits
- Extract register allocator
- Extract MIR lowering

### Phase 3: Cleanup (Layers 6-7)
- Remove x86 defaults
- Fix architecture boundaries
- Document the new structure

## Testing Strategy

Each layer must:
1. **Not break x86** - Existing tests still pass
2. **Improve others** - ARM64/WASM get more functional
3. **Be revertable** - Can back out if needed

## Success Metrics

- [ ] Can build with only `--feature arm64-backend`
- [ ] Can build with only `--feature wasm-backend`  
- [ ] No x86 imports in core modules
- [ ] All architectures use same trait interfaces
- [ ] Clear architecture boundaries

## Key Insights

1. **Don't fix everything at once** - Incremental progress
2. **Type system is the keystone** - Fix this first
3. **Traits can be minimal** - Don't overdesign
4. **Proof system can wait** - It's already bypassed
5. **Test continuously** - Each layer must work

## Next Immediate Action

Fix the remaining WASM compilation errors. This proves we can actually build without x86 and gives us a concrete target to test our refactoring against.