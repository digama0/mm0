# ARM64 Integration Plan for MM0 Compiler

## Current State Analysis

### What We Have Built
1. **Architecture Abstraction** (`arch/traits.rs`) - Well-designed trait system
2. **ARM64 Implementation** - Complete registers, instructions, encoding
3. **Mach-O Generation** - Proper file format that works on macOS
4. **Target Selection** - Framework for choosing architecture at compile time

### Why It Doesn't Work Yet
The MM0 compiler (specifically MMC) was built with x86-64 hardcoded throughout:
- MIR (Middle IR) assumes x86 instructions
- Register allocation uses x86-specific classes
- Code generation directly emits x86 opcodes
- Proof generation may assume x86 semantics

### Build Failures
When we try to build with our changes:
```
error[E0119]: conflicting implementations of trait `PhysicalInstruction`
error[E0277]: `()` is not an iterator
error[E0050]: method `has_syscalls` has 0 parameters but declaration has 1
error[E0308]: mismatched types (Size vs Option<Size>)
```

## Integration Strategy

### Phase 1: Minimal Working ARM64 (Highest Priority)
Goal: Generate a working ARM64 "Hello World" without breaking x86

1. **Fix immediate build errors**
   - Resolve trait conflicts by namespacing
   - Fix type mismatches (Size vs Option<Size>)
   - Add missing trait implementations

2. **Create parallel ARM64 pipeline**
   - Keep existing x86 code unchanged
   - Add new ARM64-specific MIR lowering
   - Use target flag to switch between pipelines

3. **Test with minimal examples**
   - Start with `exit(42)`
   - Add sys_write for "Hello ARM64"
   - Verify on actual Mac hardware

### Phase 2: Architecture Abstraction Refactor
Goal: Unify x86 and ARM64 under common abstraction

1. **Extract x86-specific assumptions**
   - Identify all places assuming x86
   - Create abstraction points
   - Move x86 code behind traits

2. **Implement trait-based dispatch**
   - MIR → Architecture-specific IR
   - Register allocation per architecture
   - Instruction selection via traits

3. **Update proof generation**
   - Ensure proofs work for both architectures
   - May need architecture-specific proof rules

### Phase 3: Full Multi-Architecture Support
Goal: Production-ready multi-arch compiler

1. **Add WASM backend**
   - Stack machine vs register machine
   - Different syscall model (WASI)
   - Test abstraction completeness

2. **Optimize code generation**
   - Architecture-specific optimizations
   - Better register allocation
   - Peephole optimizations

3. **Complete test suite**
   - Cross-architecture tests
   - Performance benchmarks
   - Proof verification tests

## Technical Challenges

### 1. MIR Assumptions
The MIR (Middle Intermediate Representation) makes assumptions:
- Registers exist (problem for WASM)
- Certain instructions map 1:1 to x86
- Calling conventions match x86

**Solution**: Create architecture-neutral MIR or allow arch-specific MIR variants

### 2. Proof Generation
MM0 generates proofs of program correctness. These may assume:
- x86 instruction semantics
- Specific memory models
- x86 calling conventions

**Solution**: Abstract proof generation or create per-arch proof rules

### 3. Type System Integration
The current type system in `build_vcode.rs` assumes x86:
- Instruction types
- Register types
- Memory addressing modes

**Solution**: Parameterize types by architecture

## Implementation Approach

### Step 1: Parallel Implementation (Recommended)
```rust
// In codegen.rs
impl LinkedCode {
    pub fn write_elf(&self, w: &mut impl Write) -> io::Result<()> {
        #[cfg(feature = "arm64-experiment")]
        if let Some(target) = self.target {
            return self.write_for_target(w, target);
        }
        
        // Original x86 code unchanged
        self.write_x86_elf(w)
    }
}
```

### Step 2: Gradual Migration
1. Add feature flag `arm64-experiment`
2. Implement ARM64 pipeline behind flag
3. Test thoroughly
4. Remove flag when stable

### Step 3: Final Architecture
```
MIR → Architecture Selector → Arch-Specific Backend → Machine Code
                                    ↓
                              Proof Generator
```

## Time Estimate

- **Phase 1**: 2-3 weeks (minimal ARM64 working)
- **Phase 2**: 4-6 weeks (proper abstraction)
- **Phase 3**: 2-3 weeks (WASM + optimization)

Total: 2-3 months for production-ready multi-architecture support

## Alternative: Pure ARM64 Fork

If full integration proves too complex, consider:
1. Fork MM0 as "MM0-ARM64"
2. Replace x86 code with ARM64 directly
3. Simpler but loses multi-arch benefits
4. Could be done in 1-2 weeks

## Recommendation

Start with Phase 1 - get minimal ARM64 working in parallel with x86. This provides:
- Immediate value (ARM64 binaries)
- Validation of our architecture
- Learning for full integration
- Fallback option (fork) if needed

The key insight: **Don't try to refactor everything at once**. Build ARM64 alongside x86, then unify later.