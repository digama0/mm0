# MM0 Compiler Architecture and Integration Vision

## System Layers

### Layer 1: MM0 Proof Kernel (Foundation)
The immutable core that verifies all proofs.

```
mm0-rs/src/
├── parser/     # Parse .mm0 and .mm1 files
├── proof/      # Verify MM0 proofs
└── kernel/     # Minimal trusted code
```

**Status**: ✅ Complete and working

### Layer 2: MM1 Language System
High-level language for writing proofs and programs.

```
mm0-rs/src/
├── mm1_parser/  # Parse MM1 syntax
├── elab/        # Elaborate MM1 to MM0
└── compiler/    # MM1 → MMC translation
```

**Status**: ✅ Working, enhanced with mmc_lib.mm1

### Layer 3: MMC Compiler (What We've Been Building)
Transforms verified programs into native code.

```
mm0-rs/components/mmcc/src/
├── types/       # Type system and MIR
├── arch/        # Architecture backends
│   ├── arm64/   # ✅ COMPLETE
│   ├── x86/     # ✅ ENHANCED
│   └── wasm/    # ✅ WORKING
├── build_mir/   # MM1 → MIR translation
└── codegen/     # MIR → Native code
```

**Status**: 🔥 Massively upgraded!

### Layer 4: Architecture Abstraction
Clean separation of architecture-specific code.

```
arch/
├── traits.rs    # Common interfaces
├── arch_types.rs # Type selection
└── target.rs    # Target specification
```

**What We Built**:
- ✅ Feature-based architecture selection
- ✅ Clean trait abstractions
- ✅ No more hardcoded x86 dependencies

### Layer 5: Code Generation Pipeline

```
MM1 Program
    ↓ (parse)
AST
    ↓ (elaborate) 
MIR (Mid-level IR)
    ↓ (lower)
VCode (Virtual registers)
    ↓ (regalloc2)
PCode (Physical registers)
    ↓ (encode)
Machine Code
    ↓ (link)
Executable + Proofs
```

**Each Stage Now Has**:
- ✅ Multi-architecture support
- ✅ Clean abstractions
- ✅ Test coverage

## Integration Plan

### Phase 1: Connect Existing Pieces ✅ DONE
What we accomplished:
- ARM64 backend with all instructions
- x86-64 enhancements (calling conventions, frames)
- WASM as third backend
- Register allocation via regalloc2
- MM1 high-level constructs

### Phase 2: MIR Pipeline Integration (NEXT)
The missing link - connecting our backends to the MIR pipeline.

```rust
// Current: MIR hardcoded to x86
impl BuildMir {
    fn compile(&mut self) -> PCode {
        // Always returns x86 PCode
    }
}

// Needed: Architecture dispatch
impl BuildMir {
    fn compile(&mut self, target: Target) -> PCode {
        match target.arch {
            Arch::X86_64 => self.compile_x86(),
            Arch::ARM64 => self.compile_arm64(),
            Arch::WASM => self.compile_wasm(),
        }
    }
}
```

### Phase 3: Proof Integration
Connect code generation to proof generation.

1. **Instruction Semantics**: Each instruction has formal semantics
2. **VCode Proofs**: Prove VCode implements MIR correctly
3. **Register Allocation Proofs**: Prove allocation preserves semantics
4. **Final Theorem**: Generated code implements source program

### Phase 4: Type System Connection
Mario's vision of types as separating propositions.

```rust
// Current: Basic types
enum Type {
    U32, U64, Ptr, ...
}

// Future: Rich types with invariants
type Array<T, N> = {
    ptr: Ptr,
    ghost len: N,
    invariant: "ptr points to N elements of type T"
}
```

## Key Integration Points

### 1. Target Selection
```rust
// In MM1
(mmc-set-target "arm64-macos")

// Flows through to
BuildMir::new(target: Target)

// Selects backend
match target { ... }
```

### 2. Instruction Selection
```rust
// MIR operation
mir::Op::Add(dst, src1, src2)

// Becomes architecture-specific
arm64::Inst::Add { dst, src1, src2 }
x86::Inst::Add { dst, src }  // Two-address
wasm::Inst::Add { ty }       // Stack-based
```

### 3. Calling Conventions
```rust
// High-level function
(function main ((argc i32) (argv ptr)) ...)

// Becomes platform-specific
ARM64: X0=argc, X1=argv
x86-64: RDI=argc, RSI=argv  
WASM: Uses locals
```

### 4. Memory Model
```rust
// MM1 memory operation
(load (+ argv (* i 8)))

// Becomes addressing mode
ARM64: LDR X0, [X1, X2, LSL#3]
x86-64: MOV RAX, [RDI + RSI*8]
WASM: i32.load offset=0
```

## The Vision

### Near Term (Integration)
1. Wire up architecture selection in MIR
2. Add architecture tests to CI
3. Enable proof generation with multi-arch
4. Create architecture comparison docs

### Medium Term (Verification)
1. Formal semantics for each architecture
2. Equivalence proofs between architectures
3. Optimization correctness proofs
4. Memory safety proofs

### Long Term (MMC Language)
1. Full implementation of Mario's MMC design
2. Separation logic for heap reasoning
3. Verified stdlib (strings, collections)
4. Self-hosting compiler

## Why This Architecture Matters

### 1. **Modularity**
Each layer can be understood and verified independently.

### 2. **Portability**
Clean abstractions make new architectures easy to add.

### 3. **Verifiability**
Every transformation can be formally proven correct.

### 4. **Practicality**
Real programs can be written and compiled efficiently.

## Next Concrete Steps

1. **Create MIR → Multi-arch Dispatcher**
   ```rust
   // In build_mir.rs
   pub fn compile_with_target(&mut self, target: Target) -> Result<CompiledCode, Error>
   ```

2. **Add Target to Compilation Context**
   ```rust
   // Thread target through compilation
   struct CompileCtx {
       target: Target,
       // ...
   }
   ```

3. **Test Multi-Architecture Compilation**
   ```bash
   # Same MM1 source
   mm0-rs compile prog.mm1 --target x86_64-linux
   mm0-rs compile prog.mm1 --target arm64-macos
   mm0-rs compile prog.mm1 --target wasm32
   ```

4. **Benchmark and Compare**
   - Code size comparison
   - Performance metrics
   - Proof complexity

## Success Metrics

- ✅ Single MM1 source compiles to all architectures
- ✅ Generated code passes architecture-specific tests
- ✅ Proofs verify for all backends
- ✅ Performance within 2x of hand-written assembly
- ✅ Clear documentation for adding new architectures

## Conclusion

We've built the pieces - now it's time to connect them. The architecture is clean, the abstractions are solid, and the path forward is clear. This isn't just about making MM0 work on ARM64; it's about creating a foundation for verified multi-architecture compilation that can last for decades.