# Multi-Architecture Proof System

This document describes the architecture-agnostic proof generation system for the MM0 compiler.

## Overview

The proof system allows each target architecture to generate correctness proofs about the code it produces, while keeping the core proof logic independent of any specific architecture. This design enables:

1. **Portability**: New architectures can be added without modifying core proof code
2. **Consistency**: All architectures use the same abstractions and proof obligations
3. **Modularity**: Architecture-specific details are isolated in implementation modules

## Architecture

### Core Components

```
┌─────────────────────┐
│   Proof Traits      │  ← Architecture-agnostic interfaces
│  (proof_traits.rs)  │
└──────────┬──────────┘
           │
     ┌─────┴─────┐
     │           │
┌────▼────┐ ┌───▼────┐
│  x86    │ │ ARM64  │  ← Architecture-specific implementations
│ Proof   │ │ Proof  │
│ Impl    │ │ Impl   │
└─────────┘ └────────┘
```

### Key Traits

1. **`ArchProof`**: Core trait for architecture-specific proof generation
   - Converts concrete instructions to abstract representation
   - Maps physical registers to abstract registers
   - Generates proof obligations for instructions
   - Verifies properties are preserved by instruction sequences

2. **`ProofGen`**: Extended trait for generating proof terms
   - Produces proofs for specific operations (moves, calls, syscalls)
   - Handles stack operations and calling conventions
   - Generates MM0-compatible proof terms

### Abstract Representations

The system uses abstract representations to unify concepts across architectures:

1. **`AbstractInst`**: Architecture-independent instruction representation
   - Move, Arith, Call, Syscall, Branch, Jump, Return
   - Captures semantic intent rather than encoding details

2. **`AbstractReg`**: Unified register abstraction
   - General purpose registers (Gpr)
   - Special registers (StackPointer, FramePointer, ReturnValue)
   - Argument and syscall registers

3. **`AbstractOperand`**: Operand abstraction
   - Register, Immediate, Memory references
   - Independent of architecture-specific addressing modes

## Implementation Guide

### Adding a New Architecture

1. Create `arch/<arch>/proof_impl.rs` implementing the traits:

```rust
pub struct MyArchProofGen;

impl ArchProof for MyArchProofGen {
    type Inst = MyArchInst;
    type Reg = MyArchReg;
    
    fn abstract_inst(&self, inst: &Self::Inst) -> AbstractInst {
        // Convert architecture-specific instruction to abstract form
    }
    
    fn abstract_reg(&self, reg: &Self::Reg) -> AbstractReg {
        // Map physical register to abstract register
    }
    
    // ... other required methods
}

impl ProofGen for MyArchProofGen {
    // Implement proof generation methods
}
```

2. Add the architecture to `ProofGenFactory` in `proof_gen.rs`:

```rust
match target.arch {
    TargetArch::MyArch => {
        Box::new(MyArchProofGenAdapter {
            gen: MyArchProofGen::new(target.os),
        })
    }
    // ... other architectures
}
```

### Proof Obligations

Each instruction may generate proof obligations that must be satisfied:

1. **Register Values**: Ensuring registers contain expected values
2. **Memory Safety**: Validating memory accesses are within bounds
3. **Stack Alignment**: Maintaining required stack alignment
4. **Calling Conventions**: Following ABI requirements

Example:

```rust
fn proof_obligations(&self, inst: &Self::Inst) -> Vec<ProofObligation> {
    match inst {
        Inst::Call { .. } => vec![
            ProofObligation {
                property: ProofProperty::StackAlignment { alignment: 16 },
                reason: "Stack must be aligned before call".to_string(),
            }
        ],
        // ... other instructions
    }
}
```

## Integration with MM0

The proof system generates MM0-compatible proof terms that can be verified by the MM0 proof checker. The integration works as follows:

1. **During Compilation**: Architecture-specific code generation produces instructions
2. **Proof Generation**: The trait-based system generates abstract proofs
3. **MM0 Translation**: Abstract proofs are converted to MM0 theorem statements
4. **Verification**: MM0 verifies the correctness of the generated code

### Example MM0 Output

For a simple function prologue:

```mm0
theorem func_prologue_correct:
  $ okProc gctx start args ret clob se $ =
  '{ ... proof that prologue maintains invariants ... };
```

## Testing

The proof system includes comprehensive tests:

1. **Unit Tests**: In each architecture's `proof_impl.rs`
2. **Integration Tests**: In `tests/multi_arch_proof_test.rs`
3. **Property Tests**: Verify consistency across architectures

Key test areas:
- Instruction abstraction consistency
- Calling convention correctness
- Proof obligation generation
- Cross-architecture compatibility

## Future Work

1. **Complete ARM64 Implementation**: Finish proof generation for ARM64
2. **WASM Support**: Add proof generation for WebAssembly
3. **Optimization Proofs**: Prove correctness of optimizations
4. **Automated Proof Search**: Generate proofs automatically from semantics
5. **Formal Verification**: Connect to external theorem provers

## References

- MM0 specification: https://github.com/digama0/mm0
- x86-64 ABI: https://gitlab.com/x86-psABIs/x86-64-ABI
- ARM64 ABI: https://github.com/ARM-software/abi-aa
- Proof-carrying code: https://www.cs.cmu.edu/~rwh/papers/pcc/pcc.pdf