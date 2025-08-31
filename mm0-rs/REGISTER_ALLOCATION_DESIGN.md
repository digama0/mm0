# Register Allocation Design for MM0 Compiler

## Current State

The compiler currently uses naive register allocation:
- Virtual registers map directly to physical registers (VReg(0) → X0, etc.)
- No register reuse or optimization
- Will fail with more than 16 virtual registers on ARM64
- No spilling support

## Proper Register Allocation

### Overview

Register allocation solves the problem of mapping unlimited virtual registers to limited physical registers. The MM0 compiler uses regalloc2, which implements state-of-the-art algorithms.

### Key Components

#### 1. Live Range Analysis
Determine when each virtual register is "live" (holds a needed value):
```
v0 = 1        // v0 live from here...
v1 = 2        // v1 live from here...
v2 = v0 + v1  // ...to here (last use)
v3 = v2 * 2   // v2 live from definition to here
```

#### 2. Interference Graph
Build a graph where:
- Nodes = Virtual registers
- Edges = Registers that are live simultaneously
- Colors = Physical registers

Registers connected by edges cannot share the same physical register.

#### 3. Register Assignment
Use graph coloring algorithms to assign physical registers:
- Linear scan (fast, good results)
- Graph coloring with heuristics
- Chaitin-Briggs algorithm

#### 4. Spilling
When we run out of registers:
1. Choose a register to spill (heuristics: least used, most costly)
2. Insert store after definition
3. Insert load before each use
4. Retry allocation with reduced pressure

### Integration with regalloc2

The compiler already has regalloc2 integration started:

```rust
// In arch/arm64/regalloc.rs
pub fn regalloc_arm64(vcode: &VCode<Inst>) -> Result<PCode, String> {
    let output = regalloc2::run(
        vcode,
        &ARM64_MACHINE_ENV,
        &regalloc2::RegallocOptions::default()
    )?;
    
    // Apply allocation results...
}
```

### Implementation Plan

#### Phase 1: Complete regalloc2 Integration ✅
- [x] Define machine environment (register sets)
- [ ] Implement VCode trait for regalloc2
- [ ] Convert allocation results to physical instructions
- [ ] Handle move insertions and spills

#### Phase 2: Improve VCode Generation
- [ ] Better instruction selection
- [ ] Reduce register pressure through scheduling
- [ ] Implement rematerialization (recompute vs reload)

#### Phase 3: Architecture-Specific Optimizations
- [ ] Use ARM64 register pairs (X0/X1, etc.)
- [ ] Exploit x86-64 two-address instructions
- [ ] WASM local variable optimization

### Example: Before and After

#### Before (Naive)
```asm
// Computing (a+b) * (c+d) * (e+f)
mov x0, #1    // a
mov x1, #2    // b
mov x2, #3    // c
mov x3, #4    // d
mov x4, #5    // e
mov x5, #6    // f
add x6, x0, x1  // t1 = a + b
add x7, x2, x3  // t2 = c + d
add x8, x4, x5  // t3 = e + f
mul x9, x6, x7  // t4 = t1 * t2
mul x10, x9, x8 // result = t4 * t3
// Uses 11 registers!
```

#### After (With Proper Allocation)
```asm
// Computing (a+b) * (c+d) * (e+f)
mov x0, #1    // a
mov x1, #2    // b
add x0, x0, x1  // a = a + b (reuse x0)
mov x1, #3    // c (reuse x1)
mov x2, #4    // d
add x1, x1, x2  // c = c + d
mul x0, x0, x1  // a = a * c
mov x1, #5    // e
mov x2, #6    // f
add x1, x1, x2  // e = e + f
mul x0, x0, x1  // result = a * e
// Uses only 3 registers!
```

### Benefits

1. **Correctness**: Handle arbitrary numbers of variables
2. **Performance**: Minimize memory access through smart allocation
3. **Code Size**: Fewer spill/reload instructions
4. **Foundation**: Enables more complex optimizations

### Testing Strategy

1. **Unit Tests**: Test individual allocation decisions
2. **Integration Tests**: Full programs with high register pressure
3. **Benchmarks**: Measure spill counts and performance
4. **Validation**: Ensure correctness with different allocation strategies

## Connection to MMC Vision

Proper register allocation is essential for Mario's vision of predictable, verifiable code generation:
- Deterministic allocation for reproducible proofs
- Explicit spill decisions for memory reasoning
- Foundation for verified optimization passes
- Enables complex programs while maintaining formal properties

With proper register allocation, the MM0 compiler can handle real-world programs while maintaining the formal verification properties that make it unique.