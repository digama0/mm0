# SIMD 128-bit Intrinsics Design

## Overview

This document outlines the design for unified 128-bit SIMD intrinsics across x86-64 (SSE), ARM64 (NEON), and WebAssembly (SIMD128).

## Goals

1. **Unified API**: Single set of intrinsics that map to platform-specific instructions
2. **Type Safety**: MM0 type system integration for verified SIMD operations  
3. **Performance**: Zero-cost abstraction - direct mapping to hardware
4. **Portability**: Same MM1 code compiles to all three targets

## Type System

### SIMD Vector Types

```mm1
-- 128-bit vector types
type v128;           -- Generic 128-bit vector
type v4f32;          -- 4 x float32
type v2f64;          -- 2 x float64
type v4i32;          -- 4 x int32  
type v2i64;          -- 2 x int64
type v8i16;          -- 8 x int16
type v16i8;          -- 16 x int8
```

### Type Conversions

```mm1
-- Reinterpret casts (no-op at runtime)
intrinsic (v128.as_v4f32 (v: v128): v4f32);
intrinsic (v128.as_v4i32 (v: v128): v4i32);
-- etc.
```

## Core Intrinsics

### Load/Store Operations

```mm1
-- Aligned loads (16-byte alignment required)
intrinsic (v128.load (ptr: (&sn (array u8 16))): v128);
intrinsic (v128.store (ptr: (&mut (array u8 16))) (v: v128));

-- Unaligned loads (slower but no alignment requirement)
intrinsic (v128.load_unaligned (ptr: (&sn (array u8 16))): v128);
```

**Instruction Mapping**:
- x86-64: `movaps`/`movups` (aligned/unaligned)
- ARM64: `ldr q0, [x0]` / `ldur q0, [x0]`
- WASM: `v128.load` / `v128.load`

### Arithmetic Operations

```mm1
-- Addition
intrinsic (v4f32.add (a: v4f32) (b: v4f32): v4f32);
intrinsic (v4i32.add (a: v4i32) (b: v4i32): v4i32);

-- Subtraction
intrinsic (v4f32.sub (a: v4f32) (b: v4f32): v4f32);
intrinsic (v4i32.sub (a: v4i32) (b: v4i32): v4i32);

-- Multiplication
intrinsic (v4f32.mul (a: v4f32) (b: v4f32): v4f32);
intrinsic (v4i32.mul (a: v4i32) (b: v4i32): v4i32);

-- Division (float only)
intrinsic (v4f32.div (a: v4f32) (b: v4f32): v4f32);
```

**Instruction Mapping**:
- x86-64: `addps`, `subps`, `mulps`, `divps` (float), `paddd` (int)
- ARM64: `fadd`, `fsub`, `fmul`, `fdiv` (float), `add`, `sub`, `mul` (int)
- WASM: `f32x4.add`, `i32x4.add`, etc.

### Comparison Operations

```mm1
-- Float comparisons (returns mask)
intrinsic (v4f32.eq (a: v4f32) (b: v4f32): v4i32);
intrinsic (v4f32.lt (a: v4f32) (b: v4f32): v4i32);
intrinsic (v4f32.le (a: v4f32) (b: v4f32): v4i32);

-- Integer comparisons
intrinsic (v4i32.eq (a: v4i32) (b: v4i32): v4i32);
intrinsic (v4i32.gt_s (a: v4i32) (b: v4i32): v4i32); -- signed
intrinsic (v4i32.gt_u (a: v4i32) (b: v4i32): v4i32); -- unsigned
```

### Shuffle/Permute Operations

```mm1
-- Shuffle within vector
intrinsic (v4f32.shuffle (v: v4f32) (indices: u32): v4f32);

-- Shuffle between two vectors
intrinsic (v4f32.shuffle2 (a: v4f32) (b: v4f32) (indices: u32): v4f32);
```

### Reduction Operations

```mm1
-- Horizontal sum
intrinsic (v4f32.sum (v: v4f32): f32);
intrinsic (v4i32.sum (v: v4i32): i32);

-- Min/max reductions
intrinsic (v4f32.min_element (v: v4f32): f32);
intrinsic (v4f32.max_element (v: v4f32): f32);
```

## Implementation Strategy

### 1. MIR Extensions

Add SIMD types to the MIR type system:

```rust
// In types/mir.rs
pub enum Type {
    // ... existing types ...
    V128,
    V4F32,
    V2F64,
    V4I32,
    // etc.
}
```

### 2. Instruction Selection

Each backend maps MIR SIMD operations to native instructions:

```rust
// In arch/x86/lower.rs
match op {
    MirOp::V4F32Add(dst, src1, src2) => {
        emit(Inst::Addps { dst, src1, src2 })
    }
    // ...
}
```

### 3. Type Checking

Ensure SIMD operations are type-safe at elaboration time:

```mm1
-- This should fail type checking:
{v1 : v4f32} := ...
{v2 : v4i32} := ...
{result := (v4f32.add v1 v2)} -- Error: type mismatch
```

### 4. Verification

For each intrinsic, provide formal semantics:

```mm1
-- Theorem: vector addition is element-wise
theorem v4f32_add_elementwise (a b: v4f32):
  $ (v4f32.add a b) = 
    v4f32.pack 
      (f32.add (v4f32.extract a 0) (v4f32.extract b 0))
      (f32.add (v4f32.extract a 1) (v4f32.extract b 1))
      (f32.add (v4f32.extract a 2) (v4f32.extract b 2))
      (f32.add (v4f32.extract a 3) (v4f32.extract b 3)) $;
```

## Example Usage

### Vector Dot Product

```mm1
(proc (dot_product {a : v4f32} {b : v4f32} : f32)
  {product := (v4f32.mul a b)}
  (return (v4f32.sum product)))
```

### Matrix Multiplication (4x4)

```mm1
(proc (mat4_mul {a : (array v4f32 4)} {b : (array v4f32 4)} 
                {out : (&mut (array v4f32 4))})
  -- Transpose b for efficient dot products
  {b_t := (transpose_4x4 b)}
  
  -- Compute each output row
  (for {i : u32} 0 4
    {row := (v128.load (& a[i]))}
    {result := (v4f32.zero)}
    
    (for {j : u32} 0 4
      {col := (v128.load (& b_t[j]))}
      {prod := (v4f32.mul row col)}
      {result := (v4f32.add result prod)})
    
    (v128.store (& out[i]) result)))
```

## Platform-Specific Considerations

### x86-64 SSE
- Requires 16-byte alignment for best performance
- Has both packed (all elements) and scalar (single element) operations
- SSE4.1 adds useful instructions like `ptest`, `blendps`

### ARM64 NEON
- More orthogonal instruction set than SSE
- Better support for different data sizes
- Has unique features like polynomial multiplication

### WebAssembly SIMD128
- Most portable but may be slower than native
- Limited to operations in the SIMD128 proposal
- No alignment requirements

## Testing Strategy

1. **Unit Tests**: Test each intrinsic in isolation
2. **Cross-Platform Tests**: Same test runs on all architectures
3. **Performance Tests**: Ensure SIMD is faster than scalar
4. **Verification Tests**: Prove correctness properties

## Future Extensions

1. **AVX/AVX2**: 256-bit vectors for x86-64
2. **SVE**: Scalable vectors for ARM64
3. **Automatic Vectorization**: Compiler identifies vectorizable loops
4. **SIMD-aware Optimization**: Instruction scheduling for SIMD

## References

- [Intel Intrinsics Guide](https://software.intel.com/sites/landingpage/IntrinsicsGuide/)
- [ARM NEON Intrinsics Reference](https://developer.arm.com/architectures/instruction-sets/intrinsics/)
- [WebAssembly SIMD Proposal](https://github.com/WebAssembly/simd/blob/main/proposals/simd/SIMD.md)