# Arithmetic Instruction Comparison Across Architectures

## Overview

This document compares how arithmetic operations are implemented across x86-64, ARM64, and WASM architectures in the MM0 compiler.

## Basic Arithmetic Operations

### Addition

**x86-64**
```asm
ADD RAX, RBX        ; RAX = RAX + RBX
ADD RCX, 42         ; RCX = RCX + 42
```
- Two-operand form (destination is also source)
- Supports register-register and register-immediate
- Sets condition flags

**ARM64**
```asm
ADD X0, X1, X2      ; X0 = X1 + X2
ADD X3, X4, #42     ; X3 = X4 + 42
```
- Three-operand form (separate destination)
- Supports register-register and register-immediate
- Optional flag setting with ADDS variant

**WASM**
```wasm
local.get 0         ; Push first operand
local.get 1         ; Push second operand
i32.add            ; Pop both, push result
local.set 2        ; Store result
```
- Stack-based (no registers)
- Operands pushed onto stack
- Result left on stack

### Subtraction

**x86-64**
```asm
SUB RAX, RBX        ; RAX = RAX - RBX
SUB RCX, 100        ; RCX = RCX - 100
```

**ARM64**
```asm
SUB X0, X1, X2      ; X0 = X1 - X2
SUB X3, X4, #100    ; X3 = X4 - 100
```

**WASM**
```wasm
local.get 0         ; Push minuend
local.get 1         ; Push subtrahend
i32.sub            ; Pop both, push difference
```

### Multiplication

**x86-64**
```asm
IMUL RAX, RBX       ; RAX = RAX * RBX (signed)
MUL RBX             ; RDX:RAX = RAX * RBX (unsigned)
```
- IMUL for signed, MUL for unsigned
- MUL produces 128-bit result in RDX:RAX

**ARM64**
```asm
MUL X0, X1, X2      ; X0 = X1 * X2 (lower 64 bits)
SMULL X0, W1, W2    ; X0 = W1 * W2 (32→64 bit signed)
```
- Separate signed/unsigned variants
- MADD for multiply-accumulate

**WASM**
```wasm
local.get 0
local.get 1
i32.mul            ; 32-bit multiplication
```

### Division

**x86-64**
```asm
IDIV RBX            ; RAX = RDX:RAX / RBX, RDX = remainder
```
- Dividend in RDX:RAX
- Quotient in RAX, remainder in RDX

**ARM64**
```asm
SDIV X0, X1, X2     ; X0 = X1 / X2 (signed)
UDIV X0, X1, X2     ; X0 = X1 / X2 (unsigned)
```
- No remainder calculation
- Separate signed/unsigned instructions

**WASM**
```wasm
local.get 0
local.get 1
i32.div_s          ; Signed division
```

## Encoding Examples

### ADD Instruction Encoding

**x86-64**: `ADD RAX, RBX`
```
48 01 D8
│  │  └─ ModR/M: reg=RBX, r/m=RAX
│  └──── ADD opcode
└─────── REX.W (64-bit)
```

**ARM64**: `ADD X0, X1, X2`
```
8B 02 00 20
│  │  │  └─ Rd=X0 (bits 0-4)
│  │  └──── Rn=X1 (bits 5-9)
│  └─────── Rm=X2 (bits 16-20)
└────────── ADD opcode + 64-bit flag
```

**WASM**: `i32.add`
```
6A
└─ Single-byte opcode
```

## Key Differences

### 1. Instruction Format
- **x86-64**: Variable length (1-15 bytes), CISC
- **ARM64**: Fixed 32-bit instructions, RISC
- **WASM**: Variable length bytecode, stack machine

### 2. Operand Model
- **x86-64**: Two-operand (dst = dst op src)
- **ARM64**: Three-operand (dst = src1 op src2)
- **WASM**: Zero-operand (stack-based)

### 3. Register Usage
- **x86-64**: 16 GPRs (RAX-R15)
- **ARM64**: 31 GPRs (X0-X30)
- **WASM**: No registers, uses locals

### 4. Condition Codes
- **x86-64**: Most arithmetic sets flags automatically
- **ARM64**: Separate flag-setting variants (ADDS, SUBS)
- **WASM**: No flags, use comparison instructions

## Implementation in MM0

The MM0 compiler handles these differences through:

1. **Architecture traits**: Define common interface
2. **Instruction selection**: Convert MIR to architecture-specific instructions
3. **Register allocation**: Handle register vs stack differences
4. **Code emission**: Generate correct encodings

Each architecture backend implements the same arithmetic operations but with architecture-specific details handled internally.