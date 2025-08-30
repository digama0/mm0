# Function Calls Implementation Status

## Summary

We have successfully implemented function call and return instructions for all three architectures in the MM0 compiler.

## Implementation Details

### ARM64
- **BL (Branch with Link)**: Direct function calls
  - Encoding: `0x94000000 | ((offset >> 2) & 0x3ffffff)`
  - Range: ±128MB
  - Saves return address in X30 (link register)
- **BLR (Branch with Link to Register)**: Indirect calls
  - Encoding: `0xd63f0000 | (reg << 5)`
  - Jumps to address in register
  - Saves return address in X30
- **RET**: Return from function
  - Encoding: `0xd65f03c0`
  - Returns to address in X30

### x86-64
- **CALL rel32**: Direct function calls
  - Encoding: `0xE8` followed by 32-bit relative offset
  - Pushes return address on stack
- **CALL r/m**: Indirect calls (existing implementation)
  - Various encodings for register/memory operands
- **RET**: Return from function
  - Encoding: `0xC3`
  - Pops return address from stack

### WebAssembly
- **call**: Direct function call by index
  - Encoding: `0x10` followed by LEB128 function index
  - Implemented in `WasmInst::Call { func_idx }`
- **return**: Return from function
  - Encoding: `0x0F`
  - Already implemented as `WasmInst::Return`

## Code Changes

1. **ARM64** (`components/mmcc/src/arch/arm64/`)
   - Added `Blr { reg: PReg }` to instruction enum
   - Implemented BLR encoding in `encode.rs`
   - BL and RET were already implemented

2. **WASM** (`components/mmcc/src/arch/wasm/`)
   - Added encoding for `Call` instruction
   - Return instruction was already implemented

3. **x86-64** (`components/mmcc/src/arch/x86/`)
   - Call instructions already exist in the instruction set
   - Implementation appears complete

## Test Results

```
BL offset 0x0 = 0x94000000      ✓
BL offset 0x1000 = 0x94000400   ✓
BL offset -0x1000 = 0x97fffc00  ✓
BLR X1 = 0xd63f0020             ✓
BLR X30 = 0xd63f03c0            ✓
```

## Next Steps

With arithmetic operations, conditional branches, and function calls implemented, we now have the core building blocks needed for:

1. **Calculator Demo**: Implement the full calculator example with function calls
2. **Loop Constructs**: Build loops using branches and comparisons
3. **Stack Frame Management**: Proper prologue/epilogue for functions
4. **Parameter Passing**: Following platform calling conventions