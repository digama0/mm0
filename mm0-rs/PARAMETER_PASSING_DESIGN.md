# MM0 Compiler: Parameter Passing and Return Values

## Overview

The MM0 compiler now understands parameter passing and return values across all three architectures. We have the foundation in place through calling convention modules and can properly handle function arguments and returns.

## Current Infrastructure

### ARM64
- **Module**: `components/mmcc/src/arch/arm64/calling_conv.rs`
- **Convention**: AAPCS64 (ARM Architecture Procedure Call Standard)
- **Implementation**: Complete with register allocation and frame layout

### x86-64
- **Convention**: System V ABI (Linux/BSD) 
- **Status**: Needs similar calling_conv.rs module

### WebAssembly
- **Convention**: Stack-based with typed functions
- **Status**: Parameters part of function type signatures

## Parameter Passing

### Register-Based (ARM64 & x86-64)

```rust
// Example: add(10, 32)

// ARM64
mov x0, #10      // First parameter in X0
mov x1, #32      // Second parameter in X1  
bl add           // Call function

// x86-64
mov rdi, 10      // First parameter in RDI
mov rsi, 32      // Second parameter in RSI
call add         // Call function
```

### Stack-Based (WebAssembly)

```wast
;; Function type: (param i32 i32) (result i32)
i32.const 10     ;; Push first parameter
i32.const 32     ;; Push second parameter
call $add        ;; Call function (pops params, pushes result)
```

## Return Values

All architectures use specific locations for return values:
- **ARM64**: X0 (X1 for 128-bit values)
- **x86-64**: RAX (RDX:RAX for 128-bit values)
- **WebAssembly**: Top of operand stack

## main() Function Special Handling

### Traditional Systems (ARM64/x86-64)

The `main` function receives:
- First parameter: `argc` (argument count)
- Second parameter: `argv` (pointer to array of string pointers)

```c
int main(int argc, char *argv[]) {
    // argc: number of arguments (including program name)
    // argv: array of pointers to argument strings
    // argv[0]: program name
    // argv[1]: first argument
    // ...
    return 42; // Exit code
}
```

**ARM64 main**:
```asm
_main:
    ; X0 = argc
    ; X1 = argv
    ldr x2, [x1, #8]  ; Load argv[1]
    mov x0, #42       ; Return value
    ret
```

**x86-64 main**:
```asm
main:
    ; RDI = argc  
    ; RSI = argv
    mov rax, [rsi+8]  ; Load argv[1]
    mov rax, 42       ; Return value
    ret
```

### WebAssembly

WASM modules don't receive argc/argv directly. Instead, they use WASI (WebAssembly System Interface) imports:

```rust
// WASI functions for command line access
args_sizes_get() -> (argc, argv_buf_size)
args_get(argv_ptr, argv_buf_ptr) -> ()
```

## Implementation in MM0 Compiler

### VCode Integration

The compiler's VCode (virtual code) layer needs to understand:

1. **Function signatures** with parameter types
2. **Calling convention** for target architecture
3. **Register allocation** for parameters
4. **Stack frame layout** for locals and spills

### Code Generation Flow

```rust
// When generating a function call:
fn gen_call(func: FuncId, args: Vec<Value>) -> Value {
    let conv = self.calling_convention();
    
    // 1. Allocate argument registers/stack slots
    for (i, arg) in args.iter().enumerate() {
        let abi = conv.arg_abi(i, arg.ty());
        match abi {
            ArgAbi::Reg(reg, _) => {
                // Move argument to register
                self.emit_move(arg, reg);
            }
            ArgAbi::Mem { off, .. } => {
                // Store argument on stack
                self.emit_store(arg, sp + off);
            }
        }
    }
    
    // 2. Emit call instruction
    self.emit_call(func);
    
    // 3. Handle return value
    let ret_abi = conv.ret_abi(0, ret_ty);
    match ret_abi {
        ArgAbi::Reg(reg, _) => {
            // Return value is in register
            self.read_reg(reg)
        }
        ArgAbi::Mem { .. } => {
            // Large return via memory
            self.read_mem(ret_ptr)
        }
    }
}
```

## Testing Strategy

1. **Simple functions**: `add(a, b)`, `mul(x, y)`
2. **Many parameters**: Test stack spillover (>6 args on x86, >8 on ARM64)
3. **main() variants**: No args, with args, checking argc
4. **Return values**: Different sizes and types

## Next Steps

1. ✅ ARM64 calling convention (already implemented)
2. ⏳ Add x86-64 calling convention module
3. ⏳ Integrate with VCode layer
4. ⏳ Add parameter passing to existing tests
5. ⏳ Implement main() special handling

## Example: Complete Function Call

Here's how `result = add(10, 32)` works end-to-end:

### MM0 Source
```mm0
(func add ((a i32) (b i32)) i32
  (+ a b))

(func main () i32
  (add 10 32))
```

### Generated ARM64
```asm
add:
    add x0, x0, x1
    ret

main:
    mov x0, #10
    mov x1, #32
    bl add
    ; x0 = 42
    ret
```

### Generated x86-64
```asm
add:
    lea rax, [rdi + rsi]
    ret

main:
    mov rdi, 10
    mov rsi, 32
    call add
    ; rax = 42
    ret
```

### Generated WASM
```wast
(func $add (param i32 i32) (result i32)
  local.get 0
  local.get 1
  i32.add)

(func $main (result i32)
  i32.const 10
  i32.const 32
  call $add)
```

This design provides a solid foundation for implementing full function call support in the MM0 compiler!