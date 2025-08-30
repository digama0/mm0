# Understanding main(argc, argv) and Return Values

## Summary

Yes, we now fully understand how `main` receives optional arguments and handles return values across all architectures. Here's what we've learned:

## main() Function Arguments

### ARM64
```asm
_main:
    ; X0 = argc (argument count, always >= 1)
    ; X1 = argv (pointer to array of string pointers)
    
    ; Example: ./program hello world
    ; X0 = 3 (program name + 2 args)
    ; X1 points to: ["./program", "hello", "world", NULL]
```

### x86-64
```asm
main:
    ; RDI = argc (argument count)
    ; RSI = argv (pointer to array)
    
    ; Or in _start (Linux entry point):
    ; [RSP] = argc
    ; [RSP+8] = argv[0]
    ; [RSP+16] = argv[1], etc.
```

### WebAssembly
WASM doesn't receive argc/argv directly. Instead uses WASI:
```rust
// Import WASI functions
@import("wasi_unstable", "args_sizes_get") 
fn args_sizes_get(argc_ptr: *u32, argv_size_ptr: *u32) -> i32;

@import("wasi_unstable", "args_get")
fn args_get(argv_ptr: *[*]u8, argv_buf_ptr: *u8) -> i32;
```

## Return Values

The value returned from `main` becomes the process exit code:

### Success/Failure Convention
- 0 = Success
- Non-zero = Error (1-255 on Unix systems)

### Architecture Implementation
```asm
; ARM64
mov x0, #42    ; Set return value
ret            ; Return to OS

; x86-64
mov rax, 42    ; Set return value
ret            ; Or use exit syscall

; WASM
i32.const 42   ; Push return value
return         ; Or let it be top of stack at function end
```

## Practical Example

We tested this with a program that:
1. Returns 42 when no arguments provided (argc = 1)
2. Returns argc when one argument provided (argc = 2) 
3. Returns 100 + argc when multiple arguments provided

```bash
$ ./program
# Exit code: 42

$ ./program hello
# Exit code: 2

$ ./program one two three
# Exit code: 104 (100 + 4)
```

## Key Insights

1. **argc is never 0** - It's always at least 1 (the program name)
2. **argv is NULL-terminated** - Last element is always NULL pointer
3. **Platform differences**:
   - Linux/BSD: `_start` gets args on stack
   - macOS: `main` gets args in registers
   - WASM: Must use WASI imports

4. **Return value limits**: 
   - Unix: 0-255 (8-bit)
   - Windows: Full 32-bit range
   - WASM: 32-bit integer

## MM0 Compiler Implementation

The compiler needs to:

1. **Recognize main as special**:
   ```mm0
   (func main ((argc i32) (argv ptr)) i32
     ; Can access command line arguments
     (if (> argc 1)
       (print (load argv 1))  ; Print first argument
       (return 0)))
   ```

2. **Generate proper prologue**:
   - Save/setup frame pointer
   - Preserve callee-saved registers
   - Access parameters correctly

3. **Handle different signatures**:
   ```mm0
   ; No arguments
   (func main () i32 ...)
   
   ; With arguments  
   (func main ((argc i32) (argv ptr)) i32 ...)
   
   ; With environment
   (func main ((argc i32) (argv ptr) (envp ptr)) i32 ...)
   ```

## Testing Approach

Our test successfully demonstrated:
- ✅ Parameter passing in registers
- ✅ Accessing argc value
- ✅ Different return values based on arguments
- ✅ Calling conventions work correctly

This gives us confidence that the MM0 compiler can properly implement main() with full argument support!