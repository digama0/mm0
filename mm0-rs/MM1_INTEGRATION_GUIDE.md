# MM1 Integration Guide for MM0 Compiler

## Overview

The MM1 integration provides a high-level language for writing programs that compile to native code through the MM0 compiler. This guide shows how to use the improved MMC library for easier program development.

## Quick Start

### 1. Basic Program Structure

```mm1
import "mmc_lib.mm1";

def my_program: string =
  (function 'main () 'i32
    '(block
      -- Your code here
      (return 0)));

do {
  (compile_function "my_program" my_program)
};
```

### 2. Using High-Level Constructs

The MMC library provides familiar programming constructs:

#### Variables
```mm1
(let x i32 42)          -- Declare with initial value
(set x (+ x 1))         -- Update value
```

#### Control Flow
```mm1
-- If-then-else
(if (< x 10)
  (return 1)
  (return 0))

-- While loop
(while (< i 10)
  (block
    (print_num i)
    (set i (+ i 1))))

-- For loop
(for i 0 10
  (print_num i))
```

#### Functions
```mm1
def add_func: string =
  (function 'add '((a i32) (b i32)) 'i32
    '(return (+ a b)));
```

## Architecture Support

### ARM64 (Darwin/macOS)
- Primary development platform
- Native execution on Apple Silicon
- Full instruction set support

### x86-64 (Linux/BSD)
- System V ABI compliance
- Can test with Apple containers
- Red zone optimization

### WebAssembly
- Platform-independent
- Stack-based architecture
- Different programming model

## Example Programs

### 1. Hello World
```mm1
import "mmc_lib.mm1";

do {
  (compile_function "hello" hello_world)
};
```

### 2. Fibonacci Calculator
```mm1
def fib_func: string =
  (function 'fib '((n i32)) 'i32
    '(if (<= n 1)
      (return n)
      (return (+ (fib (- n 1)) (fib (- n 2))))));
```

### 3. Command Line Arguments
```mm1
def main_with_args: string =
  (function 'main '((argc i32) (argv ptr)) 'i32
    '(block
      (if (> argc 1)
        (print (load (+ argv 8)))  -- argv[1]
        (print "No args\n"))
      (return 0)));
```

### 4. Array Processing
```mm1
def sum_array: string =
  (function 'sum '((arr ptr) (len i32)) 'i32
    '(block
      (let sum i32 0)
      (for i 0 len
        (set sum (+ sum (load (+ arr (* i 8))))))
      (return sum)));
```

## Memory Model

### Stack Allocation
```mm1
(let arr (array i32 10) 0)  -- Array of 10 integers on stack
```

### Load/Store Operations
```mm1
(store ptr value)           -- Store value at address
(load ptr)                  -- Load value from address
```

### Pointer Arithmetic
```mm1
(+ ptr (* index size))      -- Calculate array element address
```

## Type System

### Basic Types
- `i32`, `i64` - Signed integers
- `u8`, `u16`, `u32`, `u64` - Unsigned integers
- `ptr` - Pointer type

### Composite Types
- `(array T n)` - Array of n elements
- `(ref T)` - Reference to T

## Compilation Process

### 1. Write MM1 Program
Create a `.mm1` file using the MMC library constructs.

### 2. Compile with mm0-rs
```bash
mm0-rs compile program.mm1 --output program
```

### 3. Run the Binary
```bash
./program
```

## Advanced Features

### System Calls
```mm1
-- Write to stdout
(syscall 1 1 buffer length)

-- Exit with code
(syscall 60 exit_code)
```

### Inline Assembly (Future)
Support for inline assembly blocks for architecture-specific optimizations.

### Verification Integration
Programs can include MM0 theorems to prove properties about the code.

## Best Practices

1. **Use High-Level Constructs**: The MMC library provides safer abstractions
2. **Test on Multiple Architectures**: Ensure portability
3. **Add Comments**: Document complex algorithms
4. **Verify Properties**: Use MM0 theorems for critical code

## Debugging Tips

1. **Check Exit Codes**: Return values become process exit codes
2. **Use Print Statements**: Debug with print_num/print_str
3. **Examine Generated Code**: Use objdump or similar tools
4. **Test Incrementally**: Build complex programs step by step

## Future Enhancements

- [ ] Heap allocation support
- [ ] String manipulation library
- [ ] File I/O operations
- [ ] Network socket support
- [ ] Debugging symbols generation
- [ ] Optimization passes

## Conclusion

The improved MM1 integration makes it much easier to write programs for the MM0 compiler. The high-level constructs in `mmc_lib.mm1` provide a familiar programming experience while maintaining the formal verification capabilities that make MM0 unique.