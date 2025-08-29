# MM0 Argument Passing Implementation Progress

## What We've Accomplished

### 1. Successfully Modified MM0 Compiler to Pass Arguments
- Modified `build_mir.rs` to pass arguments to main functions
- Currently passing hardcoded value 42 as proof of concept
- Debug output confirms: "DEBUG: main has 1 argument, passing hardcoded 42 for now"

### 2. Discovered and Worked Around Proof Generation Issue
- MM0's proof system expects procedures without arguments to have type `set`
- Procedures with arguments have type `nat`, causing: "Expected sort set, got nat"
- Found workaround using `mmc->string` to bypass proof generation and generate ELF directly

### 3. Created Test Programs
- `test_simple_print.mm1` - Shows argument passing with debug output
- `test_use_arg.mm1` - Uses passed argument in computation
- Both compile successfully when using `(print (mmc->string))` approach

## Technical Details

### The Change
In `components/mmcc/src/build_mir.rs` around line 1814:
```rust
vec![(true, Constant::int(IntTy::UInt(Size::S32), 42.into()).into())]
```

This passes a hardcoded u32 value of 42 to any main function that accepts one argument.

### Next Steps to Connect to Real argc/argv

1. **Read argc from stack at _start entry**
   - Linux x86-64 ABI puts argc at [RSP] when program starts
   - Need to generate code to: `mov rax, [rsp]`

2. **Pass argv pointer**
   - argv array starts at RSP+8
   - For full argc/argv support, need to pass both values

3. **Fix proof generation**
   - Either fix the type system to handle procedures with arguments
   - Or create separate proof rules for main functions

## Example Working Program

```mm1
import "compiler.mm1";

do {
  (mmc-add '(
    (proc (main {n : u32})
      -- n will receive the value 42
      {x := n}  
    )
  ))
  (print (mmc->string))  -- Bypasses proof generation
};
```

## Key Finding
The MM0 compiler infrastructure for passing arguments works! The main obstacles are:
1. Connecting to actual command-line arguments (engineering task)
2. Fixing proof generation for procedures with arguments (theoretical task)

The path forward is clear for creating a calculator that can process command-line arguments.

## Update: Deeper Investigation Shows Path to Real argc/argv

### What We Need
To read argc from the stack at program start:
1. At entry to _start, RSP points to argc (Linux x86-64 ABI)
2. Need to generate: `mov rax, [rsp]` to read argc
3. argv array starts at RSP+8

### Architecture Layers
- **MIR Level** (where we made changes): Mid-level representation, too high for direct register access
- **Assembly Level** (where we need to be): Can generate `mov` instructions with RSP
- **Challenge**: Need to bridge between these layers

### Possible Approaches
1. **Add intrinsic for stack access**: Create a special intrinsic like `__builtin_read_rsp()`
2. **Modify _start prologue**: Add assembly directly to read argc before calling main
3. **Use inline assembly**: If MM0 supports it (investigation needed)

### Next Steps
1. Look at how sys_write intrinsic is implemented (it accesses memory)
2. Study the assembly generation layer in more detail
3. Consider adding a `__builtin_argc` intrinsic that the start routine can use

The infrastructure is solid - we just need the right hook to access the initial stack values.

## Update 2: Arithmetic Operations Working!

We've successfully demonstrated:

1. **Arithmetic operations**: Addition (+), subtraction (-), multiplication (*) all work
   - Division (/) and modulo (%) are not yet implemented in MM0
   - All arithmetic returns `nat` type, requiring `cast` to `u32`

2. **Number to ASCII conversion**: Can convert single digits to characters
   ```mm1
   {{d : u8} := (cast {digit + 48})}  -- '0' = ASCII 48
   ```

3. **Complete computation example**:
   - Pass 123 as argument to main
   - Add 77 to get 200
   - Display both "123" and "200" as output

### Working Examples
- `test_arithmetic.mm1` - Basic addition with output
- `test_calc_ops.mm1` - Multiple arithmetic operations
- `test_digit_convert.mm1` - Convert numbers to displayable strings

### Next Steps
1. Create proper number-to-string conversion (handle multi-digit numbers)
2. Parse command-line arguments when we get real argc/argv access
3. Build the calculator: `./calc add 42 58` → `100`

The foundation for a working calculator is now in place!