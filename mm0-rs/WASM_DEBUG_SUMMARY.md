# WASM Generation Debug Summary

## The Problem
Our WASM calculator was generating invalid modules that failed validation with "unexpected end-of-file" error.

## Root Cause
The code section had incorrect byte counts:
- Function body size was declared as 0x0c (12) but was actually 0x0d (13) bytes
- Code section length was declared as 0x0e (14) but needed to be 0x0f (15) bytes

## The Fix
Changed in `generate_calculator_binaries.rs`:
```rust
// Before (incorrect):
0x0a, // section id
0x0e, // section length ❌
0x01, // number of functions
0x0c, // function body size ❌

// After (correct):
0x0a, // section id
0x0f, // section length ✅ 
0x01, // number of functions
0x0d, // function body size ✅
```

## Why It Matters
WASM uses precise byte counts for parsing. The validator reads exactly the number of bytes specified, so incorrect counts cause it to stop reading mid-instruction, resulting in "unexpected EOF".

## Function Body Breakdown (13 bytes)
```
0x00        // number of locals (1 byte)
0x41 0x0a   // i32.const 10 (2 bytes)
0x41 0x05   // i32.const 5 (2 bytes)
0x6a        // i32.add (1 byte)
0x41 0x03   // i32.const 3 (2 bytes)
0x6c        // i32.mul (1 byte)
0x41 0x02   // i32.const 2 (2 bytes)
0x6b        // i32.sub (1 byte)
0x0b        // end (1 byte)
```
Total: 1 + 2 + 2 + 1 + 2 + 1 + 2 + 1 + 1 = 13 bytes

## Test Results
- ARM64: Exit code 43 ✅
- WASM: Output 43 ✅ (via stdout, not exit code)
- x86-64: Binary generated (needs Linux to test)

## Key Lesson
When debugging binary formats:
1. Verify all length fields match actual data
2. Count bytes carefully, including all prefixes
3. Use hex dumps to verify file contents
4. Test with multiple validators/runtimes for better error messages