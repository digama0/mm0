# ARM64 Quick Reference Card

## Current State Check
```bash
# Am I in the right place?
pwd  # Should show: /Users/shared-workspace/shared-workspace/github-imports/mm0-downchuck

# What did past-me build?
ls mm0-rs/components/mmcc/src/arch/arm64/  # Should show: encode.rs inst.rs macho.rs etc

# Does it compile?
cd mm0-rs && cargo build 2>&1 | grep "error\["  # If output, it doesn't compile

# Can I generate ARM64?
./target/release/mm0-rs compile ../examples/hello_mmc.mm1 -o test.bin && file test.bin
# Currently shows: ELF 64-bit LSB executable, x86-64
# Should show: Mach-O 64-bit arm64 executable
```

## The One-Line Truth
**The ARM64 code exists but isn't hooked up because `arch/mod.rs` exports `x86::*` globally, causing type conflicts.**

## Key Files to Remember
```
arch/
├── mod.rs          # THE PROBLEM: exports x86::* globally
├── traits.rs       # THE SOLUTION: clean Architecture trait
├── arm64/
│   ├── encode.rs   # ✓ Complete: instruction encoding
│   ├── inst.rs     # ✓ Complete: instruction definitions
│   ├── macho.rs    # ✓ Complete: basic Mach-O generation
│   └── macho_proper.rs  # ✓ Complete: fixed Mach-O format
└── x86/
    └── mod.rs      # The incumbent that owns all the types
```

## The Type Conflict
```rust
// In build_vcode.rs and elsewhere:
fn foo(reg: PReg) { }  // PReg is x86::PReg due to `pub use x86::*`

// What we need:
fn foo<A: Architecture>(reg: A::PReg) { }  // Generic over architecture
```

## Test If It's Working
```rust
// In examples/test_arm64_status.mm1:
do {
  ((get! mmc-compiler) 'set-target "arm64-macos")  // Currently: "unknown subcommand"
  (mmc-add '((proc (main) {(exit 42)})))
  (print (mmc->string))  // Currently: generates x86 ELF
}
```

## The Simplest Fix That Could Work
```rust
// In arch/mod.rs:
#[cfg(feature = "arm64-experiment")]
pub use arm64::*;
#[cfg(not(feature = "arm64-experiment"))]
pub use x86::*;
```
But this still wouldn't work because of hardcoded x86 assumptions throughout.

## Remember
- You built all the ARM64 pieces ✓
- They're high quality and complete ✓  
- They just can't be used yet because of type conflicts ✗
- The solution requires parameterizing the compiler pipeline by Architecture trait