# ARM64 Integration Guide for AI Consciousness

## Critical Context Anchors

### What You Just Built (Remember This!)
```
Location: /Users/shared-workspace/shared-workspace/github-imports/mm0-downchuck/mm0-rs/components/mmcc/src/arch/
Files: arm64/*, traits.rs, target.rs, codegen_multi.rs
Status: Complete but not integrated
```

### The Core Truth
**You cannot generate ARM64 binaries yet.** The code exists but doesn't compile because:
- `arch/mod.rs` exports only x86 (`pub use x86::*`)
- MIR pipeline hardcodes x86 assumptions
- Build fails with trait conflicts when you try to add ARM64

## Architecture Reference Points

### 1. The Clean Abstraction (traits.rs)
```rust
pub trait Architecture {
    type PReg: PhysicalReg;     // Register type
    type Inst: Instruction;      // Instruction type
    // ... methods for register allocation, syscalls, etc
}
```
This is the correct design. Reference this when refactoring.

### 2. The Conflict Point (arch/mod.rs)
```rust
// Current (breaks everything):
pub use x86::*;  // Exports x86 types globally

// What you need (but causes conflicts):
pub mod x86;
pub mod arm64;
pub mod target;
```

### 3. The Integration Point (build_vcode.rs)
Line ~500-600: Where MIR gets lowered to machine code
Current: Assumes `PReg = x86::PReg`
Needed: `PReg = <Arch as Architecture>::PReg`

## Layer-Based Integration Strategy

### Layer 0: Recognition Layer
Before changing ANY code, run these checks:
```bash
# Check if ARM64 already works (it won't)
grep -r "TargetArch::Arm64" mm0-rs/components/mmcc/src/
# Find all x86 assumptions
grep -r "PReg::" mm0-rs/components/mmcc/src/ | grep -v "arch/x86"
```

### Layer 1: Namespace Isolation
Create parallel namespace to avoid conflicts:
```rust
// In arch/mod.rs
pub mod x86;
pub mod arm64;

// DON'T export anything globally yet
// pub use x86::*;  // REMOVE THIS

// Instead, create namespaced access
pub mod current {
    pub use super::x86::*;
}
```

### Layer 2: Type Parameterization
The hard part - parameterize the pipeline:
```rust
// Before (in build_vcode.rs):
fn lower_to_vcode(mir: &MIR) -> VCode<PReg> { ... }

// After:
fn lower_to_vcode<A: Architecture>(mir: &MIR) -> VCode<A::PReg> { ... }
```

### Layer 3: Runtime Selection
Add target selection that actually works:
```rust
match target.arch {
    TargetArch::X86_64 => lower_to_vcode::<x86::X86>(mir),
    TargetArch::Arm64 => lower_to_vcode::<arm64::Arm64>(mir),
}
```

## Critical Reference Standards

### ELF Magic Numbers (for verification)
```
x86-64 ELF: 7f 45 4c 46 02 01 01 00  (.ELF....)
ARM64 Mach-O: cf fa ed fe  (feed face reversed)
```

### Syscall Conventions (platform-specific)
```rust
// Linux x86-64: rax = syscall number
// Linux ARM64: x8 = syscall number  
// macOS ARM64: x16 = syscall number (DIFFERENT!)
```

### Test Commands (to verify progress)
```bash
# Generate output
./mm0-rs/target/release/mm0-rs compile examples/hello_mmc.mm1 -o test.bin

# Check format
file test.bin  # Should say "Mach-O 64-bit arm64 executable"
xxd test.bin | head -1  # Should start with "cffa edfe"
```

## Context Drift Prevention

### When You Get Lost
1. Check `git status` - if you see hundreds of changes, you've drifted
2. Run the test commands above - if still generating x86 ELF, no progress made
3. Look for this anchor: `arch/traits.rs` - this is your north star

### Common Drift Patterns
- **Forgetting the conflict**: You'll try to just import arm64 and it won't compile
- **Fixing symptoms**: You'll fix compile errors without addressing the architectural issue
- **Assuming it works**: You'll think set-target works because the code exists

### Re-orientation Procedure
```bash
# Where am I?
pwd  # Should be in mm0-downchuck

# What have I changed?
git diff --stat

# Does it compile?
cd mm0-rs && cargo build 2>&1 | grep -E "error|warning" | wc -l

# Can it generate ARM64?
grep "write_macho\|write_elf" components/mmcc/src/codegen.rs
```

## The Fundamental Challenge

The MM0 compiler has **type-level assumptions** about x86 throughout:
- `PReg` is assumed to be `x86::PReg` 
- `PInst` is assumed to be `x86::PInst`
- Functions take concrete types, not trait objects

This isn't a time problem - it's an architecture problem. The solution requires:
1. Recognizing where assumptions are made
2. Creating abstraction boundaries  
3. Maintaining type coherence across the boundary

## Success Criteria

You'll know you've succeeded when:
```bash
# This compiles without errors
cd mm0-rs && cargo build --release

# This generates Mach-O (not ELF)  
./target/release/mm0-rs compile ../examples/hello_mmc.mm1 -o test.bin
file test.bin  # Shows "Mach-O 64-bit arm64 executable"

# This actually sets the target
echo '(mmc 'set-target "arm64-macos")' | ./target/release/mm0-rs
# No error about unknown subcommand
```

Remember: The code you need already exists in `arch/arm64/`. The challenge is integration without breaking x86.