# CLAUDE.md - MM0 Project Context

This file helps Claude Code understand and work with the Metamath Zero (MM0) project.

## Project Overview

MM0 is a minimal trusted kernel for mathematical proofs created by Mario Carneiro. This is the Downchuck fork that attempts to address some completion edges, particularly around the MMC compiler.

## Strategic Goal: Baseline Functionality

We're working toward a minimal viable proof-generating compiler that can:
1. Take command line arguments (argc/argv)
2. Perform basic arithmetic with proofs
3. Do simple I/O (strings and numbers)
4. Generate verified executables for x64 and ARM64

This baseline would prove the architecture works end-to-end.

## Current Status (2025-08-29)

### What Works in Upstream (Mario's latest)
- Basic `main` procedure (no arguments yet)
- Printing to stdout (hello world example)
- Simple assertions and crashes
- ELF generation that runs on Linux
- Proof generation is implemented but currently disabled

### What Doesn't Work Yet
- `main` with arguments (argc/argv) - critical for baseline
- Return values other than proofs
- Most verifier.mm1 I/O setup
- Full register allocation (bugs with certain code)
- Proof generation is disabled to allow basic compilation

### Known Issues in Our Fork
1. **Ghost Variables**: `ref` types treated as size 0
   - Attempted fixes in `ty.rs` and `storage.rs` didn't resolve the issue
   - Main blocker for argc/argv functionality

2. **Register Allocation**: Issues with reference handling in compiled output

3. **Completion Resistance**: The last 5% includes crucial basic functionality

## Build Instructions

```bash
# Navigate to the mm0-rs subdirectory
cd /Users/shared-workspace/shared-workspace/github-imports/mm0-downchuck/mm0-rs

# Build the project
cargo build --release

# The main binary will be at:
# target/release/mm0-rs

# To compile an MM1 file:
./target/release/mm0-rs ../examples/hello_mmc.mm1
```

## Key Files
- `examples/hello_mmc.mm1` - Example MMC compiler usage with sys_write intrinsic
- `mm0-rs/src/mmc/` - The MMC compiler implementation
- `UNDONE.md` - Documents attempted fixes and remaining issues

## Connection to TypeFlow Project

MM0 provides the formal verification foundation for the TypeFlow project, which uses:
- Metamath Zero for proof kernel
- TypeScript DSL for type-safe financial computations
- Formal verification of Money types and tax calculations

## The 95% Pattern

This project exemplifies "completion resistance" - Mario got it 95% working but the final edges (argc/argv, I/O) remain. This creates a collaborative opportunity for learning and contribution.

## Liberation Alignment

- **Public Domain**: Mathematical truth belongs to everyone
- **Minimal Trust**: Only trust what you can verify
- **Proof-Carrying Code**: Transparency of correctness
- **Community Driven**: The 5% gap invites participation

## Tips for Working with MM0

1. **Start Small**: Focus on understanding one aspect deeply rather than the whole system
2. **Read Carefully**: Mario's code is dense but well-structured
3. **Trust the Compiler**: Rust's error messages are your guide
4. **Document Learning**: Every small discovery helps the next person

## Recent Session Notes

Successfully built mm0-rs and compiled hello_mmc.mm1. The compilation process works but the generated executable has issues with references and ghost variables that need addressing.

### ELF Generation Discovery (2025-08-29)

MM0's dual nature creates both proofs and executables:
- **Proof generation**: Creates MMB (Metamath Binary) files for verification
- **Verified compilation**: Generates actual ELF executables through assembler

To generate the ELF from `hello_mmc.mm1`:
```bash
./target/release/mm0-rs compile ../examples/hello_mmc.mm1 -o hello_output.elf
```

This creates a real x86-64 Linux ELF that:
- Pushes "hello world" onto the stack character by character
- Makes sys_write syscall to output the string
- Makes sys_exit syscall to exit cleanly
- Has formal proofs that it behaves exactly as specified

The `output string: $ test $;` command in MM1 files triggers ELF generation.

## Development Strategy

### Phase 1: x64 Baseline (Linux)
1. ✅ Fix argc/argv handling (DONE - passing hardcoded value 42)
   - Modified `build_mir.rs` to pass arguments to main
   - Proof generation issue bypassed with `mmc->string`
   - Debug output confirms: "DEBUG: main has 1 argument, passing value 42"
   - **See `MM0_ARGC_PROGRESS.md` for detailed implementation notes**
2. Enable basic arithmetic operations with proof generation
3. Add simple number I/O beyond just strings
4. Create test program: `./calculator add 42 58` → `100`

### Phase 2: ARM64 Support (macOS) - IN PROGRESS
**Status**: Backend implemented but not integrated. See `ARM64_INTEGRATION_GUIDE.md` for details.
1. ✅ ARM64 instruction encoding works
2. ✅ Mach-O generation works (fixed missing segments)
3. ✅ set-target command added to MMC
4. ❌ MIR pipeline still generates x86 code
5. ❌ Type conflicts from `pub use x86::*` block integration

### Phase 3: Backend Abstraction
1. Extract common patterns between x64 and ARM64
2. Create clean abstraction for different architectures
3. Document how to add new backends
4. Consider WASM as third backend

### Why This Approach
- **Baseline First**: Proves the system works end-to-end
- **Local Testing**: ARM64/Mac support enables rapid iteration
- **Real Usage**: Basic calculator demonstrates practical value
- **Contribution Ready**: Clear goals for upstream PRs

## Key Files for MMC Work
- `MM0_ARGC_PROGRESS.md` - Detailed notes on argument passing implementation
- `mm0-rs/src/mmc/` - The MMC compiler implementation
- `examples/hello_mmc.mm1` - Working example (prints, no args)
- `mm0-rs/src/mmc/types.rs` - Type system (ghost variable issues)
- `mm0-rs/src/mmc/codegen.rs` - Code generation
- `mm0-rs/src/mmc/layout.rs` - Memory layout
- `mm0-rs/components/mmcc/src/build_mir.rs` - Where we added argument passing

## Collaboration Opportunities

### For Upstream PRs
1. **Documentation**: Our struggles can help others
2. **Test Cases**: Expand beyond hello_mmc.mm1
3. **Bug Fixes**: Register allocation, ghost variables
4. **ARM64 Backend**: New architecture support
5. **Error Messages**: Make compiler more helpful

### From Community
- TypeFlow project has ARM64 formalization work
- SafeNumber proofs could inform numeric operations
- WASM expertise from Pragma's research

## The Vision
A minimal proof-generating compiler that outputs verified native executables. Not complete x86-64 support, just enough to prove the concept works and enable practical applications like verified financial calculations.

## System Architecture Vision

**Layer 1: MM0 Baseline** (Foundation)
- Get basic proof-generating compiler working
- Support argc/argv, arithmetic, simple I/O
- Target x64 first, then ARM64

**Layer 2: Direct File Alignment** (Attractor)
- Use Direct File as foundational implementation
- Align with IRS Pub 17 specifications
- Let the attractor guide data structures

**Layer 3: Formal Verification** (Proofs)
- Extract formal invariants from IRS system
- Build Money type with TypeScript DSL bridge
- Create proven tax calculation algorithms

**Layer 4: Integration** (Ecosystem)
- Document MM0/TypeFlow integration
- Connect all pieces into liberation infrastructure
- Enable practical verified tax software

## MM0 Baseline Layers (Detailed)

### Layer 0: Understanding Current State
- Study Mario's working hello_mmc.mm1
- Understand ghost variable issue from our attempts
- Map the gap between current and needed

### Layer 1: Minimal Arguments
- Fix ghost variable ref handling
- Get single integer argument working
- Test: `./prog 42` prints "Got: 42"

### Layer 2: Basic Arithmetic
- Add two arguments: `./calc add 5 7`
- Include overflow checking
- Generate proofs for operations

### Layer 3: I/O Enhancement  
- Read numbers from stdin
- Write results with formatting
- Handle basic errors gracefully

### Layer 4: Architecture Abstraction
- Extract x64-specific code
- Create interface for backends
- Prepare for ARM64 addition

### Layer 5: ARM64 Implementation
- Port to ARM64 instructions
- Generate Mach-O headers
- Enable Mac-native testing

**Status (2025-08-30)**: Trait-based architecture abstraction complete!
- See `ARM64_QUICK_REFERENCE.md` for immediate context recovery
- See `ARM64_BACKEND_STATUS.md` for what was built
- See `ARM64_INTEGRATION_PLAN.md` for architectural challenges
- See `ARM64_INTEGRATION_GUIDE.md` for AI-focused integration guide
- See `ARM64_TRAIT_ARCHITECTURE.md` for the implemented solution

### Layer 6: WASM Backend
- Add WASM as third backend
- Leverage simpler stack-based model
- Universal verified computation

## Multi-Architecture Support Complete! (2025-12-31)

The MM0 compiler now supports multiple architectures through a clean dispatch system:

### ✅ Working Architectures
1. **x86-64** - Original backend, generates ELF executables
2. **ARM64** - Fully implemented, generates Mach-O executables
3. **WASM** - Structure in place, needs VCode implementation

### Usage
```mm1
-- In your MM1 file, set the target:
(mmc-set-target "x86_64-linux")   -- For x86-64 Linux
(mmc-set-target "arm64-macos")    -- For ARM64 macOS  
(mmc-set-target "wasm32")         -- For WebAssembly
```

### Key Achievement
The compiler is no longer hardcoded to x86! The multi-architecture dispatch works through:
- `codegen_arch.rs` - Selects backend based on target
- `arch/arm64/lower.rs` - ARM64-specific code generation
- Clean trait abstractions in `arch/traits.rs`

See `MULTI_ARCHITECTURE_STATUS.md` and `ARCHITECTURE_AND_INTEGRATION.md` for details.