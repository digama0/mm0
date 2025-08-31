# Multi-Architecture Support in MM0 Compiler

The MM0 compiler (mmcc) now supports multiple target architectures:
- **x86-64** (default)
- **ARM64/AArch64** 
- **WebAssembly (WASM)**

## Building for Different Architectures

### Single Architecture Builds

```bash
# x86-64 (default)
cargo build --release

# ARM64
cargo build --release --features arm64-backend --no-default-features

# WebAssembly
cargo build --release --features wasm-backend --no-default-features
```

### Building All Architectures

Use the provided build script:

```bash
./build_all_architectures.sh
```

This creates architecture-specific executables in `target/multi-arch/`:
- `mmcc-x86_64` - x86-64 compiler
- `mmcc-arm64` - ARM64 compiler  
- `mmcc-wasm` - WebAssembly compiler
- `mmcc` - Wrapper script that auto-selects based on your CPU

## Architecture Features

### x86-64
- Full instruction set support
- System V ABI calling convention
- ELF executable generation
- Comprehensive instruction selection
- Mature and well-tested

### ARM64
- ARMv8-A instruction set
- AAPCS64 calling convention
- Mach-O executable generation (macOS)
- Basic instruction selection
- Under active development

### WebAssembly
- Stack-based virtual machine
- No register allocation needed
- WASM module generation
- SIMD support (relaxed SIMD)
- Experimental status

## Development Status

| Architecture | Code Generation | Register Allocation | Binary Output | Testing |
|--------------|----------------|-------------------|---------------|---------|
| x86-64       | ✅ Complete    | ✅ Complete       | ✅ ELF        | ✅ Full |
| ARM64        | ✅ Basic       | 🚧 In Progress    | 🚧 Mach-O     | 🚧 Basic|
| WASM         | 🚧 Basic       | ✅ N/A            | 📋 Planned    | 📋 Planned|

## Testing

Run architecture-specific tests:

```bash
# Test x86-64
cargo test

# Test ARM64
cargo test --features arm64-backend --no-default-features

# Test WASM
cargo test --features wasm-backend --no-default-features
```

## Known Limitations

1. **Type System**: Cannot build multiple architectures in the same binary due to type system constraints. Each architecture must be built separately.

2. **Cross-compilation**: Currently, the compiler generates code for its own architecture. Cross-compilation support is planned.

3. **Feature Completeness**: ARM64 and WASM backends are less mature than x86-64.

## Adding a New Architecture

To add support for a new architecture:

1. Create a new module in `src/arch/your_arch/`
2. Implement the required traits:
   - `Architecture` - Basic architecture properties
   - `Inst` - Instruction representation
   - `PhysicalReg` - Register types
3. Add lowering from MIR to your instruction set
4. Implement register allocation (if needed)
5. Add binary output generation

See the ARM64 implementation for a complete example.

## Future Improvements

- Cross-compilation support
- Unified type system for multi-arch builds
- More complete ARM64 instruction selection
- WASM binary writer
- RISC-V support
- Optimization passes per architecture