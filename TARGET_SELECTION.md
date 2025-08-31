# Target Selection in MM0 Compiler

## Current Approach

Target architecture is specified within MM1 files using the `mmc-set-target` command:

```mm1
(mmc-set-target "arm64-macos")   -- ARM64 macOS
(mmc-set-target "x86_64-linux")  -- x86-64 Linux (default)
(mmc-set-target "wasm32")        -- WebAssembly
```

## Examples

### ARM64 Binary
```mm1
import "compiler.mm1";

do {
  (mmc-set-target "arm64-macos")
  
  (mmc-add '(
    (proc (main)
      {{msg : (array u8 14)} := (list . ,(string->list "Hello, ARM64!\n"))}
      {_ := (sys_write 1 14 msg (& msg))}
      )
  ))
  
  (mmc-finish 'test_arm64)
};

output string: $ test_arm64 $;
```

### Multi-Architecture Build Script
If you need to build for multiple targets, create separate MM1 files:

```bash
# Build for ARM64
mm0-rs compile hello_arm64.mm1 -o hello_arm64

# Build for x86-64  
mm0-rs compile hello_x86.mm1 -o hello_x86

# Build for WASM
mm0-rs compile hello_wasm.mm1 -o hello.wasm
```

## Future Enhancement: Command-Line Flag

A `--target` flag would be more convenient:
```bash
mm0-rs compile hello.mm1 --target arm64-macos -o hello_arm64
```

This would require:
1. Adding `--target` to the CLI args
2. Passing target through elaboration context
3. Having CLI override take precedence over `mmc-set-target`

The infrastructure for this is partially implemented in:
- `components/mmcc/src/target_override.rs` - Target override mechanism
- `src/compiler.rs` - CLI args structure

## Supported Targets

- `x86_64-linux` - x86-64 Linux (ELF) - Default
- `x86_64-macos` - x86-64 macOS (Mach-O)
- `arm64-linux` - ARM64 Linux (ELF)
- `arm64-macos` - ARM64 macOS (Mach-O) - Tested on Apple Silicon
- `wasm32` - WebAssembly 32-bit
- `wasm64` - WebAssembly 64-bit

## SIMD Support

For SIMD 128-bit intrinsics across architectures:
- x86-64: SSE/AVX instructions
- ARM64: NEON instructions  
- WASM: SIMD128 proposal

These would be exposed through a unified API in MM1.