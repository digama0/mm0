#!/bin/bash
# Test script for ARM64 code generation

cd components/mmcc

echo "Testing ARM64 code generation..."

# First, let's try to compile a simple MM0 file for ARM64
cat > test_arm64.mm1 <<'EOF'
-- Simple exit program for ARM64
theorem exit_zero: $ 0 = 0 $ = '(eq 0 0);

do {
  (main) {
    -- Just exit with code 0
    @ 0 exit
  }
};
EOF

# Try to compile it with ARM64 target
echo "Compiling with ARM64 target..."
RUST_BACKTRACE=1 cargo run -- test_arm64.mm1 --target arm64-macos -o test_arm64.out 2>&1 | tee compile_output.txt

echo "Compilation complete. Check compile_output.txt for details."