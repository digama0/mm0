#!/bin/bash

echo "Testing x86 compilation..."
cargo build --release 2>&1 | grep -c "error\[E"

echo "Testing minimal MMC program..."
cat > test_minimal.mmc << 'EOF'
proc main() {
    return 0;
}
EOF

echo "Attempting to compile with mmcc..."
if [ -f target/release/mmcc ]; then
    target/release/mmcc test_minimal.mmc -o test_minimal
    echo "Exit code: $?"
else
    echo "mmcc binary not found"
fi