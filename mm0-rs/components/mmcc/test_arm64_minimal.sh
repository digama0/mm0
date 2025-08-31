#!/bin/bash
echo "Testing minimal ARM64 build..."

# Try to build just the ARM64 binary
echo "Building mmcc with ARM64 backend..."
cargo build --bin mmcc --no-default-features --features arm64-backend 2>&1 | tail -20

# Check if binary was created
if [ -f target/debug/mmcc ]; then
    echo "Binary created successfully!"
    
    # Try to compile hello world
    echo "Attempting to compile hello.mmc..."
    target/debug/mmcc examples/hello.mmc -o hello_arm64 --target arm64-macos
else
    echo "Failed to create mmcc binary"
fi