#!/bin/bash

# Test script for calculator compilation with multi-architecture support

set -e  # Exit on error

echo "=== MM0 Calculator Demo Compilation Test ==="
echo

# Function to test compilation with a specific backend
test_backend() {
    local backend=$1
    local features=""
    local binary_suffix=""
    
    case $backend in
        "x86-64")
            features=""  # Default
            binary_suffix="x64"
            ;;
        "arm64")
            features="--features arm64-backend"
            binary_suffix="arm64"
            ;;
        "wasm")
            features="--features wasm-backend"
            binary_suffix="wasm"
            ;;
    esac
    
    echo "Testing $backend backend..."
    
    # Build mm0-rs with the appropriate backend
    echo "  Building mm0-rs with $backend support..."
    cargo build --release $features
    
    # Try to compile the calculator example
    echo "  Compiling calculator example..."
    if target/release/mm0-rs compile examples/calc_simple.mm1 calc_$binary_suffix.mmb; then
        echo "  ✓ Compilation successful"
        
        # Check if binary was generated
        if [ -f "calc_$binary_suffix" ]; then
            echo "  ✓ Binary generated: calc_$binary_suffix"
            
            # Try to run it (only for native architectures)
            if [ "$backend" = "arm64" ] && [ "$(uname -m)" = "arm64" ]; then
                echo "  Running binary..."
                ./calc_$binary_suffix || echo "  Exit code: $?"
            fi
        else
            echo "  ⚠ Binary not found (may need output extraction)"
        fi
    else
        echo "  ✗ Compilation failed"
    fi
    
    echo
}

# Test each backend
# Note: Only one backend can be active at a time due to architecture coupling
echo "Note: Testing one backend at a time due to compile-time architecture selection"
echo

# Uncomment the backend you want to test:
# test_backend "x86-64"
test_backend "arm64"
# test_backend "wasm"

echo "=== Manual Testing Instructions ==="
echo
echo "To test a specific backend:"
echo "1. Build: cargo build --release [--features <backend>]"
echo "2. Compile: target/release/mm0-rs compile examples/calc_simple.mm1"
echo "3. Extract binary from output (implementation needed)"
echo
echo "Current limitation: Binary extraction from .mmb files not yet implemented"