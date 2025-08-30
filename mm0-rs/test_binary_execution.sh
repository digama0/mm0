#!/bin/bash

# Test binary execution for all three architectures
set -e  # Exit on error

echo "=== MM0 Multi-Architecture Binary Execution Test ==="
echo
echo "Testing simple exit(42) program on all architectures..."
echo

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Create test directory
TEST_DIR="test_binaries"
mkdir -p $TEST_DIR

# Function to compile for a specific architecture
compile_for_arch() {
    local arch=$1
    local feature_flag=""
    
    case $arch in
        "x86-64")
            feature_flag=""  # Default
            ;;
        "arm64")
            feature_flag="--features arm64-backend"
            ;;
        "wasm")
            feature_flag="--features wasm-backend"
            ;;
    esac
    
    echo -e "${YELLOW}Compiling for $arch...${NC}"
    
    # Build mmcc with the appropriate backend
    cd components/mmcc
    cargo build --release $feature_flag
    cd ../..
    
    # TODO: Actually invoke mmcc to compile the test program
    # For now, we'll create test binaries manually
}

# Function to create test binary manually (temporary)
create_test_binary() {
    local arch=$1
    local output_file="$TEST_DIR/exit42_$arch"
    
    case $arch in
        "x86-64")
            # Create minimal Linux ELF that exits with 42
            # This is a hand-crafted binary for testing
            python3 -c "
import struct
# ELF header
elf = b'\\x7fELF'  # Magic
elf += b'\\x02\\x01\\x01\\x00'  # 64-bit, little endian, version 1
elf += b'\\x00' * 8  # padding
elf += struct.pack('<H', 2)  # e_type: ET_EXEC
elf += struct.pack('<H', 62)  # e_machine: EM_X86_64
elf += struct.pack('<I', 1)  # e_version
elf += struct.pack('<Q', 0x400078)  # e_entry
elf += struct.pack('<Q', 64)  # e_phoff
elf += struct.pack('<Q', 0)  # e_shoff
elf += struct.pack('<I', 0)  # e_flags
elf += struct.pack('<H', 64)  # e_ehsize
elf += struct.pack('<H', 56)  # e_phentsize
elf += struct.pack('<H', 1)  # e_phnum
elf += struct.pack('<H', 0)  # e_shentsize
elf += struct.pack('<H', 0)  # e_shnum
elf += struct.pack('<H', 0)  # e_shstrndx

# Program header
elf += struct.pack('<I', 1)  # p_type: PT_LOAD
elf += struct.pack('<I', 5)  # p_flags: PF_R | PF_X
elf += struct.pack('<Q', 0)  # p_offset
elf += struct.pack('<Q', 0x400000)  # p_vaddr
elf += struct.pack('<Q', 0x400000)  # p_paddr
elf += struct.pack('<Q', 0x84)  # p_filesz
elf += struct.pack('<Q', 0x84)  # p_memsz
elf += struct.pack('<Q', 0x1000)  # p_align

# Code: mov rax, 60; mov rdi, 42; syscall
elf += b'\\x48\\xc7\\xc0\\x3c\\x00\\x00\\x00'  # mov rax, 60 (sys_exit)
elf += b'\\x48\\xc7\\xc7\\x2a\\x00\\x00\\x00'  # mov rdi, 42
elf += b'\\x0f\\x05'  # syscall

with open('$output_file', 'wb') as f:
    f.write(elf)
" 
            chmod +x "$output_file"
            ;;
            
        "arm64")
            # Use our ARM64 test encoding
            echo "Creating ARM64 Mach-O binary..."
            rustc --edition 2021 -o "$output_file" - << 'EOF'
fn main() {
    std::process::exit(42);
}
EOF
            ;;
            
        "wasm")
            # Create minimal WASM module that returns 42
            python3 -c "
wasm = bytearray()
# WASM magic and version
wasm.extend(b'\\x00asm\\x01\\x00\\x00\\x00')

# Type section (1)
wasm.append(0x01)  # section id
wasm.append(0x05)  # section size
wasm.append(0x01)  # number of types
wasm.extend(b'\\x60\\x00\\x01\\x7f')  # func type: [] -> [i32]

# Function section (3)
wasm.append(0x03)  # section id
wasm.append(0x02)  # section size
wasm.append(0x01)  # number of functions
wasm.append(0x00)  # function 0 uses type 0

# Export section (7)
wasm.append(0x07)  # section id
wasm.append(0x08)  # section size
wasm.append(0x01)  # number of exports
wasm.append(0x04)  # string length
wasm.extend(b'main')  # export name
wasm.append(0x00)  # export kind: function
wasm.append(0x00)  # function index

# Code section (10)
wasm.append(0x0a)  # section id
wasm.append(0x06)  # section size
wasm.append(0x01)  # number of functions
wasm.append(0x04)  # function body size
wasm.append(0x00)  # local declarations count
wasm.append(0x41)  # i32.const
wasm.append(0x2a)  # 42 (LEB128)
wasm.append(0x0b)  # end

with open('${output_file}.wasm', 'wb') as f:
    f.write(wasm)
"
            ;;
    esac
}

# Function to run the test binary
run_test_binary() {
    local arch=$1
    local binary="$TEST_DIR/exit42_$arch"
    
    echo -e "Running $arch binary..."
    
    case $arch in
        "x86-64")
            if command -v container &> /dev/null; then
                # Use Apple container for x86-64 Linux ELF
                echo "Using Apple container for x86-64 Linux binary..."
                # container run --platform linux/amd64 "$binary"
                # For now, skip as it needs more setup
                echo -e "${YELLOW}Skipping x86-64 test (needs container setup)${NC}"
            else
                echo -e "${YELLOW}Apple container not available, skipping x86-64${NC}"
            fi
            ;;
            
        "arm64")
            # Run native ARM64 binary
            if [[ $(uname -m) == "arm64" ]]; then
                "$binary"
                local exit_code=$?
                if [[ $exit_code -eq 42 ]]; then
                    echo -e "${GREEN}✓ ARM64 binary returned 42${NC}"
                else
                    echo -e "${RED}✗ ARM64 binary returned $exit_code (expected 42)${NC}"
                fi
            else
                echo -e "${YELLOW}Not on ARM64, skipping native test${NC}"
            fi
            ;;
            
        "wasm")
            # Try different WASM runtimes
            if command -v wasmer &> /dev/null; then
                echo "Using wasmer..."
                wasmer run "${binary}.wasm" --invoke main
                local exit_code=$?
                if [[ $exit_code -eq 42 ]]; then
                    echo -e "${GREEN}✓ WASM (wasmer) returned 42${NC}"
                else
                    echo -e "${RED}✗ WASM (wasmer) returned $exit_code (expected 42)${NC}"
                fi
            elif command -v wasmtime &> /dev/null; then
                echo "Using wasmtime..."
                # wasmtime doesn't return the WASM return value as exit code
                result=$(wasmtime run "${binary}.wasm" --invoke main)
                echo "WASM returned: $result"
                if [[ "$result" == "42" ]]; then
                    echo -e "${GREEN}✓ WASM (wasmtime) returned 42${NC}"
                else
                    echo -e "${RED}✗ WASM (wasmtime) returned $result (expected 42)${NC}"
                fi
            elif command -v wasmedge &> /dev/null; then
                echo "Using wasmedge..."
                wasmedge "${binary}.wasm" main
            else
                echo -e "${YELLOW}No WASM runtime found (wasmer/wasmtime/wasmedge)${NC}"
            fi
            ;;
    esac
    echo
}

# Main test sequence
echo "1. Creating test binaries..."
for arch in "x86-64" "arm64" "wasm"; do
    create_test_binary "$arch"
done

echo
echo "2. Testing binary execution..."
for arch in "x86-64" "arm64" "wasm"; do
    run_test_binary "$arch"
done

echo "=== Test Summary ==="
echo "This test framework demonstrates how we'll run compiled binaries"
echo "on all three architectures once the MM0 compiler integration is complete."
echo
echo "Next steps:"
echo "1. Hook up mmcc to actually compile MM1 files"
echo "2. Generate proper binary formats for each architecture"
echo "3. Test with more complex programs (calculator, loops, etc.)"