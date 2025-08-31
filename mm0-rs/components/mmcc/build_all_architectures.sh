#!/bin/bash
# Build MM0 compiler for all supported architectures

set -e  # Exit on error

echo "Building MM0 compiler for all architectures..."

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# Create output directory
mkdir -p target/multi-arch

# Build x86-64 (default)
echo -e "${BLUE}Building x86-64 version...${NC}"
cargo build --release
cp target/release/mmcc target/multi-arch/mmcc-x86_64
echo -e "${GREEN}✓ x86-64 build complete${NC}"

# Build ARM64
echo -e "${BLUE}Building ARM64 version...${NC}"
cargo build --release --features arm64-backend --no-default-features
cp target/release/mmcc target/multi-arch/mmcc-arm64
echo -e "${GREEN}✓ ARM64 build complete${NC}"

# Build WASM
echo -e "${BLUE}Building WASM version...${NC}"
cargo build --release --features wasm-backend --no-default-features
cp target/release/mmcc target/multi-arch/mmcc-wasm
echo -e "${GREEN}✓ WASM build complete${NC}"

# Summary
echo -e "\n${GREEN}All builds complete!${NC}"
echo "Executables are in target/multi-arch/"
ls -la target/multi-arch/

# Create a wrapper script that selects the right executable
cat > target/multi-arch/mmcc << 'EOF'
#!/bin/bash
# MM0 compiler wrapper - selects appropriate architecture

ARCH=$(uname -m)
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

case "$ARCH" in
    x86_64)
        exec "$SCRIPT_DIR/mmcc-x86_64" "$@"
        ;;
    arm64|aarch64)
        exec "$SCRIPT_DIR/mmcc-arm64" "$@"
        ;;
    *)
        echo "Warning: Unknown architecture $ARCH, using x86_64"
        exec "$SCRIPT_DIR/mmcc-x86_64" "$@"
        ;;
esac
EOF

chmod +x target/multi-arch/mmcc
echo -e "\n${GREEN}Created wrapper script 'mmcc' that auto-selects architecture${NC}"