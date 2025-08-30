#!/bin/bash

# Demonstration of arithmetic operations across all three architectures

echo "=== MM0 Compiler Multi-Architecture Arithmetic Demo ==="
echo

# Function to show arithmetic encoding for each architecture
show_arithmetic() {
    local arch=$1
    echo "--- $arch Arithmetic Operations ---"
    
    case $arch in
        "x86-64")
            echo "ADD instruction: ADD RAX, RBX"
            echo "  Encoding: 48 01 D8"
            echo "  Operation: RAX = RAX + RBX"
            echo
            echo "SUB instruction: SUB RCX, 100" 
            echo "  Encoding: 48 83 E9 64"
            echo "  Operation: RCX = RCX - 100"
            echo
            echo "IMUL instruction: IMUL RSI, RDI"
            echo "  Encoding: 48 0F AF F7"
            echo "  Operation: RSI = RSI * RDI"
            ;;
            
        "ARM64")
            echo "ADD instruction: ADD X0, X1, X2"
            echo "  Encoding: 8B 02 00 20"
            echo "  Operation: X0 = X1 + X2"
            echo
            echo "SUB instruction: SUB X3, X4, #100"
            echo "  Encoding: D1 01 90 83"
            echo "  Operation: X3 = X4 - 100"
            echo
            echo "MUL instruction: MUL X0, X1, X2"
            echo "  Encoding: 9B 02 7C 20"
            echo "  Operation: X0 = X1 * X2"
            ;;
            
        "WASM")
            echo "ADD sequence:"
            echo "  local.get 0    ; Push first operand"
            echo "  local.get 1    ; Push second operand"
            echo "  i32.add        ; Pop both, push sum"
            echo "  Encoding: 20 00 20 01 6A"
            echo
            echo "SUB sequence:"
            echo "  local.get 0    ; Push minuend"
            echo "  local.get 1    ; Push subtrahend"
            echo "  i32.sub        ; Pop both, push difference"
            echo "  Encoding: 20 00 20 01 6B"
            echo
            echo "MUL sequence:"
            echo "  local.get 0    ; Push first operand"
            echo "  local.get 1    ; Push second operand"
            echo "  i32.mul        ; Pop both, push product"
            echo "  Encoding: 20 00 20 01 6C"
            ;;
    esac
    echo
}

# Show arithmetic for all architectures
show_arithmetic "x86-64"
show_arithmetic "ARM64"
show_arithmetic "WASM"

# Show calculator example
echo "=== Calculator Example: (10 + 5) * 3 - 2 = 43 ==="
echo

echo "x86-64 Implementation:"
echo "  MOV RAX, 10     ; Load 10"
echo "  ADD RAX, 5      ; Add 5 (result: 15)"
echo "  MOV RBX, 3      ; Load 3"
echo "  IMUL RAX, RBX   ; Multiply (result: 45)"
echo "  SUB RAX, 2      ; Subtract 2 (result: 43)"
echo

echo "ARM64 Implementation:"
echo "  MOV X0, #10     ; Load 10"
echo "  ADD X0, X0, #5  ; Add 5 (result: 15)"
echo "  MOV X1, #3      ; Load 3"
echo "  MUL X0, X0, X1  ; Multiply (result: 45)"
echo "  SUB X0, X0, #2  ; Subtract 2 (result: 43)"
echo

echo "WASM Implementation:"
echo "  i32.const 10    ; Push 10"
echo "  i32.const 5     ; Push 5"
echo "  i32.add         ; Add (result: 15)"
echo "  i32.const 3     ; Push 3"
echo "  i32.mul         ; Multiply (result: 45)"
echo "  i32.const 2     ; Push 2"
echo "  i32.sub         ; Subtract (result: 43)"
echo

echo "=== Architecture Comparison Summary ==="
echo
echo "Instruction Format:"
echo "  x86-64: Variable length (1-15 bytes)"
echo "  ARM64:  Fixed 32-bit instructions"
echo "  WASM:   Variable length bytecode"
echo
echo "Operand Model:"
echo "  x86-64: Two-operand (dst = dst op src)"
echo "  ARM64:  Three-operand (dst = src1 op src2)"
echo "  WASM:   Stack-based (no explicit operands)"
echo
echo "The MM0 compiler abstracts these differences through:"
echo "- Architecture traits for common interface"
echo "- Feature flags for compile-time selection"
echo "- Architecture-specific code generation"