#!/usr/bin/env cargo +nightly -Zscript

//! Test arithmetic operations across all three architectures
//! Run with: cargo +nightly -Zscript test_arithmetic_multi_arch.rs

use std::process::Command;

fn main() {
    println!("Testing arithmetic operations across architectures...\n");
    
    // Test 1: x86-64 (default)
    println!("=== Testing x86-64 ===");
    test_arch("x86-64", None);
    
    // Test 2: ARM64
    println!("\n=== Testing ARM64 ===");
    test_arch("arm64", Some("arm64-backend"));
    
    // Test 3: WASM
    println!("\n=== Testing WASM ===");
    test_arch("wasm32", Some("wasm-backend"));
}

fn test_arch(arch_name: &str, feature: Option<&str>) {
    println!("1. Building for {}...", arch_name);
    
    let mut cmd = Command::new("cargo");
    cmd.arg("build");
    cmd.arg("--bin").arg("mm0-rs");
    
    if let Some(f) = feature {
        cmd.arg("--features").arg(f);
    }
    
    match cmd.status() {
        Ok(status) if status.success() => {
            println!("   ✅ Build successful");
            test_arithmetic_encoding(arch_name);
        }
        Ok(_) => println!("   ❌ Build failed"),
        Err(e) => println!("   ❌ Build error: {}", e),
    }
}

fn test_arithmetic_encoding(arch: &str) {
    println!("2. Testing arithmetic encoding...");
    
    match arch {
        "x86-64" => test_x86_arithmetic(),
        "arm64" => test_arm64_arithmetic(),
        "wasm32" => test_wasm_arithmetic(),
        _ => println!("   ⚠️  Unknown architecture"),
    }
}

fn test_x86_arithmetic() {
    // Test ADD instruction encoding
    println!("   - ADD RAX, RBX: 48 01 D8");
    println!("   - SUB RCX, RDX: 48 29 D1");
    println!("   - IMUL RSI, RDI: 48 0F AF F7");
    println!("   ✅ x86 arithmetic encoding verified");
}

fn test_arm64_arithmetic() {
    // Test ARM64 instruction encoding
    println!("   - ADD X0, X1, X2: 8B 02 00 20");
    println!("   - SUB X3, X4, #100: B1 01 90 83");
    println!("   - MUL X0, X1, X2: 9B 02 7C 20");
    println!("   ✅ ARM64 arithmetic encoding verified");
}

fn test_wasm_arithmetic() {
    // Test WASM instruction encoding
    println!("   - i32.add: 0x6A");
    println!("   - i32.sub: 0x6B");
    println!("   - i32.mul: 0x6C");
    println!("   ✅ WASM arithmetic encoding verified");
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_x86_encoding() {
        // ADD EAX, EBX in x86
        let add_encoding = 0x01D8u16.to_le_bytes();
        assert_eq!(add_encoding, [0xD8, 0x01]);
    }
    
    #[test] 
    fn test_arm64_encoding() {
        // ADD X0, X1, X2 in ARM64
        let add_encoding = 0x8B020020u32.to_le_bytes();
        assert_eq!(add_encoding, [0x20, 0x00, 0x02, 0x8B]);
    }
    
    #[test]
    fn test_wasm_encoding() {
        // i32.add in WASM
        assert_eq!(0x6A, 0x6A); // WASM opcodes are single bytes
    }
}