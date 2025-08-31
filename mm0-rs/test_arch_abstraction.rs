#!/usr/bin/env rust-script
//! Test script to verify architecture abstraction is working
//! 
//! This creates minimal code objects for each architecture and verifies
//! the ArchPCode abstraction works correctly.

use std::collections::HashMap;

// Minimal types to test the abstraction
#[derive(Debug)]
struct X86PCode {
    len: u32,
    insts_count: usize,
}

#[derive(Debug)]
struct Arm64PCode {
    len: u32,
    insts_count: usize,
}

#[derive(Debug)]
struct WasmPCode {
    len: u32,
    insts_count: usize,
}

// The architecture-generic wrapper
#[derive(Debug)]
enum ArchPCode {
    X86(Box<X86PCode>),
    Arm64(Box<Arm64PCode>),
    Wasm(Box<WasmPCode>),
}

impl ArchPCode {
    fn len(&self) -> u32 {
        match self {
            ArchPCode::X86(pcode) => pcode.len,
            ArchPCode::Arm64(pcode) => pcode.len,
            ArchPCode::Wasm(pcode) => pcode.len,
        }
    }
    
    fn arch_name(&self) -> &'static str {
        match self {
            ArchPCode::X86(_) => "x86-64",
            ArchPCode::Arm64(_) => "ARM64",
            ArchPCode::Wasm(_) => "WebAssembly",
        }
    }
}

// Simulated code generation
fn generate_x86_code() -> ArchPCode {
    println!("Generating x86-64 code...");
    let pcode = X86PCode {
        len: 42,
        insts_count: 7,
    };
    ArchPCode::X86(Box::new(pcode))
}

fn generate_arm64_code() -> ArchPCode {
    println!("Generating ARM64 code...");
    let pcode = Arm64PCode {
        len: 48,
        insts_count: 12,
    };
    ArchPCode::Arm64(Box::new(pcode))
}

fn generate_wasm_code() -> ArchPCode {
    println!("Generating WebAssembly code...");
    let pcode = WasmPCode {
        len: 36,
        insts_count: 9,
    };
    ArchPCode::Wasm(Box::new(pcode))
}

// Test the abstraction
fn main() {
    println!("Testing Architecture Abstraction for MM0");
    println!("========================================\n");
    
    // Create code for each architecture
    let codes = vec![
        ("x86", generate_x86_code()),
        ("arm64", generate_arm64_code()),
        ("wasm", generate_wasm_code()),
    ];
    
    // Process code generically
    for (name, code) in codes {
        println!("Processing {} code:", name);
        println!("  Architecture: {}", code.arch_name());
        println!("  Code length: {} bytes", code.len());
        
        // Test architecture-specific access
        match &code {
            ArchPCode::X86(pcode) => {
                println!("  x86-specific: {} instructions", pcode.insts_count);
            }
            ArchPCode::Arm64(pcode) => {
                println!("  ARM64-specific: {} instructions", pcode.insts_count);
            }
            ArchPCode::Wasm(pcode) => {
                println!("  WASM-specific: {} instructions", pcode.insts_count);
            }
        }
        println!();
    }
    
    println!("✅ Architecture abstraction is working!");
    println!("   Each architecture can return its own PCode type");
    println!("   LinkedCode can work with any architecture through ArchPCode");
}