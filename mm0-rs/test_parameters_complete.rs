#!/usr/bin/env cargo +nightly -Zscript

//! Complete parameter passing and return value test
//! Demonstrates:
//! 1. Function parameters (add function)
//! 2. Return values
//! 3. main(argc, argv) handling

use std::fs;
use std::process::Command;

fn main() -> std::io::Result<()> {
    println!("=== Complete Parameter & Return Value Test ===\n");
    
    // Create test directory
    fs::create_dir_all("test_binaries")?;
    
    test_arm64_complete()?;
    test_x86_complete()?;
    test_wasm_complete()?;
    
    println!("\n=== Key Insights on main(argc, argv) ===");
    println!("1. ARM64: main receives argc in X0, argv in X1");
    println!("2. x86-64: main receives argc in RDI, argv in RSI");  
    println!("3. WASM: main typically doesn't receive args directly (uses WASI)");
    println!("4. Return values: exit code from main becomes process exit status");
    
    Ok(())
}

fn test_arm64_complete() -> std::io::Result<()> {
    println!("1. ARM64 Complete Test");
    println!("   Creating assembly that accesses command line args...\n");
    
    let asm = r#"
.global _main
.align 2

// add function: int add(int a, int b) 
// Parameters: X0 = a, X1 = b
// Return: X0 = a + b
_add:
    add x0, x0, x1
    ret

// main function: int main(int argc, char *argv[])
// Parameters: X0 = argc, X1 = argv
// Return: X0 = exit code
_main:
    // Save frame pointer and link register
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    
    // Save argc for later
    mov x19, x0         // x19 = argc (callee-saved register)
    
    // Test 1: Call add(10, 32)
    mov x0, #10
    mov x1, #32
    bl _add             // Result in x0 = 42
    mov x20, x0         // Save result
    
    // Test 2: Return different values based on argc
    cmp x19, #1         // If argc == 1 (no args)
    b.eq .return_42     // Return 42
    
    cmp x19, #2         // If argc == 2 (one arg)
    b.eq .return_argc   // Return argc (2)
    
    // If argc > 2, return 100 + argc
    mov x0, #100
    add x0, x0, x19
    b .exit
    
.return_42:
    mov x0, x20         // Return add result (42)
    b .exit
    
.return_argc:
    mov x0, x19         // Return argc
    
.exit:
    // Restore and return
    ldp x29, x30, [sp], #16
    ret
"#;
    
    fs::write("test_binaries/param_complete.s", asm)?;
    
    // Compile if on ARM64
    if is_arm64() {
        println!("   Compiling ARM64 assembly...");
        Command::new("as")
            .args(&["-o", "test_binaries/param_complete.o", "test_binaries/param_complete.s"])
            .status()?;
            
        Command::new("ld")
            .args(&["-o", "test_binaries/param_complete_arm64", 
                   "test_binaries/param_complete.o",
                   "-lSystem", "-syslibroot", 
                   "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk",
                   "-e", "_main", "-arch", "arm64"])
            .status()?;
            
        // Test it
        println!("\n   Testing ARM64 binary:");
        
        // Test with no args
        let status = Command::new("./test_binaries/param_complete_arm64").status()?;
        println!("   No args: exit code = {} (expect 42)", status.code().unwrap_or(-1));
        
        // Test with one arg
        let status = Command::new("./test_binaries/param_complete_arm64")
            .arg("hello")
            .status()?;
        println!("   One arg: exit code = {} (expect 2)", status.code().unwrap_or(-1));
        
        // Test with multiple args
        let status = Command::new("./test_binaries/param_complete_arm64")
            .args(&["hello", "world", "test"])
            .status()?;
        println!("   Four args total: exit code = {} (expect 104)", status.code().unwrap_or(-1));
    }
    
    Ok(())
}

fn test_x86_complete() -> std::io::Result<()> {
    println!("\n2. x86-64 Complete Test");
    println!("   Creating assembly that accesses command line args...\n");
    
    let asm = r#"
.global _start
.text

# add function: int add(int a, int b)
# Parameters: RDI = a, RSI = b  
# Return: RAX = a + b
add:
    mov rax, rdi
    add rax, rsi
    ret

# main function logic
# Parameters: RDI = argc, RSI = argv
_start:
    # In Linux _start, we need to get argc/argv from stack
    mov rdi, [rsp]      # argc is at top of stack
    lea rsi, [rsp+8]    # argv starts after argc
    
    # Save argc
    push rdi            # Save argc on stack
    
    # Test 1: Call add(10, 32)
    mov rdi, 10
    mov rsi, 32
    call add            # Result in RAX = 42
    push rax            # Save result
    
    # Get argc back
    mov rdi, [rsp+8]    # Restore argc
    
    # Test 2: Return based on argc
    cmp rdi, 1
    je .return_42
    
    cmp rdi, 2
    je .return_argc
    
    # argc > 2: return 100 + argc
    mov rax, 100
    add rax, rdi
    jmp .exit
    
.return_42:
    pop rax             # Get saved add result
    jmp .exit2
    
.return_argc:
    mov rax, rdi        # Return argc
    
.exit2:
    add rsp, 8          # Clean up stack
.exit:
    # Exit syscall
    mov rdi, rax        # Exit code
    mov rax, 60         # sys_exit
    syscall
"#;
    
    fs::write("test_binaries/param_complete_x86.s", asm)?;
    println!("   Assembly saved to test_binaries/param_complete_x86.s");
    
    Ok(())
}

fn test_wasm_complete() -> std::io::Result<()> {
    println!("\n3. WebAssembly Complete Test");
    println!("   Creating WASM module with proper parameter passing...\n");
    
    let mut wasm = Vec::new();
    
    // WASM header
    wasm.extend(&[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]);
    
    // Type section - FIXED byte count
    wasm.push(0x01); // section id
    wasm.push(0x0b); // section length (11 bytes, was incorrectly 0x0d)
    wasm.push(0x02); // number of types
    
    // Type 0: add function (param i32 i32) (result i32)
    wasm.extend(&[0x60, 0x02, 0x7f, 0x7f, 0x01, 0x7f]); // 6 bytes
    
    // Type 1: main function () (result i32)
    wasm.extend(&[0x60, 0x00, 0x01, 0x7f]); // 4 bytes
    
    // Total: 1 + 6 + 4 = 11 bytes ✓
    
    // Function section
    wasm.push(0x03); // section id
    wasm.push(0x03); // section length
    wasm.push(0x02); // number of functions
    wasm.push(0x00); // func 0 uses type 0 (add)
    wasm.push(0x01); // func 1 uses type 1 (main)
    
    // Export section
    wasm.push(0x07); // section id
    wasm.push(0x11); // section length (17 bytes)
    wasm.push(0x02); // number of exports
    
    // Export "add"
    wasm.push(0x03); // string length
    wasm.extend(b"add");
    wasm.push(0x00); // function export
    wasm.push(0x00); // function index 0
    
    // Export "main"  
    wasm.push(0x04); // string length
    wasm.extend(b"main");
    wasm.push(0x00); // function export
    wasm.push(0x01); // function index 1
    
    // Code section
    wasm.push(0x0a); // section id
    wasm.push(0x11); // section length (17 bytes)
    wasm.push(0x02); // number of functions
    
    // Function 0 (add): receives two params, returns sum
    wasm.push(0x07); // function body size (7 bytes)
    wasm.push(0x00); // no locals
    wasm.push(0x20); wasm.push(0x00); // local.get 0 (first param)
    wasm.push(0x20); wasm.push(0x01); // local.get 1 (second param)
    wasm.push(0x6a); // i32.add
    wasm.push(0x0b); // end
    
    // Function 1 (main): calls add(10, 32)
    wasm.push(0x08); // function body size (8 bytes)
    wasm.push(0x00); // no locals
    wasm.push(0x41); wasm.push(0x0a); // i32.const 10
    wasm.push(0x41); wasm.push(0x20); // i32.const 32  
    wasm.push(0x10); wasm.push(0x00); // call 0 (add function)
    wasm.push(0x0b); // end
    
    fs::write("test_binaries/param_complete.wasm", &wasm)?;
    println!("   Generated: test_binaries/param_complete.wasm");
    
    // Test with wasmer if available
    println!("\n   Testing WASM module:");
    
    // Test add function
    match Command::new("wasmer")
        .args(&["run", "test_binaries/param_complete.wasm", "--invoke", "add", "10", "32"])
        .output()
    {
        Ok(output) => {
            let result = String::from_utf8_lossy(&output.stdout).trim().to_string();
            println!("   add(10, 32) = {} {}", result,
                if result == "42" { "✅" } else { "❌" });
        }
        Err(_) => println!("   Wasmer not available for testing"),
    }
    
    // Test main function
    match Command::new("wasmer")
        .args(&["run", "test_binaries/param_complete.wasm", "--invoke", "main"])
        .output()
    {
        Ok(output) => {
            let result = String::from_utf8_lossy(&output.stdout).trim().to_string();
            println!("   main() = {} {}", result,
                if result == "42" { "✅" } else { "❌" });
            
            // Note about WASM and command line args
            println!("\n   Note: WASM modules don't receive argc/argv directly.");
            println!("   They use WASI imports like args_get() and args_sizes_get()");
            println!("   to access command line arguments when needed.");
        }
        Err(_) => {},
    }
    
    Ok(())
}

fn is_arm64() -> bool {
    Command::new("uname")
        .arg("-m")
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim() == "arm64")
        .unwrap_or(false)
}

// Additional demonstration of calling conventions
fn explain_calling_conventions() {
    println!("\n=== Calling Convention Details ===\n");
    
    println!("ARM64 (AAPCS64):");
    println!("  Parameters: X0-X7 (8 registers)");
    println!("  Return: X0 (X1 for 128-bit)");
    println!("  Stack params: 8-byte aligned, right-to-left");
    println!("  Preserved: X19-X29, SP");
    println!("  main(argc, argv): X0=argc, X1=argv");
    
    println!("\nx86-64 (System V ABI):");
    println!("  Parameters: RDI, RSI, RDX, RCX, R8, R9 (6 registers)");
    println!("  Return: RAX (RDX:RAX for 128-bit)");
    println!("  Stack params: 8-byte aligned, right-to-left");
    println!("  Preserved: RBX, RBP, R12-R15");
    println!("  main(argc, argv): RDI=argc, RSI=argv");
    
    println!("\nWebAssembly:");
    println!("  Parameters: Part of function signature");
    println!("  Passed implicitly on operand stack");
    println!("  Return: Also part of signature");
    println!("  No direct argc/argv - uses WASI for args");
}