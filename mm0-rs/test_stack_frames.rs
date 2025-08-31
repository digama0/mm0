#!/usr/bin/env cargo +nightly -Zscript

//! Test proper stack frame management
//! Demonstrates function prologues, epilogues, and local variable storage

use std::fs;
use std::process::Command;

fn main() -> std::io::Result<()> {
    println!("=== Stack Frame Management Test ===\n");
    
    fs::create_dir_all("test_binaries")?;
    
    test_arm64_frames()?;
    test_x86_frames()?;
    test_wasm_frames()?;
    
    println!("\n=== Key Concepts ===");
    explain_stack_frames();
    
    Ok(())
}

fn test_arm64_frames() -> std::io::Result<()> {
    println!("1. ARM64 Stack Frames\n");
    
    // Test 1: Leaf function (no calls)
    let leaf_asm = r#"
.global _leaf_function
.align 2

// Leaf function: no need to save LR
_leaf_function:
    // Simple computation
    add x0, x0, x1
    ret

.global _main
"#;
    
    // Test 2: Non-leaf function with locals
    let non_leaf_asm = r#"
.global _non_leaf
.align 2

// Function that calls another and uses locals
_non_leaf:
    // Prologue: save FP, LR and allocate space
    stp x29, x30, [sp, #-32]!   // Save FP, LR and allocate 32 bytes
    mov x29, sp                  // Set up frame pointer
    
    // Save callee-saved register we'll use
    str x19, [sp, #16]
    
    // Use local variable space
    mov x19, x0                  // Save argument
    str x19, [x29, #24]         // Store in local
    
    // Call another function
    bl _leaf_function
    
    // Restore and use local
    ldr x1, [x29, #24]
    add x0, x0, x1
    
    // Epilogue: restore registers and return
    ldr x19, [sp, #16]          // Restore x19
    ldp x29, x30, [sp], #32     // Restore FP, LR and deallocate
    ret
"#;
    
    // Test 3: Function with many locals
    let complex_frame_asm = r#"
.global _complex_frame
.global _main
.align 2

_complex_frame:
    // Prologue for function with many locals
    stp x29, x30, [sp, #-80]!   // 80 bytes total
    mov x29, sp
    
    // Save multiple callee-saved registers
    stp x19, x20, [sp, #16]
    stp x21, x22, [sp, #32]
    
    // Initialize locals
    mov x19, #10
    str x19, [x29, #48]         // local1 = 10
    mov x20, #20
    str x20, [x29, #56]         // local2 = 20
    mov x21, #30
    str x21, [x29, #64]         // local3 = 30
    
    // Sum locals
    ldr x0, [x29, #48]
    ldr x1, [x29, #56]
    add x0, x0, x1
    ldr x1, [x29, #64]
    add x0, x0, x1              // result = 60
    
    // Epilogue
    ldp x21, x22, [sp, #32]
    ldp x19, x20, [sp, #16]
    ldp x29, x30, [sp], #80
    ret

_main:
    // Simple main that calls complex_frame
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    
    bl _complex_frame
    
    ldp x29, x30, [sp], #16
    ret
"#;
    
    fs::write("test_binaries/stack_frame_test.s", complex_frame_asm)?;
    
    if is_arm64() {
        Command::new("as")
            .args(&["-o", "test_binaries/stack_frame_test.o", 
                   "test_binaries/stack_frame_test.s"])
            .status()?;
            
        Command::new("ld")
            .args(&["-o", "test_binaries/stack_frame_test", 
                   "test_binaries/stack_frame_test.o",
                   "-lSystem", "-syslibroot",
                   "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk",
                   "-e", "_main", "-arch", "arm64"])
            .status()?;
            
        println!("   Testing ARM64 stack frames:");
        match Command::new("./test_binaries/stack_frame_test").status() {
            Ok(status) => {
                println!("   Complex frame test: exit code = {} (expect 60)", 
                    status.code().unwrap_or(-1));
            }
            Err(e) => println!("   Failed: {}", e),
        }
    }
    
    println!("\n   ARM64 Frame Layout:");
    println!("   +------------------+ <- Old SP");
    println!("   | Caller's data    |");
    println!("   +------------------+");
    println!("   | X30 (LR)         | <- SP after STP");
    println!("   | X29 (FP)         |");
    println!("   +------------------+ <- FP points here");
    println!("   | Saved registers  |");
    println!("   | (X19-X28)       |");
    println!("   +------------------+");
    println!("   | Local variables  |");
    println!("   +------------------+");
    println!("   | Spill slots      |");
    println!("   +------------------+ <- SP");
    
    Ok(())
}

fn test_x86_frames() -> std::io::Result<()> {
    println!("\n2. x86-64 Stack Frames\n");
    
    let x86_asm = r#"
.global _start
.text

# Non-leaf function with proper frame
non_leaf:
    # Prologue
    push rbp                # Save old frame pointer
    mov rbp, rsp           # Set up new frame pointer
    sub rsp, 32            # Allocate locals
    
    # Save callee-saved registers
    push rbx
    push r12
    
    # Use locals
    mov dword [rbp-4], 10  # local1 = 10
    mov dword [rbp-8], 20  # local2 = 20
    
    # Call leaf function
    mov rdi, [rbp-4]
    call leaf_add
    
    # Epilogue
    pop r12
    pop rbx
    mov rsp, rbp           # Restore stack pointer
    pop rbp                # Restore frame pointer
    ret

leaf_add:
    # Simple leaf - no frame needed
    lea rax, [rdi + rsi]
    ret

_start:
    # Set up initial frame
    mov rbp, rsp
    
    # Call non-leaf
    call non_leaf
    
    # Exit
    mov rdi, 60            # Exit code
    mov rax, 60            # sys_exit
    syscall
"#;
    
    fs::write("test_binaries/stack_frame_x86.s", x86_asm)?;
    
    println!("   x86-64 Frame Layout:");
    println!("   +------------------+ <- Old RSP");
    println!("   | Return address   |");
    println!("   +------------------+");
    println!("   | Old RBP          | <- RSP after push rbp");
    println!("   +------------------+ <- RBP points here");
    println!("   | Local variables  |");
    println!("   | ...              |");
    println!("   +------------------+");
    println!("   | Saved registers  |");
    println!("   | (RBX,R12-R15)   |");
    println!("   +------------------+ <- RSP");
    
    Ok(())
}

fn test_wasm_frames() -> std::io::Result<()> {
    println!("\n3. WebAssembly Frames\n");
    
    println!("   WASM uses a different model:");
    println!("   - No explicit frame pointer");
    println!("   - Locals are part of function signature");
    println!("   - Stack is implicit (operand stack)");
    println!("   - No register saving needed");
    
    println!("\n   Example WASM function with locals:");
    println!("   (func $add_locals (param $a i32) (param $b i32) (result i32)");
    println!("     (local $sum i32)");
    println!("     local.get $a");
    println!("     local.get $b");
    println!("     i32.add");
    println!("     local.set $sum");
    println!("     local.get $sum)");
    
    Ok(())
}

fn explain_stack_frames() {
    println!("\n1. **Purpose of Stack Frames**:");
    println!("   - Save return address");
    println!("   - Preserve caller's registers");
    println!("   - Allocate space for locals");
    println!("   - Enable stack unwinding/debugging");
    
    println!("\n2. **Prologue Tasks**:");
    println!("   - Save frame pointer and link register");
    println!("   - Set up new frame pointer");
    println!("   - Allocate stack space");
    println!("   - Save callee-saved registers");
    
    println!("\n3. **Epilogue Tasks**:");
    println!("   - Restore callee-saved registers");
    println!("   - Deallocate stack space");
    println!("   - Restore frame pointer");
    println!("   - Return to caller");
    
    println!("\n4. **Optimization Opportunities**:");
    println!("   - Leaf functions may skip frame setup");
    println!("   - Combine register saves with STP/LDP");
    println!("   - Red zone usage (platform-specific)");
    println!("   - Shrink-wrapping (partial frames)");
}

fn is_arm64() -> bool {
    Command::new("uname")
        .arg("-m")
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim() == "arm64")
        .unwrap_or(false)
}