#!/usr/bin/env cargo +nightly -Zscript

//! Test memory load/store operations across architectures
//! Essential for accessing arrays like argv and building real programs

use std::fs;
use std::process::Command;

fn main() -> std::io::Result<()> {
    println!("=== Memory Operations Test ===");
    println!("Testing load/store for arrays and pointer access\n");
    
    fs::create_dir_all("test_binaries")?;
    
    test_arm64_memory()?;
    test_x86_memory()?;
    test_wasm_memory()?;
    
    println!("\n=== Memory Operation Patterns ===");
    explain_memory_patterns();
    
    Ok(())
}

fn test_arm64_memory() -> std::io::Result<()> {
    println!("1. ARM64 Memory Operations");
    
    // Test accessing argv array
    let asm = r#"
.global _main
.align 2

_main:
    // Save frame
    stp x29, x30, [sp, #-32]!
    mov x29, sp
    
    // Test 1: Store and load
    mov x0, #42
    str x0, [sp, #16]      // Store 42 at sp+16
    mov x0, #0             // Clear x0
    ldr x0, [sp, #16]      // Load back from sp+16
    // x0 should be 42 again
    
    // Test 2: Array access (simulating argv)
    // X1 contains argv on entry
    cmp x1, #0             // Check if argv is NULL
    b.eq .no_args
    
    // Load argv[0] (program name)
    ldr x2, [x1]           // x2 = argv[0]
    
    // Load argv[1] if argc > 1
    mov x3, x0             // Save argc
    cmp x3, #1
    b.le .done
    
    ldr x2, [x1, #8]       // x2 = argv[1]
    
    // Test 3: Byte operations
    mov x4, #0x4142        // 'AB'
    strh w4, [sp, #24]     // Store halfword
    ldrb w5, [sp, #24]     // Load byte (should be 0x42 = 'B')
    
    // Return loaded byte value
    mov x0, x5
    b .exit
    
.no_args:
    mov x0, #255           // Error code for no args
    
.done:
    mov x0, #42            // Default return
    
.exit:
    ldp x29, x30, [sp], #32
    ret
"#;
    
    fs::write("test_binaries/memory_test.s", asm)?;
    
    if is_arm64() {
        println!("   Compiling ARM64 memory test...");
        Command::new("as")
            .args(&["-o", "test_binaries/memory_test.o", "test_binaries/memory_test.s"])
            .status()?;
            
        Command::new("ld")
            .args(&["-o", "test_binaries/memory_test_arm64", 
                   "test_binaries/memory_test.o",
                   "-lSystem", "-syslibroot",
                   "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk",
                   "-e", "_main", "-arch", "arm64"])
            .status()?;
            
        // Test execution
        println!("\n   Testing ARM64 binary:");
        let status = Command::new("./test_binaries/memory_test_arm64").status()?;
        println!("   Basic load/store test: exit code = {} (expect 66 = 'B')", 
            status.code().unwrap_or(-1));
    }
    
    // Show key ARM64 memory instructions
    println!("\n   ARM64 Memory Instructions:");
    println!("   LDR  Xd, [Xn, #imm]    - Load 64-bit");
    println!("   STR  Xs, [Xn, #imm]    - Store 64-bit");
    println!("   LDRB Wd, [Xn, #imm]    - Load byte (zero-extend)");
    println!("   STRB Ws, [Xn, #imm]    - Store byte");
    println!("   LDRH Wd, [Xn, #imm]    - Load halfword");
    println!("   STRH Ws, [Xn, #imm]    - Store halfword");
    println!("   LDP  X1, X2, [Xn, #imm] - Load pair");
    println!("   STP  X1, X2, [Xn, #imm] - Store pair");
    
    Ok(())
}

fn test_x86_memory() -> std::io::Result<()> {
    println!("\n2. x86-64 Memory Operations");
    
    let asm = r#"
.global _start
.text

_start:
    # Get argc/argv from stack
    mov rdi, [rsp]         # argc
    lea rsi, [rsp+8]       # argv
    
    # Test 1: Basic store/load
    mov rax, 42
    push rax               # Store on stack
    mov rax, 0             # Clear
    pop rax                # Load back
    
    # Test 2: Array access
    cmp rsi, 0
    je .no_args
    
    mov rdx, [rsi]         # argv[0]
    
    cmp rdi, 1
    jle .done
    
    mov rdx, [rsi+8]       # argv[1]
    
    # Test 3: Byte operations
    mov eax, 0x4142        # 'AB'
    mov [rsp-8], ax        # Store word
    movzx eax, byte [rsp-8] # Load byte zero-extended
    
    jmp .exit
    
.no_args:
    mov rax, 255
    
.done:
    mov rax, 42
    
.exit:
    mov rdi, rax
    mov rax, 60            # sys_exit
    syscall
"#;
    
    fs::write("test_binaries/memory_test_x86.s", asm)?;
    
    println!("\n   x86-64 Memory Instructions:");
    println!("   MOV  rax, [rbx+rcx*8+16] - Flexible addressing");
    println!("   MOV  [rdi], rsi          - Store 64-bit");
    println!("   MOVZX eax, byte [rsi]    - Load byte, zero-extend");
    println!("   MOVSX rax, dword [rsi]   - Load dword, sign-extend");
    println!("   LEA  rax, [rbx+8]        - Load effective address");
    println!("   PUSH/POP                 - Stack operations");
    
    Ok(())
}

fn test_wasm_memory() -> std::io::Result<()> {
    println!("\n3. WebAssembly Memory Operations");
    
    let mut wasm = Vec::new();
    
    // WASM header
    wasm.extend(&[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]);
    
    // Type section
    wasm.push(0x01); // section id
    wasm.push(0x05); // section length
    wasm.push(0x01); // number of types
    // Type 0: () -> i32
    wasm.extend(&[0x60, 0x00, 0x01, 0x7f]);
    
    // Import section (memory)
    wasm.push(0x02); // section id
    wasm.push(0x0b); // section length
    wasm.push(0x01); // number of imports
    // Import memory
    wasm.push(0x03); wasm.extend(b"env"); // module "env"
    wasm.push(0x06); wasm.extend(b"memory"); // field "memory"
    wasm.push(0x02); // memory import
    wasm.push(0x00); // no flags
    wasm.push(0x01); // min 1 page (64KB)
    
    // Function section
    wasm.push(0x03); // section id
    wasm.push(0x02); // section length
    wasm.push(0x01); // number of functions
    wasm.push(0x00); // func 0 uses type 0
    
    // Export section
    wasm.push(0x07); // section id
    wasm.push(0x08); // section length
    wasm.push(0x01); // number of exports
    wasm.push(0x04); wasm.extend(b"main");
    wasm.push(0x00); // function export
    wasm.push(0x00); // function index 0
    
    // Code section
    wasm.push(0x0a); // section id
    wasm.push(0x1a); // section length (26 bytes)
    wasm.push(0x01); // number of functions
    
    // Function 0: memory test
    wasm.push(0x18); // function body size (24 bytes)
    wasm.push(0x01); // 1 local
    wasm.push(0x01); wasm.push(0x7f); // local i32
    
    // Store 42 at address 0
    wasm.push(0x41); wasm.push(0x00); // i32.const 0 (address)
    wasm.push(0x41); wasm.push(0x2a); // i32.const 42
    wasm.push(0x36); wasm.push(0x02); wasm.push(0x00); // i32.store offset=0
    
    // Load from address 0
    wasm.push(0x41); wasm.push(0x00); // i32.const 0
    wasm.push(0x28); wasm.push(0x02); wasm.push(0x00); // i32.load offset=0
    
    // Store in local
    wasm.push(0x21); wasm.push(0x00); // local.set 0
    
    // Return local
    wasm.push(0x20); wasm.push(0x00); // local.get 0
    wasm.push(0x0b); // end
    
    fs::write("test_binaries/memory_test.wasm", &wasm)?;
    
    println!("\n   WASM Memory Instructions:");
    println!("   i32.load    offset align - Load 32-bit from memory");
    println!("   i32.store   offset align - Store 32-bit to memory");
    println!("   i32.load8_s offset align - Load byte, sign-extend");
    println!("   i32.load8_u offset align - Load byte, zero-extend");
    println!("   i32.load16_s/u           - Load 16-bit");
    println!("   i64.load/store           - 64-bit operations");
    println!("   memory.grow              - Expand memory");
    println!("   memory.size              - Get current size");
    
    Ok(())
}

fn explain_memory_patterns() {
    println!("\nKey patterns for argv access:");
    
    println!("\n1. Getting argc and argv:");
    println!("   ARM64:  X0=argc, X1=argv at function entry");
    println!("   x86-64: RDI=argc, RSI=argv (or stack for _start)");
    println!("   WASM:   Must use WASI imports");
    
    println!("\n2. Accessing argv[i]:");
    println!("   ARM64:  ldr x2, [x1, #8]    ; argv[1] (8 bytes per pointer)");
    println!("   x86-64: mov rax, [rsi+8]    ; argv[1]");
    println!("   WASM:   Use args_get() to fill buffer");
    
    println!("\n3. String access from argv[i]:");
    println!("   After loading pointer to argv[i], dereference again:");
    println!("   ARM64:  ldrb w3, [x2]       ; First char of argv[i]");
    println!("   x86-64: movzx eax, byte [rax] ; First char");
    
    println!("\n4. Array iteration:");
    println!("   - Use base + index*size addressing");
    println!("   - Check bounds (argc) before access");
    println!("   - argv array is NULL-terminated");
}

fn is_arm64() -> bool {
    Command::new("uname")
        .arg("-m")
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim() == "arm64")
        .unwrap_or(false)
}