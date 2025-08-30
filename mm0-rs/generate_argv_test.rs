// Generate test binaries that demonstrate accessing argv array

use std::fs;
use std::process::Command;

fn main() -> std::io::Result<()> {
    println!("=== Testing argv Array Access ===\n");
    
    fs::create_dir_all("test_binaries")?;
    
    generate_arm64_argv_test()?;
    generate_x86_argv_test()?;
    generate_wasm_argv_test()?;
    
    println!("\nTesting generated binaries...\n");
    test_binaries();
    
    Ok(())
}

fn generate_arm64_argv_test() -> std::io::Result<()> {
    println!("1. Generating ARM64 argv test...");
    
    // Assembly that counts command line arguments
    let asm = r#"
.global _main
.align 2

_main:
    // Save frame
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    
    // X0 = argc, X1 = argv
    
    // Test 1: Return argc
    cmp x0, #1
    b.eq .just_program_name
    
    // Test 2: If we have args, count characters in first arg
    ldr x2, [x1, #8]    // Load argv[1] - pointer to first argument
    mov x3, #0          // Character counter
    
.count_loop:
    ldrb w4, [x2, x3]   // Load byte at argv[1][x3]
    cbz w4, .done       // If null terminator, we're done
    add x3, x3, #1      // Increment counter
    b .count_loop
    
.done:
    mov x0, x3          // Return string length
    b .exit
    
.just_program_name:
    mov x0, #0          // No args provided
    
.exit:
    ldp x29, x30, [sp], #16
    ret
"#;
    
    fs::write("test_binaries/argv_test.s", asm)?;
    
    if is_arm64() {
        Command::new("as")
            .args(&["-o", "test_binaries/argv_test.o", "test_binaries/argv_test.s"])
            .status()?;
            
        Command::new("ld")
            .args(&["-o", "test_binaries/argv_test_arm64", 
                   "test_binaries/argv_test.o",
                   "-lSystem", "-syslibroot",
                   "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk",
                   "-e", "_main", "-arch", "arm64"])
            .status()?;
            
        println!("   Generated: test_binaries/argv_test_arm64");
    }
    
    Ok(())
}

fn generate_x86_argv_test() -> std::io::Result<()> {
    println!("\n2. Generating x86-64 argv test...");
    
    let asm = r#"
.global _start
.text

_start:
    # Get argc and argv from stack
    mov rdi, [rsp]      # argc
    lea rsi, [rsp+8]    # argv
    
    # Test 1: Return argc
    cmp rdi, 1
    je .just_program_name
    
    # Test 2: Count characters in first arg
    mov rdx, [rsi+8]    # argv[1]
    xor rcx, rcx        # Counter
    
.count_loop:
    movzx eax, byte [rdx+rcx]  # Load byte
    test al, al         # Check for null
    jz .done
    inc rcx
    jmp .count_loop
    
.done:
    mov rax, rcx        # Return string length
    jmp .exit
    
.just_program_name:
    xor rax, rax        # Return 0
    
.exit:
    mov rdi, rax
    mov rax, 60         # sys_exit
    syscall
"#;
    
    fs::write("test_binaries/argv_test_x86.s", asm)?;
    println!("   Assembly saved to test_binaries/argv_test_x86.s");
    
    Ok(())
}

fn generate_wasm_argv_test() -> std::io::Result<()> {
    println!("\n3. Generating WASM argv test...");
    
    // WASM doesn't have direct argv access, but we can demonstrate memory ops
    let mut wasm = Vec::new();
    
    // WASM header
    wasm.extend(&[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]);
    
    // Type section
    wasm.push(0x01); // section id
    wasm.push(0x05); // section length
    wasm.push(0x01); // number of types
    // Type 0: () -> i32
    wasm.extend(&[0x60, 0x00, 0x01, 0x7f]);
    
    // Memory section
    wasm.push(0x05); // section id
    wasm.push(0x03); // section length
    wasm.push(0x01); // number of memories
    wasm.push(0x00); // no flags
    wasm.push(0x01); // min 1 page
    
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
    
    // Code section - demonstrate memory store/load
    wasm.push(0x0a); // section id
    wasm.push(0x17); // section length
    wasm.push(0x01); // number of functions
    
    wasm.push(0x15); // function body size
    wasm.push(0x00); // no locals
    
    // Store "Hello" at address 0
    wasm.push(0x41); wasm.push(0x00); // i32.const 0 (address)
    wasm.push(0x41); wasm.push(0x48); // i32.const 72 ('H')
    wasm.push(0x3a); wasm.push(0x00); wasm.push(0x00); // i32.store8
    
    // Count non-zero bytes starting at 0
    wasm.push(0x41); wasm.push(0x00); // i32.const 0 (counter)
    wasm.push(0x41); wasm.push(0x00); // i32.const 0 (address)
    wasm.push(0x2d); wasm.push(0x00); wasm.push(0x00); // i32.load8_u
    wasm.push(0x0d); wasm.push(0x00); // br_if 0 (if non-zero)
    wasm.push(0x41); wasm.push(0x01); // i32.const 1 (found one byte)
    wasm.push(0x0b); // end
    
    fs::write("test_binaries/argv_test.wasm", &wasm)?;
    println!("   Generated: test_binaries/argv_test.wasm");
    
    Ok(())
}

fn test_binaries() {
    if is_arm64() {
        println!("Testing ARM64 argv access:");
        
        // Test with no args
        match Command::new("./test_binaries/argv_test_arm64").status() {
            Ok(status) => {
                println!("   No args: exit code = {} (expect 0)", 
                    status.code().unwrap_or(-1));
            }
            Err(e) => println!("   Failed: {}", e),
        }
        
        // Test with "hello"
        match Command::new("./test_binaries/argv_test_arm64")
            .arg("hello")
            .status() 
        {
            Ok(status) => {
                println!("   With 'hello': exit code = {} (expect 5)", 
                    status.code().unwrap_or(-1));
            }
            Err(e) => println!("   Failed: {}", e),
        }
        
        // Test with longer string
        match Command::new("./test_binaries/argv_test_arm64")
            .arg("testing123")
            .status() 
        {
            Ok(status) => {
                println!("   With 'testing123': exit code = {} (expect 10)", 
                    status.code().unwrap_or(-1));
            }
            Err(e) => println!("   Failed: {}", e),
        }
    }
}

fn is_arm64() -> bool {
    Command::new("uname")
        .arg("-m")
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim() == "arm64")
        .unwrap_or(false)
}