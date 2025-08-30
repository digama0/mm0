#!/usr/bin/env cargo +nightly -Zscript

//! Direct test of calculator code generation
//! This bypasses MM1 and directly generates code for (10 + 5) * 3 - 2 = 43

use std::fs::File;
use std::io::Write;

fn main() -> std::io::Result<()> {
    println!("=== Direct Calculator Code Generation ===\n");
    
    // Generate for each architecture
    generate_arm64_calculator()?;
    generate_x86_calculator()?;
    generate_wasm_calculator()?;
    
    println!("\nCalculator implementations complete!");
    println!("Expected result for all: 43");
    
    Ok(())
}

fn generate_arm64_calculator() -> std::io::Result<()> {
    println!("1. ARM64 Calculator:");
    println!("   Expression: (10 + 5) * 3 - 2");
    
    // ARM64 code sequence
    let code = vec![
        // mov x0, #10
        0x40, 0x01, 0x80, 0x52,
        // mov x1, #5
        0xa0, 0x00, 0x80, 0x52,
        // add x0, x0, x1    ; x0 = 15
        0x00, 0x00, 0x01, 0x8b,
        // mov x1, #3
        0x60, 0x00, 0x80, 0x52,
        // mul x0, x0, x1    ; x0 = 45
        0x00, 0x7c, 0x01, 0x9b,
        // sub x0, x0, #2    ; x0 = 43
        0x00, 0x08, 0x00, 0xd1,
        // Exit sequence
        // mov x16, #1       ; exit syscall
        0x30, 0x00, 0x80, 0xd2,
        // svc #0
        0x01, 0x00, 0x00, 0xd4,
    ];
    
    println!("   Instructions:");
    println!("     mov x0, #10");
    println!("     mov x1, #5");
    println!("     add x0, x0, x1    ; = 15");
    println!("     mov x1, #3");
    println!("     mul x0, x0, x1    ; = 45");
    println!("     sub x0, x0, #2    ; = 43");
    println!("     mov x16, #1       ; exit");
    println!("     svc #0");
    
    // Save raw code for testing
    std::fs::write("test_binaries/calc_arm64_raw.bin", &code)?;
    println!("   Saved to: test_binaries/calc_arm64_raw.bin");
    
    Ok(())
}

fn generate_x86_calculator() -> std::io::Result<()> {
    println!("\n2. x86-64 Calculator:");
    println!("   Expression: (10 + 5) * 3 - 2");
    
    // x86-64 code sequence
    let code = vec![
        // mov rax, 10
        0x48, 0xc7, 0xc0, 0x0a, 0x00, 0x00, 0x00,
        // mov rbx, 5
        0x48, 0xc7, 0xc3, 0x05, 0x00, 0x00, 0x00,
        // add rax, rbx      ; rax = 15
        0x48, 0x01, 0xd8,
        // mov rbx, 3
        0x48, 0xc7, 0xc3, 0x03, 0x00, 0x00, 0x00,
        // imul rax, rbx     ; rax = 45
        0x48, 0x0f, 0xaf, 0xc3,
        // sub rax, 2        ; rax = 43
        0x48, 0x83, 0xe8, 0x02,
        // Exit sequence
        // mov rdi, rax      ; exit code
        0x48, 0x89, 0xc7,
        // mov rax, 60       ; sys_exit
        0x48, 0xc7, 0xc0, 0x3c, 0x00, 0x00, 0x00,
        // syscall
        0x0f, 0x05,
    ];
    
    println!("   Instructions:");
    println!("     mov rax, 10");
    println!("     mov rbx, 5");
    println!("     add rax, rbx      ; = 15");
    println!("     mov rbx, 3");
    println!("     imul rax, rbx     ; = 45");
    println!("     sub rax, 2        ; = 43");
    println!("     mov rdi, rax      ; exit code");
    println!("     mov rax, 60       ; sys_exit");
    println!("     syscall");
    
    Ok(())
}

fn generate_wasm_calculator() -> std::io::Result<()> {
    println!("\n3. WebAssembly Calculator:");
    println!("   Expression: (10 + 5) * 3 - 2");
    
    // Create a complete WASM module
    let mut wasm = Vec::new();
    
    // WASM header
    wasm.extend(b"\0asm");
    wasm.extend(&[1, 0, 0, 0]);
    
    // Type section (id=1)
    wasm.push(0x01);  // section id
    wasm.push(0x05);  // section size
    wasm.push(0x01);  // 1 type
    wasm.extend(&[0x60, 0x00, 0x01, 0x7f]); // () -> i32
    
    // Function section (id=3)
    wasm.push(0x03);  // section id
    wasm.push(0x02);  // section size
    wasm.push(0x01);  // 1 function
    wasm.push(0x00);  // function 0 uses type 0
    
    // Export section (id=7)
    wasm.push(0x07);  // section id
    wasm.push(0x08);  // section size
    wasm.push(0x01);  // 1 export
    wasm.push(0x04);  // name length
    wasm.extend(b"main");
    wasm.push(0x00);  // function export
    wasm.push(0x00);  // function index 0
    
    // Code section (id=10)
    wasm.push(0x0a);  // section id
    wasm.push(0x10);  // section size
    wasm.push(0x01);  // 1 function
    wasm.push(0x0e);  // function body size
    wasm.push(0x00);  // 0 locals
    
    // Function body: (10 + 5) * 3 - 2
    wasm.push(0x41); wasm.push(0x0a);  // i32.const 10
    wasm.push(0x41); wasm.push(0x05);  // i32.const 5
    wasm.push(0x6a);                    // i32.add      ; = 15
    wasm.push(0x41); wasm.push(0x03);  // i32.const 3
    wasm.push(0x6c);                    // i32.mul      ; = 45
    wasm.push(0x41); wasm.push(0x02);  // i32.const 2
    wasm.push(0x6b);                    // i32.sub      ; = 43
    wasm.push(0x0b);                    // end
    
    println!("   Stack operations:");
    println!("     i32.const 10");
    println!("     i32.const 5");
    println!("     i32.add           ; = 15");
    println!("     i32.const 3");
    println!("     i32.mul           ; = 45");
    println!("     i32.const 2");
    println!("     i32.sub           ; = 43");
    
    // Save WASM module
    std::fs::write("test_binaries/calc.wasm", &wasm)?;
    println!("   Saved to: test_binaries/calc.wasm");
    
    // Test with wasmer
    println!("\n   Testing with wasmer:");
    let output = std::process::Command::new("wasmer")
        .arg("run")
        .arg("test_binaries/calc.wasm")
        .arg("-i")
        .arg("main")
        .output();
    
    match output {
        Ok(out) => {
            let result = String::from_utf8_lossy(&out.stdout);
            println!("   Result: {}", result.trim());
            if result.trim() == "43" {
                println!("   ✅ Correct!");
            }
        }
        Err(_) => println!("   (wasmer not available)"),
    }
    
    Ok(())
}