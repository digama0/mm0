#!/usr/bin/env cargo +nightly -Zscript

//! Demonstration of function calls in generated code
//! This shows how to generate a simple program with function calls

use std::fs::File;
use std::io::Write;

fn main() -> std::io::Result<()> {
    println!("=== Function Call Demo ===\n");
    
    // Generate code for each architecture
    generate_arm64_function_demo()?;
    generate_x86_64_function_demo()?;
    generate_wasm_function_demo()?;
    
    println!("\nFunction call implementations complete!");
    println!("Next step: Integrate with MM1 compiler for automatic generation");
    
    Ok(())
}

fn generate_arm64_function_demo() -> std::io::Result<()> {
    println!("1. ARM64 Function Call Demo:");
    println!("   Program: main calls add(10, 5), returns result");
    
    // ARM64 code for:
    // add_func:
    //     add x0, x0, x1    ; x0 = x0 + x1
    //     ret               ; return to caller
    // main:
    //     mov x0, #10       ; first arg
    //     mov x1, #5        ; second arg
    //     bl add_func       ; call add
    //     mov x16, #1       ; exit syscall
    //     svc #0            ; exit(result)
    
    let code = vec![
        // add_func at offset 0:
        0x00, 0x00, 0x01, 0x8b,  // add x0, x0, x1
        0xc0, 0x03, 0x5f, 0xd6,  // ret
        
        // main at offset 8:
        0x40, 0x01, 0x80, 0x52,  // mov x0, #10
        0x01, 0x00, 0x80, 0x52,  // mov x1, #5
        0xfc, 0xff, 0xff, 0x97,  // bl -16 (to add_func)
        0x30, 0x00, 0x80, 0xd2,  // mov x16, #1
        0x01, 0x00, 0x00, 0xd4,  // svc #0
    ];
    
    println!("   Generated code ({} bytes):", code.len());
    println!("     add_func:");
    println!("       add x0, x0, x1");
    println!("       ret");
    println!("     main:");
    println!("       mov x0, #10");
    println!("       mov x1, #5");
    println!("       bl add_func     ; offset -16");
    println!("       mov x16, #1");
    println!("       svc #0");
    println!("   Expected result: exit(15)");
    
    Ok(())
}

fn generate_x86_64_function_demo() -> std::io::Result<()> {
    println!("\n2. x86-64 Function Call Demo:");
    println!("   Program: main calls add(10, 5), returns result");
    
    // x86-64 code for:
    // add_func:
    //     lea rax, [rdi + rsi]  ; rax = rdi + rsi
    //     ret
    // main:
    //     mov rdi, 10           ; first arg
    //     mov rsi, 5            ; second arg
    //     call add_func
    //     mov rdi, rax          ; exit code
    //     mov rax, 60           ; sys_exit
    //     syscall
    
    let code = vec![
        // add_func:
        0x48, 0x8d, 0x04, 0x37,  // lea rax, [rdi + rsi]
        0xc3,                    // ret
        
        // main:
        0x48, 0xc7, 0xc7, 0x0a, 0x00, 0x00, 0x00,  // mov rdi, 10
        0x48, 0xc7, 0xc6, 0x05, 0x00, 0x00, 0x00,  // mov rsi, 5
        0xe8, 0xe7, 0xff, 0xff, 0xff,              // call -25 (to add_func)
        0x48, 0x89, 0xc7,                          // mov rdi, rax
        0x48, 0xc7, 0xc0, 0x3c, 0x00, 0x00, 0x00,  // mov rax, 60
        0x0f, 0x05,                                // syscall
    ];
    
    println!("   Generated code ({} bytes)", code.len());
    println!("   Expected result: exit(15)");
    
    Ok(())
}

fn generate_wasm_function_demo() -> std::io::Result<()> {
    println!("\n3. WebAssembly Function Call Demo:");
    println!("   Program: main calls add(10, 5), returns result");
    
    // WASM module with two functions
    let mut wasm = Vec::new();
    
    // Header
    wasm.extend(b"\0asm");
    wasm.extend(&[1, 0, 0, 0]);
    
    // Type section - two function types
    wasm.push(0x01); // section id
    wasm.push(0x0b); // section size
    wasm.push(0x02); // 2 types
    // Type 0: (i32, i32) -> i32
    wasm.extend(&[0x60, 0x02, 0x7f, 0x7f, 0x01, 0x7f]);
    // Type 1: () -> i32
    wasm.extend(&[0x60, 0x00, 0x01, 0x7f]);
    
    // Function section
    wasm.push(0x03); // section id
    wasm.push(0x03); // section size
    wasm.push(0x02); // 2 functions
    wasm.push(0x00); // func 0 uses type 0
    wasm.push(0x01); // func 1 uses type 1
    
    // Export section
    wasm.push(0x07); // section id
    wasm.push(0x08); // section size
    wasm.push(0x01); // 1 export
    wasm.push(0x04); // name length
    wasm.extend(b"main");
    wasm.push(0x00); // function export
    wasm.push(0x01); // function index 1
    
    // Code section
    wasm.push(0x0a); // section id
    wasm.push(0x13); // section size
    wasm.push(0x02); // 2 functions
    
    // Function 0 (add): (i32, i32) -> i32
    wasm.push(0x07); // body size
    wasm.push(0x00); // 0 locals
    wasm.push(0x20); wasm.push(0x00); // local.get 0
    wasm.push(0x20); wasm.push(0x01); // local.get 1
    wasm.push(0x6a); // i32.add
    wasm.push(0x0b); // end
    
    // Function 1 (main): () -> i32
    wasm.push(0x0a); // body size
    wasm.push(0x00); // 0 locals
    wasm.push(0x41); wasm.push(0x0a); // i32.const 10
    wasm.push(0x41); wasm.push(0x05); // i32.const 5
    wasm.push(0x10); wasm.push(0x00); // call 0 (add)
    wasm.push(0x0b); // end
    
    println!("   Generated WASM module ({} bytes)", wasm.len());
    println!("   Functions:");
    println!("     (func $add (param i32 i32) (result i32)");
    println!("       local.get 0");
    println!("       local.get 1");
    println!("       i32.add)");
    println!("     (func $main (result i32)");
    println!("       i32.const 10");
    println!("       i32.const 5");
    println!("       call $add)");
    println!("   Expected result: 15");
    
    // Save for testing
    std::fs::write("test_binaries/function_demo.wasm", &wasm)?;
    
    Ok(())
}