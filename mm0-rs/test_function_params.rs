#!/usr/bin/env cargo +nightly -Zscript

//! Test function parameter passing and return values
//! We'll implement: int add(int a, int b) { return a + b; }
//! And for main: main(argc, argv) handling

fn main() {
    println!("=== Function Parameters and Return Values ===\n");
    
    println!("Goal: Implement add(a, b) and test main(argc, argv)");
    
    test_arm64_params();
    test_x86_params();
    test_wasm_params();
    
    println!("\n=== Key Insights ===");
    println!("1. Each architecture has specific parameter passing conventions");
    println!("2. main() receives argc/argv differently on each platform");
    println!("3. Return values use specific registers/stack locations");
}

fn test_arm64_params() {
    println!("\n1. ARM64 Parameter Passing (AAPCS64):");
    println!("   Integer parameters: X0-X7 (first 8 args)");
    println!("   Return value: X0 (X1 for 128-bit)");
    println!("   main(argc, argv): X0=argc, X1=argv\n");
    
    println!("   add(int a, int b) implementation:");
    println!("   add:");
    println!("     add x0, x0, x1    ; return a + b in x0");
    println!("     ret");
    
    println!("\n   Calling add(5, 3):");
    println!("     mov x0, #5        ; first arg");
    println!("     mov x1, #3        ; second arg");
    println!("     bl add            ; call");
    println!("     ; result in x0 = 8");
    
    println!("\n   main with args:");
    println!("   main:");
    println!("     ; x0 = argc (argument count)");
    println!("     ; x1 = argv (pointer to array of strings)");
    println!("     ldr x2, [x1, #8]  ; argv[1] - first command line arg");
    println!("     ret");
}

fn test_x86_params() {
    println!("\n2. x86-64 Parameter Passing (System V ABI):");
    println!("   Integer parameters: RDI, RSI, RDX, RCX, R8, R9");
    println!("   Return value: RAX (RDX:RAX for 128-bit)");
    println!("   main(argc, argv): RDI=argc, RSI=argv\n");
    
    println!("   add(int a, int b) implementation:");
    println!("   add:");
    println!("     mov rax, rdi      ; move first arg");
    println!("     add rax, rsi      ; add second arg");
    println!("     ret               ; return in rax");
    
    println!("\n   Calling add(5, 3):");
    println!("     mov rdi, 5        ; first arg");
    println!("     mov rsi, 3        ; second arg");
    println!("     call add");
    println!("     ; result in rax = 8");
    
    println!("\n   main with args:");
    println!("   main:");
    println!("     ; rdi = argc");
    println!("     ; rsi = argv");
    println!("     mov rax, [rsi+8]  ; argv[1]");
    println!("     ret");
}

fn test_wasm_params() {
    println!("\n3. WebAssembly Parameter Passing:");
    println!("   Parameters are part of function type");
    println!("   Passed on the stack implicitly");
    println!("   Return values also on stack\n");
    
    println!("   add function type: (func (param i32 i32) (result i32))");
    println!("   add implementation:");
    println!("     local.get 0       ; get first param");
    println!("     local.get 1       ; get second param");
    println!("     i32.add           ; add them");
    println!("     ; implicit return of top stack value");
    
    println!("\n   Calling add(5, 3):");
    println!("     i32.const 5       ; push first arg");
    println!("     i32.const 3       ; push second arg");
    println!("     call $add         ; call function");
    println!("     ; result on stack = 8");
    
    println!("\n   WASM main typically doesn't receive argc/argv directly");
    println!("   Instead, uses WASI imports for command line access");
}

// Now let's create actual working examples

fn generate_add_examples() {
    println!("\n=== Generating Working Examples ===");
    
    // ARM64 add function
    let arm64_add = vec![
        0x00, 0x00, 0x01, 0x8b,  // add x0, x0, x1
        0xc0, 0x03, 0x5f, 0xd6,  // ret
    ];
    
    // x86-64 add function  
    let x86_add = vec![
        0x48, 0x89, 0xf8,        // mov rax, rdi
        0x48, 0x01, 0xf0,        // add rax, rsi
        0xc3,                    // ret
    ];
    
    // WASM add function (complete module)
    let wasm_add = vec![
        // Type: (func (param i32 i32) (result i32))
        0x60, 0x02, 0x7f, 0x7f, 0x01, 0x7f,
        // Function body
        0x20, 0x00,              // local.get 0
        0x20, 0x01,              // local.get 1
        0x6a,                    // i32.add
        0x0b,                    // end
    ];
    
    println!("Generated add functions for all architectures!");
}