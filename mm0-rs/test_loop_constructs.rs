#!/usr/bin/env cargo +nightly -Zscript

//! Test loop construct implementation for all architectures
//! We'll implement a simple loop that sums 1 to 10 = 55

fn main() {
    println!("=== Loop Construct Implementation ===\n");
    
    println!("Goal: Sum numbers 1 to 10 (result = 55)");
    println!("Loop structure: for(i=1; i<=10; i++) sum += i\n");
    
    test_arm64_loops();
    test_x86_loops();
    test_wasm_loops();
    
    println!("\n=== Implementation Strategy ===");
    println!("All architectures use their existing branch instructions:");
    println!("- Initialize counter and sum");
    println!("- Loop: add counter to sum, increment counter");
    println!("- Compare counter with limit");
    println!("- Branch back if not done");
}

fn test_arm64_loops() {
    println!("1. ARM64 Loop Implementation:");
    println!("   Using: CMP, B.LE (branch if less or equal)\n");
    
    // ARM64 code for sum 1 to 10
    let code = vec![
        // Initialize
        0x20, 0x00, 0x80, 0x52,  // mov x0, #1     ; counter = 1
        0x01, 0x00, 0x80, 0x52,  // mov x1, #0     ; sum = 0
        0x42, 0x01, 0x80, 0x52,  // mov x2, #10    ; limit = 10
        
        // Loop start (offset 12)
        0x21, 0x00, 0x00, 0x8b,  // add x1, x1, x0 ; sum += counter
        0x00, 0x04, 0x00, 0x91,  // add x0, x0, #1 ; counter++
        0x5f, 0x00, 0x02, 0xeb,  // cmp x2, x0     ; compare limit with counter
        0xa2, 0xff, 0xff, 0x54,  // b.cs -12       ; branch if carry set (unsigned >=)
        
        // Exit with sum in x0
        0xe0, 0x03, 0x01, 0xaa,  // mov x0, x1     ; result = sum
        0x30, 0x00, 0x80, 0xd2,  // mov x16, #1    ; exit
        0x01, 0x00, 0x00, 0xd4,  // svc #0
    ];
    
    println!("   Instructions:");
    println!("     mov x0, #1        ; counter = 1");
    println!("     mov x1, #0        ; sum = 0");
    println!("     mov x2, #10       ; limit = 10");
    println!("   loop:");
    println!("     add x1, x1, x0    ; sum += counter");
    println!("     add x0, x0, #1    ; counter++");
    println!("     cmp x2, x0        ; limit vs counter");
    println!("     b.cs loop         ; loop if counter <= limit");
    println!("     mov x0, x1        ; return sum");
    
    // Calculate branch offset
    println!("\n   Branch offset calculation:");
    println!("     Target: -12 bytes (3 instructions back)");
    println!("     Encoding: 0x54ffffa2 (b.cs with -12 offset)");
    
    // Save code
    std::fs::write("test_binaries/loop_arm64.bin", &code).unwrap();
}

fn test_x86_loops() {
    println!("\n2. x86-64 Loop Implementation:");
    println!("   Using: CMP, JLE (jump if less or equal)\n");
    
    // x86-64 code for sum 1 to 10
    let code = vec![
        // Initialize
        0x48, 0xc7, 0xc0, 0x01, 0x00, 0x00, 0x00,  // mov rax, 1    ; counter
        0x48, 0xc7, 0xc3, 0x00, 0x00, 0x00, 0x00,  // mov rbx, 0    ; sum
        0x48, 0xc7, 0xc1, 0x0a, 0x00, 0x00, 0x00,  // mov rcx, 10   ; limit
        
        // Loop start (offset 21)
        0x48, 0x01, 0xc3,              // add rbx, rax  ; sum += counter
        0x48, 0xff, 0xc0,              // inc rax       ; counter++
        0x48, 0x39, 0xc8,              // cmp rax, rcx  ; counter vs limit
        0x7e, 0xf4,                    // jle -12       ; loop if <=
        
        // Exit with sum
        0x48, 0x89, 0xd8,              // mov rax, rbx  ; result = sum
        0x48, 0xc7, 0xc7, 0x00, 0x00, 0x00, 0x00,  // mov rdi, rax
        0x48, 0xc7, 0xc0, 0x3c, 0x00, 0x00, 0x00,  // mov rax, 60
        0x0f, 0x05,                    // syscall
    ];
    
    println!("   Instructions:");
    println!("     mov rax, 1        ; counter = 1");
    println!("     mov rbx, 0        ; sum = 0");
    println!("     mov rcx, 10       ; limit = 10");
    println!("   .loop:");
    println!("     add rbx, rax      ; sum += counter");
    println!("     inc rax           ; counter++");
    println!("     cmp rax, rcx      ; counter vs limit");
    println!("     jle .loop         ; loop if counter <= limit");
    println!("     mov rax, rbx      ; return sum");
    
    println!("\n   Jump encoding: JLE rel8 = 0x7E 0xF4 (-12 bytes)");
}

fn test_wasm_loops() {
    println!("\n3. WebAssembly Loop Implementation:");
    println!("   Using: loop/br_if structure\n");
    
    // WASM code for sum 1 to 10
    let code = vec![
        // Function setup
        0x02, 0x7f,          // 2 locals of type i32
        
        // Initialize counter = 1, sum = 0
        0x41, 0x01,          // i32.const 1
        0x21, 0x00,          // local.set 0 (counter)
        0x41, 0x00,          // i32.const 0
        0x21, 0x01,          // local.set 1 (sum)
        
        // Loop
        0x03, 0x40,          // loop (blocktype void)
          // sum = sum + counter
          0x20, 0x01,        // local.get 1 (sum)
          0x20, 0x00,        // local.get 0 (counter)
          0x6a,              // i32.add
          0x21, 0x01,        // local.set 1 (sum)
          
          // counter++
          0x20, 0x00,        // local.get 0 (counter)
          0x41, 0x01,        // i32.const 1
          0x6a,              // i32.add
          0x21, 0x00,        // local.set 0 (counter)
          
          // if counter <= 10, continue loop
          0x20, 0x00,        // local.get 0 (counter)
          0x41, 0x0b,        // i32.const 11 (we check <= 10)
          0x48,              // i32.lt_s
          0x0d, 0x00,        // br_if 0 (loop again)
        0x0b,                // end loop
        
        // Return sum
        0x20, 0x01,          // local.get 1 (sum)
        0x0b,                // end function
    ];
    
    println!("   WASM structure:");
    println!("     (local $counter i32)");
    println!("     (local $sum i32)");
    println!("     (local.set $counter (i32.const 1))");
    println!("     (local.set $sum (i32.const 0))");
    println!("     (loop");
    println!("       (local.set $sum");
    println!("         (i32.add (local.get $sum) (local.get $counter)))");
    println!("       (local.set $counter");
    println!("         (i32.add (local.get $counter) (i32.const 1)))");
    println!("       (br_if 0");
    println!("         (i32.lt_s (local.get $counter) (i32.const 11)))");
    println!("     )");
    println!("     (local.get $sum)");
    
    println!("\n   Key instructions:");
    println!("     loop (0x03 0x40) - start loop block");
    println!("     br_if 0 - branch to loop start if condition true");
}