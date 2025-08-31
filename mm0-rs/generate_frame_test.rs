// Generate test binaries that demonstrate proper stack frame management
// Shows prologue/epilogue generation and local variable access

use std::fs;
use std::process::Command;

fn main() -> std::io::Result<()> {
    println!("=== Generating Stack Frame Tests ===\n");
    
    fs::create_dir_all("test_binaries")?;
    
    // Generate tests for each architecture
    generate_arm64_frame_test()?;
    generate_x86_frame_test()?;
    generate_wasm_frame_test()?;
    
    println!("\nRunning generated tests...\n");
    test_binaries();
    
    Ok(())
}

fn generate_arm64_frame_test() -> std::io::Result<()> {
    println!("1. ARM64 Frame Test");
    
    // Function that uses locals, calls another function, and returns result
    let asm = r#"
.global _factorial
.global _main
.align 2

// Recursive factorial function
_factorial:
    // Prologue
    stp x29, x30, [sp, #-32]!   // Save FP/LR, allocate 32 bytes
    mov x29, sp                  // Set up frame pointer
    str x19, [sp, #16]          // Save x19 (callee-saved)
    
    // Check base case (n <= 1)
    cmp x0, #1
    b.le .base_case
    
    // Recursive case: n * factorial(n-1)
    mov x19, x0                 // Save n in x19
    sub x0, x0, #1             // n-1
    bl _factorial              // Call factorial(n-1)
    
    // Multiply result by n
    mul x0, x0, x19            // result * n
    
    // Epilogue
    ldr x19, [sp, #16]         // Restore x19
    ldp x29, x30, [sp], #32    // Restore FP/LR, deallocate
    ret
    
.base_case:
    mov x0, #1                 // Return 1
    ldr x19, [sp, #16]         // Restore x19
    ldp x29, x30, [sp], #32    // Restore FP/LR, deallocate
    ret

// Function with multiple locals
_sum_squares:
    // Prologue - need space for locals
    stp x29, x30, [sp, #-48]!  // Save FP/LR, allocate 48 bytes
    mov x29, sp
    stp x19, x20, [sp, #16]    // Save x19, x20
    
    // Local variables:
    // [x29, #32] = a*a
    // [x29, #40] = b*b
    
    // Calculate a*a
    mul x19, x0, x0
    str x19, [x29, #32]        // Store a*a
    
    // Calculate b*b
    mul x20, x1, x1
    str x20, [x29, #40]        // Store b*b
    
    // Load and sum
    ldr x0, [x29, #32]         // Load a*a
    ldr x1, [x29, #40]         // Load b*b
    add x0, x0, x1             // Return a*a + b*b
    
    // Epilogue
    ldp x19, x20, [sp, #16]    // Restore saved registers
    ldp x29, x30, [sp], #48    // Restore FP/LR, deallocate
    ret

_main:
    // Simple frame for main
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    
    // Test 1: factorial(5) = 120
    mov x0, #5
    bl _factorial
    
    // Test 2: sum_squares(3, 4) = 9 + 16 = 25
    // But return factorial result for simplicity
    
    ldp x29, x30, [sp], #16
    ret
"#;
    
    fs::write("test_binaries/frame_test_arm64.s", asm)?;
    
    if is_arm64() {
        Command::new("as")
            .args(&["-o", "test_binaries/frame_test_arm64.o", 
                   "test_binaries/frame_test_arm64.s"])
            .status()?;
            
        Command::new("ld")
            .args(&["-o", "test_binaries/frame_test_arm64", 
                   "test_binaries/frame_test_arm64.o",
                   "-lSystem", "-syslibroot",
                   "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk",
                   "-e", "_main", "-arch", "arm64"])
            .status()?;
            
        println!("   Generated: test_binaries/frame_test_arm64");
    }
    
    Ok(())
}

fn generate_x86_frame_test() -> std::io::Result<()> {
    println!("\n2. x86-64 Frame Test");
    
    let asm = r#"
.global _start
.text

# Recursive factorial
factorial:
    # Prologue
    push rbp               # Save old frame pointer
    mov rbp, rsp          # Set up new frame pointer
    push rbx              # Save callee-saved register
    
    # Check base case
    cmp rdi, 1
    jle .base_case
    
    # Recursive case
    mov rbx, rdi          # Save n in rbx
    dec rdi               # n-1
    call factorial        # factorial(n-1)
    
    # Multiply by n
    imul rax, rbx         # result * n
    
    # Epilogue
    pop rbx               # Restore rbx
    pop rbp               # Restore frame pointer
    ret
    
.base_case:
    mov rax, 1            # Return 1
    pop rbx
    pop rbp
    ret

# Function with locals
sum_squares:
    # Prologue with locals
    push rbp
    mov rbp, rsp
    sub rsp, 16           # Space for 2 locals
    
    # Calculate a*a
    mov rax, rdi
    imul rax, rax
    mov [rbp-8], rax      # Store a*a
    
    # Calculate b*b
    mov rax, rsi
    imul rax, rax
    mov [rbp-16], rax     # Store b*b
    
    # Sum them
    mov rax, [rbp-8]      # Load a*a
    add rax, [rbp-16]     # Add b*b
    
    # Epilogue
    mov rsp, rbp          # Restore stack pointer
    pop rbp
    ret

_start:
    # Set up initial stack frame
    mov rbp, rsp
    
    # Test factorial(5)
    mov rdi, 5
    call factorial
    
    # Exit with result (120)
    mov rdi, rax
    mov rax, 60           # sys_exit
    syscall
"#;
    
    fs::write("test_binaries/frame_test_x86.s", asm)?;
    println!("   Generated: test_binaries/frame_test_x86.s");
    
    Ok(())
}

fn generate_wasm_frame_test() -> std::io::Result<()> {
    println!("\n3. WASM Frame Test");
    
    let mut wasm = Vec::new();
    
    // WASM header
    wasm.extend(&[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]);
    
    // Type section - two function types
    wasm.push(0x01); // section id
    wasm.push(0x0b); // section length
    wasm.push(0x02); // number of types
    
    // Type 0: factorial (param i32) (result i32)
    wasm.extend(&[0x60, 0x01, 0x7f, 0x01, 0x7f]);
    
    // Type 1: main () (result i32)
    wasm.extend(&[0x60, 0x00, 0x01, 0x7f]);
    
    // Function section
    wasm.push(0x03); // section id
    wasm.push(0x03); // section length
    wasm.push(0x02); // number of functions
    wasm.push(0x00); // func 0 uses type 0
    wasm.push(0x01); // func 1 uses type 1
    
    // Export section
    wasm.push(0x07); // section id
    wasm.push(0x08); // section length
    wasm.push(0x01); // number of exports
    wasm.push(0x04); wasm.extend(b"main");
    wasm.push(0x00); // function export
    wasm.push(0x01); // function index 1
    
    // Code section
    wasm.push(0x0a); // section id
    wasm.push(0x2c); // section length (44 bytes)
    wasm.push(0x02); // number of functions
    
    // Function 0: factorial
    wasm.push(0x1b); // function body size (27 bytes)
    wasm.push(0x01); // 1 local
    wasm.push(0x01); wasm.push(0x7f); // local i32
    
    // if (n <= 1) return 1
    wasm.push(0x20); wasm.push(0x00); // local.get 0 (n)
    wasm.push(0x41); wasm.push(0x01); // i32.const 1
    wasm.push(0x4c); // i32.le_s
    wasm.push(0x04); wasm.push(0x40); // if
    wasm.push(0x41); wasm.push(0x01); // i32.const 1
    wasm.push(0x0f); // return
    wasm.push(0x0b); // end
    
    // Save n in local
    wasm.push(0x20); wasm.push(0x00); // local.get 0
    wasm.push(0x21); wasm.push(0x01); // local.set 1
    
    // Call factorial(n-1)
    wasm.push(0x20); wasm.push(0x00); // local.get 0
    wasm.push(0x41); wasm.push(0x01); // i32.const 1
    wasm.push(0x6b); // i32.sub
    wasm.push(0x10); wasm.push(0x00); // call 0
    
    // Multiply by n
    wasm.push(0x20); wasm.push(0x01); // local.get 1
    wasm.push(0x6c); // i32.mul
    wasm.push(0x0b); // end
    
    // Function 1: main
    wasm.push(0x0d); // function body size (13 bytes)
    wasm.push(0x00); // no locals
    
    // Call factorial(5)
    wasm.push(0x41); wasm.push(0x05); // i32.const 5
    wasm.push(0x10); wasm.push(0x00); // call 0
    
    // For testing, divide by 2 to get 60 (fits in exit code)
    wasm.push(0x41); wasm.push(0x02); // i32.const 2
    wasm.push(0x6d); // i32.div_s
    wasm.push(0x0b); // end
    
    fs::write("test_binaries/frame_test.wasm", &wasm)?;
    println!("   Generated: test_binaries/frame_test.wasm");
    
    Ok(())
}

fn test_binaries() {
    if is_arm64() {
        println!("Testing ARM64 frame management:");
        match Command::new("./test_binaries/frame_test_arm64").status() {
            Ok(status) => {
                println!("   factorial(5) = {} (expect 120)", 
                    status.code().unwrap_or(-1));
            }
            Err(e) => println!("   Failed: {}", e),
        }
    }
    
    println!("\nTesting WASM frame management:");
    match Command::new("wasmer")
        .args(&["run", "test_binaries/frame_test.wasm", "--invoke", "main"])
        .output()
    {
        Ok(output) => {
            let result = String::from_utf8_lossy(&output.stdout).trim().to_string();
            println!("   factorial(5)/2 = {} (expect 60)", result);
        }
        Err(_) => println!("   Wasmer not available"),
    }
}

fn is_arm64() -> bool {
    Command::new("uname")
        .arg("-m")
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim() == "arm64")
        .unwrap_or(false)
}