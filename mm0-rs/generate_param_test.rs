// Generate binaries that test parameter passing and return values
// We'll implement: result = add(10, 32) = 42

use std::fs;
use std::process::Command;

fn main() -> std::io::Result<()> {
    println!("=== Testing Parameter Passing ===\n");
    
    generate_arm64_param_test()?;
    generate_wasm_param_test()?;
    
    println!("\nTesting generated binaries...\n");
    test_binaries();
    
    Ok(())
}

fn generate_arm64_param_test() -> std::io::Result<()> {
    println!("1. Generating ARM64 parameter test...");
    
    // Rust program that tests parameters
    let rust_code = r#"
// Test add function with parameters
fn add(a: i32, b: i32) -> i32 {
    a + b
}

fn main() {
    // Test 1: Simple add
    let result = add(10, 32);
    
    // Test 2: Access command line args
    let args: Vec<String> = std::env::args().collect();
    let argc = args.len();
    
    // Exit with result (should be 42)
    std::process::exit(result);
}
"#;
    
    fs::write("test_binaries/param_test_arm64.rs", rust_code)?;
    
    Command::new("rustc")
        .args(&["-o", "test_binaries/param_test_arm64", "test_binaries/param_test_arm64.rs"])
        .status()?;
    
    println!("   Generated: test_binaries/param_test_arm64");
    
    // Also generate raw assembly version
    generate_arm64_raw()?;
    
    Ok(())
}

fn generate_arm64_raw() -> std::io::Result<()> {
    println!("   Generating raw ARM64 assembly...");
    
    // Assembly that demonstrates parameter passing
    let asm_code = r#"
.global _main
.align 2

// add function: add(x0, x1) -> x0
_add:
    add x0, x0, x1      // result = a + b
    ret

_main:
    // Save frame
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    
    // Call add(10, 32)
    mov x0, #10         // first parameter
    mov x1, #32         // second parameter
    bl _add             // call add
    // x0 now contains 42
    
    // Exit with result
    mov x16, #1         // exit syscall
    svc #0
"#;
    
    fs::write("test_binaries/param_test.s", asm_code)?;
    
    // Note: Would need assembler to compile this
    println!("   Assembly code saved to test_binaries/param_test.s");
    
    Ok(())
}

fn generate_wasm_param_test() -> std::io::Result<()> {
    println!("\n2. Generating WASM parameter test...");
    
    let mut wasm = Vec::new();
    
    // WASM header
    wasm.extend(&[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]);
    
    // Type section - two function types
    wasm.push(0x01); // section id
    wasm.push(0x0d); // section length
    wasm.push(0x02); // number of types
    
    // Type 0: add function (param i32 i32) (result i32)
    wasm.extend(&[0x60, 0x02, 0x7f, 0x7f, 0x01, 0x7f]);
    
    // Type 1: main function () (result i32)
    wasm.extend(&[0x60, 0x00, 0x01, 0x7f]);
    
    // Function section
    wasm.push(0x03); // section id
    wasm.push(0x03); // section length
    wasm.push(0x02); // number of functions
    wasm.push(0x00); // func 0 uses type 0 (add)
    wasm.push(0x01); // func 1 uses type 1 (main)
    
    // Export section
    wasm.push(0x07); // section id
    wasm.push(0x11); // section length
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
    wasm.push(0x11); // section length
    wasm.push(0x02); // number of functions
    
    // Function 0 (add): receives two params, returns sum
    wasm.push(0x07); // function body size
    wasm.push(0x00); // no locals
    wasm.push(0x20); wasm.push(0x00); // local.get 0
    wasm.push(0x20); wasm.push(0x01); // local.get 1
    wasm.push(0x6a); // i32.add
    wasm.push(0x0b); // end
    
    // Function 1 (main): calls add(10, 32)
    wasm.push(0x08); // function body size
    wasm.push(0x00); // no locals
    wasm.push(0x41); wasm.push(0x0a); // i32.const 10
    wasm.push(0x41); wasm.push(0x20); // i32.const 32
    wasm.push(0x10); wasm.push(0x00); // call 0 (add)
    wasm.push(0x0b); // end
    
    fs::write("test_binaries/param_test.wasm", &wasm)?;
    println!("   Generated: test_binaries/param_test.wasm");
    
    Ok(())
}

fn test_binaries() {
    // Test ARM64
    if Command::new("uname").arg("-m").output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim() == "arm64")
        .unwrap_or(false) 
    {
        println!("Testing ARM64 parameter passing:");
        match Command::new("test_binaries/param_test_arm64").status() {
            Ok(status) => {
                if let Some(code) = status.code() {
                    println!("   add(10, 32) = {} {}", code, 
                        if code == 42 { "✅" } else { "❌" });
                }
            }
            Err(e) => println!("   Failed to run: {}", e),
        }
        
        // Test with command line args
        println!("\n   Testing with command line arguments:");
        match Command::new("test_binaries/param_test_arm64")
            .args(&["hello", "world"])
            .status() 
        {
            Ok(status) => {
                println!("   With 3 args (program + 2), exit code: {}", 
                    status.code().unwrap_or(-1));
            }
            Err(e) => println!("   Failed: {}", e),
        }
    }
    
    // Test WASM
    println!("\nTesting WASM parameter passing:");
    
    // Test add function
    match Command::new("wasmer")
        .args(&["run", "test_binaries/param_test.wasm", "--invoke", "add", "10", "32"])
        .output()
    {
        Ok(output) => {
            let result = String::from_utf8_lossy(&output.stdout).trim().to_string();
            println!("   add(10, 32) = {} {}", result,
                if result == "42" { "✅" } else { "❌" });
        }
        Err(_) => println!("   Wasmer not available"),
    }
    
    // Test main function
    match Command::new("wasmer")
        .args(&["run", "test_binaries/param_test.wasm", "--invoke", "main"])
        .output()
    {
        Ok(output) => {
            let result = String::from_utf8_lossy(&output.stdout).trim().to_string();
            println!("   main() calls add(10,32) = {} {}", result,
                if result == "42" { "✅" } else { "❌" });
        }
        Err(_) => {},
    }
}