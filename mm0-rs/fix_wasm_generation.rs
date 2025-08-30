// Fix WASM generation with correct byte counts

fn main() {
    println!("=== Fixing WASM Generation ===\n");
    
    // Count bytes carefully
    let function_body = vec![
        0x00,             // number of locals (1 byte)
        0x41, 0x0a,       // i32.const 10 (2 bytes)
        0x41, 0x05,       // i32.const 5 (2 bytes)
        0x6a,             // i32.add (1 byte)
        0x41, 0x03,       // i32.const 3 (2 bytes)
        0x6c,             // i32.mul (1 byte)
        0x41, 0x02,       // i32.const 2 (2 bytes)
        0x6b,             // i32.sub (1 byte)
        0x0b,             // end (1 byte)
    ];
    
    println!("Function body size: {} bytes", function_body.len());
    
    // Build WASM with correct sizes
    let mut wasm = Vec::new();
    
    // Magic and version
    wasm.extend(&[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]);
    
    // Type section
    wasm.push(0x01); // section id
    wasm.push(0x05); // section length
    wasm.push(0x01); // number of types
    wasm.push(0x60); // function type
    wasm.push(0x00); // no params
    wasm.push(0x01); // one result
    wasm.push(0x7f); // i32 result
    
    // Function section
    wasm.push(0x03); // section id
    wasm.push(0x02); // section length
    wasm.push(0x01); // number of functions
    wasm.push(0x00); // function 0 has type 0
    
    // Export section
    wasm.push(0x07); // section id
    wasm.push(0x08); // section length
    wasm.push(0x01); // number of exports
    wasm.push(0x04); // string length
    wasm.extend(b"main"); // export name
    wasm.push(0x00); // export kind (function)
    wasm.push(0x00); // function index
    
    // Code section
    wasm.push(0x0a); // section id
    
    // Calculate section length: 1 (num functions) + 1 (body size) + body_len
    let section_len = 1 + 1 + function_body.len() as u8;
    wasm.push(section_len); // section length
    
    wasm.push(0x01); // number of functions
    wasm.push(function_body.len() as u8); // function body size
    wasm.extend(&function_body); // function body
    
    println!("Total WASM size: {} bytes", wasm.len());
    
    // Write the fixed file
    std::fs::write("test_binaries/calc_fixed.wasm", &wasm).unwrap();
    println!("\nWrote test_binaries/calc_fixed.wasm");
    
    // Validate
    let validate = std::process::Command::new("wasmer")
        .args(&["validate", "test_binaries/calc_fixed.wasm"])
        .output()
        .unwrap();
    
    if validate.status.success() {
        println!("✅ WASM validation passed!");
        
        // Run it
        let run = std::process::Command::new("wasmer")
            .args(&["run", "test_binaries/calc_fixed.wasm", "--invoke", "main"])
            .output()
            .unwrap();
        
        let exit_code = run.status.code().unwrap_or(-1);
        println!("\nExecution result:");
        println!("  Exit code: {} {}", exit_code, 
            if exit_code == 43 { "✅" } else { "❌" });
            
        // Also try wasmtime
        println!("\nTrying wasmtime:");
        let wasmtime = std::process::Command::new("wasmtime")
            .args(&["run", "test_binaries/calc_fixed.wasm", "--invoke", "main"])
            .output()
            .unwrap();
            
        if wasmtime.status.success() {
            let output = String::from_utf8_lossy(&wasmtime.stdout);
            println!("  Result: {} {}", output.trim(),
                if output.trim() == "43" { "✅" } else { "❌" });
        }
    } else {
        println!("❌ WASM validation failed:");
        println!("{}", String::from_utf8_lossy(&validate.stderr));
    }
    
    // Now let's fix our WASM encoder in the compiler
    println!("\n=== Fixing WASM Encoding in Compiler ===");
    println!("The issue: We need to emit proper LEB128 for section lengths!");
    println!("Current code emits single bytes, but WASM uses LEB128 encoding.");
}