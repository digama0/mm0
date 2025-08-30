// Fix WASM loop generation

fn main() {
    println!("=== Fixing WASM Loop Generation ===\n");
    
    let mut wasm = Vec::new();
    
    // Header
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
    wasm.extend(b"main");
    wasm.push(0x00); // export kind (function)
    wasm.push(0x00); // function index
    
    // Build function body first to get size
    let mut body = Vec::new();
    
    // Local declarations: 2 locals of type i32
    body.push(0x02); // number of local declaration groups
    body.push(0x01); // count
    body.push(0x7f); // type i32
    body.push(0x01); // count
    body.push(0x7f); // type i32
    
    // Initialize counter = 1, sum = 0
    body.push(0x41); body.push(0x01);  // i32.const 1
    body.push(0x21); body.push(0x00);  // local.set 0 (counter)
    body.push(0x41); body.push(0x00);  // i32.const 0
    body.push(0x21); body.push(0x01);  // local.set 1 (sum)
    
    // Loop
    body.push(0x03); body.push(0x40);  // loop (void)
      body.push(0x20); body.push(0x01);  // local.get 1 (sum)
      body.push(0x20); body.push(0x00);  // local.get 0 (counter)
      body.push(0x6a);                    // i32.add
      body.push(0x21); body.push(0x01);  // local.set 1
      
      body.push(0x20); body.push(0x00);  // local.get 0 (counter)
      body.push(0x41); body.push(0x01);  // i32.const 1
      body.push(0x6a);                    // i32.add
      body.push(0x22); body.push(0x00);  // local.tee 0
      
      body.push(0x41); body.push(0x0b);  // i32.const 11
      body.push(0x49);                    // i32.ne
      body.push(0x0d); body.push(0x00);  // br_if 0
    body.push(0x0b);                      // end loop
    
    body.push(0x20); body.push(0x01);    // local.get 1
    body.push(0x0b);                      // end function
    
    println!("Function body size: {} bytes", body.len());
    
    // Code section
    wasm.push(0x0a); // section id
    wasm.push((1 + 1 + body.len()) as u8); // section length
    wasm.push(0x01); // number of functions
    wasm.push(body.len() as u8); // function body size
    wasm.extend(&body);
    
    println!("Total WASM size: {} bytes", wasm.len());
    
    // Write file
    std::fs::write("test_binaries/loop_fixed.wasm", &wasm).unwrap();
    
    // Validate
    let validate = std::process::Command::new("wasmer")
        .args(&["validate", "test_binaries/loop_fixed.wasm"])
        .output()
        .unwrap();
    
    if validate.status.success() {
        println!("✅ Validation passed!");
        
        // Run it
        let run = std::process::Command::new("wasmer")
            .args(&["run", "test_binaries/loop_fixed.wasm", "--invoke", "main"])
            .output()
            .unwrap();
        
        let result = String::from_utf8_lossy(&run.stdout).trim().to_string();
        println!("\nExecution result: {} {}", result,
            if result == "55" { "✅" } else { "❌" });
    } else {
        println!("❌ Validation failed:");
        println!("{}", String::from_utf8_lossy(&validate.stderr));
    }
}