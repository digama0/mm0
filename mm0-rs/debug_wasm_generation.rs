// Debug WASM generation to find the truncation issue

fn main() {
    println!("=== Debugging WASM Generation ===\n");
    
    // Build WASM byte by byte with verification
    let mut wasm = Vec::new();
    let mut offset = 0;
    
    // Magic and version (8 bytes)
    let header = vec![0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];
    wasm.extend(&header);
    println!("Header: {} bytes at offset 0x{:02x}", header.len(), offset);
    offset += header.len();
    
    // Type section
    let type_section = vec![
        0x01, // section id
        0x05, // section length (should contain 5 bytes after this)
        0x01, // number of types
        0x60, // function type
        0x00, // no params
        0x01, // one result
        0x7f, // i32 result
    ];
    wasm.extend(&type_section);
    println!("Type section: {} bytes at offset 0x{:02x}", type_section.len(), offset);
    println!("  Section data length: {} (declared: {})", type_section.len() - 2, type_section[1]);
    offset += type_section.len();
    
    // Function section
    let func_section = vec![
        0x03, // section id
        0x02, // section length
        0x01, // number of functions
        0x00, // function 0 has type 0
    ];
    wasm.extend(&func_section);
    println!("Function section: {} bytes at offset 0x{:02x}", func_section.len(), offset);
    println!("  Section data length: {} (declared: {})", func_section.len() - 2, func_section[1]);
    offset += func_section.len();
    
    // Export section
    let export_section = vec![
        0x07, // section id
        0x08, // section length
        0x01, // number of exports
        0x04, // string length
        0x6d, 0x61, 0x69, 0x6e, // "main"
        0x00, // export kind (function)
        0x00, // function index
    ];
    wasm.extend(&export_section);
    println!("Export section: {} bytes at offset 0x{:02x}", export_section.len(), offset);
    println!("  Section data length: {} (declared: {})", export_section.len() - 2, export_section[1]);
    offset += export_section.len();
    
    // Code section
    let code_body = vec![
        0x00, // number of locals
        0x41, 0x0a,       // i32.const 10
        0x41, 0x05,       // i32.const 5
        0x6a,             // i32.add
        0x41, 0x03,       // i32.const 3
        0x6c,             // i32.mul
        0x41, 0x02,       // i32.const 2
        0x6b,             // i32.sub
        0x0b,             // end
    ];
    
    let code_section = vec![
        0x0a, // section id
        0x0e, // section length (14 bytes)
        0x01, // number of functions
        0x0c, // function body size (12 bytes)
    ];
    
    let mut full_code_section = code_section.clone();
    full_code_section.extend(&code_body);
    
    wasm.extend(&full_code_section);
    println!("Code section: {} bytes at offset 0x{:02x}", full_code_section.len(), offset);
    println!("  Section header: {} bytes", code_section.len());
    println!("  Function body: {} bytes (declared: {})", code_body.len(), code_section[3]);
    println!("  Total section data: {} bytes (declared: {})", 
        full_code_section.len() - 2, code_section[1]);
    offset += full_code_section.len();
    
    println!("\nTotal WASM size: {} bytes (0x{:02x})", wasm.len(), wasm.len());
    
    // Write the file
    std::fs::write("test_binaries/calc_debug.wasm", &wasm).unwrap();
    println!("\nWrote test_binaries/calc_debug.wasm");
    
    // Verify with hexdump
    println!("\nHexdump of generated file:");
    std::process::Command::new("hexdump")
        .args(&["-C", "test_binaries/calc_debug.wasm"])
        .status()
        .unwrap();
    
    // Try to validate
    println!("\nValidation results:");
    let validate = std::process::Command::new("wasmer")
        .args(&["validate", "test_binaries/calc_debug.wasm"])
        .output()
        .unwrap();
    
    if validate.status.success() {
        println!("✅ WASM validation passed!");
        
        // Try to run it
        println!("\nExecution test:");
        let run = std::process::Command::new("wasmer")
            .args(&["run", "test_binaries/calc_debug.wasm", "--invoke", "main"])
            .output()
            .unwrap();
        
        println!("Exit code: {}", run.status.code().unwrap_or(-1));
        if !run.stdout.is_empty() {
            println!("Stdout: {}", String::from_utf8_lossy(&run.stdout));
        }
        if !run.stderr.is_empty() {
            println!("Stderr: {}", String::from_utf8_lossy(&run.stderr));
        }
    } else {
        println!("❌ WASM validation failed:");
        println!("{}", String::from_utf8_lossy(&validate.stderr));
    }
}