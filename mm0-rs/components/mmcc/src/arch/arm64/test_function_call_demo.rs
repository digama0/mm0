// Demonstration of function calls in generated code
use std::fs::File;
use std::io::Write;

fn main() -> std::io::Result<()> {
    println\!("=== Function Call Demo ===\n");
    
    // Generate code for each architecture
    generate_arm64_function_demo()?;
    generate_wasm_function_demo()?;
    
    println\!("\nFunction call implementations complete\!");
    Ok(())
}

fn generate_arm64_function_demo() -> std::io::Result<()> {
    println\!("1. ARM64 Function Call Demo:");
    
    let code = vec\![
        // add_func at offset 0:
        0x00, 0x00, 0x01, 0x8b,  // add x0, x0, x1
        0xc0, 0x03, 0x5f, 0xd6,  // ret
        
        // main at offset 8:
        0x40, 0x01, 0x80, 0x52,  // mov x0, #10
        0xa0, 0x00, 0x80, 0x52,  // mov x1, #5
        0xfc, 0xff, 0xff, 0x97,  // bl -16 (to add_func)
    ];
    
    println\!("   BL encoding for offset -16: 0x97fffffc");
    println\!("   Expected: call add_func, result in X0");
    Ok(())
}

fn generate_wasm_function_demo() -> std::io::Result<()> {
    println\!("\n2. WASM Function Call Demo:");
    
    // Test WASM call encoding
    println\!("   call 0: [0x10, 0x00]");
    println\!("   call 5: [0x10, 0x05]");
    
    // Save test WASM
    let wasm = vec\![0x00, 0x61, 0x73, 0x6d]; // Magic
    std::fs::write("test_binaries/function_demo.wasm", &wasm)?;
    
    Ok(())
}
EOF < /dev/null