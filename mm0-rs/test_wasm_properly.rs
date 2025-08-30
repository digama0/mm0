// Test WASM properly by checking stdout, not exit code

fn main() {
    println!("=== Testing WASM Calculator ===\n");
    
    // Test with wasmer
    println!("Testing with wasmer:");
    let wasmer = std::process::Command::new("wasmer")
        .args(&["run", "test_binaries/calc_fixed.wasm", "--invoke", "main"])
        .output()
        .unwrap();
    
    let stdout = String::from_utf8_lossy(&wasmer.stdout);
    let result = stdout.trim();
    println!("  Output: '{}'", result);
    println!("  Result: {} {}", result, if result == "43" { "✅" } else { "❌" });
    
    // Test with wasmtime
    println!("\nTesting with wasmtime:");
    let wasmtime = std::process::Command::new("wasmtime")
        .args(&["run", "test_binaries/calc_fixed.wasm", "--invoke", "main"])
        .output()
        .unwrap();
    
    let stdout = String::from_utf8_lossy(&wasmtime.stdout);
    let result = stdout.trim();
    println!("  Output: '{}'", result);
    println!("  Result: {} {}", result, if result == "43" { "✅" } else { "❌" });
    
    // Now let's fix our original generator to use correct sizes
    println!("\n=== Fixed WASM Generation Code ===");
    println!("The fix needed in generate_calculator_binaries.rs:");
    println!("1. Change function body size from 0x0c to 0x0d (12 to 13)");
    println!("2. Change code section length from 0x0e to 0x0f (14 to 15)");
}