// Generate and test loop implementations for all architectures
// Computes: sum of 1 to 10 = 55

use std::fs;
use std::process::Command;

fn main() -> std::io::Result<()> {
    println!("=== Generating Loop Binaries ===\n");
    
    generate_arm64_loop()?;
    generate_x86_loop()?;
    generate_wasm_loop()?;
    
    println!("\nTesting generated binaries...\n");
    test_binaries();
    
    Ok(())
}

fn generate_arm64_loop() -> std::io::Result<()> {
    println!("1. Generating ARM64 loop binary...");
    
    // Simple Rust implementation for ARM64
    let rust_code = r#"
fn main() {
    let mut sum = 0;
    for i in 1..=10 {
        sum += i;
    }
    std::process::exit(sum);
}
"#;
    
    fs::write("test_binaries/loop_arm64.rs", rust_code)?;
    
    // Compile it
    Command::new("rustc")
        .args(&["-o", "test_binaries/loop_arm64", "test_binaries/loop_arm64.rs"])
        .status()?;
    
    println!("   Generated: test_binaries/loop_arm64");
    
    Ok(())
}

fn generate_x86_loop() -> std::io::Result<()> {
    println!("2. Generating x86-64 loop binary...");
    
    // Create ELF with loop: sum 1 to 10
    let mut elf = Vec::new();
    
    // ELF header (64 bytes)
    elf.extend(b"\x7fELF");                    // Magic
    elf.push(2); elf.push(1); elf.push(1);     // 64-bit, little-endian, v1
    elf.extend(&[0; 9]);                        // padding
    elf.extend(&2u16.to_le_bytes());            // e_type: ET_EXEC
    elf.extend(&62u16.to_le_bytes());           // e_machine: EM_X86_64
    elf.extend(&1u32.to_le_bytes());            // e_version
    elf.extend(&0x400078u64.to_le_bytes());     // e_entry
    elf.extend(&64u64.to_le_bytes());           // e_phoff
    elf.extend(&0u64.to_le_bytes());            // e_shoff
    elf.extend(&0u32.to_le_bytes());            // e_flags
    elf.extend(&64u16.to_le_bytes());           // e_ehsize
    elf.extend(&56u16.to_le_bytes());           // e_phentsize
    elf.extend(&1u16.to_le_bytes());            // e_phnum
    elf.extend(&0u16.to_le_bytes());            // e_shentsize
    elf.extend(&0u16.to_le_bytes());            // e_shnum
    elf.extend(&0u16.to_le_bytes());            // e_shstrndx
    
    // Program header (56 bytes)
    elf.extend(&1u32.to_le_bytes());            // p_type: PT_LOAD
    elf.extend(&5u32.to_le_bytes());            // p_flags: PF_R | PF_X
    elf.extend(&0u64.to_le_bytes());            // p_offset
    elf.extend(&0x400000u64.to_le_bytes());     // p_vaddr
    elf.extend(&0x400000u64.to_le_bytes());     // p_paddr
    elf.extend(&0xc0u64.to_le_bytes());         // p_filesz
    elf.extend(&0xc0u64.to_le_bytes());         // p_memsz
    elf.extend(&0x1000u64.to_le_bytes());       // p_align
    
    // Code at offset 0x78 (entry point)
    // Loop to sum 1 to 10
    let code = vec![
        // Initialize
        0x48, 0xc7, 0xc1, 0x01, 0x00, 0x00, 0x00,  // mov rcx, 1    ; counter
        0x48, 0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00,  // mov rax, 0    ; sum
        
        // Loop start
        0x48, 0x01, 0xc8,              // add rax, rcx  ; sum += counter
        0x48, 0xff, 0xc1,              // inc rcx       ; counter++
        0x48, 0x83, 0xf9, 0x0b,        // cmp rcx, 11   ; counter vs 11
        0x75, 0xf5,                    // jne -11       ; loop if != 11
        
        // Exit with sum
        0x48, 0x89, 0xc7,              // mov rdi, rax  ; exit code = sum
        0x48, 0xc7, 0xc0, 0x3c, 0x00, 0x00, 0x00,  // mov rax, 60   ; sys_exit
        0x0f, 0x05,                    // syscall
    ];
    elf.extend(&code);
    
    // Pad to file size
    while elf.len() < 0xc0 {
        elf.push(0);
    }
    
    fs::write("test_binaries/loop_x86", &elf)?;
    fs::set_permissions("test_binaries/loop_x86", 
        std::os::unix::fs::PermissionsExt::from_mode(0o755))?;
    
    println!("   Generated: test_binaries/loop_x86");
    
    Ok(())
}

fn generate_wasm_loop() -> std::io::Result<()> {
    println!("3. Generating WebAssembly loop module...");
    
    let wasm = vec![
        // Magic and version
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
        
        // Type section
        0x01, // section id
        0x05, // section length
        0x01, // number of types
        0x60, // function type
        0x00, // no params
        0x01, // one result
        0x7f, // i32 result
        
        // Function section
        0x03, // section id
        0x02, // section length
        0x01, // number of functions
        0x00, // function 0 has type 0
        
        // Export section
        0x07, // section id
        0x08, // section length
        0x01, // number of exports
        0x04, // string length
        0x6d, 0x61, 0x69, 0x6e, // "main"
        0x00, // export kind (function)
        0x00, // function index
        
        // Code section
        0x0a, // section id
        0x1d, // section length (29 bytes)
        0x01, // number of functions
        0x1b, // function body size (27 bytes)
        0x02, 0x01, 0x7f, 0x01, 0x7f, // 2 locals: counter, sum (both i32)
        
        // Function body: sum 1 to 10
        0x41, 0x01,          // i32.const 1
        0x21, 0x00,          // local.set 0 (counter = 1)
        0x41, 0x00,          // i32.const 0
        0x21, 0x01,          // local.set 1 (sum = 0)
        
        // Loop
        0x03, 0x40,          // loop (blocktype void)
          0x20, 0x01,        // local.get 1 (sum)
          0x20, 0x00,        // local.get 0 (counter)
          0x6a,              // i32.add
          0x21, 0x01,        // local.set 1 (sum += counter)
          
          0x20, 0x00,        // local.get 0 (counter)
          0x41, 0x01,        // i32.const 1
          0x6a,              // i32.add
          0x22, 0x00,        // local.tee 0 (counter++ and keep on stack)
          
          0x41, 0x0b,        // i32.const 11
          0x49,              // i32.ne (not equal)
          0x0d, 0x00,        // br_if 0 (loop if counter != 11)
        0x0b,                // end loop
        
        0x20, 0x01,          // local.get 1 (return sum)
        0x0b,                // end function
    ];
    
    fs::write("test_binaries/loop.wasm", &wasm)?;
    println!("   Generated: test_binaries/loop.wasm");
    
    Ok(())
}

fn test_binaries() {
    // Test ARM64
    if Command::new("uname").arg("-m").output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim() == "arm64")
        .unwrap_or(false) 
    {
        println!("Testing ARM64 loop:");
        match Command::new("test_binaries/loop_arm64").status() {
            Ok(status) => {
                if let Some(code) = status.code() {
                    println!("   Exit code: {} {}", code, 
                        if code == 55 { "✅" } else { "❌" });
                }
            }
            Err(e) => println!("   Failed to run: {}", e),
        }
    }
    
    // Test x86
    println!("\nTesting x86-64 loop:");
    println!("   (Requires Linux environment)");
    
    // Test WASM
    println!("\nTesting WASM loop:");
    match Command::new("wasmer")
        .args(&["run", "test_binaries/loop.wasm", "--invoke", "main"])
        .output()
    {
        Ok(output) => {
            let result = String::from_utf8_lossy(&output.stdout).trim().to_string();
            println!("   Wasmer output: {} {}", result,
                if result == "55" { "✅" } else { "❌" });
        }
        Err(_) => {
            // Try wasmtime
            match Command::new("wasmtime")
                .args(&["run", "test_binaries/loop.wasm", "--invoke", "main"])
                .output()
            {
                Ok(output) => {
                    let result = String::from_utf8_lossy(&output.stdout);
                    println!("   Wasmtime result: {}", result.trim());
                }
                Err(_) => println!("   No WASM runtime available"),
            }
        }
    }
}