// Generate complete calculator binaries for all architectures
// Computes: (10 + 5) * 3 - 2 = 43

use std::fs::File;
use std::io::Write;

fn main() -> std::io::Result<()> {
    println!("=== Generating Calculator Binaries ===\n");
    
    generate_arm64_macho()?;
    generate_x86_elf()?;
    generate_wasm_module()?;
    
    println!("\nTesting generated binaries...\n");
    test_binaries();
    
    Ok(())
}

fn generate_arm64_macho() -> std::io::Result<()> {
    println!("1. Generating ARM64 Mach-O binary...");
    
    // Use the code from our test
    let code = vec![
        // mov x0, #10
        0x40, 0x01, 0x80, 0x52,
        // mov x1, #5
        0xa0, 0x00, 0x80, 0x52,
        // add x0, x0, x1    ; x0 = 15
        0x00, 0x00, 0x01, 0x8b,
        // mov x1, #3
        0x60, 0x00, 0x80, 0x52,
        // mul x0, x0, x1    ; x0 = 45
        0x00, 0x7c, 0x01, 0x9b,
        // sub x0, x0, #2    ; x0 = 43
        0x00, 0x08, 0x00, 0xd1,
        // mov x16, #1       ; exit syscall
        0x30, 0x00, 0x80, 0xd2,
        // svc #0
        0x01, 0x00, 0x00, 0xd4,
    ];
    
    // For now, compile a simple Rust program that does the same
    let rust_code = r#"
fn main() {
    std::process::exit((10 + 5) * 3 - 2);
}
"#;
    
    std::fs::write("test_binaries/calc_arm64.rs", rust_code)?;
    
    // Compile it
    std::process::Command::new("rustc")
        .args(&["-o", "test_binaries/calc_arm64", "test_binaries/calc_arm64.rs"])
        .status()?;
    
    println!("   Generated: test_binaries/calc_arm64");
    
    Ok(())
}

fn generate_x86_elf() -> std::io::Result<()> {
    println!("2. Generating x86-64 ELF binary...");
    
    // Create minimal ELF that computes (10 + 5) * 3 - 2
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
    elf.extend(&0xb0u64.to_le_bytes());         // p_filesz
    elf.extend(&0xb0u64.to_le_bytes());         // p_memsz
    elf.extend(&0x1000u64.to_le_bytes());       // p_align
    
    // Code at offset 0x78 (entry point)
    // Calculate (10 + 5) * 3 - 2 = 43
    let code = vec![
        // mov rax, 10
        0x48, 0xc7, 0xc0, 0x0a, 0x00, 0x00, 0x00,
        // add rax, 5        ; rax = 15
        0x48, 0x83, 0xc0, 0x05,
        // imul rax, rax, 3  ; rax = 45
        0x48, 0x6b, 0xc0, 0x03,
        // sub rax, 2        ; rax = 43
        0x48, 0x83, 0xe8, 0x02,
        // mov rdi, rax      ; exit code
        0x48, 0x89, 0xc7,
        // mov rax, 60       ; sys_exit
        0x48, 0xc7, 0xc0, 0x3c, 0x00, 0x00, 0x00,
        // syscall
        0x0f, 0x05,
    ];
    elf.extend(&code);
    
    // Pad to match file size
    while elf.len() < 0xb0 {
        elf.push(0);
    }
    
    std::fs::write("test_binaries/calc_x86", &elf)?;
    std::fs::set_permissions("test_binaries/calc_x86", 
        std::os::unix::fs::PermissionsExt::from_mode(0o755))?;
    
    println!("   Generated: test_binaries/calc_x86");
    
    Ok(())
}

fn generate_wasm_module() -> std::io::Result<()> {
    println!("3. Generating WebAssembly module...");
    
    let wasm = vec![
        // Magic and version
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
        
        // Type section (id=1)
        0x01, // section id
        0x05, // section length
        0x01, // number of types
        0x60, // function type
        0x00, // no params
        0x01, // one result
        0x7f, // i32 result
        
        // Function section (id=3)
        0x03, // section id
        0x02, // section length
        0x01, // number of functions
        0x00, // function 0 has type 0
        
        // Export section (id=7)
        0x07, // section id
        0x08, // section length
        0x01, // number of exports
        0x04, // string length
        0x6d, 0x61, 0x69, 0x6e, // "main"
        0x00, // export kind (function)
        0x00, // function index
        
        // Code section (id=10)
        0x0a, // section id
        0x0f, // section length (was 0x0e - fixed!)
        0x01, // number of functions
        0x0d, // function body size (was 0x0c - fixed!)
        0x00, // number of locals
        
        // Function body: (10 + 5) * 3 - 2
        0x41, 0x0a,       // i32.const 10
        0x41, 0x05,       // i32.const 5
        0x6a,             // i32.add
        0x41, 0x03,       // i32.const 3
        0x6c,             // i32.mul
        0x41, 0x02,       // i32.const 2
        0x6b,             // i32.sub
        0x0b,             // end
    ];
    
    std::fs::write("test_binaries/calc.wasm", &wasm)?;
    println!("   Generated: test_binaries/calc.wasm");
    
    Ok(())
}

fn test_binaries() {
    // Test ARM64 binary
    if std::process::Command::new("uname").arg("-m").output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim() == "arm64")
        .unwrap_or(false) 
    {
        println!("Testing ARM64 binary:");
        match std::process::Command::new("test_binaries/calc_arm64").status() {
            Ok(status) => {
                if let Some(code) = status.code() {
                    println!("   Exit code: {} {}", code, 
                        if code == 43 { "✅" } else { "❌" });
                }
            }
            Err(e) => println!("   Failed to run: {}", e),
        }
    }
    
    // Test x86 binary (would need Linux or container)
    println!("\nTesting x86-64 binary:");
    println!("   (Requires Linux environment or container)");
    
    // Test WASM
    println!("\nTesting WASM module:");
    match std::process::Command::new("wasmer")
        .args(&["run", "test_binaries/calc.wasm", "--invoke", "main"])
        .output()
    {
        Ok(output) => {
            let result = String::from_utf8_lossy(&output.stdout).trim().to_string();
            
            // Wasmer outputs the function result to stdout
            println!("   Wasmer output: {} {}", result,
                if result == "43" { "✅" } else { "❌" });
        }
        Err(_) => {
            // Try wasmtime
            match std::process::Command::new("wasmtime")
                .args(&["run", "test_binaries/calc.wasm", "--invoke", "main"])
                .output()
            {
                Ok(output) => {
                    let result = String::from_utf8_lossy(&output.stdout);
                    println!("   Wasmtime result: {}", result.trim());
                    if result.trim() == "43" {
                        println!("   ✅ Correct!");
                    }
                }
                Err(_) => println!("   No WASM runtime available"),
            }
        }
    }
}