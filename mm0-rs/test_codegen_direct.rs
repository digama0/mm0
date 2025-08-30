#!/usr/bin/env cargo +nightly -Zscript

//! Direct code generation test for all architectures
//! This bypasses the MM1 compiler and directly generates exit(42) for each architecture

use std::fs::File;
use std::io::Write;
use std::path::Path;

fn main() {
    println!("=== Direct Code Generation Test ===\n");
    
    // Test x86-64 code generation
    test_x86_64();
    
    // Test ARM64 code generation
    test_arm64();
    
    // Test WASM code generation
    test_wasm();
    
    println!("\n=== Summary ===");
    println!("This test demonstrates direct code generation for each architecture.");
    println!("Next step: Integrate this with the MM1 compiler pipeline.");
}

fn test_x86_64() {
    println!("1. x86-64 Linux ELF:");
    
    // Minimal ELF that does: mov rax, 60; mov rdi, 42; syscall
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
    elf.extend(&0x84u64.to_le_bytes());         // p_filesz
    elf.extend(&0x84u64.to_le_bytes());         // p_memsz
    elf.extend(&0x1000u64.to_le_bytes());       // p_align
    
    // Code at offset 0x78 (entry point)
    let code = [
        0x48, 0xc7, 0xc0, 0x3c, 0x00, 0x00, 0x00,  // mov rax, 60 (sys_exit)
        0x48, 0xc7, 0xc7, 0x2a, 0x00, 0x00, 0x00,  // mov rdi, 42
        0x0f, 0x05,                                  // syscall
    ];
    elf.extend(&code);
    
    // Write to file
    let path = "test_binaries/direct_x86_64";
    std::fs::write(path, &elf).unwrap();
    std::fs::set_permissions(path, std::os::unix::fs::PermissionsExt::from_mode(0o755)).unwrap();
    
    println!("   Generated: {} ({} bytes)", path, elf.len());
    println!("   Code: mov rax, 60; mov rdi, 42; syscall");
    println!("   Expected: exit(42)");
}

fn test_arm64() {
    println!("\n2. ARM64 macOS Mach-O:");
    
    // For now, use the encoding from our encode.rs
    // In real implementation, this would use our macho_proper.rs
    
    let code = vec![
        // mov w0, #42
        0x40, 0x05, 0x80, 0x52,
        // mov x16, #1 (exit syscall)
        0x30, 0x00, 0x80, 0xd2,
        // svc #0
        0x01, 0x00, 0x00, 0xd4,
    ];
    
    println!("   Code bytes: {:02x?}", code);
    println!("   Instructions:");
    println!("     mov w0, #42      ; 52800540");
    println!("     mov x16, #1      ; d2800030");
    println!("     svc #0           ; d4000001");
    println!("   Expected: exit(42)");
    
    // Note: Full Mach-O generation would use our macho_proper.rs
    println!("   (Full Mach-O binary generation available in macho_proper.rs)");
}

fn test_wasm() {
    println!("\n3. WebAssembly:");
    
    let mut wasm = Vec::new();
    
    // WASM header
    wasm.extend(b"\0asm");                      // Magic
    wasm.extend(&[1, 0, 0, 0]);                 // Version 1
    
    // Type section (id=1)
    wasm.push(0x01);                            // Section ID
    wasm.push(0x05);                            // Section size
    wasm.push(0x01);                            // Number of types
    wasm.extend(&[0x60, 0x00, 0x01, 0x7f]);     // func type: [] -> [i32]
    
    // Function section (id=3)
    wasm.push(0x03);                            // Section ID
    wasm.push(0x02);                            // Section size
    wasm.push(0x01);                            // Number of functions
    wasm.push(0x00);                            // Function 0 uses type 0
    
    // Export section (id=7)
    wasm.push(0x07);                            // Section ID
    wasm.push(0x08);                            // Section size
    wasm.push(0x01);                            // Number of exports
    wasm.push(0x04);                            // String length
    wasm.extend(b"main");                       // Export name
    wasm.push(0x00);                            // Export kind: function
    wasm.push(0x00);                            // Function index
    
    // Code section (id=10)
    wasm.push(0x0a);                            // Section ID
    wasm.push(0x06);                            // Section size
    wasm.push(0x01);                            // Number of functions
    wasm.push(0x04);                            // Function body size
    wasm.push(0x00);                            // Local declarations count
    wasm.push(0x41);                            // i32.const
    wasm.push(0x2a);                            // 42 (LEB128)
    wasm.push(0x0b);                            // end
    
    // Write to file
    let path = "test_binaries/direct.wasm";
    std::fs::write(path, &wasm).unwrap();
    
    println!("   Generated: {} ({} bytes)", path, wasm.len());
    println!("   Code section: i32.const 42; end");
    println!("   Expected: return 42");
}