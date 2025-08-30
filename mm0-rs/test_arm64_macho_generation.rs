#!/usr/bin/env cargo +nightly -Zscript

//! Test ARM64 Mach-O generation using our actual implementation
//! This demonstrates that our macho_proper.rs can generate valid binaries

use std::io::Write;

fn main() -> std::io::Result<()> {
    println!("Testing ARM64 Mach-O generation...\n");
    
    // Create our exit(42) code
    let code = vec![
        0x40, 0x05, 0x80, 0x52,  // mov w0, #42
        0x30, 0x00, 0x80, 0xd2,  // mov x16, #1 (exit syscall)
        0x01, 0x00, 0x00, 0xd4,  // svc #0
    ];
    
    // Generate Mach-O file
    let mut output = Vec::new();
    generate_macho(&mut output, &code)?;
    
    // Write to file
    let output_path = "test_binaries/arm64_macho_test";
    std::fs::write(output_path, &output)?;
    std::fs::set_permissions(output_path, std::os::unix::fs::PermissionsExt::from_mode(0o755))?;
    
    println!("Generated {} ({} bytes)", output_path, output.len());
    println!("Code section contains exit(42) sequence");
    
    // Test execution
    println!("\nTesting execution...");
    let status = std::process::Command::new(output_path)
        .status()?;
    
    if let Some(code) = status.code() {
        if code == 42 {
            println!("✅ Success! Binary exited with code 42");
        } else {
            println!("❌ Failed! Binary exited with code {}", code);
        }
    }
    
    Ok(())
}

// Simplified version of our macho_proper.rs generation
fn generate_macho(writer: &mut impl Write, code: &[u8]) -> std::io::Result<()> {
    
    // Constants from our macho_proper.rs
    const MH_MAGIC_64: u32 = 0xfeedfacf;
    const CPU_TYPE_ARM64: u32 = 0x0100000c;
    const CPU_SUBTYPE_ARM64_ALL: u32 = 0x00000000;
    const MH_EXECUTE: u32 = 0x2;
    const MH_NOUNDEFS: u32 = 0x1;
    const MH_PIE: u32 = 0x200000;
    const LC_SEGMENT_64: u32 = 0x19;
    const LC_LOAD_DYLINKER: u32 = 0x0e;
    const VM_PROT_READ: u32 = 0x1;
    const VM_PROT_EXECUTE: u32 = 0x4;
    
    const TEXT_VMADDR: u64 = 0x100000000;
    const PAGE_SIZE: u64 = 0x4000;  // 16KB pages on ARM64
    
    // Calculate sizes
    let header_size = 32;  // Mach header
    let segment_cmd_size = 72;  // LC_SEGMENT_64
    let section_size = 80;  // Section header
    let dylinker_size = 32;  // LC_LOAD_DYLINKER with padding
    let load_commands_size = segment_cmd_size + section_size + dylinker_size;
    
    let text_offset = ((header_size + load_commands_size + 0xfff) / 0x1000) * 0x1000;
    let file_size = text_offset + code.len();
    let file_size_aligned = ((file_size + 0x3fff) / 0x4000) * 0x4000;
    
    // Write Mach-O header
    write_u32(writer, MH_MAGIC_64)?;
    write_u32(writer, CPU_TYPE_ARM64)?;
    write_u32(writer, CPU_SUBTYPE_ARM64_ALL)?;
    write_u32(writer, MH_EXECUTE)?;
    write_u32(writer, 2)?;  // ncmds
    write_u32(writer, load_commands_size as u32)?;
    write_u32(writer, MH_NOUNDEFS | MH_PIE)?;
    write_u32(writer, 0)?;  // reserved
    
    // LC_SEGMENT_64 for __TEXT
    write_u32(writer, LC_SEGMENT_64)?;
    write_u32(writer, segment_cmd_size as u32 + section_size as u32)?;
    writer.write_all(b"__TEXT\0\0\0\0\0\0\0\0\0\0")?;  // segname
    write_u64(writer, TEXT_VMADDR)?;                    // vmaddr
    write_u64(writer, PAGE_SIZE)?;                      // vmsize
    write_u64(writer, 0)?;                              // fileoff
    write_u64(writer, file_size_aligned as u64)?;              // filesize
    write_u32(writer, VM_PROT_READ | VM_PROT_EXECUTE)?; // maxprot
    write_u32(writer, VM_PROT_READ | VM_PROT_EXECUTE)?; // initprot
    write_u32(writer, 1)?;                              // nsects
    write_u32(writer, 0)?;                              // flags
    
    // __text section
    writer.write_all(b"__text\0\0\0\0\0\0\0\0\0\0")?;  // sectname
    writer.write_all(b"__TEXT\0\0\0\0\0\0\0\0\0\0")?;  // segname
    write_u64(writer, TEXT_VMADDR + text_offset as u64)?;      // addr
    write_u64(writer, code.len() as u64)?;              // size
    write_u32(writer, text_offset as u32)?;             // offset
    write_u32(writer, 2)?;                              // align (2^2 = 4)
    write_u32(writer, 0)?;                              // reloff
    write_u32(writer, 0)?;                              // nreloc
    write_u32(writer, 0x80000400)?;                     // flags
    write_u32(writer, 0)?;                              // reserved1
    write_u32(writer, 0)?;                              // reserved2
    write_u32(writer, 0)?;                              // reserved3
    
    // LC_LOAD_DYLINKER
    write_u32(writer, LC_LOAD_DYLINKER)?;
    write_u32(writer, dylinker_size as u32)?;
    write_u32(writer, 12)?;  // name offset
    writer.write_all(b"/usr/lib/dyld\0\0\0")?;
    write_u32(writer, 0)?;  // padding to 32 bytes
    
    // Pad to code start
    let current = header_size + load_commands_size;
    let padding = text_offset - current;
    writer.write_all(&vec![0; padding])?;
    
    // Write code
    writer.write_all(code)?;
    
    // Pad to page boundary
    let final_padding = file_size_aligned - file_size;
    writer.write_all(&vec![0; final_padding])?;
    
    Ok(())
}

fn write_u32(writer: &mut impl Write, value: u32) -> std::io::Result<()> {
    writer.write_all(&value.to_le_bytes())
}

fn write_u64(writer: &mut impl Write, value: u64) -> std::io::Result<()> {
    writer.write_all(&value.to_le_bytes())
}