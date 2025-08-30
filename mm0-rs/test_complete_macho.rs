#!/usr/bin/env cargo +nightly -Zscript

//! Test complete ARM64 Mach-O generation using the proper implementation

use std::io::Write;
use std::fs::File;

fn main() -> std::io::Result<()> {
    println!("Testing complete ARM64 Mach-O generation...\n");
    
    // Create exit(42) code
    let code = vec![
        0x40, 0x05, 0x80, 0x52,  // mov w0, #42
        0x30, 0x00, 0x80, 0xd2,  // mov x16, #1 
        0x01, 0x00, 0x00, 0xd4,  // svc #0
    ];
    
    // Create a simple test using the pattern from macho_proper.rs
    let output_path = "test_binaries/arm64_complete_test";
    let mut file = File::create(output_path)?;
    
    // Write a minimal but complete Mach-O based on macho_proper.rs
    write_complete_macho(&mut file, &code)?;
    
    // Make executable
    std::fs::set_permissions(output_path, std::os::unix::fs::PermissionsExt::from_mode(0o755))?;
    
    println!("Generated: {}", output_path);
    println!("\nNow testing with otool to verify structure...");
    
    // Verify with otool
    let output = std::process::Command::new("otool")
        .arg("-h")  // Show header
        .arg(output_path)
        .output()?;
    
    println!("Header info:\n{}", String::from_utf8_lossy(&output.stdout));
    
    // Test execution
    println!("Testing execution...");
    match std::process::Command::new(output_path).status() {
        Ok(status) => {
            if let Some(code) = status.code() {
                if code == 42 {
                    println!("✅ Success! Binary exited with code 42");
                } else {
                    println!("❌ Binary exited with code {} (expected 42)", code);
                }
            }
        }
        Err(e) => {
            println!("❌ Failed to execute: {}", e);
            
            // Try to get more info
            println!("\nChecking load commands with otool -l:");
            let output = std::process::Command::new("otool")
                .arg("-l")
                .arg(output_path)
                .output()?;
            println!("{}", String::from_utf8_lossy(&output.stdout));
        }
    }
    
    Ok(())
}

// Based on the working implementation in macho_proper.rs
fn write_complete_macho(writer: &mut impl Write, code: &[u8]) -> std::io::Result<()> {
    use byteorder::{LittleEndian, WriteBytesExt};
    
    // Constants
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
    
    // Mach-O header (32 bytes)
    writer.write_u32::<LittleEndian>(MH_MAGIC_64)?;
    writer.write_u32::<LittleEndian>(CPU_TYPE_ARM64)?;
    writer.write_u32::<LittleEndian>(CPU_SUBTYPE_ARM64_ALL)?;
    writer.write_u32::<LittleEndian>(MH_EXECUTE)?;
    writer.write_u32::<LittleEndian>(2)?;  // ncmds
    writer.write_u32::<LittleEndian>(184)?; // sizeofcmds: segment(72) + section(80) + dylinker(32)
    writer.write_u32::<LittleEndian>(MH_NOUNDEFS | MH_PIE)?;
    writer.write_u32::<LittleEndian>(0)?;   // reserved
    
    // LC_SEGMENT_64 command
    writer.write_u32::<LittleEndian>(LC_SEGMENT_64)?;
    writer.write_u32::<LittleEndian>(152)?; // cmdsize: 72 + 80
    writer.write_all(b"__TEXT\0\0\0\0\0\0\0\0\0\0")?;
    writer.write_u64::<LittleEndian>(0x100000000)?; // vmaddr
    writer.write_u64::<LittleEndian>(0x4000)?;      // vmsize (16KB)
    writer.write_u64::<LittleEndian>(0)?;           // fileoff
    writer.write_u64::<LittleEndian>(0x4000)?;      // filesize
    writer.write_u32::<LittleEndian>(VM_PROT_READ | VM_PROT_EXECUTE)?; // maxprot
    writer.write_u32::<LittleEndian>(VM_PROT_READ | VM_PROT_EXECUTE)?; // initprot
    writer.write_u32::<LittleEndian>(1)?;   // nsects
    writer.write_u32::<LittleEndian>(0)?;   // flags
    
    // __text section
    writer.write_all(b"__text\0\0\0\0\0\0\0\0\0\0")?;
    writer.write_all(b"__TEXT\0\0\0\0\0\0\0\0\0\0")?;
    writer.write_u64::<LittleEndian>(0x100004000)?; // addr (after headers)
    writer.write_u64::<LittleEndian>(code.len() as u64)?; // size
    writer.write_u32::<LittleEndian>(0x4000)?;      // offset
    writer.write_u32::<LittleEndian>(2)?;           // align (2^2)
    writer.write_u32::<LittleEndian>(0)?;           // reloff
    writer.write_u32::<LittleEndian>(0)?;           // nreloc
    writer.write_u32::<LittleEndian>(0x80000400)?;  // flags
    writer.write_u32::<LittleEndian>(0)?;           // reserved1
    writer.write_u32::<LittleEndian>(0)?;           // reserved2
    writer.write_u32::<LittleEndian>(0)?;           // reserved3
    
    // LC_LOAD_DYLINKER (32 bytes total with padding)
    writer.write_u32::<LittleEndian>(LC_LOAD_DYLINKER)?;
    writer.write_u32::<LittleEndian>(32)?;  // cmdsize
    writer.write_u32::<LittleEndian>(12)?;  // name offset
    writer.write_all(b"/usr/lib/dyld\0\0\0")?;
    writer.write_u32::<LittleEndian>(0)?;   // padding to 32 bytes
    
    // Pad to 0x4000 (16KB page boundary)
    let header_size = 32 + 184; // mach header + load commands
    let padding = 0x4000 - header_size;
    writer.write_all(&vec![0; padding])?;
    
    // Write code at 0x4000
    writer.write_all(code)?;
    
    // Pad to page boundary
    let code_padding = 0x4000 - code.len();
    writer.write_all(&vec![0; code_padding])?;
    
    Ok(())
}

// Add dependencies for cargo script
/*
[dependencies]
byteorder = "1.5"
*/