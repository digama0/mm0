// Test complete ARM64 Mach-O generation
use std::io::Write;
use std::fs::File;

fn main() -> std::io::Result<()> {
    println!("Testing complete ARM64 Mach-O generation...\n");
    
    // Let's use the exact code from our working macho_proper.rs
    // This creates: mov w0, #42; mov x16, #1; svc #0
    let code = vec![
        0x40, 0x05, 0x80, 0x52,  // mov w0, #42
        0x30, 0x00, 0x80, 0xd2,  // mov x16, #1 
        0x01, 0x00, 0x00, 0xd4,  // svc #0
    ];
    
    let output_path = "test_binaries/arm64_working_test";
    
    // Create binary using our exact macho_proper.rs logic
    create_macho_file(output_path, &code)?;
    
    // Test execution
    println!("Testing execution of {}...", output_path);
    match std::process::Command::new(output_path).status() {
        Ok(status) => {
            if let Some(code) = status.code() {
                if code == 42 {
                    println!("✅ Success! ARM64 binary exited with code 42");
                } else {
                    println!("❌ Binary exited with code {} (expected 42)", code);
                }
            }
        }
        Err(e) => {
            println!("❌ Failed to execute: {}", e);
            
            // Debug with file command
            let output = std::process::Command::new("file")
                .arg(output_path)
                .output()?;
            println!("File type: {}", String::from_utf8_lossy(&output.stdout));
        }
    }
    
    Ok(())
}

fn create_macho_file(path: &str, code: &[u8]) -> std::io::Result<()> {
    use std::io::Cursor;
    
    // First create the binary in memory exactly as macho_proper.rs does
    let mut buffer = Vec::new();
    
    // Constants from macho_proper.rs
    const TEXT_START: u32 = 0x4000;
    
    // Write the exact header as in macho_proper.rs
    buffer.extend_from_slice(&[
        0xcf, 0xfa, 0xed, 0xfe,  // MH_MAGIC_64
        0x0c, 0x00, 0x00, 0x01,  // CPU_TYPE_ARM64  
        0x00, 0x00, 0x00, 0x00,  // CPU_SUBTYPE_ARM64_ALL
        0x02, 0x00, 0x00, 0x00,  // MH_EXECUTE
        0x02, 0x00, 0x00, 0x00,  // ncmds = 2
        0xb8, 0x00, 0x00, 0x00,  // sizeofcmds = 184
        0x01, 0x00, 0x20, 0x00,  // flags = MH_NOUNDEFS | MH_PIE
        0x00, 0x00, 0x00, 0x00,  // reserved
    ]);
    
    // LC_SEGMENT_64 command
    buffer.extend_from_slice(&[
        0x19, 0x00, 0x00, 0x00,  // LC_SEGMENT_64
        0x98, 0x00, 0x00, 0x00,  // cmdsize = 152
    ]);
    buffer.extend_from_slice(b"__TEXT\0\0\0\0\0\0\0\0\0\0");  // segname
    buffer.extend_from_slice(&[
        0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,  // vmaddr = 0x100000000
        0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // vmsize = 0x4000
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // fileoff = 0
        0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // filesize = 0x4000
        0x05, 0x00, 0x00, 0x00,  // maxprot = VM_PROT_READ | VM_PROT_EXECUTE
        0x05, 0x00, 0x00, 0x00,  // initprot = VM_PROT_READ | VM_PROT_EXECUTE
        0x01, 0x00, 0x00, 0x00,  // nsects = 1
        0x00, 0x00, 0x00, 0x00,  // flags = 0
    ]);
    
    // __text section
    buffer.extend_from_slice(b"__text\0\0\0\0\0\0\0\0\0\0");  // sectname
    buffer.extend_from_slice(b"__TEXT\0\0\0\0\0\0\0\0\0\0");  // segname
    buffer.extend_from_slice(&[
        0x00, 0x40, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,  // addr = 0x100004000
    ]);
    buffer.extend_from_slice(&(code.len() as u64).to_le_bytes());  // size
    buffer.extend_from_slice(&[
        0x00, 0x40, 0x00, 0x00,  // offset = 0x4000
        0x02, 0x00, 0x00, 0x00,  // align = 2
        0x00, 0x00, 0x00, 0x00,  // reloff = 0
        0x00, 0x00, 0x00, 0x00,  // nreloc = 0
        0x00, 0x04, 0x00, 0x80,  // flags
        0x00, 0x00, 0x00, 0x00,  // reserved1
        0x00, 0x00, 0x00, 0x00,  // reserved2
        0x00, 0x00, 0x00, 0x00,  // reserved3
    ]);
    
    // LC_LOAD_DYLINKER
    buffer.extend_from_slice(&[
        0x0e, 0x00, 0x00, 0x00,  // LC_LOAD_DYLINKER
        0x20, 0x00, 0x00, 0x00,  // cmdsize = 32
        0x0c, 0x00, 0x00, 0x00,  // name offset = 12
    ]);
    buffer.extend_from_slice(b"/usr/lib/dyld\0\0\0");
    buffer.extend_from_slice(&[0x00, 0x00, 0x00, 0x00]);  // padding
    
    // Pad to TEXT_START
    while buffer.len() < TEXT_START as usize {
        buffer.push(0);
    }
    
    // Add code
    buffer.extend_from_slice(code);
    
    // Pad to page size
    while buffer.len() < 0x4000 {
        buffer.push(0);
    }
    
    // Write file
    std::fs::write(path, &buffer)?;
    std::fs::set_permissions(path, std::os::unix::fs::PermissionsExt::from_mode(0o755))?;
    
    println!("Created {} ({} bytes)", path, buffer.len());
    
    Ok(())
}