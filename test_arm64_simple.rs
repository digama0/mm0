#!/usr/bin/env rust-script
//! Quick test to generate a minimal ARM64 macOS executable
//! 
//! Run with: rust-script test_arm64_simple.rs
//! Or compile and run: rustc test_arm64_simple.rs && ./test_arm64_simple

use std::fs::File;
use std::io::Write;
use std::os::unix::fs::PermissionsExt;

fn main() {
    // Generate a simple ARM64 program that exits with code 42
    let code = vec![
        // mov x0, #42 (exit code)
        0x40, 0x05, 0x80, 0x52,  // movz w0, #42
        
        // mov x16, #1 (exit syscall number for macOS)
        0x30, 0x00, 0x80, 0xd2,  // movz x16, #1
        
        // svc #0 (make system call)
        0x01, 0x00, 0x00, 0xd4,
    ];
    
    // Minimal Mach-O file for ARM64
    let mut output = Vec::new();
    
    // Mach-O header
    output.extend_from_slice(&[
        0xcf, 0xfa, 0xed, 0xfe,  // MH_MAGIC_64
        0x0c, 0x00, 0x00, 0x01,  // CPU_TYPE_ARM64
        0x00, 0x00, 0x00, 0x00,  // CPU_SUBTYPE_ARM64_ALL
        0x02, 0x00, 0x00, 0x00,  // MH_EXECUTE
        0x02, 0x00, 0x00, 0x00,  // ncmds = 2
        0xb0, 0x00, 0x00, 0x00,  // sizeofcmds
        0x01, 0x00, 0x20, 0x00,  // flags (MH_NOUNDEFS | MH_PIE)
        0x00, 0x00, 0x00, 0x00,  // reserved
    ]);
    
    // LC_SEGMENT_64 __TEXT
    output.extend_from_slice(&[
        0x19, 0x00, 0x00, 0x00,  // LC_SEGMENT_64
        0x98, 0x00, 0x00, 0x00,  // cmdsize
    ]);
    output.extend_from_slice(b"__TEXT\0\0\0\0\0\0\0\0\0\0");  // segname
    output.extend_from_slice(&[
        0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,  // vmaddr = 0x100000000
        0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // vmsize = 0x4000
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // fileoff = 0
        0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // filesize
        0x07, 0x00, 0x00, 0x00,  // maxprot
        0x05, 0x00, 0x00, 0x00,  // initprot
        0x01, 0x00, 0x00, 0x00,  // nsects = 1
        0x00, 0x00, 0x00, 0x00,  // flags
    ]);
    
    // __text section
    output.extend_from_slice(b"__text\0\0\0\0\0\0\0\0\0\0");  // sectname
    output.extend_from_slice(b"__TEXT\0\0\0\0\0\0\0\0\0\0");  // segname
    output.extend_from_slice(&[
        0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,  // addr = 0x100000000
        0x0c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // size = 12 (code size)
        0x00, 0x40, 0x00, 0x00,  // offset = 0x4000
        0x02, 0x00, 0x00, 0x00,  // align = 2^2 = 4
        0x00, 0x00, 0x00, 0x00,  // reloff
        0x00, 0x00, 0x00, 0x00,  // nreloc
        0x00, 0x04, 0x00, 0x80,  // flags
        0x00, 0x00, 0x00, 0x00,  // reserved1
        0x00, 0x00, 0x00, 0x00,  // reserved2
        0x00, 0x00, 0x00, 0x00,  // reserved3
    ]);
    
    // LC_MAIN
    output.extend_from_slice(&[
        0x28, 0x00, 0x00, 0x80,  // LC_MAIN
        0x18, 0x00, 0x00, 0x00,  // cmdsize = 24
        0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // entryoff = 0x4000 (relative to __TEXT)
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // stacksize = 0
    ]);
    
    // Pad to 0x4000
    while output.len() < 0x4000 {
        output.push(0);
    }
    
    // Add code
    output.extend_from_slice(&code);
    
    // Write file
    let mut file = File::create("test_arm64_exit42").unwrap();
    file.write_all(&output).unwrap();
    
    // Make executable
    let mut perms = file.metadata().unwrap().permissions();
    perms.set_mode(0o755);
    std::fs::set_permissions("test_arm64_exit42", perms).unwrap();
    
    println!("Created test_arm64_exit42");
    println!("Run: ./test_arm64_exit42; echo $?");
    println!("Expected: 42");
}