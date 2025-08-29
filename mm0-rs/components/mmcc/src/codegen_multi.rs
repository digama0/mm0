//! Multi-architecture code generation
//!
//! This module extends the existing codegen to support multiple architectures.

use std::io::{self, Write};
use crate::{LinkedCode, arch::target::{Target, TargetArch, OperatingSystem}};

impl LinkedCode {
    /// Write executable for the given target
    pub fn write_executable(&self, w: &mut impl Write, target: Target) -> io::Result<()> {
        match (target.arch, target.os) {
            (TargetArch::X86_64, _) => {
                // Use existing ELF writer for x86-64
                self.write_elf(w)
            }
            (TargetArch::Arm64, OperatingSystem::MacOS) => {
                // Generate Mach-O for ARM64 macOS
                self.write_macho_arm64(w)
            }
            (TargetArch::Arm64, OperatingSystem::Linux) => {
                // Generate ELF for ARM64 Linux
                self.write_elf_arm64(w)
            }
            _ => Err(io::Error::new(
                io::ErrorKind::Unsupported,
                format!("Unsupported target: {}", target)
            ))
        }
    }
    
    /// Write Mach-O file for ARM64 macOS
    fn write_macho_arm64(&self, w: &mut impl Write) -> io::Result<()> {
        // For now, just write a minimal test executable
        // This will be expanded to use the actual generated code
        
        // TODO: Replace with proper ARM64 code generation
        // For now, use a placeholder implementation
        
        // For now, just write a minimal test executable
        // This will be expanded to use the actual generated code
        
        // TODO: Replace with proper ARM64 code generation from MIR
        // For now, use a simple exit(42) program
        
        // mov w0, #42  (0x52800540)
        // mov x16, #1  (0xd2800030) 
        // svc #0       (0xd4000001)
        let code = vec![
            0x40, 0x05, 0x80, 0x52, // mov w0, #42
            0x30, 0x00, 0x80, 0xd2, // mov x16, #1
            0x01, 0x00, 0x00, 0xd4, // svc #0
        ];
        
        crate::arch::arm64::macho_proper::write_proper_macho_arm64(w, &code)
    }
    
    /// Write ELF file for ARM64 Linux
    fn write_elf_arm64(&self, w: &mut impl Write) -> io::Result<()> {
        // TODO: Implement ARM64 Linux ELF generation
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "ARM64 Linux ELF generation not yet implemented"
        ))
    }
}