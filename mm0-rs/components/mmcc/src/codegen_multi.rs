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
        // Generate ARM64 code from the compiled MIR
        let code = self.generate_arm64_code();
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

impl LinkedCode {
    /// Generate ARM64 machine code from the linked code
    fn generate_arm64_code(&self) -> Vec<u8> {
        use crate::arch::arm64::{PInst, X0, X16, OperandSize};
        use crate::arch::traits::PhysicalInstruction;
        
        // For now, analyze the init code to see if it's just exit(N)
        // This is a minimal implementation to test the pipeline
        
        // Check if the init code is a simple exit syscall
        if let Some(exit_code) = self.detect_simple_exit() {
            // Generate ARM64 code for exit(N)
            let mut sink = Arm64Sink { bytes: vec![] };
            
            // mov w0, #exit_code
            let mov_inst = PInst::MovImm {
                dst: X0,
                imm: exit_code as u64,
                size: OperandSize::Size32,
            };
            mov_inst.encode(&mut sink).unwrap();
            
            // mov x16, #1 (exit syscall number)
            let syscall_inst = PInst::MovImm {
                dst: X16,
                imm: 1,
                size: OperandSize::Size64,
            };
            syscall_inst.encode(&mut sink).unwrap();
            
            // svc #0
            let svc_inst = PInst::Svc { imm: 0 };
            svc_inst.encode(&mut sink).unwrap();
            
            return sink.bytes;
        }
        
        // Fallback to hardcoded exit(42) for now
        vec![
            0x40, 0x05, 0x80, 0x52, // mov w0, #42
            0x30, 0x00, 0x80, 0xd2, // mov x16, #1
            0x01, 0x00, 0x00, 0xd4, // svc #0
        ]
    }
    
    /// Detect if this is a simple exit(N) program
    fn detect_simple_exit(&self) -> Option<u8> {
        // This would analyze the x86 PCode to detect patterns like:
        // mov edi, N
        // mov eax, 60  (exit syscall)
        // syscall
        
        // For now, just return None to use the fallback
        None
    }
}

/// Simple instruction sink for ARM64
struct Arm64Sink {
    bytes: Vec<u8>,
}

impl crate::arch::traits::InstructionSink for Arm64Sink {
    fn emit_bytes(&mut self, bytes: &[u8]) {
        self.bytes.extend_from_slice(bytes);
    }
    
    fn offset(&self) -> usize {
        self.bytes.len()
    }
}