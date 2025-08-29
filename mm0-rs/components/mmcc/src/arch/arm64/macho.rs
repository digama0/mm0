//! Mach-O file generation for ARM64 macOS
//!
//! This generates minimal Mach-O executables for testing on Apple Silicon.

use crate::arch::traits::InstructionSink;
use std::io::Write;

/// Minimal Mach-O file header for ARM64
pub fn write_macho_arm64<W: Write>(
    writer: &mut W,
    code: &[u8],
    entry_offset: u64,
) -> std::io::Result<()> {
    // Mach-O header constants
    const MH_MAGIC_64: u32 = 0xfeedfacf;
    const CPU_TYPE_ARM64: u32 = 0x0100000c;
    const CPU_SUBTYPE_ARM64_ALL: u32 = 0;
    const MH_EXECUTE: u32 = 2;
    const MH_NOUNDEFS: u32 = 1;
    const MH_PIE: u32 = 0x200000;
    
    // Load command constants
    const LC_SEGMENT_64: u32 = 0x19;
    const LC_UNIXTHREAD: u32 = 0x5;
    const LC_MAIN: u32 = 0x80000028;
    
    // VM addresses
    const TEXT_VMADDR: u64 = 0x100000000;  // Standard text segment address
    const PAGE_SIZE: u64 = 0x4000;         // 16KB pages on Apple Silicon
    
    // Calculate sizes
    let header_size = 32;  // Mach header
    let segment_cmd_size = 72;  // LC_SEGMENT_64
    let section_size = 80;  // __text section
    let main_cmd_size = 24; // LC_MAIN
    let load_commands_size = segment_cmd_size + section_size + main_cmd_size;
    
    let file_offset = ((header_size + load_commands_size + PAGE_SIZE - 1) / PAGE_SIZE) * PAGE_SIZE;
    let code_size = code.len() as u64;
    let file_size = file_offset + code_size;
    
    // Write Mach-O header
    writer.write_all(&MH_MAGIC_64.to_le_bytes())?;
    writer.write_all(&CPU_TYPE_ARM64.to_le_bytes())?;
    writer.write_all(&CPU_SUBTYPE_ARM64_ALL.to_le_bytes())?;
    writer.write_all(&MH_EXECUTE.to_le_bytes())?;
    writer.write_all(&2u32.to_le_bytes())?;  // ncmds (2 load commands)
    writer.write_all(&load_commands_size.to_le_bytes())?;
    writer.write_all(&(MH_NOUNDEFS | MH_PIE).to_le_bytes())?;
    writer.write_all(&0u32.to_le_bytes())?;  // reserved
    
    // LC_SEGMENT_64 for __TEXT
    writer.write_all(&LC_SEGMENT_64.to_le_bytes())?;
    writer.write_all(&segment_cmd_size.to_le_bytes())?;
    writer.write_all(b"__TEXT\0\0\0\0\0\0\0\0\0\0")?;  // segname (16 bytes)
    writer.write_all(&TEXT_VMADDR.to_le_bytes())?;     // vmaddr
    writer.write_all(&PAGE_SIZE.to_le_bytes())?;       // vmsize
    writer.write_all(&0u64.to_le_bytes())?;            // fileoff
    writer.write_all(&file_size.to_le_bytes())?;       // filesize
    writer.write_all(&7u32.to_le_bytes())?;            // maxprot (rwx)
    writer.write_all(&5u32.to_le_bytes())?;            // initprot (r-x)
    writer.write_all(&1u32.to_le_bytes())?;            // nsects
    writer.write_all(&0u32.to_le_bytes())?;            // flags
    
    // Section __text in __TEXT
    writer.write_all(b"__text\0\0\0\0\0\0\0\0\0\0")?;   // sectname (16 bytes)
    writer.write_all(b"__TEXT\0\0\0\0\0\0\0\0\0\0")?;   // segname (16 bytes)
    writer.write_all(&(TEXT_VMADDR + file_offset).to_le_bytes())?;  // addr
    writer.write_all(&code_size.to_le_bytes())?;        // size
    writer.write_all(&file_offset.to_le_bytes())?;      // offset
    writer.write_all(&4u32.to_le_bytes())?;             // align (2^4 = 16)
    writer.write_all(&0u32.to_le_bytes())?;             // reloff
    writer.write_all(&0u32.to_le_bytes())?;             // nreloc
    writer.write_all(&0x80000400u32.to_le_bytes())?;    // flags (S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS)
    writer.write_all(&0u32.to_le_bytes())?;             // reserved1
    writer.write_all(&0u32.to_le_bytes())?;             // reserved2
    writer.write_all(&0u32.to_le_bytes())?;             // reserved3
    
    // LC_MAIN
    writer.write_all(&LC_MAIN.to_le_bytes())?;
    writer.write_all(&main_cmd_size.to_le_bytes())?;
    writer.write_all(&entry_offset.to_le_bytes())?;     // entryoff
    writer.write_all(&0u64.to_le_bytes())?;             // stacksize (0 = default)
    
    // Pad to page boundary
    let padding = file_offset as usize - (header_size + load_commands_size) as usize;
    writer.write_all(&vec![0u8; padding])?;
    
    // Write code
    writer.write_all(code)?;
    
    Ok(())
}

/// Simple instruction sink for collecting ARM64 code
pub struct Arm64Sink {
    pub code: Vec<u8>,
}

impl Arm64Sink {
    pub fn new() -> Self {
        Self { code: Vec::new() }
    }
}

impl InstructionSink for Arm64Sink {
    fn emit_bytes(&mut self, bytes: &[u8]) {
        self.code.extend_from_slice(bytes);
    }
    
    fn offset(&self) -> usize {
        self.code.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_minimal_macho() {
        // Minimal ARM64 program: mov x0, #42; ret
        let code = vec![
            0x40, 0x05, 0x80, 0x52,  // mov w0, #42
            0xc0, 0x03, 0x5f, 0xd6,  // ret
        ];
        
        let mut output = Vec::new();
        write_macho_arm64(&mut output, &code, 0).unwrap();
        
        // Check magic number
        assert_eq!(&output[0..4], &[0xcf, 0xfa, 0xed, 0xfe]);  // Little-endian 0xfeedfacf
    }
}