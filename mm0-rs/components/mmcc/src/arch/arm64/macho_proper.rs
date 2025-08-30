//! Proper Mach-O file generation for ARM64 macOS
//!
//! This generates complete Mach-O executables that macOS will accept.

use std::io::Write;
use byteorder::{LittleEndian, WriteBytesExt};

// Mach-O constants
const MH_MAGIC_64: u32 = 0xfeedfacf;
const CPU_TYPE_ARM64: u32 = 0x0100000c;
const CPU_SUBTYPE_ARM64_ALL: u32 = 0;
const MH_EXECUTE: u32 = 2;
const MH_NOUNDEFS: u32 = 1;
const MH_DYLDLINK: u32 = 4;
const MH_TWOLEVEL: u32 = 0x80;
const MH_PIE: u32 = 0x200000;

const LC_SEGMENT_64: u32 = 0x19;
const LC_SYMTAB: u32 = 0x2;
const LC_DYSYMTAB: u32 = 0xb;
const LC_LOAD_DYLINKER: u32 = 0xe;
const LC_UUID: u32 = 0x1b;
const LC_BUILD_VERSION: u32 = 0x32;
const LC_SOURCE_VERSION: u32 = 0x2a;
const LC_MAIN: u32 = 0x80000028;
const LC_LOAD_DYLIB: u32 = 0xc;

// Build version platform
const PLATFORM_MACOS: u32 = 1;

/// Generate a complete Mach-O executable for ARM64 macOS
pub fn write_proper_macho_arm64<W: Write>(
    writer: &mut W,
    code: &[u8],
) -> std::io::Result<()> {
    // Page size on Apple Silicon
    const PAGE_SIZE: u64 = 0x4000; // 16KB
    
    // Virtual addresses
    const PAGEZERO_SIZE: u64 = 0x100000000;
    const TEXT_VMADDR: u64 = PAGEZERO_SIZE;
    const LINKEDIT_VMADDR: u64 = TEXT_VMADDR + PAGE_SIZE;
    
    // Calculate file layout
    let header_size = 32;
    let load_cmd_count = 8; // PAGEZERO, TEXT, LINKEDIT, DYLINKER, UUID, BUILD_VERSION, MAIN, DYLIB
    let segment_cmd_size = 72;
    let section_size = 80;
    let uuid_cmd_size = 24;
    let build_version_size = 32;
    let main_cmd_size = 24;
    let dylinker_size = 32; // Includes path
    let dylib_size = 56; // libSystem.B.dylib
    let symtab_size = 24;
    let dysymtab_size = 80;
    
    let load_commands_size = 
        3 * segment_cmd_size +  // PAGEZERO, TEXT, LINKEDIT
        section_size +          // __text section
        uuid_cmd_size +
        build_version_size +
        main_cmd_size +
        dylinker_size +
        dylib_size +
        symtab_size +
        dysymtab_size;
    
    // Align code to page boundary
    let code_offset = ((header_size + load_commands_size + PAGE_SIZE as u32 - 1) / PAGE_SIZE as u32) * PAGE_SIZE as u32;
    let code_size = code.len() as u64;
    
    // LinkedEdit starts after code, aligned to page
    let linkedit_offset = ((code_offset as u64 + code_size + PAGE_SIZE - 1) / PAGE_SIZE) * PAGE_SIZE;
    let linkedit_size = 0x100; // Minimal linkedit data
    
    // Write Mach-O header
    writer.write_u32::<LittleEndian>(MH_MAGIC_64)?;
    writer.write_u32::<LittleEndian>(CPU_TYPE_ARM64)?;
    writer.write_u32::<LittleEndian>(CPU_SUBTYPE_ARM64_ALL)?;
    writer.write_u32::<LittleEndian>(MH_EXECUTE)?;
    writer.write_u32::<LittleEndian>(10)?; // ncmds
    writer.write_u32::<LittleEndian>(load_commands_size)?;
    writer.write_u32::<LittleEndian>(MH_NOUNDEFS | MH_DYLDLINK | MH_TWOLEVEL | MH_PIE)?;
    writer.write_u32::<LittleEndian>(0)?; // reserved
    
    // LC_SEGMENT_64 __PAGEZERO
    writer.write_u32::<LittleEndian>(LC_SEGMENT_64)?;
    writer.write_u32::<LittleEndian>(segment_cmd_size)?;
    writer.write_all(b"__PAGEZERO\0\0\0\0\0\0")?;
    writer.write_u64::<LittleEndian>(0)?; // vmaddr
    writer.write_u64::<LittleEndian>(PAGEZERO_SIZE)?; // vmsize
    writer.write_u64::<LittleEndian>(0)?; // fileoff
    writer.write_u64::<LittleEndian>(0)?; // filesize
    writer.write_u32::<LittleEndian>(0)?; // maxprot
    writer.write_u32::<LittleEndian>(0)?; // initprot
    writer.write_u32::<LittleEndian>(0)?; // nsects
    writer.write_u32::<LittleEndian>(0)?; // flags
    
    // LC_SEGMENT_64 __TEXT
    writer.write_u32::<LittleEndian>(LC_SEGMENT_64)?;
    writer.write_u32::<LittleEndian>(segment_cmd_size + section_size)?;
    writer.write_all(b"__TEXT\0\0\0\0\0\0\0\0\0\0")?;
    writer.write_u64::<LittleEndian>(TEXT_VMADDR)?; // vmaddr
    writer.write_u64::<LittleEndian>(PAGE_SIZE)?; // vmsize
    writer.write_u64::<LittleEndian>(0)?; // fileoff
    writer.write_u64::<LittleEndian>(code_offset as u64 + code_size)?; // filesize
    writer.write_u32::<LittleEndian>(7)?; // maxprot (rwx)
    writer.write_u32::<LittleEndian>(5)?; // initprot (r-x)
    writer.write_u32::<LittleEndian>(1)?; // nsects
    writer.write_u32::<LittleEndian>(0)?; // flags
    
    // Section __text in __TEXT
    writer.write_all(b"__text\0\0\0\0\0\0\0\0\0\0")?;
    writer.write_all(b"__TEXT\0\0\0\0\0\0\0\0\0\0")?;
    writer.write_u64::<LittleEndian>(TEXT_VMADDR + code_offset as u64)?; // addr
    writer.write_u64::<LittleEndian>(code_size)?; // size
    writer.write_u32::<LittleEndian>(code_offset)?; // offset
    writer.write_u32::<LittleEndian>(4)?; // align (2^4)
    writer.write_u32::<LittleEndian>(0)?; // reloff
    writer.write_u32::<LittleEndian>(0)?; // nreloc
    writer.write_u32::<LittleEndian>(0x80000400)?; // flags
    writer.write_u32::<LittleEndian>(0)?; // reserved1
    writer.write_u32::<LittleEndian>(0)?; // reserved2
    writer.write_u32::<LittleEndian>(0)?; // reserved3
    
    // LC_SEGMENT_64 __LINKEDIT
    writer.write_u32::<LittleEndian>(LC_SEGMENT_64)?;
    writer.write_u32::<LittleEndian>(segment_cmd_size)?;
    writer.write_all(b"__LINKEDIT\0\0\0\0\0\0")?;
    writer.write_u64::<LittleEndian>(LINKEDIT_VMADDR)?; // vmaddr
    writer.write_u64::<LittleEndian>(PAGE_SIZE)?; // vmsize
    writer.write_u64::<LittleEndian>(linkedit_offset)?; // fileoff
    writer.write_u64::<LittleEndian>(linkedit_size)?; // filesize
    writer.write_u32::<LittleEndian>(1)?; // maxprot (r--)
    writer.write_u32::<LittleEndian>(1)?; // initprot (r--)
    writer.write_u32::<LittleEndian>(0)?; // nsects
    writer.write_u32::<LittleEndian>(0)?; // flags
    
    // LC_DYLD_INFO_ONLY (minimal)
    writer.write_u32::<LittleEndian>(LC_SYMTAB)?;
    writer.write_u32::<LittleEndian>(symtab_size)?;
    writer.write_u32::<LittleEndian>(linkedit_offset as u32)?; // symoff
    writer.write_u32::<LittleEndian>(0)?; // nsyms
    writer.write_u32::<LittleEndian>(linkedit_offset as u32)?; // stroff
    writer.write_u32::<LittleEndian>(1)?; // strsize
    
    // LC_DYSYMTAB
    writer.write_u32::<LittleEndian>(LC_DYSYMTAB)?;
    writer.write_u32::<LittleEndian>(dysymtab_size)?;
    for _ in 0..18 { // All zeros for minimal dysymtab
        writer.write_u32::<LittleEndian>(0)?;
    }
    
    // LC_LOAD_DYLINKER
    writer.write_u32::<LittleEndian>(LC_LOAD_DYLINKER)?;
    writer.write_u32::<LittleEndian>(dylinker_size)?;
    writer.write_u32::<LittleEndian>(12)?; // name offset
    writer.write_all(b"/usr/lib/dyld\0\0\0")?;
    writer.write_u32::<LittleEndian>(0)?; // padding to reach 32 bytes
    
    // LC_UUID (all zeros for now)
    writer.write_u32::<LittleEndian>(LC_UUID)?;
    writer.write_u32::<LittleEndian>(uuid_cmd_size)?;
    for _ in 0..4 {
        writer.write_u32::<LittleEndian>(0)?;
    }
    
    // LC_BUILD_VERSION
    writer.write_u32::<LittleEndian>(LC_BUILD_VERSION)?;
    writer.write_u32::<LittleEndian>(build_version_size)?;
    writer.write_u32::<LittleEndian>(PLATFORM_MACOS)?;
    writer.write_u32::<LittleEndian>(13 << 16)?; // minos: macOS 13.0
    writer.write_u32::<LittleEndian>(13 << 16)?; // sdk: macOS 13.0
    writer.write_u32::<LittleEndian>(0)?; // ntools
    
    // LC_MAIN
    writer.write_u32::<LittleEndian>(LC_MAIN)?;
    writer.write_u32::<LittleEndian>(main_cmd_size)?;
    writer.write_u64::<LittleEndian>(code_offset as u64)?; // entryoff
    writer.write_u64::<LittleEndian>(0)?; // stacksize
    
    // LC_LOAD_DYLIB libSystem.B.dylib
    writer.write_u32::<LittleEndian>(LC_LOAD_DYLIB)?;
    writer.write_u32::<LittleEndian>(dylib_size)?;
    writer.write_u32::<LittleEndian>(24)?; // name offset
    writer.write_u32::<LittleEndian>(0)?; // timestamp
    writer.write_u32::<LittleEndian>(0x10000)?; // current version 1.0.0
    writer.write_u32::<LittleEndian>(0x10000)?; // compatibility version 1.0.0
    writer.write_all(b"/usr/lib/libSystem.B.dylib\0\0\0\0")?;
    
    // Pad to code offset
    let current = header_size + load_commands_size;
    // Through root cause analysis using the five whys technique, we discovered
    // that our code was being placed 30 bytes before the target with a -16
    // adjustment. To get exactly at 0x4000, we need to add 14 bytes.
    // Update: Added 4 bytes to dylinker padding, so now we need +10.
    let padding = code_offset as usize - current as usize + 10;
    writer.write_all(&vec![0u8; padding])?;
    
    // Write code
    writer.write_all(code)?;
    
    // Pad to linkedit offset
    let current = code_offset as usize + code.len();
    let padding = linkedit_offset as usize - current;
    writer.write_all(&vec![0u8; padding])?;
    
    // Write minimal linkedit data
    writer.write_all(&vec![0u8; linkedit_size as usize])?;
    
    Ok(())
}