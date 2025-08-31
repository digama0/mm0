//! WASM module generation
//!
//! This module handles the generation of complete WebAssembly modules,
//! including all the necessary sections (type, function, code, export, etc.)

use std::io::Write;
use crate::types::vcode::ProcId;
use crate::LinkedCode;

/// Generate a complete WASM module
pub fn write_wasm_module(code: &LinkedCode, w: &mut impl Write) -> std::io::Result<()> {
    // WASM module magic number and version
    w.write_all(&[0x00, 0x61, 0x73, 0x6d])?; // "\0asm"
    w.write_all(&[0x01, 0x00, 0x00, 0x00])?; // version 1
    
    // Type section (1)
    write_type_section(w)?;
    
    // Import section (2) - for now, empty
    
    // Function section (3)
    write_function_section(code, w)?;
    
    // Memory section (5)
    write_memory_section(w)?;
    
    // Export section (7)
    write_export_section(w)?;
    
    // Code section (10)
    write_code_section(code, w)?;
    
    Ok(())
}

/// Write the type section - defines function signatures
fn write_type_section(w: &mut impl Write) -> std::io::Result<()> {
    w.write_all(&[0x01])?; // Type section ID
    
    let mut section = Vec::new();
    
    // Number of types (for now just main: () -> i32)
    encode_leb128(&mut section, 1);
    
    // Function type 0: () -> i32
    section.push(0x60); // func type
    encode_leb128(&mut section, 0); // 0 params
    encode_leb128(&mut section, 1); // 1 result
    section.push(0x7f); // i32
    
    // Write section size and contents
    encode_leb128(w, section.len() as u32);
    w.write_all(&section)?;
    
    Ok(())
}

/// Write the function section - declares which type each function uses
fn write_function_section(code: &LinkedCode, w: &mut impl Write) -> std::io::Result<()> {
    w.write_all(&[0x03])?; // Function section ID
    
    let mut section = Vec::new();
    
    // Number of functions
    let func_count = code.funcs.0.len() + 1; // +1 for _start
    encode_leb128(&mut section, func_count as u32);
    
    // Each function uses type 0 for now
    for _ in 0..func_count {
        encode_leb128(&mut section, 0);
    }
    
    encode_leb128(w, section.len() as u32);
    w.write_all(&section)?;
    
    Ok(())
}

/// Write the memory section
fn write_memory_section(w: &mut impl Write) -> std::io::Result<()> {
    w.write_all(&[0x05])?; // Memory section ID
    
    let mut section = Vec::new();
    
    // 1 memory
    encode_leb128(&mut section, 1);
    
    // Memory type: min 1 page, no max
    section.push(0x00); // no max
    encode_leb128(&mut section, 1); // min 1 page (64KB)
    
    encode_leb128(w, section.len() as u32);
    w.write_all(&section)?;
    
    Ok(())
}

/// Write the export section
fn write_export_section(w: &mut impl Write) -> std::io::Result<()> {
    w.write_all(&[0x07])?; // Export section ID
    
    let mut section = Vec::new();
    
    // 2 exports: memory and _start
    encode_leb128(&mut section, 2);
    
    // Export "memory"
    encode_leb128(&mut section, 6); // name length
    section.extend_from_slice(b"memory");
    section.push(0x02); // memory export
    encode_leb128(&mut section, 0); // memory index 0
    
    // Export "_start"
    encode_leb128(&mut section, 6); // name length
    section.extend_from_slice(b"_start");
    section.push(0x00); // function export
    encode_leb128(&mut section, 0); // function index 0 (_start)
    
    encode_leb128(w, section.len() as u32);
    w.write_all(&section)?;
    
    Ok(())
}

/// Write the code section - actual function bodies
fn write_code_section(code: &LinkedCode, w: &mut impl Write) -> std::io::Result<()> {
    w.write_all(&[0x0a])?; // Code section ID
    
    let mut section = Vec::new();
    
    // Number of function bodies
    let func_count = 1; // Just _start for now
    encode_leb128(&mut section, func_count as u32);
    
    // Generate the _start function from init code
    let mut body = Vec::new();
    
    // Check if we have WASM code in init
    if let crate::arch_pcode::ArchPCode::Wasm(pcode) = &code.init.1 {
        // Local count from PCode
        encode_leb128(&mut body, pcode.stack_size);
        
        // Encode each instruction
        for inst in &pcode.insts.0 {
            encode_wasm_inst(&mut body, inst)?;
        }
    } else {
        // Fallback: just return 0
        encode_leb128(&mut body, 0); // 0 locals
        body.push(0x41); // i32.const
        encode_leb128(&mut body, 0);
    }
    
    body.push(0x0b); // end
    
    encode_leb128(&mut section, body.len() as u32);
    section.extend_from_slice(&body);
    
    encode_leb128(w, section.len() as u32);
    w.write_all(&section)?;
    
    Ok(())
}

/// LEB128 encoding helper
fn encode_leb128(w: &mut impl Write, mut value: u32) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        if value == 0 {
            w.write_all(&[byte]).unwrap();
            break;
        } else {
            w.write_all(&[byte | 0x80]).unwrap();
        }
    }
}

/// Encode a WASM instruction to bytes
fn encode_wasm_inst(w: &mut Vec<u8>, inst: &super::WasmInst) -> std::io::Result<()> {
    use super::WasmInst::*;
    use super::WasmType;
    
    match inst {
        Const { ty, value } => {
            match ty {
                WasmType::I32 => {
                    w.push(0x41); // i32.const
                    encode_leb128(w, *value as u32);
                }
                WasmType::I64 => {
                    w.push(0x42); // i64.const
                    encode_leb128_i64(w, *value as i64);
                }
                _ => {} // TODO: Float constants
            }
        }
        LocalGet { idx } => {
            w.push(0x20); // local.get
            encode_leb128(w, *idx);
        }
        LocalSet { idx } => {
            w.push(0x21); // local.set
            encode_leb128(w, *idx);
        }
        LocalTee { idx } => {
            w.push(0x22); // local.tee
            encode_leb128(w, *idx);
        }
        Add { ty } => {
            match ty {
                WasmType::I32 => w.push(0x6a), // i32.add
                WasmType::I64 => w.push(0x7c), // i64.add
                _ => {} // TODO: Float add
            }
        }
        Call { func_idx } => {
            w.push(0x10); // call
            encode_leb128(w, *func_idx);
        }
        Return => {
            w.push(0x0f); // return
        }
        Drop => {
            w.push(0x1a); // drop
        }
        _ => {} // TODO: Other instructions
    }
    
    Ok(())
}

/// LEB128 encoding for i64
fn encode_leb128_i64(w: &mut impl Write, mut value: i64) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        let more = !((value == 0 && (byte & 0x40) == 0) || (value == -1 && (byte & 0x40) != 0));
        if more {
            w.write_all(&[byte | 0x80]).unwrap();
        } else {
            w.write_all(&[byte]).unwrap();
            break;
        }
    }
}