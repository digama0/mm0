//! WebAssembly Text (WAT) format generation
//!
//! This module generates human-readable WAT format from PCode,
//! which is useful for debugging and verification.

use std::io::Write;
use crate::LinkedCode;
use super::{WasmInst, WasmType};

/// Generate WAT (WebAssembly Text) format
pub fn write_wat(code: &LinkedCode, w: &mut impl Write) -> std::io::Result<()> {
    writeln!(w, "(module")?;
    
    // Type section
    writeln!(w, "  (type $main_type (func (result i32)))")?;
    
    // Memory
    writeln!(w, "  (memory 1)")?;
    writeln!(w, "  (export \"memory\" (memory 0))")?;
    
    // Start function
    writeln!(w, "  (func $_start (type $main_type)")?;
    
    // Generate instructions from PCode
    if let crate::arch_pcode::ArchPCode::Wasm(pcode) = &code.init.1 {
        // Local declarations
        if pcode.stack_size > 0 {
            write!(w, "    (local")?;
            for _ in 0..pcode.stack_size {
                write!(w, " i32")?; // TODO: Use actual types from local_types
            }
            writeln!(w, ")")?;
        }
        
        // Instructions
        for inst in pcode.insts.iter() {
            write!(w, "    ")?;
            write_wat_inst(w, inst)?;
            writeln!(w)?;
        }
    } else {
        // Fallback
        writeln!(w, "    i32.const 0")?;
    }
    
    writeln!(w, "  )")?;
    writeln!(w, "  (export \"_start\" (func $_start))")?;
    writeln!(w, ")")?;
    
    Ok(())
}

/// Write a single WAT instruction
fn write_wat_inst(w: &mut impl Write, inst: &WasmInst) -> std::io::Result<()> {
    use WasmInst::*;
    
    match inst {
        Const { ty, value } => {
            match ty {
                WasmType::I32 => write!(w, "i32.const {}", *value as i32)?,
                WasmType::I64 => write!(w, "i64.const {}", *value as i64)?,
                WasmType::F32 => write!(w, "f32.const {}", f32::from_bits(*value as u32))?,
                WasmType::F64 => write!(w, "f64.const {}", f64::from_bits(*value))?,
                WasmType::V128 => write!(w, "v128.const i32x4 0 0 0 0")?, // TODO: Proper v128 const
            }
        }
        LocalGet { idx } => write!(w, "local.get {}", idx)?,
        LocalSet { idx } => write!(w, "local.set {}", idx)?,
        LocalTee { idx } => write!(w, "local.tee {}", idx)?,
        
        // Memory operations
        Load { ty, offset, align } => {
            match ty {
                WasmType::I32 => write!(w, "i32.load offset={} align={}", offset, 1 << align)?,
                WasmType::I64 => write!(w, "i64.load offset={} align={}", offset, 1 << align)?,
                WasmType::F32 => write!(w, "f32.load offset={} align={}", offset, 1 << align)?,
                WasmType::F64 => write!(w, "f64.load offset={} align={}", offset, 1 << align)?,
                WasmType::V128 => write!(w, "v128.load offset={} align={}", offset, 1 << align)?,
            }
        }
        Store { ty, offset, align } => {
            match ty {
                WasmType::I32 => write!(w, "i32.store offset={} align={}", offset, 1 << align)?,
                WasmType::I64 => write!(w, "i64.store offset={} align={}", offset, 1 << align)?,
                WasmType::F32 => write!(w, "f32.store offset={} align={}", offset, 1 << align)?,
                WasmType::F64 => write!(w, "f64.store offset={} align={}", offset, 1 << align)?,
                WasmType::V128 => write!(w, "v128.store offset={} align={}", offset, 1 << align)?,
            }
        }
        
        // Arithmetic
        Add { ty } => {
            match ty {
                WasmType::I32 => write!(w, "i32.add")?,
                WasmType::I64 => write!(w, "i64.add")?,
                WasmType::F32 => write!(w, "f32.add")?,
                WasmType::F64 => write!(w, "f64.add")?,
                _ => write!(w, ";; TODO: add for {:?}", ty)?,
            }
        }
        Sub { ty } => {
            match ty {
                WasmType::I32 => write!(w, "i32.sub")?,
                WasmType::I64 => write!(w, "i64.sub")?,
                WasmType::F32 => write!(w, "f32.sub")?,
                WasmType::F64 => write!(w, "f64.sub")?,
                _ => write!(w, ";; TODO: sub for {:?}", ty)?,
            }
        }
        Mul { ty } => {
            match ty {
                WasmType::I32 => write!(w, "i32.mul")?,
                WasmType::I64 => write!(w, "i64.mul")?,
                WasmType::F32 => write!(w, "f32.mul")?,
                WasmType::F64 => write!(w, "f64.mul")?,
                _ => write!(w, ";; TODO: mul for {:?}", ty)?,
            }
        }
        
        // Control flow
        Call { func_idx } => write!(w, "call {}", func_idx)?,
        Return => write!(w, "return")?,
        Branch { target } => write!(w, "br {}", target)?,
        BranchIf { target } => write!(w, "br_if {}", target)?,
        
        // Stack manipulation
        Drop => write!(w, "drop")?,
        Select => write!(w, "select")?,
        
        // Block instructions
        Block { label } => write!(w, "block ;; label={}", label)?,
        Loop { label } => write!(w, "loop ;; label={}", label)?,
        If { label } => write!(w, "if ;; label={}", label)?,
        Else => write!(w, "else")?,
        End => write!(w, "end")?,
        
        // Comparisons
        I32Eq => write!(w, "i32.eq")?,
        I32Ne => write!(w, "i32.ne")?,
        I32LtS => write!(w, "i32.lt_s")?,
        I32LtU => write!(w, "i32.lt_u")?,
        I32GtS => write!(w, "i32.gt_s")?,
        I32GtU => write!(w, "i32.gt_u")?,
        I32LeS => write!(w, "i32.le_s")?,
        I32LeU => write!(w, "i32.le_u")?,
        I32GeS => write!(w, "i32.ge_s")?,
        I32GeU => write!(w, "i32.ge_u")?,
        I32Eqz => write!(w, "i32.eqz")?,
        
        // SIMD operations
        V128Const { value } => {
            write!(w, "v128.const i8x16")?;
            for byte in value {
                write!(w, " {}", byte)?;
            }
        }
        V128Load { offset, align } => write!(w, "v128.load offset={} align={}", offset, 1 << align)?,
        V128Store { offset, align } => write!(w, "v128.store offset={} align={}", offset, 1 << align)?,
        
        // SIMD arithmetic
        F32x4Add => write!(w, "f32x4.add")?,
        F32x4Sub => write!(w, "f32x4.sub")?,
        F32x4Mul => write!(w, "f32x4.mul")?,
        F32x4Div => write!(w, "f32x4.div")?,
        F32x4Sqrt => write!(w, "f32x4.sqrt")?,
        F32x4Min => write!(w, "f32x4.min")?,
        F32x4Max => write!(w, "f32x4.max")?,
        
        I32x4Add => write!(w, "i32x4.add")?,
        I32x4Sub => write!(w, "i32x4.sub")?,
        I32x4Mul => write!(w, "i32x4.mul")?,
        
        _ => write!(w, ";; TODO: {:?}", inst)?,
    }
    
    Ok(())
}