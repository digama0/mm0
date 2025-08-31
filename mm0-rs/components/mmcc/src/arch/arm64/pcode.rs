//! ARM64-specific PCode representation
//!
//! This module provides an ARM64-specific PCode structure that can be used
//! instead of the x86-specific one for ARM64 targets.

use crate::types::{IdxVec, vcode::{ChunkVec, Trace}, mir};
use crate::arch_pcode::PInstId;
use super::PInst;
use std::collections::HashMap;

/// ARM64-specific physical code after register allocation
#[derive(Clone, Debug)]
pub struct Arm64PCode {
    /// The physical instructions
    pub insts: IdxVec<PInstId, PInst>,
    /// Map from MIR blocks to their instruction ranges
    pub block_map: HashMap<mir::BlockId, regalloc2::Block>,
    /// Block information: (MIR block, start instruction, end instruction)
    pub blocks: IdxVec<regalloc2::Block, (mir::BlockId, PInstId, PInstId)>,
    /// Block start addresses (byte offsets)
    pub block_addr: IdxVec<regalloc2::Block, u32>,
    /// Block parameters (for phi nodes)
    pub block_params: ChunkVec<regalloc2::Block, regalloc2::VReg>,
    /// Tracing information for debugging
    pub trace: Trace,
    /// Stack frame size in bytes
    pub stack_size: u32,
    /// Saved callee-saved registers
    pub saved_regs: Vec<super::PReg>,
    /// Total code size in bytes
    pub len: u32,
    /// Constant data to be placed after the code
    pub const_data: Vec<u8>,
    pub const_table: Option<super::const_table::Arm64ConstTable>,
}

impl Arm64PCode {
    /// Create a new ARM64 PCode structure
    pub fn new() -> Self {
        Self {
            insts: IdxVec::default(),
            block_map: HashMap::new(),
            blocks: IdxVec::default(),
            block_addr: IdxVec::default(),
            block_params: ChunkVec::default(),
            trace: Trace {
                stmts: ChunkVec::default(),
                block: IdxVec::default(),
                projs: vec![],
                lists: vec![],
            },
            stack_size: 0,
            saved_regs: vec![],
            len: 0,
            const_data: vec![],
            const_table: None,
        }
    }
    
    /// Convert to raw bytes for code generation
    pub fn to_bytes(&self) -> Vec<u8> {
        use crate::arch::traits::{PhysicalInstruction, InstructionSink};
        
        struct ByteSink {
            bytes: Vec<u8>,
        }
        
        impl InstructionSink for ByteSink {
            fn emit_bytes(&mut self, bytes: &[u8]) {
                self.bytes.extend_from_slice(bytes);
            }
            
            fn offset(&self) -> usize {
                self.bytes.len()
            }
        }
        
        let mut sink = ByteSink { bytes: Vec::new() };
        
        for (_, inst) in self.insts.enum_iter() {
            inst.encode(&mut sink).unwrap_or_else(|e| {
                eprintln!("ARM64: Failed to encode instruction: {:?}", e);
            });
        }
        
        // Append constant data after the code
        sink.bytes.extend_from_slice(&self.const_data);
        
        sink.bytes
    }
}