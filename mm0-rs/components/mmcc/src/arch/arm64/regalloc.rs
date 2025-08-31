//! ARM64 register allocation implementation
//!
//! This module provides ARM64-specific register allocation functionality,
//! replacing the x86-specific regalloc.rs when building for ARM64.

use crate::types::{IdxVec, mir, vcode::*};
use crate::arch::arm64::vcode::VCode;
use crate::Idx;
use super::{PReg, regs::PRegSet, PInst};
use super::inst::Inst;
use std::collections::HashMap;

// Re-export PCode from pcode module
pub use super::pcode::Arm64PCode as PCode;

impl PCode {
    /// Get the instructions
    pub fn insts(&self) -> &IdxVec<PInstId, PInst> {
        &self.insts
    }
    
    /// Get block addresses
    pub fn block_addrs(&self) -> &IdxVec<regalloc2::Block, u32> {
        &self.block_addr
    }
}

/// Identifier for physical instructions
mk_id! { PInstId }

/// Apply register allocation results to VCode
pub fn regalloc_arm64(vcode: &VCode) -> Result<PCode, String> {
    // Run regalloc2
    let output = regalloc2::run(
        vcode,
        &super::MACHINE_ENV,
        &regalloc2::RegallocOptions::default()
    ).map_err(|e| format!("Register allocation failed: {:?}", e))?;
    
    // Convert virtual instructions to physical instructions
    let mut pinsts = IdxVec::default();
    let mut blocks = IdxVec::default();
    let mut block_addr = IdxVec::default();
    
    // Process each block
    for (block_idx, block) in vcode.blocks.enum_iter() {
        let start = PInstId(pinsts.len() as u32);
        
        // Get instruction range for this block
        let inst_range = vcode.block_insts(block_idx);
        
        // Process each instruction
        for inst_idx in inst_range {
            let vinst = &vcode[inst_idx];
            
            // Apply register allocation edits
            // TODO: Process edits properly
            /*
            for edit in output.edits.get(&inst_idx) {
                match edit {
                    regalloc2::Edit::Move { from, to } => {
                        // Generate move instruction
                        let from_preg = allocation_to_preg(from);
                        let to_preg = allocation_to_preg(to);
                        
                        pinsts.push(PInst::Mov {
                            dst: to_preg,
                            src: from_preg,
                            size: super::OperandSize::Size64,
                        });
                    }
                }
            }
            */
            
            // Convert the instruction with allocated registers
            match vinst {
                Inst::Ret => {
                    pinsts.push(PInst::Ret);
                }
                // Add more instruction conversions as needed
                _ => {
                    // For now, skip unimplemented instructions
                    eprintln!("ARM64 regalloc: Skipping unimplemented instruction: {:?}", vinst);
                }
            }
        }
        
        let end = PInstId(pinsts.len() as u32);
        blocks.push((mir::BlockId(block_idx.index() as u32), start, end));
        block_addr.push(0); // Will be filled in later
    }
    
    // Calculate code size and block addresses
    let mut addr = 0u32;
    for (i, &(_, start, end)) in blocks.enum_iter() {
        block_addr[i] = addr;
        // Each ARM64 instruction is 4 bytes
        addr += (end.0 - start.0) * 4;
    }
    
    Ok(PCode {
        insts: pinsts,
        block_map: HashMap::new(), // TODO: Populate from VCode
        blocks,
        block_addr,
        block_params: ChunkVec::default(),
        trace: Trace::default(), // TODO: Implement proper trace generation
        stack_size: (output.num_spillslots * 8) as u32, // Each spill slot is 8 bytes
        saved_regs: vec![], // TODO: Implement callee-saved register tracking
        len: addr,
        const_data: vec![],
        const_table: None,
    })
}

/// Convert regalloc2 allocation to physical register
fn allocation_to_preg(alloc: regalloc2::Allocation) -> PReg {
    if let Some(preg) = alloc.as_reg() {
        PReg::new(preg.hw_enc() as usize)
    } else {
        panic!("ARM64: Stack slots not yet implemented: {:?}", alloc)
    }
}