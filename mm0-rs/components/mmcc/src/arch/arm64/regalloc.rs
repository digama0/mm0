//! ARM64 register allocation implementation
//!
//! This module provides ARM64-specific register allocation functionality,
//! replacing the x86-specific regalloc.rs when building for ARM64.

use crate::types::{IdxVec, mir, vcode::*};
use crate::build_vcode::VCode;
use crate::types::classify::Trace;
use crate::Idx;
use super::{PReg, regs::PRegSet, PInst};
use super::inst::Inst;
use std::collections::HashMap;

/// ARM64 machine environment for regalloc2
pub static ARM64_MACHINE_ENV: regalloc2::MachineEnv = regalloc2::MachineEnv {
    preferred_regs_by_class: [
        // Integer registers: X0-X7 for args, X8-X15 for temps
        (1 << 0) | (1 << 1) | (1 << 2) | (1 << 3) |
        (1 << 4) | (1 << 5) | (1 << 6) | (1 << 7) |
        (1 << 8) | (1 << 9) | (1 << 10) | (1 << 11) |
        (1 << 12) | (1 << 13) | (1 << 14) | (1 << 15),
        // Float registers (not used yet)
        0,
        // Vector registers (not used yet)
        0,
    ],
    non_preferred_regs_by_class: [
        // Integer: X16-X28 (excluding X18 platform register, X29 FP, X30 LR)
        (1 << 16) | (1 << 17) | (1 << 19) | (1 << 20) |
        (1 << 21) | (1 << 22) | (1 << 23) | (1 << 24) |
        (1 << 25) | (1 << 26) | (1 << 27) | (1 << 28),
        0, // Float
        0, // Vector
    ],
    // Stack pointer (X31/SP), Frame pointer (X29), Zero register
    fixed_stack_slots: &[],
};

/// Physical register code after register allocation
#[derive(Clone, Debug)]
pub struct PCode {
    /// The instructions after register allocation
    pub insts: IdxVec<PInstId, PInst>,
    /// Map from VCode block to instruction range
    pub blocks: IdxVec<regalloc2::Block, (mir::BlockId, PInstId, PInstId)>,
    /// Start address of each block
    pub block_addr: IdxVec<regalloc2::Block, u32>,
    /// Trace information for debugging
    pub trace: Trace,
    /// Stack size needed
    pub stack_size: u32,
    /// Total code size
    pub len: u32,
}

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
pub fn regalloc_arm64(vcode: &VCode<Inst>) -> Result<PCode, String> {
    // Run regalloc2
    let output = regalloc2::run(
        vcode,
        &ARM64_MACHINE_ENV,
        &regalloc2::RegallocOptions::default()
    ).map_err(|e| format!("Register allocation failed: {:?}", e))?;
    
    // Convert virtual instructions to physical instructions
    let mut pinsts = IdxVec::default();
    let mut blocks = IdxVec::default();
    let mut block_addr = IdxVec::default();
    
    // Process each block
    for (block_idx, block) in vcode.blocks() {
        let start = PInstId(pinsts.len() as u32);
        
        // Get instruction range for this block
        let inst_range = vcode.block_insts(block);
        
        // Process each instruction
        for inst_idx in inst_range {
            let vinst = &vcode[inst_idx];
            
            // Apply register allocation edits
            for edit in output.edits(&inst_idx) {
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
    for (i, &(_, start, end)) in blocks.iter() {
        block_addr[i] = addr;
        // Each ARM64 instruction is 4 bytes
        addr += (end.0 - start.0) * 4;
    }
    
    Ok(PCode {
        insts: pinsts,
        blocks,
        block_addr,
        trace: vcode.trace().clone(),
        stack_size: output.stack_slots_size as u32,
        len: addr,
    })
}

/// Convert regalloc2 allocation to physical register
fn allocation_to_preg(alloc: regalloc2::Allocation) -> PReg {
    match alloc {
        regalloc2::Allocation::Reg(vreg) => {
            let preg_idx = vreg.hw_enc();
            PReg::new(preg_idx as usize)
        }
        regalloc2::Allocation::Stack(slot) => {
            panic!("ARM64: Stack slots not yet implemented: {:?}", slot)
        }
    }
}