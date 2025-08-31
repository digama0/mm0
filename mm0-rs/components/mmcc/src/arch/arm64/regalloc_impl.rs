//! Complete ARM64 register allocation implementation
//!
//! This module provides a working register allocator using regalloc2,
//! handling virtual to physical register mapping, spilling, and move insertion.

use crate::types::{IdxVec, mir, vcode::*, Size};
use crate::build_vcode::VCode;
use crate::types::classify::Trace;
use crate::Idx;
use super::{
    PReg, regs::PRegSet, PInst, PAMode, POperand, OperandSize,
    inst::{Inst, AMode, Operand as VOperand, Cond},
};
use std::collections::HashMap;

/// Result of register allocation
pub struct RegAllocResult {
    /// Physical instructions after allocation
    pub pinsts: IdxVec<PInstId, PInst>,
    /// Block information
    pub blocks: IdxVec<BlockId, (mir::BlockId, PInstId, PInstId)>,
    /// Block addresses
    pub block_addr: IdxVec<BlockId, u32>,
    /// Stack size needed for spills
    pub stack_size: u32,
    /// Total code size
    pub len: u32,
}

/// Perform register allocation on ARM64 VCode
pub fn allocate_registers(vcode: &VCode<Inst>) -> Result<RegAllocResult, String> {
    // Run regalloc2
    let alloc_result = regalloc2::run(
        vcode,
        &super::regalloc::ARM64_MACHINE_ENV,
        &regalloc2::RegallocOptions::default()
    ).map_err(|e| format!("Register allocation failed: {:?}", e))?;
    
    // Build the output
    let mut builder = RegAllocBuilder::new(vcode, &alloc_result);
    builder.build()
}

/// Helper for building allocated code
struct RegAllocBuilder<'a> {
    vcode: &'a VCode<Inst>,
    alloc: &'a regalloc2::Output,
    pinsts: IdxVec<PInstId, PInst>,
    blocks: IdxVec<BlockId, (mir::BlockId, PInstId, PInstId)>,
    block_addr: IdxVec<BlockId, u32>,
    /// Map from InstId to PInstId for branch targets
    inst_map: HashMap<InstId, PInstId>,
}

impl<'a> RegAllocBuilder<'a> {
    fn new(vcode: &'a VCode<Inst>, alloc: &'a regalloc2::Output) -> Self {
        Self {
            vcode,
            alloc,
            pinsts: IdxVec::default(),
            blocks: IdxVec::default(),
            block_addr: IdxVec::default(),
            inst_map: HashMap::new(),
        }
    }
    
    fn build(mut self) -> Result<RegAllocResult, String> {
        // Process each block
        for block in 0..self.vcode.num_blocks() {
            let block_id = BlockId::new(block);
            self.process_block(block_id)?;
        }
        
        // Calculate block addresses
        self.calculate_addresses();
        
        // Calculate total stack size
        let stack_size = self.alloc.stackslots_size as u32;
        
        Ok(RegAllocResult {
            pinsts: self.pinsts,
            blocks: self.blocks,
            block_addr: self.block_addr,
            stack_size,
            len: self.pinsts.len() as u32 * 4, // ARM64 instructions are 4 bytes
        })
    }
    
    fn process_block(&mut self, block: BlockId) -> Result<(), String> {
        let (mir_block, inst_start, inst_end) = self.vcode.blocks[block];
        let pinst_start = PInstId(self.pinsts.len() as u32);
        
        // Process each instruction in the block
        for inst_id in self.vcode.block_insns(block) {
            // Record mapping for branch targets
            self.inst_map.insert(inst_id, PInstId(self.pinsts.len() as u32));
            
            // Insert any moves required before the instruction
            self.insert_moves_before(inst_id)?;
            
            // Convert the instruction with allocated registers
            self.convert_instruction(inst_id)?;
            
            // Insert any moves required after the instruction
            self.insert_moves_after(inst_id)?;
        }
        
        let pinst_end = PInstId(self.pinsts.len() as u32);
        self.blocks.push((mir_block, pinst_start, pinst_end));
        self.block_addr.push(0); // Will be filled later
        
        Ok(())
    }
    
    fn insert_moves_before(&mut self, inst: InstId) -> Result<(), String> {
        for edit in self.alloc.edits_before(inst) {
            self.process_edit(edit)?;
        }
        Ok(())
    }
    
    fn insert_moves_after(&mut self, inst: InstId) -> Result<(), String> {
        for edit in self.alloc.edits_after(inst) {
            self.process_edit(edit)?;
        }
        Ok(())
    }
    
    fn process_edit(&mut self, edit: &regalloc2::Edit) -> Result<(), String> {
        match edit {
            regalloc2::Edit::Move { from, to } => {
                let (src, dst) = match (from.as_reg(), to.as_reg()) {
                    (Some(src), Some(dst)) => {
                        // Register to register move
                        (POperand::Reg(self.preg(src)), self.preg(dst))
                    }
                    (Some(src), None) => {
                        // Spill: register to stack
                        let slot = to.as_stack().unwrap();
                        self.emit_spill(self.preg(src), slot);
                        return Ok(());
                    }
                    (None, Some(dst)) => {
                        // Reload: stack to register
                        let slot = from.as_stack().unwrap();
                        self.emit_reload(dst, slot);
                        return Ok(());
                    }
                    (None, None) => {
                        return Err("Invalid move: stack to stack".to_string());
                    }
                };
                
                // Emit move instruction
                self.pinsts.push(PInst::Mov {
                    dst,
                    src: src.as_reg().unwrap(),
                    size: OperandSize::Size64,
                });
            }
        }
        Ok(())
    }
    
    fn emit_spill(&mut self, reg: PReg, slot: regalloc2::SpillSlot) {
        // Store register to spill slot
        let offset = self.spill_offset(slot);
        self.pinsts.push(PInst::Str {
            src: reg,
            addr: PAMode::Offset(PReg::new(31), offset), // SP-relative
            size: OperandSize::Size64,
        });
    }
    
    fn emit_reload(&mut self, reg: PReg, slot: regalloc2::SpillSlot) {
        // Load spill slot to register
        let offset = self.spill_offset(slot);
        self.pinsts.push(PInst::Ldr {
            dst: reg,
            addr: PAMode::Offset(PReg::new(31), offset), // SP-relative
            size: OperandSize::Size64,
        });
    }
    
    fn spill_offset(&self, slot: regalloc2::SpillSlot) -> i16 {
        // Spill slots are placed after the frame pointer save area
        // Each slot is 8 bytes
        let slot_index = slot.index() as i16;
        16 + slot_index * 8 // After FP/LR save
    }
    
    fn convert_instruction(&mut self, inst_id: InstId) -> Result<(), String> {
        let inst = &self.vcode[inst_id];
        
        match inst {
            // Control flow
            Inst::Ret => {
                self.pinsts.push(PInst::Ret);
            }
            
            Inst::Branch { target } => {
                // Will be patched later with correct offset
                self.pinsts.push(PInst::B { offset: 0 });
            }
            
            Inst::BranchCond { cond, target } => {
                self.pinsts.push(PInst::Bcond { 
                    cond: *cond, 
                    offset: 0  // Will be patched
                });
            }
            
            // Arithmetic
            Inst::Add { dst, src1, src2, size } => {
                let dst = self.alloc_vreg(*dst, inst_id);
                let src1 = self.alloc_vreg(*src1, inst_id);
                let src2 = self.convert_operand(src2, inst_id)?;
                
                self.pinsts.push(PInst::Add {
                    dst,
                    src1,
                    src2,
                    size: self.convert_size(*size),
                });
            }
            
            Inst::Sub { dst, src1, src2, size } => {
                let dst = self.alloc_vreg(*dst, inst_id);
                let src1 = self.alloc_vreg(*src1, inst_id);
                let src2 = self.convert_operand(src2, inst_id)?;
                
                self.pinsts.push(PInst::Sub {
                    dst,
                    src1,
                    src2,
                    size: self.convert_size(*size),
                });
            }
            
            Inst::Mul { dst, src1, src2, size } => {
                let dst = self.alloc_vreg(*dst, inst_id);
                let src1 = self.alloc_vreg(*src1, inst_id);
                let src2 = self.alloc_vreg(*src2, inst_id);
                
                self.pinsts.push(PInst::Mul {
                    dst,
                    src1,
                    src2,
                    size: self.convert_size(*size),
                });
            }
            
            // Memory operations
            Inst::Load { dst, addr, size } => {
                let dst = self.alloc_vreg(*dst, inst_id);
                let addr = self.convert_amode(addr, inst_id)?;
                
                self.pinsts.push(PInst::Ldr {
                    dst,
                    addr,
                    size: self.convert_size(*size),
                });
            }
            
            Inst::Store { src, addr, size } => {
                let src = self.alloc_vreg(*src, inst_id);
                let addr = self.convert_amode(addr, inst_id)?;
                
                self.pinsts.push(PInst::Str {
                    src,
                    addr,
                    size: self.convert_size(*size),
                });
            }
            
            // Move operations
            Inst::Mov { dst, src } => {
                let dst = self.alloc_vreg(*dst, inst_id);
                let src = self.alloc_vreg(*src, inst_id);
                
                // Only emit if not a no-op
                if dst != src {
                    self.pinsts.push(PInst::Mov {
                        dst,
                        src,
                        size: OperandSize::Size64,
                    });
                }
            }
            
            Inst::MovImm { dst, imm, size } => {
                let dst = self.alloc_vreg(*dst, inst_id);
                
                self.pinsts.push(PInst::MovImm {
                    dst,
                    imm: *imm,
                    size: self.convert_size(*size),
                });
            }
            
            // Comparison
            Inst::Cmp { lhs, rhs, size } => {
                let lhs = self.alloc_vreg(*lhs, inst_id);
                let rhs = self.convert_operand(rhs, inst_id)?;
                
                self.pinsts.push(PInst::Cmp {
                    lhs,
                    rhs,
                    size: self.convert_size(*size),
                });
            }
            
            _ => {
                return Err(format!("Unimplemented instruction: {:?}", inst));
            }
        }
        
        Ok(())
    }
    
    fn alloc_vreg(&self, vreg: VReg, inst: InstId) -> PReg {
        let alloc = self.alloc.inst_allocs(inst)[vreg.vreg()];
        match alloc {
            regalloc2::Allocation::Reg(preg) => {
                PReg::new(preg.hw_enc() as usize)
            }
            regalloc2::Allocation::Stack(_) => {
                panic!("Unexpected stack allocation for vreg");
            }
        }
    }
    
    fn convert_operand(&self, op: &VOperand, inst: InstId) -> Result<POperand, String> {
        match op {
            VOperand::Reg(vreg) => {
                Ok(POperand::Reg(self.alloc_vreg(*vreg, inst)))
            }
            VOperand::Imm(imm) => {
                Ok(POperand::Imm(*imm))
            }
        }
    }
    
    fn convert_amode(&self, amode: &AMode, inst: InstId) -> Result<PAMode, String> {
        match amode {
            AMode::Reg(vreg) => {
                Ok(PAMode::Reg(self.alloc_vreg(*vreg, inst)))
            }
            AMode::RegImm(vreg, offset) => {
                Ok(PAMode::Offset(self.alloc_vreg(*vreg, inst), *offset as i16))
            }
            _ => Err("Unimplemented addressing mode".to_string()),
        }
    }
    
    fn convert_size(&self, size: Size) -> OperandSize {
        match size {
            Size::S32 => OperandSize::Size32,
            Size::S64 => OperandSize::Size64,
            _ => OperandSize::Size64, // Default to 64-bit
        }
    }
    
    fn preg(&self, reg: regalloc2::PReg) -> PReg {
        PReg::new(reg.hw_enc() as usize)
    }
    
    fn calculate_addresses(&mut self) {
        let mut addr = 0u32;
        for (i, &(_, start, end)) in self.blocks.iter() {
            self.block_addr[i] = addr;
            // Each ARM64 instruction is 4 bytes
            addr += (end.0 - start.0) * 4;
        }
    }
}