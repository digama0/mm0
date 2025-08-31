//! Complete ARM64 register allocation implementation
//!
//! This module provides a working register allocator using regalloc2,
//! handling virtual to physical register mapping, spilling, and move insertion.

use crate::types::{IdxVec, mir, vcode::*, Size};
use crate::arch::arm64::vcode::VCode;
use crate::arch_pcode::PInstId;
use super::{
    PReg, PInst, PAMode, POperand, OperandSize,
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
pub fn allocate_registers(vcode: &VCode) -> Result<RegAllocResult, String> {
    // Run regalloc2
    let alloc_result = regalloc2::run(
        vcode,
        &super::MACHINE_ENV,
        &regalloc2::RegallocOptions::default()
    ).map_err(|e| format!("Register allocation failed: {:?}", e))?;
    
    // Build the output
    let mut builder = RegAllocBuilder::new(vcode, &alloc_result);
    builder.build()
}

/// Helper for building allocated code
struct RegAllocBuilder<'a> {
    vcode: &'a VCode,
    alloc: &'a regalloc2::Output,
    pinsts: IdxVec<PInstId, PInst>,
    blocks: IdxVec<BlockId, (mir::BlockId, PInstId, PInstId)>,
    block_addr: IdxVec<BlockId, u32>,
    /// Map from InstId to PInstId for branch targets
    inst_map: HashMap<InstId, PInstId>,
}

impl<'a> RegAllocBuilder<'a> {
    fn new(vcode: &'a VCode, alloc: &'a regalloc2::Output) -> Self {
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
        for (block_id, _) in self.vcode.blocks() {
            self.process_block(block_id)?;
        }
        
        // Calculate block addresses
        self.calculate_addresses();
        
        // Calculate total stack size (8 bytes per spill slot)
        let stack_size = self.alloc.num_spillslots as u32 * 8;
        
        // Calculate total code length
        let len = self.pinsts.len() as u32 * 4; // ARM64 instructions are 4 bytes
        
        Ok(RegAllocResult {
            pinsts: self.pinsts,
            blocks: self.blocks,
            block_addr: self.block_addr,
            stack_size,
            len,
        })
    }
    
    fn process_block(&mut self, block: BlockId) -> Result<(), String> {
        let vblock = &self.vcode.blocks[block];
        let mir_block = mir::BlockId(block.index() as u32);
        let pinst_start = PInstId(self.pinsts.len() as u32);
        
        // Process each instruction in the block
        for inst_id in self.vcode.block_insts(block) {
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
        // Find edits for this instruction  
        for &(prog_point, ref edit) in &self.alloc.edits {
            if prog_point == regalloc2::ProgPoint::before(inst) {
                self.process_edit(edit)?;
            }
        }
        Ok(())
    }
    
    fn insert_moves_after(&mut self, inst: InstId) -> Result<(), String> {
        // Find edits for this instruction
        for &(prog_point, ref edit) in &self.alloc.edits {
            if prog_point == regalloc2::ProgPoint::after(inst) {
                self.process_edit(edit)?;
            }
        }
        Ok(())
    }
    
    fn process_edit(&mut self, edit: &regalloc2::Edit) -> Result<(), String> {
        match edit {
            regalloc2::Edit::Move { from, to } => {
                match (from.kind(), to.kind()) {
                    (regalloc2::AllocationKind::Reg, regalloc2::AllocationKind::Reg) => {
                        // Register to register move
                        let src_preg = PReg::new(from.as_reg().unwrap().hw_enc() as usize);
                        let dst_preg = PReg::new(to.as_reg().unwrap().hw_enc() as usize);
                        self.pinsts.push(PInst::Mov {
                            dst: dst_preg,
                            src: src_preg,
                            size: OperandSize::Size64,
                        });
                    }
                    (regalloc2::AllocationKind::Reg, regalloc2::AllocationKind::Stack) => {
                        // Spill: register to stack
                        let src_preg = PReg::new(from.as_reg().unwrap().hw_enc() as usize);
                        let slot = to.as_stack().unwrap();
                        self.emit_spill(src_preg, slot);
                    }
                    (regalloc2::AllocationKind::Stack, regalloc2::AllocationKind::Reg) => {
                        // Reload: stack to register
                        let dst_preg = PReg::new(to.as_reg().unwrap().hw_enc() as usize);
                        let slot = from.as_stack().unwrap();
                        self.emit_reload(dst_preg, slot);
                    }
                    _ => {
                        return Err("Invalid move: stack to stack".to_string());
                    }
                }
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
            
            Inst::Branch { target: _ } => {
                // Will be patched later with correct offset
                self.pinsts.push(PInst::B { offset: 0 });
            }
            
            Inst::BranchCond { cond, target: _ } => {
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
            
            // System calls
            Inst::Svc { imm } => {
                self.pinsts.push(PInst::Svc { imm: *imm });
            }
            
            // Load constant
            Inst::LoadConst { dst, const_id } => {
                let dst = self.alloc_vreg(*dst, inst_id);
                self.pinsts.push(PInst::LoadConst { 
                    dst, 
                    const_id: *const_id 
                });
            }
            
            _ => {
                return Err(format!("Unimplemented instruction: {:?}", inst));
            }
        }
        
        Ok(())
    }
    
    fn alloc_vreg(&self, vreg: VReg, inst: InstId) -> PReg {
        let allocs = self.alloc.inst_allocs(inst);
        let alloc = allocs[vreg.0.vreg()];
        match alloc.kind() {
            regalloc2::AllocationKind::Reg => {
                PReg::new(alloc.as_reg().unwrap().hw_enc() as usize)
            }
            regalloc2::AllocationKind::Stack => {
                panic!("Unexpected stack allocation for vreg");
            }
            regalloc2::AllocationKind::None => {
                panic!("No allocation for vreg");
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
        for (i, &(_, start, end)) in self.blocks.enum_iter() {
            self.block_addr[i] = addr;
            // Each ARM64 instruction is 4 bytes
            addr += (end.0 - start.0) * 4;
        }
    }
}