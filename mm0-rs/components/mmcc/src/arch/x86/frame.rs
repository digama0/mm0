//! x86-64 stack frame generation
//!
//! This module handles function prologue and epilogue generation,
//! implementing proper stack frame setup according to System V ABI.

use super::{
    RegMemImm, AMode, Inst, InstExt, Offset,
    PReg, PRegSet, VReg, 
    calling_conv::{X86CallConv, X86FrameLayout},
};
use crate::types::Size;
use crate::arch::target::OperatingSystem;

/// Generate function prologue instructions
pub fn generate_prologue(
    layout: &X86FrameLayout,
    os: OperatingSystem,
) -> Vec<Inst> {
    let mut insts = Vec::new();
    let conv = X86CallConv::new(os);
    
    // Check if we can use red zone optimization
    if layout.can_use_red_zone(&conv) && layout.saved_regs.is_empty() {
        // Leaf function with small frame - use red zone
        return insts;
    }
    
    // Standard prologue
    // 1. Save callee-saved registers (including RBP)
    for &reg in &layout.saved_regs {
        insts.push(Inst::push64(RegMemImm::reg(reg)));
    }
    
    // 2. Set up frame pointer if RBP was saved
    if layout.saved_regs.first() == Some(&conv.frame_pointer()) {
        // mov rbp, rsp
        insts.push(Inst::mov(
            Size::S64,
            RegMemImm::reg(conv.stack_pointer()),
            conv.frame_pointer().into(),
        ));
    }
    
    // 3. Allocate stack space
    let adjustment = layout.stack_adjustment(&conv);
    if adjustment > 0 {
        if adjustment <= 127 {
            // sub rsp, imm8
            insts.push(Inst::alu_rmi_r(
                Size::S64,
                InstExt::Sub,
                RegMemImm::imm(adjustment as u32),
                conv.stack_pointer().into(),
            ));
        } else {
            // sub rsp, imm32
            insts.push(Inst::alu_rmi_r(
                Size::S64,
                InstExt::Sub,
                RegMemImm::imm(adjustment as u32),
                conv.stack_pointer().into(),
            ));
        }
    }
    
    insts
}

/// Generate function epilogue instructions
pub fn generate_epilogue(
    layout: &X86FrameLayout,
    os: OperatingSystem,
) -> Vec<Inst> {
    let mut insts = Vec::new();
    let conv = X86CallConv::new(os);
    
    // Check if we used red zone optimization
    if layout.can_use_red_zone(&conv) && layout.saved_regs.is_empty() {
        // Leaf function - just return
        insts.push(Inst::ret());
        return insts;
    }
    
    // Standard epilogue (reverse of prologue)
    // 1. Deallocate stack space
    let adjustment = layout.stack_adjustment(&conv);
    if adjustment > 0 {
        // If we used frame pointer, restore RSP from it
        if layout.saved_regs.first() == Some(&conv.frame_pointer()) {
            // mov rsp, rbp
            insts.push(Inst::mov(
                Size::S64,
                RegMemImm::reg(conv.frame_pointer()),
                conv.stack_pointer().into(),
            ));
        } else {
            // add rsp, adjustment
            insts.push(Inst::alu_rmi_r(
                Size::S64,
                InstExt::Add,
                RegMemImm::imm(adjustment as u32),
                conv.stack_pointer().into(),
            ));
        }
    }
    
    // 2. Restore callee-saved registers (in reverse order)
    for &reg in layout.saved_regs.iter().rev() {
        insts.push(Inst::pop64(reg.into()));
    }
    
    // 3. Return
    insts.push(Inst::ret());
    
    insts
}

/// Helper functions for accessing stack slots
impl X86FrameLayout {
    /// Create an addressing mode for a local variable
    pub fn local_addr(&self, offset: u32) -> AMode {
        let conv = X86CallConv::new(OperatingSystem::Linux); // OS doesn't matter here
        
        if self.saved_regs.first() == Some(&conv.frame_pointer()) {
            // Use frame pointer relative addressing
            AMode {
                off: Offset::Local(offset),
                base: conv.frame_pointer().into(),
                si: None,
            }
        } else {
            // Use stack pointer relative addressing
            // Need to account for current stack depth
            let stack_offset = self.frame_size - self.locals_size + offset;
            AMode {
                off: Offset::Local(stack_offset),
                base: conv.stack_pointer().into(),
                si: None,
            }
        }
    }
    
    /// Create an addressing mode for a spill slot
    pub fn spill_addr(&self, slot: u32) -> AMode {
        let offset = self.locals_size + slot * 8;
        self.local_addr(offset)
    }
}

/// Stack slot allocation helper
pub struct StackSlotAllocator {
    current_offset: u32,
    alignment: u32,
}

impl StackSlotAllocator {
    pub fn new() -> Self {
        Self {
            current_offset: 0,
            alignment: 8, // Default 8-byte alignment
        }
    }
    
    /// Allocate space for a local variable
    pub fn allocate(&mut self, size: u32, align: u32) -> u32 {
        // Align current offset
        let align = align.max(self.alignment);
        self.current_offset = (self.current_offset + align - 1) & !(align - 1);
        
        let offset = self.current_offset;
        self.current_offset += size;
        
        offset
    }
    
    /// Get total space allocated
    pub fn total_size(&self) -> u32 {
        self.current_offset
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_red_zone_optimization() {
        let mut used_regs = PRegSet::default();
        let conv = X86CallConv::new(OperatingSystem::Linux);
        
        // Small leaf function should use red zone
        let layout = X86FrameLayout::calculate(64, 0, &used_regs, &conv);
        assert!(layout.can_use_red_zone(&conv));
        
        let prologue = generate_prologue(&layout, OperatingSystem::Linux);
        assert!(prologue.is_empty(), "Red zone function should have no prologue");
    }
    
    #[test]
    fn test_standard_frame() {
        let mut used_regs = PRegSet::default();
        used_regs.insert(PReg::new(3)); // RBX
        
        let conv = X86CallConv::new(OperatingSystem::Linux);
        let layout = X86FrameLayout::calculate(32, 16, &used_regs, &conv);
        
        let prologue = generate_prologue(&layout, OperatingSystem::Linux);
        assert!(!prologue.is_empty());
        
        // Should start with push rbp
        // Then push rbx
        // Then sub rsp, ...
    }
}