//! ARM64 stack frame generation
//!
//! This module handles function prologue and epilogue generation,
//! implementing proper stack frame setup according to AAPCS64.

use super::{
    inst::{PInst, PAMode, OperandSize, POperand},
    regs::{PReg, PRegSet, SP, FP, LR},
    calling_conv::{Arm64CallConv, Arm64FrameLayout},
};
use crate::arch::target::OperatingSystem;

/// Generate function prologue instructions
pub fn generate_prologue(
    layout: &Arm64FrameLayout,
    os: OperatingSystem,
) -> Vec<PInst> {
    let mut insts = Vec::new();
    
    // If frame size is 0 and no registers to save, we're a leaf function
    if layout.frame_size == 0 && layout.saved_regs.is_empty() {
        return insts;
    }
    
    // Save callee-saved registers
    // ARM64 convention: save registers in pairs when possible
    let mut saved_pairs = Vec::new();
    let mut saved_singles = Vec::new();
    
    // Group registers into pairs
    for chunk in layout.saved_regs.chunks(2) {
        if chunk.len() == 2 {
            saved_pairs.push((chunk[0], chunk[1]));
        } else {
            saved_singles.push(chunk[0]);
        }
    }
    
    // Calculate initial stack adjustment
    let initial_adjust = layout.frame_size;
    
    if !saved_pairs.is_empty() || !saved_singles.is_empty() {
        // Use STP (store pair) with pre-decrement for first pair
        if let Some((reg1, reg2)) = saved_pairs.first() {
            // stp x29, x30, [sp, #-frame_size]!
            insts.push(PInst::StpPreIndex {
                src1: *reg1,
                src2: *reg2,
                base: SP,
                offset: -(initial_adjust as i16),
            });
            
            // Save remaining pairs
            let mut offset = 16; // First pair already saved
            for &(reg1, reg2) in &saved_pairs[1..] {
                insts.push(PInst::Stp {
                    src1: reg1,
                    src2: reg2,
                    addr: PAMode::Offset(SP, offset),
                });
                offset += 16;
            }
            
            // Save singles
            for &reg in &saved_singles {
                insts.push(PInst::Str {
                    src: reg,
                    addr: PAMode::Offset(SP, offset),
                    size: OperandSize::Size64,
                });
                offset += 8;
            }
        } else if !saved_singles.is_empty() {
            // Only single registers to save
            // sub sp, sp, #frame_size
            insts.push(PInst::Sub {
                dst: SP,
                src1: SP,
                src2: POperand::Imm(initial_adjust as u64),
                size: OperandSize::Size64,
            });
            
            let mut offset = 0;
            for &reg in &saved_singles {
                insts.push(PInst::Str {
                    src: reg,
                    addr: PAMode::Offset(SP, offset),
                    size: OperandSize::Size64,
                });
                offset += 8;
            }
        }
    } else {
        // Just allocate stack space
        if initial_adjust > 0 {
            insts.push(PInst::Sub {
                dst: SP,
                src1: SP,
                src2: POperand::Imm(initial_adjust as u64),
                size: OperandSize::Size64,
            });
        }
    }
    
    // Set up frame pointer if used
    if layout.saved_regs.contains(&FP) {
        // mov x29, sp
        insts.push(PInst::Mov {
            dst: FP,
            src: SP,
            size: OperandSize::Size64,
        });
    }
    
    insts
}

/// Generate function epilogue instructions
pub fn generate_epilogue(
    layout: &Arm64FrameLayout,
    os: OperatingSystem,
) -> Vec<PInst> {
    let mut insts = Vec::new();
    
    // If frame size is 0 and no registers to save, just return
    if layout.frame_size == 0 && layout.saved_regs.is_empty() {
        insts.push(PInst::Ret);
        return insts;
    }
    
    // Group registers into pairs for restoration
    let mut saved_pairs = Vec::new();
    let mut saved_singles = Vec::new();
    
    for chunk in layout.saved_regs.chunks(2) {
        if chunk.len() == 2 {
            saved_pairs.push((chunk[0], chunk[1]));
        } else {
            saved_singles.push(chunk[0]);
        }
    }
    
    // Restore singles first
    let mut offset = (saved_pairs.len() * 16) as i16;
    for &reg in &saved_singles {
        insts.push(PInst::Ldr {
            dst: reg,
            addr: PAMode::Offset(SP, offset),
            size: OperandSize::Size64,
        });
        offset += 8;
    }
    
    // Restore pairs (except first which we'll do with post-increment)
    if saved_pairs.len() > 1 {
        let mut offset = 16; // Skip first pair
        for &(reg1, reg2) in &saved_pairs[1..] {
            insts.push(PInst::Ldp {
                dst1: reg1,
                dst2: reg2,
                addr: PAMode::Offset(SP, offset),
            });
            offset += 16;
        }
    }
    
    // Restore first pair with post-increment to deallocate frame
    if let Some((reg1, reg2)) = saved_pairs.first() {
        // ldp x29, x30, [sp], #frame_size
        insts.push(PInst::LdpPostIndex {
            dst1: *reg1,
            dst2: *reg2,
            base: SP,
            offset: layout.frame_size as i16,
        });
    } else if layout.frame_size > 0 {
        // Just deallocate stack
        insts.push(PInst::Add {
            dst: SP,
            src1: SP,
            src2: POperand::Imm(layout.frame_size as u64),
            size: OperandSize::Size64,
        });
    }
    
    insts.push(PInst::Ret);
    insts
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
    fn test_leaf_function_prologue() {
        let layout = Arm64FrameLayout {
            locals_size: 0,
            spill_size: 0,
            saved_regs: vec![],
            frame_size: 0,
        };
        
        let prologue = generate_prologue(&layout, OperatingSystem::Linux);
        assert!(prologue.is_empty(), "Leaf function should have no prologue");
    }
    
    #[test]
    fn test_simple_frame() {
        let layout = Arm64FrameLayout {
            locals_size: 16,
            spill_size: 0,
            saved_regs: vec![FP, LR],
            frame_size: 32,
        };
        
        let prologue = generate_prologue(&layout, OperatingSystem::Linux);
        assert!(!prologue.is_empty());
        
        // Should start with stp x29, x30, [sp, #-32]!
        match &prologue[0] {
            PInst::StpPreIndex { src1, src2, base, offset } => {
                assert_eq!(*src1, FP);
                assert_eq!(*src2, LR);
                assert_eq!(*base, SP);
                assert_eq!(*offset, -32);
            }
            _ => panic!("Expected StpPreIndex"),
        }
    }
    
    #[test]
    fn test_slot_allocator() {
        let mut allocator = StackSlotAllocator::new();
        
        let slot1 = allocator.allocate(8, 8);
        assert_eq!(slot1, 0);
        
        let slot2 = allocator.allocate(4, 4);
        assert_eq!(slot2, 8);
        
        let slot3 = allocator.allocate(8, 16);
        assert_eq!(slot3, 16); // Aligned to 16
        
        assert_eq!(allocator.total_size(), 24);
    }
}