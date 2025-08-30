//! ARM64 stack frame management
//!
//! This module implements prologue and epilogue generation for ARM64 functions,
//! handling stack allocation, register saving, and frame pointer setup.

use super::inst::{PInst, OperandSize, POperand, PAMode};
use super::regs::{PReg, PRegSet};
use super::calling_conv::{Arm64CallConv, Arm64FrameLayout};
use crate::arch::target::OperatingSystem;

/// Generate function prologue
pub fn generate_prologue(
    layout: &Arm64FrameLayout,
    call_conv: &Arm64CallConv,
) -> Vec<PInst> {
    let mut insts = Vec::new();
    let sp = call_conv.stack_pointer();
    let fp = call_conv.frame_pointer();
    let lr = call_conv.link_register();
    
    if layout.frame_size == 0 && layout.saved_regs.is_empty() {
        // Leaf function with no locals - no prologue needed
        return insts;
    }
    
    // Save FP and LR as a pair (common ARM64 pattern)
    // stp x29, x30, [sp, #-16]!
    insts.push(PInst::Str {
        src: fp,
        addr: PAMode::PreIndex(sp, -16),
        size: OperandSize::Size64,
    });
    insts.push(PInst::Str {
        src: lr,
        addr: PAMode::Offset(sp, 8),
        size: OperandSize::Size64,
    });
    
    // Set up frame pointer
    // mov x29, sp
    insts.push(PInst::Mov {
        dst: fp,
        src: sp,
        size: OperandSize::Size64,
    });
    
    // Save other callee-saved registers
    let mut offset = 16; // Start after FP/LR
    for &reg in &layout.saved_regs {
        if reg != fp && reg != lr {
            insts.push(PInst::Str {
                src: reg,
                addr: PAMode::Offset(sp, -(offset as i16)),
                size: OperandSize::Size64,
            });
            offset += 8;
        }
    }
    
    // Allocate stack space
    if layout.frame_size > 0 {
        // sub sp, sp, #frame_size
        insts.push(PInst::Sub {
            dst: sp,
            src1: sp,
            src2: POperand::Imm(layout.frame_size as u64),
            size: OperandSize::Size64,
        });
    }
    
    insts
}

/// Generate function epilogue
pub fn generate_epilogue(
    layout: &Arm64FrameLayout,
    call_conv: &Arm64CallConv,
) -> Vec<PInst> {
    let mut insts = Vec::new();
    let sp = call_conv.stack_pointer();
    let fp = call_conv.frame_pointer();
    let lr = call_conv.link_register();
    
    if layout.frame_size == 0 && layout.saved_regs.is_empty() {
        // Leaf function - just return
        insts.push(PInst::Ret);
        return insts;
    }
    
    // Deallocate stack space
    if layout.frame_size > 0 {
        // add sp, sp, #frame_size
        insts.push(PInst::Add {
            dst: sp,
            src1: sp,
            src2: POperand::Imm(layout.frame_size as u64),
            size: OperandSize::Size64,
        });
    }
    
    // Restore callee-saved registers (in reverse order)
    let mut offset = 16;
    for &reg in layout.saved_regs.iter().rev() {
        if reg != fp && reg != lr {
            insts.push(PInst::Ldr {
                dst: reg,
                addr: PAMode::Offset(sp, -(offset as i16)),
                size: OperandSize::Size64,
            });
            offset += 8;
        }
    }
    
    // Restore FP and LR
    insts.push(PInst::Ldr {
        dst: fp,
        addr: PAMode::Offset(sp, 0),
        size: OperandSize::Size64,
    });
    insts.push(PInst::Ldr {
        dst: lr,
        addr: PAMode::Offset(sp, 8),
        size: OperandSize::Size64,
    });
    
    // Adjust stack pointer
    // add sp, sp, #16
    insts.push(PInst::Add {
        dst: sp,
        src1: sp,
        src2: POperand::Imm(16),
        size: OperandSize::Size64,
    });
    
    // Return
    insts.push(PInst::Ret);
    
    insts
}

/// Helper to generate stack allocation
pub fn allocate_stack(size: u32) -> Vec<PInst> {
    if size == 0 {
        return vec![];
    }
    
    vec![PInst::Sub {
        dst: PReg::new(31), // SP
        src1: PReg::new(31),
        src2: POperand::Imm(size as u64),
        size: OperandSize::Size64,
    }]
}

/// Helper to generate stack deallocation
pub fn deallocate_stack(size: u32) -> Vec<PInst> {
    if size == 0 {
        return vec![];
    }
    
    vec![PInst::Add {
        dst: PReg::new(31), // SP
        src1: PReg::new(31),
        src2: POperand::Imm(size as u64),
        size: OperandSize::Size64,
    }]
}

/// Generate instructions to save a register on the stack
pub fn save_register(reg: PReg, offset: i16) -> PInst {
    PInst::Str {
        src: reg,
        addr: PAMode::Offset(PReg::new(31), offset), // SP + offset
        size: OperandSize::Size64,
    }
}

/// Generate instructions to restore a register from the stack
pub fn restore_register(reg: PReg, offset: i16) -> PInst {
    PInst::Ldr {
        dst: reg,
        addr: PAMode::Offset(PReg::new(31), offset), // SP + offset
        size: OperandSize::Size64,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_simple_prologue() {
        let call_conv = Arm64CallConv::new(OperatingSystem::Linux);
        let mut used_regs = PRegSet::default();
        used_regs.insert(PReg::new(19)); // X19 is callee-saved
        
        let layout = Arm64FrameLayout::calculate(32, 0, &used_regs, &call_conv);
        let prologue = generate_prologue(&layout, &call_conv);
        
        // Should have:
        // 1. Save FP/LR
        // 2. Setup FP
        // 3. Save X19
        // 4. Allocate stack
        assert!(prologue.len() >= 4);
        
        // First instruction should save FP
        match &prologue[0] {
            PInst::Str { src, .. } => assert_eq!(src.index(), 29), // FP
            _ => panic!("Expected STR"),
        }
    }
    
    #[test]
    fn test_leaf_function() {
        let call_conv = Arm64CallConv::new(OperatingSystem::Linux);
        let layout = Arm64FrameLayout {
            locals_size: 0,
            spill_size: 0,
            saved_regs: vec![],
            frame_size: 0,
        };
        
        let prologue = generate_prologue(&layout, &call_conv);
        assert!(prologue.is_empty()); // No prologue needed
        
        let epilogue = generate_epilogue(&layout, &call_conv);
        assert_eq!(epilogue.len(), 1); // Just RET
        assert!(matches!(epilogue[0], PInst::Ret));
    }
}