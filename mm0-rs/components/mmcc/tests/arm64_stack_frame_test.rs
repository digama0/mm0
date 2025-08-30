//! Integration test for ARM64 stack frame management

use mmcc::arch::arm64::{
    calling_conv::{Arm64CallConv, Arm64FrameLayout},
    stack_frame::{generate_prologue, generate_epilogue},
    regs::{PReg, PRegSet},
    inst::{PInst, OperandSize},
};
use mmcc::arch::target::OperatingSystem;

/// Test a simple function with local variables
#[test]
fn test_function_with_locals() {
    let call_conv = Arm64CallConv::new(OperatingSystem::Linux);
    let mut used_regs = PRegSet::default();
    
    // Function uses X19 and X20 (callee-saved)
    used_regs.insert(PReg::new(19));
    used_regs.insert(PReg::new(20));
    
    // 48 bytes of locals, no spills
    let layout = Arm64FrameLayout::calculate(48, 0, &used_regs, &call_conv);
    
    // Generate prologue
    let prologue = generate_prologue(&layout, &call_conv);
    
    // Should save FP, LR, X19, X20 and allocate space
    assert!(prologue.len() >= 4);
    
    // Generate epilogue
    let epilogue = generate_epilogue(&layout, &call_conv);
    
    // Should restore everything and return
    assert!(epilogue.len() >= 4);
    assert!(matches!(epilogue.last(), Some(PInst::Ret)));
}

/// Test stack alignment
#[test]
fn test_stack_alignment() {
    let call_conv = Arm64CallConv::new(OperatingSystem::MacOS);
    let used_regs = PRegSet::default();
    
    // Test various sizes to ensure 16-byte alignment
    for locals in [0, 8, 16, 24, 32, 40, 48, 56, 64] {
        let layout = Arm64FrameLayout::calculate(locals, 0, &used_regs, &call_conv);
        assert_eq!(layout.frame_size % 16, 0, "Frame size {} not aligned for locals {}", layout.frame_size, locals);
    }
}

/// Test a complex function with many saved registers
#[test]
fn test_many_saved_registers() {
    let call_conv = Arm64CallConv::new(OperatingSystem::Linux);
    let mut used_regs = PRegSet::default();
    
    // Use all callee-saved registers
    for i in 19..=28 {
        used_regs.insert(PReg::new(i));
    }
    
    let layout = Arm64FrameLayout::calculate(32, 16, &used_regs, &call_conv);
    
    // Should save FP, LR, and X19-X28 (12 registers total)
    assert_eq!(layout.saved_regs.len(), 12);
    
    let prologue = generate_prologue(&layout, &call_conv);
    let epilogue = generate_epilogue(&layout, &call_conv);
    
    // Count STR instructions in prologue
    let str_count = prologue.iter().filter(|inst| matches!(inst, PInst::Str { .. })).count();
    assert!(str_count >= 12); // At least one STR per saved register
    
    // Count LDR instructions in epilogue
    let ldr_count = epilogue.iter().filter(|inst| matches!(inst, PInst::Ldr { .. })).count();
    assert!(ldr_count >= 12); // At least one LDR per saved register
}

/// Test red zone handling
#[test]
fn test_red_zone() {
    // macOS has 128-byte red zone
    let macos_conv = Arm64CallConv::new(OperatingSystem::MacOS);
    assert_eq!(macos_conv.red_zone_size(), 128);
    
    // Linux has no red zone
    let linux_conv = Arm64CallConv::new(OperatingSystem::Linux);
    assert_eq!(linux_conv.red_zone_size(), 0);
}

/// Test frame pointer offsets
#[test]
fn test_frame_offsets() {
    let call_conv = Arm64CallConv::new(OperatingSystem::Linux);
    let mut used_regs = PRegSet::default();
    used_regs.insert(PReg::new(19));
    
    let layout = Arm64FrameLayout::calculate(32, 16, &used_regs, &call_conv);
    
    // Check saved register offset
    let x19_offset = layout.saved_reg_offset(PReg::new(19));
    assert!(x19_offset.is_some());
    assert!(x19_offset.unwrap() < 0); // Should be below FP
    
    // Check local variable offsets
    let local0 = layout.local_offset(0);
    let local8 = layout.local_offset(8);
    assert!(local0 < 0); // Below FP
    assert!(local8 < local0); // Further from FP
    
    // Check spill slot offsets
    let spill0 = layout.spill_offset(0);
    let spill1 = layout.spill_offset(1);
    assert!(spill0 < local0); // Spills below locals
    assert_eq!(spill1 - spill0, -8); // 8 bytes apart
}