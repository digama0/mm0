//! x86-64 calling convention implementation (System V ABI)
//!
//! This module implements the x86-64 calling convention for function calls,
//! following the System V ABI used on Linux/BSD/macOS.

use crate::types::vcode::{VReg, ArgAbi};
use crate::types::{Size, IntTy};
use crate::arch::target::OperatingSystem;
use super::{PReg, PRegSet};

/// x86-64 calling convention parameters
pub struct X86CallConv {
    /// Target operating system
    os: OperatingSystem,
}

impl X86CallConv {
    /// Create calling convention for target OS
    pub fn new(os: OperatingSystem) -> Self {
        Self { os }
    }
    
    /// Get registers used for passing integer arguments
    pub fn arg_regs(&self) -> &'static [PReg] {
        // RDI, RSI, RDX, RCX, R8, R9 for first 6 arguments
        &[
            PReg::new(7),  // RDI
            PReg::new(6),  // RSI
            PReg::new(2),  // RDX
            PReg::new(1),  // RCX
            PReg::new(8),  // R8
            PReg::new(9),  // R9
        ]
    }
    
    /// Get registers used for return values
    pub fn ret_regs(&self) -> &'static [PReg] {
        // RAX for primary return, RDX for 128-bit values
        &[
            PReg::new(0),  // RAX
            PReg::new(2),  // RDX
        ]
    }
    
    /// Get callee-saved registers (must be preserved across calls)
    pub fn callee_saved(&self) -> &'static [PReg] {
        // RBX, RBP, R12-R15
        &[
            PReg::new(3),   // RBX
            PReg::new(5),   // RBP
            PReg::new(12),  // R12
            PReg::new(13),  // R13
            PReg::new(14),  // R14
            PReg::new(15),  // R15
        ]
    }
    
    /// Get caller-saved registers (can be clobbered by calls)
    pub fn caller_saved(&self) -> &'static [PReg] {
        // RAX, RCX, RDX, RSI, RDI, R8-R11
        &[
            PReg::new(0),   // RAX
            PReg::new(1),   // RCX
            PReg::new(2),   // RDX
            PReg::new(6),   // RSI
            PReg::new(7),   // RDI
            PReg::new(8),   // R8
            PReg::new(9),   // R9
            PReg::new(10),  // R10
            PReg::new(11),  // R11
        ]
    }
    
    /// Get registers clobbered by a function call
    pub fn call_clobbers(&self) -> PRegSet {
        let mut clobbers = PRegSet::default();
        for &reg in self.caller_saved() {
            clobbers.insert(reg);
        }
        clobbers
    }
    
    /// Determine how an argument should be passed
    pub fn arg_abi(&self, arg_idx: usize, ty: IntTy) -> ArgAbi {
        let arg_regs = self.arg_regs();
        
        if arg_idx < arg_regs.len() {
            // Pass in register
            ArgAbi::Reg(arg_regs[arg_idx], Size::S64)
        } else {
            // Pass on stack
            // Stack slots are 8-byte aligned, pushed right-to-left
            let stack_offset = (arg_idx - arg_regs.len()) * 8;
            ArgAbi::Mem { off: stack_offset as u32, sz: 8 }
        }
    }
    
    /// Determine how a return value should be passed
    pub fn ret_abi(&self, ret_idx: usize, ty: IntTy) -> ArgAbi {
        let ret_regs = self.ret_regs();
        
        if ret_idx < ret_regs.len() && ty.size().bytes().unwrap_or(8) <= 8 {
            // Return in register
            ArgAbi::Reg(ret_regs[ret_idx], Size::S64)
        } else {
            // Large returns via hidden pointer (passed in RDI, others shift)
            ArgAbi::Mem { off: 0, sz: 8 }
        }
    }
    
    /// Get the frame pointer register
    pub fn frame_pointer(&self) -> PReg {
        PReg::new(5) // RBP
    }
    
    /// Get the stack pointer register
    pub fn stack_pointer(&self) -> PReg {
        PReg::new(4) // RSP
    }
    
    /// Stack alignment requirement (16 bytes for x86-64)
    pub fn stack_alignment(&self) -> u32 {
        16
    }
    
    /// Red zone size (area below RSP that won't be clobbered)
    pub fn red_zone_size(&self) -> u32 {
        match self.os {
            OperatingSystem::Linux | OperatingSystem::MacOS => 128,
            _ => 0, // Windows has no red zone
        }
    }
}

/// Function prologue/epilogue generation for x86-64
pub struct X86FrameLayout {
    /// Size of local variables
    pub locals_size: u32,
    /// Size needed for spilled registers
    pub spill_size: u32,
    /// Callee-saved registers to preserve
    pub saved_regs: Vec<PReg>,
    /// Total frame size (aligned to 16 bytes)
    pub frame_size: u32,
}

impl X86FrameLayout {
    /// Calculate frame layout for a function
    pub fn calculate(
        locals: u32,
        spills: u32,
        used_regs: &PRegSet,
        call_conv: &X86CallConv,
    ) -> Self {
        // Determine which callee-saved registers need preserving
        let mut saved_regs = Vec::new();
        for &reg in call_conv.callee_saved() {
            if used_regs.get(reg) {
                saved_regs.push(reg);
            }
        }
        
        // Always save RBP for non-leaf functions
        let rbp = call_conv.frame_pointer();
        if !saved_regs.contains(&rbp) {
            saved_regs.insert(0, rbp); // RBP goes first
        }
        
        // Calculate space needed
        let saved_regs_size = saved_regs.len() as u32 * 8;
        let total = locals + spills + saved_regs_size;
        
        // Align to 16 bytes (accounting for return address)
        // Stack must be 16-byte aligned BEFORE the call instruction
        let frame_size = (total + 15) & !15;
        
        Self {
            locals_size: locals,
            spill_size: spills,
            saved_regs,
            frame_size,
        }
    }
    
    /// Offset of saved registers from frame pointer
    pub fn saved_reg_offset(&self, reg: PReg) -> Option<i32> {
        self.saved_regs.iter().position(|&r| r == reg)
            .map(|i| -(8 + i as i32 * 8)) // RBP at [RBP-8], others below
    }
    
    /// Offset of local variable from frame pointer
    pub fn local_offset(&self, offset: u32) -> i32 {
        -(self.saved_regs.len() as i32 * 8 + 8 + offset as i32)
    }
    
    /// Offset of spill slot from frame pointer
    pub fn spill_offset(&self, slot: u32) -> i32 {
        self.local_offset(self.locals_size + slot * 8)
    }
}

/// x86-64 specific frame helpers
impl X86FrameLayout {
    /// Check if we can use the red zone for this function
    pub fn can_use_red_zone(&self, call_conv: &X86CallConv) -> bool {
        // Can use red zone if:
        // 1. Platform has red zone
        // 2. Function is leaf (no calls)
        // 3. Total frame size fits in red zone
        call_conv.red_zone_size() > 0 && 
        self.frame_size <= call_conv.red_zone_size()
    }
    
    /// Get actual stack adjustment needed
    pub fn stack_adjustment(&self, call_conv: &X86CallConv) -> u32 {
        if self.can_use_red_zone(call_conv) {
            0 // No adjustment needed, use red zone
        } else {
            self.frame_size
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_arg_passing() {
        let conv = X86CallConv::new(OperatingSystem::Linux);
        
        // First 6 args go in registers
        let regs = conv.arg_regs();
        assert_eq!(regs.len(), 6);
        
        // Check first arg goes in RDI
        match conv.arg_abi(0, IntTy::Int(Size::S64)) {
            ArgAbi::Reg(reg, _) => assert_eq!(reg.index(), 7), // RDI
            _ => panic!("Expected register for arg 0"),
        }
        
        // 7th arg goes on stack
        match conv.arg_abi(6, IntTy::Int(Size::S64)) {
            ArgAbi::Mem { off: 0, .. } => {}
            _ => panic!("Expected stack for arg 6"),
        }
    }
    
    #[test]
    fn test_frame_layout() {
        let conv = X86CallConv::new(OperatingSystem::Linux);
        let mut used_regs = PRegSet::default();
        used_regs.insert(PReg::new(3)); // RBX is callee-saved
        
        let layout = X86FrameLayout::calculate(24, 16, &used_regs, &conv);
        
        // Should save RBP and RBX
        assert!(layout.saved_regs.contains(&PReg::new(5))); // RBP
        assert!(layout.saved_regs.contains(&PReg::new(3))); // RBX
        
        // Frame size should be aligned to 16
        assert_eq!(layout.frame_size % 16, 0);
    }
}