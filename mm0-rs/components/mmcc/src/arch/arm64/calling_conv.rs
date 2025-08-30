//! ARM64 calling convention implementation (AAPCS64)
//!
//! This module implements the ARM64 calling convention for function calls,
//! following the ARM64 ABI (AAPCS64) for Linux/BSD and Apple's variant for macOS.

use crate::types::vcode::{VReg, ArgAbi};
use crate::types::{Size, IntTy};
use crate::arch::target::OperatingSystem;
use super::regs::{PReg, PRegSet};

/// ARM64 calling convention parameters
pub struct Arm64CallConv {
    /// Target operating system (affects some ABI details)
    os: OperatingSystem,
}

impl Arm64CallConv {
    /// Create calling convention for target OS
    pub fn new(os: OperatingSystem) -> Self {
        Self { os }
    }
    
    /// Get registers used for passing integer arguments
    pub fn arg_regs(&self) -> &'static [PReg] {
        // X0-X7 are used for the first 8 arguments
        &[
            PReg::new(0),  // X0
            PReg::new(1),  // X1
            PReg::new(2),  // X2
            PReg::new(3),  // X3
            PReg::new(4),  // X4
            PReg::new(5),  // X5
            PReg::new(6),  // X6
            PReg::new(7),  // X7
        ]
    }
    
    /// Get registers used for return values
    pub fn ret_regs(&self) -> &'static [PReg] {
        // X0-X7 can be used for returning large structs
        // But typically only X0 (and X1 for 128-bit values)
        &[
            PReg::new(0),  // X0
            PReg::new(1),  // X1
        ]
    }
    
    /// Get callee-saved registers (must be preserved across calls)
    pub fn callee_saved(&self) -> &'static [PReg] {
        &[
            // X19-X28 are callee-saved
            PReg::new(19), PReg::new(20), PReg::new(21), PReg::new(22),
            PReg::new(23), PReg::new(24), PReg::new(25), PReg::new(26),
            PReg::new(27), PReg::new(28),
            // X29 (FP) and X30 (LR) are also callee-saved
            PReg::new(29), // FP
            PReg::new(30), // LR
        ]
    }
    
    /// Get caller-saved registers (can be clobbered by calls)
    pub fn caller_saved(&self) -> &'static [PReg] {
        &[
            // X0-X18 are caller-saved
            PReg::new(0),  PReg::new(1),  PReg::new(2),  PReg::new(3),
            PReg::new(4),  PReg::new(5),  PReg::new(6),  PReg::new(7),
            PReg::new(8),  PReg::new(9),  PReg::new(10), PReg::new(11),
            PReg::new(12), PReg::new(13), PReg::new(14), PReg::new(15),
            PReg::new(16), PReg::new(17), PReg::new(18),
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
            ArgAbi::Reg(arg_regs[arg_idx], 0)
        } else {
            // Pass on stack
            // Stack slots are 8-byte aligned
            let stack_offset = (arg_idx - arg_regs.len()) * 8;
            ArgAbi::Mem(stack_offset as u32)
        }
    }
    
    /// Determine how a return value should be passed
    pub fn ret_abi(&self, ret_idx: usize, ty: IntTy) -> ArgAbi {
        let ret_regs = self.ret_regs();
        
        if ret_idx < ret_regs.len() && ty.size().bytes().unwrap_or(8) <= 8 {
            // Return in register
            ArgAbi::Reg(ret_regs[ret_idx], 0)
        } else {
            // Large returns via memory (caller allocates, passes pointer in X8)
            ArgAbi::Mem(0)
        }
    }
    
    /// Get the link register (return address)
    pub fn link_register(&self) -> PReg {
        PReg::new(30) // X30/LR
    }
    
    /// Get the frame pointer register
    pub fn frame_pointer(&self) -> PReg {
        PReg::new(29) // X29/FP
    }
    
    /// Get the stack pointer register
    pub fn stack_pointer(&self) -> PReg {
        PReg::new(31) // SP
    }
    
    /// Stack alignment requirement (16 bytes for ARM64)
    pub fn stack_alignment(&self) -> u32 {
        16
    }
    
    /// Red zone size (area below SP that won't be clobbered by signals)
    pub fn red_zone_size(&self) -> u32 {
        match self.os {
            OperatingSystem::MacOS => 128, // macOS has 128-byte red zone
            _ => 0, // Linux ARM64 has no red zone
        }
    }
}

/// Function prologue/epilogue generation for ARM64
pub struct Arm64FrameLayout {
    /// Size of local variables
    pub locals_size: u32,
    /// Size needed for spilled registers
    pub spill_size: u32,
    /// Callee-saved registers to preserve
    pub saved_regs: Vec<PReg>,
    /// Total frame size (aligned to 16 bytes)
    pub frame_size: u32,
}

impl Arm64FrameLayout {
    /// Calculate frame layout for a function
    pub fn calculate(
        locals: u32,
        spills: u32,
        used_regs: &PRegSet,
        call_conv: &Arm64CallConv,
    ) -> Self {
        // Determine which callee-saved registers need preserving
        let mut saved_regs = Vec::new();
        for &reg in call_conv.callee_saved() {
            if used_regs.contains(reg) {
                saved_regs.push(reg);
            }
        }
        
        // Always save FP and LR for non-leaf functions
        if !saved_regs.contains(&call_conv.frame_pointer()) {
            saved_regs.push(call_conv.frame_pointer());
        }
        if !saved_regs.contains(&call_conv.link_register()) {
            saved_regs.push(call_conv.link_register());
        }
        
        // Calculate space needed
        let saved_regs_size = saved_regs.len() as u32 * 8;
        let total = locals + spills + saved_regs_size;
        
        // Align to 16 bytes
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
            .map(|i| -(16 + i as i32 * 8)) // FP points to old FP, saved regs below
    }
    
    /// Offset of local variable from frame pointer
    pub fn local_offset(&self, offset: u32) -> i32 {
        -(self.saved_regs.len() as i32 * 8 + 16 + offset as i32)
    }
    
    /// Offset of spill slot from frame pointer
    pub fn spill_offset(&self, slot: u32) -> i32 {
        self.local_offset(self.locals_size + slot * 8)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_arg_passing() {
        let conv = Arm64CallConv::new(OperatingSystem::Linux);
        
        // First 8 args go in registers
        for i in 0..8 {
            match conv.arg_abi(i, IntTy::I64) {
                ArgAbi::Reg(reg, 0) => assert_eq!(reg.index(), i as u8),
                _ => panic!("Expected register for arg {}", i),
            }
        }
        
        // 9th arg goes on stack
        match conv.arg_abi(8, IntTy::I64) {
            ArgAbi::Mem(0) => {}
            _ => panic!("Expected stack for arg 8"),
        }
    }
    
    #[test]
    fn test_frame_layout() {
        let conv = Arm64CallConv::new(OperatingSystem::Linux);
        let mut used_regs = PRegSet::default();
        used_regs.insert(PReg::new(19)); // X19 is callee-saved
        
        let layout = Arm64FrameLayout::calculate(24, 16, &used_regs, &conv);
        
        // Should save X19, FP, and LR
        assert_eq!(layout.saved_regs.len(), 3);
        assert!(layout.saved_regs.contains(&PReg::new(19)));
        assert!(layout.saved_regs.contains(&PReg::new(29))); // FP
        assert!(layout.saved_regs.contains(&PReg::new(30))); // LR
        
        // Frame size should be aligned to 16
        assert_eq!(layout.frame_size % 16, 0);
        assert!(layout.frame_size >= 24 + 16 + 24); // locals + spills + saved regs
    }
}