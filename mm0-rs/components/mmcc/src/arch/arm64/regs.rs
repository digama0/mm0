//! ARM64 register definitions

use std::fmt::{Debug, Display};
use crate::arch::traits::{PhysicalReg, RegisterSet};

/// ARM64 general-purpose register
#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct PReg(pub regalloc2::PReg);

impl PReg {
    #[inline(always)]
    pub const fn new(reg: usize) -> Self {
        Self(regalloc2::PReg::new(reg, regalloc2::RegClass::Int))
    }

    /// The index of the register (0-30 for X0-X30)
    #[inline(always)]
    #[must_use]
    pub fn index(self) -> u8 {
        self.0.hw_enc() as u8
    }
    
    /// Check if this is the zero register (XZR/WZR)
    #[inline]
    pub fn is_zero(self) -> bool {
        self.index() == 31
    }
}

impl PhysicalReg for PReg {
    fn new(index: usize) -> Self {
        PReg::new(index)
    }
    
    fn index(self) -> u8 {
        self.index()
    }
    
    fn is_valid(self) -> bool {
        self.0 != regalloc2::PReg::invalid()
    }
    
    fn invalid() -> Self {
        Self(regalloc2::PReg::invalid())
    }
    
    fn to_regalloc(self) -> regalloc2::PReg {
        self.0
    }
}

impl Display for PReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.is_valid() {
            return write!(f, "<invalid>");
        }
        
        let idx = self.index();
        match idx {
            31 => write!(f, "xzr"), // Zero register
            30 => write!(f, "lr"),  // Link register (X30)
            29 => write!(f, "fp"),  // Frame pointer (X29)
            _ => write!(f, "x{}", idx),
        }
    }
}

impl Debug for PReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

// ARM64 general-purpose registers
pub const X0: PReg = PReg::new(0);
pub const X1: PReg = PReg::new(1);
pub const X2: PReg = PReg::new(2);
pub const X3: PReg = PReg::new(3);
pub const X4: PReg = PReg::new(4);
pub const X5: PReg = PReg::new(5);
pub const X6: PReg = PReg::new(6);
pub const X7: PReg = PReg::new(7);
pub const X8: PReg = PReg::new(8);
pub const X9: PReg = PReg::new(9);
pub const X10: PReg = PReg::new(10);
pub const X11: PReg = PReg::new(11);
pub const X12: PReg = PReg::new(12);
pub const X13: PReg = PReg::new(13);
pub const X14: PReg = PReg::new(14);
pub const X15: PReg = PReg::new(15);
pub const X16: PReg = PReg::new(16);
pub const X17: PReg = PReg::new(17);
pub const X18: PReg = PReg::new(18);
pub const X19: PReg = PReg::new(19);
pub const X20: PReg = PReg::new(20);
pub const X21: PReg = PReg::new(21);
pub const X22: PReg = PReg::new(22);
pub const X23: PReg = PReg::new(23);
pub const X24: PReg = PReg::new(24);
pub const X25: PReg = PReg::new(25);
pub const X26: PReg = PReg::new(26);
pub const X27: PReg = PReg::new(27);
pub const X28: PReg = PReg::new(28);
pub const X29: PReg = PReg::new(29); // Frame pointer
pub const X30: PReg = PReg::new(30); // Link register
// X31 is SP when used as base register, XZR when used as source/dest

// Special names
pub const FP: PReg = X29;  // Frame pointer
pub const LR: PReg = X30;  // Link register
pub const SP: PReg = PReg::new(31); // Stack pointer (special encoding)
pub const XZR: PReg = PReg::new(31); // Zero register (same encoding as SP)

// ARM64 calling convention (AAPCS64)
pub const ARG_REGS: [PReg; 8] = [X0, X1, X2, X3, X4, X5, X6, X7];
pub const RET_REGS: [PReg; 8] = [X0, X1, X2, X3, X4, X5, X6, X7];

// Caller-saved (volatile) registers
pub const CALLER_SAVED: [PReg; 18] = [
    X0, X1, X2, X3, X4, X5, X6, X7,     // Argument/result registers
    X8, X9, X10, X11, X12, X13, X14, X15, // Temporary registers
    X16, X17,                            // IP0, IP1 (intra-procedure scratch)
];

// Callee-saved (non-volatile) registers
pub const CALLEE_SAVED: [PReg; 10] = [
    X19, X20, X21, X22, X23, X24, X25, X26, X27, X28,
    // X29 (FP) and X30 (LR) are handled specially
];

// System call registers (platform-specific)
pub const SYSCALL_ARG_REGS: [PReg; 6] = [X0, X1, X2, X3, X4, X5];

/// A set of physical registers (32-bit bitfield for ARM64)
#[derive(Copy, Clone, Default, Debug)]
pub struct PRegSet(u32);

impl PRegSet {
    #[inline]
    pub fn insert(&mut self, r: PReg) {
        if r.index() < 32 {
            self.0 |= 1 << r.index();
        }
    }
    
    #[inline]
    pub fn get(self, r: PReg) -> bool {
        r.index() < 32 && (self.0 & (1 << r.index())) != 0
    }
    
    #[inline]
    pub fn remove(&mut self, r: PReg) {
        if r.index() < 32 {
            self.0 &= !(1 << r.index());
        }
    }
    
    pub fn iter(self) -> impl Iterator<Item = PReg> {
        (0..32).map(PReg::new).filter(move |&r| self.get(r))
    }
}

impl RegisterSet<PReg> for PRegSet {
    fn insert(&mut self, reg: PReg) {
        self.insert(reg);
    }
    
    fn contains(&self, reg: PReg) -> bool {
        self.get(reg)
    }
    
    fn remove(&mut self, reg: PReg) {
        self.remove(reg);
    }
    
    fn iter(&self) -> impl Iterator<Item = PReg> {
        self.iter()
    }
    
    fn to_regalloc(self) -> regalloc2::PRegSet {
        let mut out = regalloc2::PRegSet::empty();
        for r in self.iter() {
            out.add(r.to_regalloc());
        }
        out
    }
}

impl FromIterator<PReg> for PRegSet {
    fn from_iter<T: IntoIterator<Item = PReg>>(iter: T) -> Self {
        let mut out = Self::default();
        for i in iter {
            out.insert(i);
        }
        out
    }
}