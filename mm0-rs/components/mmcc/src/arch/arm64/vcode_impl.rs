//! Implementation of vcode::Inst trait for ARM64
//!
//! This module implements the vcode::Inst trait for ARM64 instructions,
//! allowing them to work with the VCode infrastructure.

use crate::types::vcode::{Inst as VcodeInst, Operand};
use crate::arch::traits::PhysicalReg;
use super::inst::{Inst, Operand as ArmOperand};
use super::regs::{PRegSet, CALLER_SAVED};

impl VcodeInst for Inst {
    fn is_call(&self) -> bool {
        matches!(self, Inst::Call { .. })
    }
    
    fn is_ret(&self) -> bool {
        matches!(self, Inst::Ret)
    }
    
    fn is_branch(&self) -> bool {
        matches!(self, 
            Inst::Branch { .. } |
            Inst::BranchCond { .. }
        )
    }
    
    fn branch_blockparams(&self, _succ_idx: usize) -> &[regalloc2::VReg] {
        // ARM64 doesn't use block parameters
        &[]
    }
    
    fn collect_operands(&self, ops: &mut Vec<Operand>) {
        match self {
            // Arithmetic operations
            Inst::Add { dst, src1, src2, .. } => {
                ops.push(Operand::reg_def(dst.0));
                ops.push(Operand::reg_use(src1.0));
                if let ArmOperand::Reg(r) = src2 {
                    ops.push(Operand::reg_use(r.0));
                }
            }
            Inst::Sub { dst, src1, src2, .. } => {
                ops.push(Operand::reg_def(dst.0));
                ops.push(Operand::reg_use(src1.0));
                if let ArmOperand::Reg(r) = src2 {
                    ops.push(Operand::reg_use(r.0));
                }
            }
            Inst::Mul { dst, src1, src2, .. } => {
                ops.push(Operand::reg_def(dst.0));
                ops.push(Operand::reg_use(src1.0));
                ops.push(Operand::reg_use(src2.0));
            }
            Inst::Sdiv { dst, src1, src2, .. } | Inst::Udiv { dst, src1, src2, .. } => {
                ops.push(Operand::reg_def(dst.0));
                ops.push(Operand::reg_use(src1.0));
                ops.push(Operand::reg_use(src2.0));
            }
            
            // Logical operations  
            Inst::And { dst, src1, src2, .. } | Inst::Orr { dst, src1, src2, .. } | Inst::Eor { dst, src1, src2, .. } => {
                ops.push(Operand::reg_def(dst.0));
                ops.push(Operand::reg_use(src1.0));
                if let ArmOperand::Reg(r) = src2 {
                    ops.push(Operand::reg_use(r.0));
                }
            }
            
            // Memory operations
            Inst::Load { dst, addr, .. } => {
                ops.push(Operand::reg_def(dst.0));
                match addr {
                    super::inst::AMode::Reg(r) => ops.push(Operand::reg_use(r.0)),
                    super::inst::AMode::RegImm(r, _) => ops.push(Operand::reg_use(r.0)),
                    _ => {}
                }
            }
            Inst::Store { src, addr, .. } => {
                ops.push(Operand::reg_use(src.0));
                match addr {
                    super::inst::AMode::Reg(r) => ops.push(Operand::reg_use(r.0)),
                    super::inst::AMode::RegImm(r, _) => ops.push(Operand::reg_use(r.0)),
                    _ => {}
                }
            }
            
            // Move operations
            Inst::Mov { dst, src } => {
                ops.push(Operand::reg_def(dst.0));
                ops.push(Operand::reg_use(src.0));
            }
            Inst::MovImm { dst, .. } => {
                ops.push(Operand::reg_def(dst.0));
            }
            
            // Comparison
            Inst::Cmp { lhs, rhs, .. } => {
                ops.push(Operand::reg_use(lhs.0));
                if let ArmOperand::Reg(r) = rhs {
                    ops.push(Operand::reg_use(r.0));
                }
            }
            
            // Calls
            Inst::Call { args, rets, .. } => {
                // Use all argument registers
                for arg in args {
                    ops.push(Operand::reg_use(arg.0));
                }
                // Define all return registers
                for ret in rets {
                    ops.push(Operand::reg_def(ret.0));
                }
            }
            
            _ => {}
        }
    }
    
    fn clobbers(&self) -> PRegSet {
        match self {
            Inst::Call { .. } => {
                // Calls clobber caller-saved registers
                let mut set = PRegSet::default();
                for reg in CALLER_SAVED {
                    set.insert(reg);
                }
                set
            }
            _ => PRegSet::default(),
        }
    }
}