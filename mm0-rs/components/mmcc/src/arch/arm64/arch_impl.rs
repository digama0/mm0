//! ARM64 architecture implementation for VCode types

use crate::types::arch_vcode::{ArchVCode, ArchInst};
use super::{Inst, PInst, PReg};
use super::regs::PRegSet;

/// ARM64 architecture marker type
pub struct Arm64Arch;

impl ArchVCode for Arm64Arch {
    type PReg = PReg;
    type PRegSet = PRegSet;
    type Inst = Inst;
    type PInst = PInst;
    
    fn name() -> &'static str { "arm64" }
}

impl ArchInst for Inst {
    type PReg = PReg;
    type PRegSet = PRegSet;
    
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
    
    fn collect_operands(&self, ops: &mut Vec<regalloc2::Operand>) {
        use regalloc2::Operand;
        
        match self {
            // Arithmetic operations
            Inst::Add { dst, src1, src2, .. } => {
                ops.push(Operand::reg_def(dst.0));
                ops.push(Operand::reg_use(src1.0));
                if let super::Operand::Reg(r) = src2 {
                    ops.push(Operand::reg_use(r.0));
                }
            }
            Inst::Sub { dst, src1, src2, .. } => {
                ops.push(Operand::reg_def(dst.0));
                ops.push(Operand::reg_use(src1.0));
                if let super::Operand::Reg(r) = src2 {
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
                if let super::Operand::Reg(r) = src2 {
                    ops.push(Operand::reg_use(r.0));
                }
            }
            
            // Memory operations
            Inst::Load { dst, addr, .. } => {
                ops.push(Operand::reg_def(dst.0));
                match addr {
                    super::AMode::Reg(r) => ops.push(Operand::reg_use(r.0)),
                    super::AMode::RegImm(r, _) => ops.push(Operand::reg_use(r.0)),
                    _ => {}
                }
            }
            Inst::Store { src, addr, .. } => {
                ops.push(Operand::reg_use(src.0));
                match addr {
                    super::AMode::Reg(r) => ops.push(Operand::reg_use(r.0)),
                    super::AMode::RegImm(r, _) => ops.push(Operand::reg_use(r.0)),
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
                if let super::Operand::Reg(r) = rhs {
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
    
    fn clobbers(&self) -> Self::PRegSet {
        match self {
            Inst::Call { .. } => {
                // Calls clobber caller-saved registers
                // This is simplified - real implementation would use calling convention
                use super::regs::CALLER_SAVED;
                let mut set = PRegSet::default();
                for reg in CALLER_SAVED {
                    set.insert(reg);
                }
                set
            }
            _ => Default::default(),
        }
    }
}