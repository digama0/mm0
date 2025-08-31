//! x86-64 architecture implementation for VCode types

use crate::types::arch_vcode::{ArchVCode, ArchInst};
use super::{Inst, PInst, PReg, PRegSet};

/// x86-64 architecture marker type
pub struct X86Arch;

impl ArchVCode for X86Arch {
    type PReg = PReg;
    type PRegSet = PRegSet;
    type Inst = Inst;
    type PInst = PInst;
    
    fn name() -> &'static str { "x86-64" }
}

impl ArchInst for Inst {
    type PReg = PReg;
    type PRegSet = PRegSet;
    
    fn is_call(&self) -> bool {
        matches!(self, Inst::CallKnown {..} | Inst::SysCall {..})
    }
    
    fn is_ret(&self) -> bool {
        matches!(self, Inst::Return {..})
    }
    
    fn is_branch(&self) -> bool {
        matches!(self,
            Inst::Jump {..} |
            Inst::CondJump {..} |
            Inst::SwitchJump {..}
        )
    }
    
    fn branch_blockparams(&self, succ_idx: usize) -> &[regalloc2::VReg] {
        match self {
            Inst::Jump { dests, .. } => &dests[0],
            Inst::CondJump { dests, .. } => &dests[succ_idx],
            Inst::SwitchJump { dests, .. } => &dests[succ_idx],
            _ => &[],
        }
    }
    
    fn collect_operands(&self, ops: &mut Vec<regalloc2::Operand>) {
        // This is the existing implementation from the Inst trait
        use crate::types::vcode::Inst as VInst;
        VInst::collect_operands(self, ops);
    }
    
    fn clobbers(&self) -> Self::PRegSet {
        match self {
            Inst::CallKnown { clobbers: Some(cl), .. } => *cl,
            Inst::SysCall { f, .. } if f.returns() => {
                [super::RCX, super::R11].into_iter().collect()
            }
            _ => Default::default(),
        }
    }
}