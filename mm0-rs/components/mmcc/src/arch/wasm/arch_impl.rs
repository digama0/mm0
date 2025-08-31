//! WebAssembly architecture implementation for VCode types

use crate::types::arch_vcode::{ArchVCode, ArchInst};
use super::{WasmInst, WasmReg, WasmRegSet};

/// WebAssembly architecture marker type
pub struct WasmArch;

/// Physical instruction for WASM (same as virtual since no register allocation)
pub type WasmPInst = WasmInst;

impl ArchVCode for WasmArch {
    type PReg = WasmReg;
    type PRegSet = WasmRegSet;
    type Inst = WasmInst;
    type PInst = WasmPInst;
    
    fn name() -> &'static str { "wasm32" }
}

impl ArchInst for WasmInst {
    type PReg = WasmReg;
    type PRegSet = WasmRegSet;
    
    fn is_call(&self) -> bool {
        matches!(self, WasmInst::Call { .. })
    }
    
    fn is_ret(&self) -> bool {
        matches!(self, WasmInst::Return)
    }
    
    fn is_branch(&self) -> bool {
        matches!(self,
            WasmInst::Branch { .. } |
            WasmInst::BranchIf { .. } |
            WasmInst::BranchTable { .. }
        )
    }
    
    fn branch_blockparams(&self, _succ_idx: usize) -> &[regalloc2::VReg] {
        // WASM doesn't use block parameters in the same way
        &[]
    }
    
    fn collect_operands(&self, _ops: &mut Vec<regalloc2::Operand>) {
        // WASM is a stack machine, so no register operands
        // Local variables are handled differently
    }
    
    fn clobbers(&self) -> Self::PRegSet {
        // WASM doesn't have physical registers to clobber
        Default::default()
    }
}