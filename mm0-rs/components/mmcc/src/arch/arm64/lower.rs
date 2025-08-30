//! MIR to ARM64 VCode lowering
//!
//! This module implements the translation from architecture-independent MIR
//! to ARM64-specific VCode instructions.

use std::collections::HashMap;
use crate::types::mir::{*, self};
use crate::types::mir::ExprKind;
use crate::types::vcode::{ProcAbi, BlockId as VBlockId, VReg, ArgAbi};
use crate::arch::x86::PRegSet;
use crate::types::{Size, IdxVec, Spanned};
use crate::mir_opt::storage::Allocations;
use crate::linker::ConstData;
use crate::build_vcode::{VCodeCtx, LowerErr};
use crate::{Symbol, Entity};
use super::vcode::VCode;
use super::{Inst, Operand};

/// Build ARM64 VCode from MIR
pub fn build_arm64_vcode(
    _names: &HashMap<Symbol, Entity>,
    _funcs: &HashMap<Symbol, crate::types::vcode::ProcId>,
    _func_abi: &IdxVec<crate::types::vcode::ProcId, ProcAbi>,
    _consts: &ConstData,
    cfg: &mir::Cfg,
    _allocs: &Allocations,
    ctx: VCodeCtx<'_>,
) -> Result<VCode, LowerErr> {
    eprintln!("ARM64: Starting VCode generation");
    
    // Create a simple ABI for now
    let abi = match ctx {
        VCodeCtx::Start(_) => ProcAbi {
            args: Box::new([]),
            rets: Box::new([]),
            reach: true,
            args_space: 0,
            clobbers: PRegSet::default(),
        },
        VCodeCtx::Proc(rets) => ProcAbi {
            args: Box::new([]), // TODO: Handle arguments
            rets: Box::new([]), // TODO: Convert from mir::Arg to ArgAbi
            reach: true,
            args_space: 0,
            clobbers: PRegSet::default(),
        },
    };
    
    let mut vcode = VCode::new(abi);
    
    // For now, just handle the simplest case - find an exit block
    for (block_id, block) in cfg.blocks() {
        eprintln!("ARM64: Processing block {:?}", block_id);
        
        if let Terminator::Exit(op) = block.terminator() {
            eprintln!("ARM64: Found exit terminator");
            
            // Create a VCode block
            let vblock = vcode.new_block();
            
            // Generate code for the exit value
            match op {
                mir::Operand::Const(c) => {
                    // Load constant into a virtual register (will be allocated to X0)
                    if let ConstKind::Int = c.k {
                        // Extract the integer value from the expression
                        let value = if let Some(expr) = &c.ety.0 {
                            if let ExprKind::Int(n) = &**expr {
                                // n is a reference to BigInt
                                n.try_into().unwrap_or(0)
                            } else {
                                0
                            }
                        } else {
                            0
                        };
                        eprintln!("ARM64: Exit with constant {}", value);
                        
                        // Allocate virtual register for exit code
                        let exit_code_vreg = vcode.new_vreg();
                        
                        // MOV vreg, #value
                        vcode.push_inst(vblock, Inst::MovImm {
                            dst: VReg::new(exit_code_vreg as usize),
                            imm: value,
                            size: Size::S64,
                        });
                    }
                }
                _ => {
                    eprintln!("ARM64: Non-constant exit not yet supported");
                }
            }
            
            // Generate exit syscall
            // On macOS: syscall number in X16, exit code in X0
            // Allocate virtual register for syscall number
            let syscall_vreg = vcode.new_vreg();
            
            // MOV vreg, #1 (exit syscall)
            vcode.push_inst(vblock, Inst::MovImm {
                dst: VReg::new(syscall_vreg as usize),
                imm: 1,
                size: Size::S64,
            });
            
            // SVC #0x80 (supervisor call for macOS)
            vcode.push_inst(vblock, Inst::Svc { imm: 0x80 });
            
            // Return instruction as terminator
            vcode.set_terminator(vblock, Inst::Ret);
            
            // For now, just handle one exit block
            return Ok(vcode);
        }
    }
    
    eprintln!("ARM64: No exit block found");
    Err(LowerErr::EntryUnreachable(cfg.span.clone()))
}