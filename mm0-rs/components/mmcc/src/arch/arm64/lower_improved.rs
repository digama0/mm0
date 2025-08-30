//! Improved ARM64 lowering with proper constant table support
//!
//! This module shows how ARM64 lowering should properly integrate with
//! the constant table system instead of using hardcoded constants.

use crate::types::mir::{*, self};
use crate::types::vcode::{ProcAbi, BlockId as VBlockId, VReg, ArgAbi};
use crate::types::{Size, IdxVec, Spanned};
use crate::mir_opt::storage::Allocations;
use crate::linker::ConstData;
use crate::build_vcode::{VCodeCtx, LowerErr};
use crate::{Symbol, Entity};
use super::vcode::VCode;
use super::{Inst, Operand};
use super::const_table::{Arm64ConstTable, ConstDataExt};
use super::regs::PRegSet;

/// Context for lowering MIR to ARM64 VCode
pub struct Arm64LowerCtx<'a> {
    vcode: &'a mut VCode,
    const_table: &'a Arm64ConstTable,
    vctx: &'a mut VCodeCtx,
}

impl<'a> Arm64LowerCtx<'a> {
    /// Lower a write syscall with proper constant lookup
    fn lower_write_syscall(
        &mut self,
        vblock: VBlockId,
        args: &[Operand],
    ) -> Result<(), LowerErr> {
        eprintln!("ARM64: Lowering write syscall with {} args", args.len());
        
        if args.len() >= 3 {
            // Extract fd (file descriptor)
            let fd_vreg = self.vcode.new_vreg();
            match &args[0] {
                Operand::Const(Const { k: ConstKind::Int(val), .. }) => {
                    self.vcode.push_inst(vblock, Inst::MovImm {
                        dst: VReg::new(fd_vreg as usize),
                        imm: *val as u64,
                        size: Size::S64,
                    });
                }
                _ => {
                    eprintln!("ARM64: Non-constant fd, using stdout");
                    self.vcode.push_inst(vblock, Inst::MovImm {
                        dst: VReg::new(fd_vreg as usize),
                        imm: 1, // stdout
                        size: Size::S64,
                    });
                }
            }
            
            // Handle buffer pointer - look up in constant table
            let buf_vreg = self.vcode.new_vreg();
            match &args[1] {
                Operand::Symbol(symbol, _) => {
                    // Find the constant ID for this symbol
                    if let Some(const_id) = self.find_const_id(symbol) {
                        eprintln!("ARM64: Loading constant {} (id={})", symbol, const_id);
                        self.vcode.push_inst(vblock, Inst::LoadConst {
                            dst: VReg::new(buf_vreg as usize),
                            const_id,
                        });
                    } else {
                        return Err(LowerErr::Unsupported(
                            format!("Constant {} not found in table", symbol)
                        ));
                    }
                }
                _ => {
                    return Err(LowerErr::Unsupported(
                        "Non-symbol buffer argument".to_string()
                    ));
                }
            }
            
            // Handle count
            let count_vreg = self.vcode.new_vreg();
            match &args[2] {
                Operand::Const(Const { k: ConstKind::Int(val), .. }) => {
                    self.vcode.push_inst(vblock, Inst::MovImm {
                        dst: VReg::new(count_vreg as usize),
                        imm: *val as u64,
                        size: Size::S64,
                    });
                }
                _ => {
                    // Try to get size from constant table
                    if let Operand::Symbol(symbol, _) = &args[1] {
                        if let Some(const_id) = self.find_const_id(symbol) {
                            if let Some(size) = self.const_table.get_size(const_id) {
                                self.vcode.push_inst(vblock, Inst::MovImm {
                                    dst: VReg::new(count_vreg as usize),
                                    imm: size as u64,
                                    size: Size::S64,
                                });
                            }
                        }
                    }
                }
            }
            
            // Set up syscall number in X16 (macOS)
            let syscall_vreg = self.vcode.new_vreg();
            self.vcode.push_inst(vblock, Inst::MovImm {
                dst: VReg::new(syscall_vreg as usize),
                imm: 4, // write syscall
                size: Size::S64,
            });
            
            // SVC instruction
            self.vcode.push_inst(vblock, Inst::Syscall {
                operands: vec![
                    VReg::new(syscall_vreg as usize), // X16
                    VReg::new(fd_vreg as usize),       // X0
                    VReg::new(buf_vreg as usize),      // X1
                    VReg::new(count_vreg as usize),    // X2
                ],
            });
        }
        
        Ok(())
    }
    
    /// Find constant ID by symbol
    fn find_const_id(&self, symbol: &Symbol) -> Option<u32> {
        // Linear search through const table to find symbol
        // In a real implementation, we'd maintain a reverse map
        for id in 0..100 {
            if let Some(s) = self.const_table.get_symbol(id) {
                if s == symbol {
                    return Some(id);
                }
            } else {
                break;
            }
        }
        None
    }
}

/// Build ARM64 VCode from MIR with proper constant table support
pub fn build_arm64_vcode_improved(
    mir: &Cfg,
    allocs: Option<&Allocations>,
    consts: &ConstData,
    names: &std::collections::HashMap<Symbol, Entity>,
) -> Result<(VCode, Arm64ConstTable), LowerErr> {
    // Convert LinkedCode constants to ARM64 constant table
    let const_table = consts.to_arm64_const_table();
    
    // Initialize VCode
    let mut vcode = VCode::new();
    let mut vctx = VCodeCtx::new(mir, allocs, names);
    
    // Set up procedure ABI
    vcode.abi = ProcAbi {
        args: vec![].into(),
        rets: vec![].into(),
        clobbers: PRegSet::default(),
    };
    
    // Create lowering context
    let mut ctx = Arm64LowerCtx {
        vcode: &mut vcode,
        const_table: &const_table,
        vctx: &mut vctx,
    };
    
    // Lower each basic block
    for (bb_id, bb) in mir.blocks.enum_iter() {
        let vblock = ctx.vcode.create_block();
        
        // Process terminator
        match &bb.term {
            Terminator::Exit(args) => {
                if let Some(arg) = args.first() {
                    match arg {
                        Operand::Const(Const { k: ConstKind::Int(val), .. }) => {
                            eprintln!("ARM64: Exit with constant {}", val);
                            // mov x0, #val
                            let exit_vreg = ctx.vcode.new_vreg();
                            ctx.vcode.push_inst(vblock, Inst::MovImm {
                                dst: VReg::new(exit_vreg as usize),
                                imm: *val as u64,
                                size: Size::S64,
                            });
                            
                            // mov x16, #1 (exit syscall)
                            let syscall_vreg = ctx.vcode.new_vreg();
                            ctx.vcode.push_inst(vblock, Inst::MovImm {
                                dst: VReg::new(syscall_vreg as usize),
                                imm: 1,
                                size: Size::S64,
                            });
                            
                            // svc #0x80
                            ctx.vcode.push_inst(vblock, Inst::Syscall {
                                operands: vec![
                                    VReg::new(syscall_vreg as usize),
                                    VReg::new(exit_vreg as usize),
                                ],
                            });
                        }
                        _ => {
                            eprintln!("ARM64: Non-constant exit not yet supported");
                        }
                    }
                }
            }
            Terminator::Call(_, func, args, _, _, _) => {
                if let Operand::Symbol(sym, _) = func {
                    match sym.0.as_str() {
                        "write" => {
                            ctx.lower_write_syscall(vblock, args)?;
                        }
                        _ => {
                            eprintln!("ARM64: Call to {} not implemented", sym);
                        }
                    }
                }
            }
            _ => {
                eprintln!("ARM64: Terminator {:?} not implemented", bb.term);
            }
        }
    }
    
    Ok((vcode, const_table))
}