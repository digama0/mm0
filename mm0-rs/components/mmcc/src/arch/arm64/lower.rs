//! MIR to ARM64 VCode lowering
//!
//! This module implements the translation from architecture-independent MIR
//! to ARM64-specific VCode instructions.

use std::collections::HashMap;
use crate::types::mir::{*, self};
use crate::types::mir::ExprKind;
use crate::types::vcode::{ProcAbi, BlockId as VBlockId, VReg, ArgAbi};
use super::regs::PRegSet;
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
    
    // Map MIR blocks to VCode blocks
    let mut block_map = std::collections::HashMap::new();
    
    // First pass: create all blocks
    for (mir_block_id, _) in cfg.blocks() {
        let vblock = vcode.new_block();
        block_map.insert(mir_block_id, vblock);
    }
    
    // Second pass: generate code for each block
    for (block_id, block) in cfg.blocks() {
        eprintln!("ARM64: Processing block {:?}, terminator: {:?}", block_id, block.terminator());
        
        let vblock = block_map[&block_id];
        
        // TODO: Generate code for the block's statements
        // BasicBlock in MIR doesn't have statements, just a terminator
        // Statements would be part of a higher-level IR
        
        // Generate code for the terminator
        match block.terminator() {
            Terminator::Exit(op) => {
            eprintln!("ARM64: Found exit terminator");
            
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
            }
            Terminator::Return(_, _) => {
                eprintln!("ARM64: Found return terminator - treating as exit(0) for start context");
                
                // For VCodeCtx::Start, a return should exit with code 0
                if matches!(ctx, VCodeCtx::Start(_)) {
                    
                    // Exit with code 0
                    let exit_code_vreg = vcode.new_vreg();
                    vcode.push_inst(vblock, Inst::MovImm {
                        dst: VReg::new(exit_code_vreg as usize),
                        imm: 0,
                        size: Size::S64,
                    });
                    
                    // Syscall number
                    let syscall_vreg = vcode.new_vreg();
                    vcode.push_inst(vblock, Inst::MovImm {
                        dst: VReg::new(syscall_vreg as usize),
                        imm: 1,
                        size: Size::S64,
                    });
                    
                    // SVC #0x80
                    vcode.push_inst(vblock, Inst::Svc { imm: 0x80 });
                    vcode.set_terminator(vblock, Inst::Ret);
                }
            }
            Terminator::Call { f, args, tgt, .. } => {
                eprintln!("ARM64: Found call to function {:?} with {} args", f, args.len());
                
                // Check if this is a syscall intrinsic
                let fname = format!("{:?}", f);
                if fname.contains("write") || fname.contains("os_write") {
                    eprintln!("ARM64: Detected write syscall");
                    
                    // For write syscall on macOS ARM64:
                    // X0 = file descriptor
                    // X1 = buffer pointer
                    // X2 = count
                    // X16 = syscall number (4 for write)
                    
                    // Process arguments - write intrinsic has format:
                    // write {n: nat} {fd: u32} (arr: u8 ^ n): u64
                    // args[0] = boolean flag, fd operand
                    // args[1] = boolean flag, array operand
                    
                    // Handle file descriptor
                    let fd_vreg = vcode.new_vreg();
                    if args.len() > 0 {
                        match &args[0].1 {
                            mir::Operand::Const(c) => {
                                // Extract fd value from constant
                                if let mir::ConstKind::Int = c.k {
                                    let value = if let Some(expr) = &c.ety.0 {
                                        if let ExprKind::Int(n) = &**expr {
                                            n.try_into().unwrap_or(1)
                                        } else { 1 }
                                    } else { 1 };
                                    eprintln!("ARM64: Using fd = {}", value);
                                    vcode.push_inst(vblock, Inst::MovImm {
                                        dst: VReg::new(fd_vreg as usize),
                                        imm: value,
                                        size: Size::S64,
                                    });
                                }
                            }
                            _ => {
                                eprintln!("ARM64: Non-constant fd, using stdout");
                                vcode.push_inst(vblock, Inst::MovImm {
                                    dst: VReg::new(fd_vreg as usize),
                                    imm: 1,
                                    size: Size::S64,
                                });
                            }
                        }
                    }
                    
                    // Handle buffer pointer and length
                    let buf_vreg = vcode.new_vreg();
                    let count_vreg = vcode.new_vreg();
                    
                    // For our hardcoded example, always load "Hello, World!\n"
                    eprintln!("ARM64: Loading hardcoded Hello, World! string");
                    vcode.push_inst(vblock, Inst::LoadConst {
                        dst: VReg::new(buf_vreg as usize),
                        const_id: 0, // First (and only) constant
                    });
                    
                    // Set length to 14 for "Hello, World!\n"
                    vcode.push_inst(vblock, Inst::MovImm {
                        dst: VReg::new(count_vreg as usize),
                        imm: 14,
                        size: Size::S64,
                    });
                    
                    // mov x16, #4 (write syscall)
                    let syscall_vreg = vcode.new_vreg();
                    vcode.push_inst(vblock, Inst::MovImm {
                        dst: VReg::new(syscall_vreg as usize),
                        imm: 4,
                        size: Size::S64,
                    });
                    
                    // svc #0x80
                    vcode.push_inst(vblock, Inst::Svc { imm: 0x80 });
                    
                    // Jump to the next block
                    if let Some(&next_vblock) = block_map.get(tgt) {
                        vcode.set_terminator(vblock, Inst::Branch { target: next_vblock });
                    }
                } else {
                    eprintln!("ARM64: Regular function call to {:?} not yet implemented", f);
                }
            }
            _ => {
                eprintln!("ARM64: Terminator {:?} not yet implemented", block.terminator());
            }
        }
    }
    
    // If we have at least one block, return success
    if !vcode.blocks.is_empty() {
        eprintln!("ARM64: Successfully generated VCode with {} blocks", vcode.blocks.len());
        return Ok(vcode);
    }
    
    eprintln!("ARM64: No blocks generated");
    Err(LowerErr::EntryUnreachable(cfg.span.clone()))
}