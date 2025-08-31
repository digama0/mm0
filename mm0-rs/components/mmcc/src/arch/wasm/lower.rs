//! MIR to WASM VCode lowering
//!
//! This module implements the translation from architecture-independent MIR
//! to WebAssembly instructions. WASM is unique among our targets as it's
//! a stack machine rather than a register machine.

use std::collections::HashMap;
use crate::types::mir::{*, self};
use crate::types::vcode::{ProcAbi, BlockId as VBlockId, VReg, ArgAbi};
use crate::types::{Size, IdxVec, Spanned, IntTy};
use crate::mir_opt::storage::Allocations;
use crate::linker::ConstData;
use crate::lower_shared::{VCodeCtx, LowerErr};
use crate::{Symbol, Entity};
use super::{WasmInst, WasmType};

/// WASM VCode - simplified since we don't need register allocation
pub struct VCode {
    /// Function ABI information
    pub abi: ProcAbi,
    /// Instructions organized by block
    pub blocks: HashMap<VBlockId, Vec<WasmInst>>,
    /// Local variable count (parameters + locals)
    pub local_count: u32,
    /// Block order for emission
    pub block_order: Vec<VBlockId>,
    /// Next local index
    next_local: u32,
    /// Variable to local mapping
    var_to_local: HashMap<mir::VarId, u32>,
}

impl VCode {
    fn new(abi: ProcAbi) -> Self {
        Self {
            abi,
            blocks: HashMap::new(),
            local_count: 0,
            block_order: Vec::new(),
            next_local: 0,
            var_to_local: HashMap::new(),
        }
    }
    
    fn new_local(&mut self) -> u32 {
        let idx = self.next_local;
        self.next_local += 1;
        self.local_count = self.local_count.max(self.next_local);
        idx
    }
    
    fn get_or_alloc_local(&mut self, var: mir::VarId) -> u32 {
        *self.var_to_local.entry(var).or_insert_with(|| self.new_local())
    }
}

/// Build WASM VCode from MIR
pub fn build_wasm_vcode(
    _names: &HashMap<Symbol, Entity>,
    _funcs: &HashMap<Symbol, crate::types::vcode::ProcId>,
    _func_abi: &IdxVec<crate::types::vcode::ProcId, ProcAbi>,
    _consts: &ConstData,
    cfg: &mir::Cfg,
    _allocs: &Allocations,
    ctx: VCodeCtx<'_>,
) -> Result<VCode, LowerErr> {
    eprintln!("WASM: Starting VCode generation");
    
    // Create a simple ABI (WASM doesn't have physical registers)
    let abi = match ctx {
        VCodeCtx::Start(_) => ProcAbi {
            args: Box::new([]),
            rets: Box::new([]),
            reach: true,
            args_space: 0,
            clobbers: Default::default(), // No register clobbers in WASM
        },
        VCodeCtx::Proc(rets) => {
            // For WASM, arguments become locals
            let arg_count = rets.len(); // TODO: Get actual args
            ProcAbi {
                args: vec![ArgAbi::Boxed { sz: 4 }; arg_count].into_boxed_slice(),
                rets: Box::new([]), // TODO: Convert return types
                reach: true,
                args_space: 0,
                clobbers: Default::default(),
            }
        },
    };
    
    let mut vcode = VCode::new(abi);
    let mut current_block = VBlockId(0);
    let mut block_map = HashMap::new();
    
    // Map MIR blocks to WASM blocks
    for (mir_block_id, _) in cfg.blocks() {
        block_map.insert(mir_block_id, VBlockId(mir_block_id.0));
    }
    
    // Generate code for each block
    for (block_id, block) in cfg.blocks() {
        eprintln!("WASM: Processing block {:?}", block_id);
        
        let vblock = block_map[&block_id];
        let mut insts = Vec::new();
        current_block = vblock;
        
        // Generate code for the terminator
        match block.terminator() {
            Terminator::Exit(op) => {
                eprintln!("WASM: Found exit terminator");
                
                // Push exit code onto stack
                match op {
                    mir::Operand::Const(c) => {
                        if let ConstKind::Int = c.k {
                            // Extract integer value
                            let value = if let Some(expr) = &c.ety.0 {
                                if let ExprKind::Int(n) = &**expr {
                                    n.try_into().unwrap_or(0)
                                } else {
                                    0
                                }
                            } else {
                                0
                            };
                            eprintln!("WASM: Exit with constant {}", value);
                            insts.push(WasmInst::Const {
                                ty: WasmType::I32,
                                value: value as u64,
                            });
                        }
                    }
                    mir::Operand::Var(v) => {
                        let local = vcode.get_or_alloc_local(*v);
                        insts.push(WasmInst::LocalGet { idx: local });
                    }
                    _ => {
                        // Default exit code 0
                        insts.push(WasmInst::Const {
                            ty: WasmType::I32,
                            value: 0,
                        });
                    }
                }
                
                // WASM functions implicitly return the top stack value
                insts.push(WasmInst::Return);
            }
            
            Terminator::Return(_, _) => {
                eprintln!("WASM: Found return terminator");
                // For now, just return
                insts.push(WasmInst::Return);
            }
            
            Terminator::Jump(_, target, _) => {
                eprintln!("WASM: Found jump to {:?}", target);
                let target_block = block_map[target];
                insts.push(WasmInst::Branch { target: target_block.0 });
            }
            
            Terminator::If(cond, then_block, else_block, _) => {
                eprintln!("WASM: Found if terminator");
                
                // Push condition onto stack
                match cond {
                    mir::Operand::Const(c) => {
                        if let ConstKind::Bool = c.k {
                            let value = if let Some(expr) = &c.ety.0 {
                                matches!(&**expr, ExprKind::Bool(true))
                            } else {
                                false
                            };
                            insts.push(WasmInst::Const {
                                ty: WasmType::I32,
                                value: if value { 1 } else { 0 },
                            });
                        }
                    }
                    mir::Operand::Var(v) => {
                        let local = vcode.get_or_alloc_local(*v);
                        insts.push(WasmInst::LocalGet { idx: local });
                    }
                    _ => {}
                }
                
                // WASM's if/else structure
                insts.push(WasmInst::If { label: 0 });
                insts.push(WasmInst::Branch { target: block_map[then_block].0 });
                insts.push(WasmInst::Else);
                insts.push(WasmInst::Branch { target: block_map[else_block].0 });
                insts.push(WasmInst::End);
            }
            
            Terminator::Call { f, args, .. } => {
                eprintln!("WASM: Found call to function {:?}", f);
                
                // Push arguments onto stack
                for (ghost, arg) in args.iter() {
                    if !ghost {
                        match arg {
                            mir::Operand::Const(c) => {
                                if let ConstKind::Int = c.k {
                                    let value = if let Some(expr) = &c.ety.0 {
                                        if let ExprKind::Int(n) = &**expr {
                                            n.try_into().unwrap_or(0)
                                        } else {
                                            0
                                        }
                                    } else {
                                        0
                                    };
                                    insts.push(WasmInst::Const {
                                        ty: WasmType::I32,
                                        value: value as u64,
                                    });
                                }
                            }
                            mir::Operand::Var(v) => {
                                let local = vcode.get_or_alloc_local(*v);
                                insts.push(WasmInst::LocalGet { idx: local });
                            }
                            _ => {}
                        }
                    }
                }
                
                // Call the function (function index would need to be resolved)
                insts.push(WasmInst::Call { func_idx: 0 }); // TODO: Resolve function index
            }
            
            _ => {
                eprintln!("WASM: Unhandled terminator: {:?}", block.terminator());
            }
        }
        
        vcode.blocks.insert(vblock, insts);
        vcode.block_order.push(vblock);
    }
    
    eprintln!("WASM: Successfully generated VCode with {} blocks", vcode.blocks.len());
    Ok(vcode)
}

// Implement the VCodeTrait for WASM VCode
impl crate::codegen_arch::VCodeTrait for VCode {
    fn regalloc(self: Box<Self>) -> (ProcAbi, Box<crate::regalloc::PCode>) {
        // WASM doesn't need register allocation - just convert to PCode
        // For now, return a minimal PCode
        let pcode = crate::regalloc::PCode {
            len: 100, // Placeholder
            insts: crate::types::vcode::ChunkVec::new(),
            jumps: vec![],
        };
        (self.abi, Box::new(pcode))
    }
}