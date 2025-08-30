//! WebAssembly (WASM) architecture support
//!
//! WebAssembly is a stack-based virtual machine, which presents unique
//! challenges for our code generation pipeline that was designed for
//! register-based architectures.

use std::fmt::{Debug, Display};
use crate::arch::{traits::*, target::Target};

/// WebAssembly architecture implementation
pub struct Wasm;

impl Architecture for Wasm {
    const KIND: ArchKind = ArchKind::StackMachine;
    const NAME: &'static str = "wasm32";
    
    type PReg = WasmReg;
    type PRegSet = WasmRegSet;
    type Inst = WasmInst;
    type PInst = WasmInst; // No register allocation needed
    
    fn machine_env() -> &'static regalloc2::MachineEnv {
        // WASM doesn't need register allocation
        &DUMMY_MACHINE_ENV
    }
    
    // Stack pointer is implicit in WASM
    fn stack_pointer() -> Option<Self::PReg> {
        None
    }
    
    // No syscalls in WASM - must use imports
    fn has_syscalls(_target: Target) -> bool {
        false
    }
}

/// Dummy register type for WASM
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct WasmReg;

impl Display for WasmReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<wasm-stack>")
    }
}

impl PhysicalReg for WasmReg {
    fn new(_index: usize) -> Self { WasmReg }
    fn index(self) -> u8 { 0 }
    fn is_valid(self) -> bool { false }
    fn invalid() -> Self { WasmReg }
    fn to_regalloc(self) -> regalloc2::PReg {
        regalloc2::PReg::invalid()
    }
}

/// Dummy register set for WASM
#[derive(Copy, Clone, Default, Debug)]
pub struct WasmRegSet;

impl RegisterSet<WasmReg> for WasmRegSet {
    fn insert(&mut self, _reg: WasmReg) {}
    fn contains(&self, _reg: WasmReg) -> bool { false }
    fn remove(&mut self, _reg: WasmReg) {}
    fn iter(&self) -> impl Iterator<Item = WasmReg> {
        std::iter::empty()
    }
    fn to_regalloc(self) -> regalloc2::PRegSet {
        regalloc2::PRegSet::empty()
    }
}

pub mod regalloc;

/// WASM instructions
#[derive(Clone, Debug)]
pub enum WasmInst {
    /// Push a constant onto the stack
    Const { ty: WasmType, value: u64 },
    
    /// Local variable access
    LocalGet { idx: u32 },
    LocalSet { idx: u32 },
    LocalTee { idx: u32 },
    
    /// Memory operations
    Load { ty: WasmType, offset: u32, align: u32 },
    Store { ty: WasmType, offset: u32, align: u32 },
    
    /// Arithmetic (pops operands, pushes result)
    Add { ty: WasmType },
    Sub { ty: WasmType },
    Mul { ty: WasmType },
    
    /// Control flow
    Call { func_idx: u32 },
    Return,
    Branch { target: u32 },
    BranchIf { target: u32 },
    BranchTable { targets: Vec<u32>, default: u32 },
    
    /// Comparison operations
    I32Eq,   // Equal
    I32Ne,   // Not equal
    I32LtS,  // Less than (signed)
    I32LtU,  // Less than (unsigned)
    I32GtS,  // Greater than (signed)
    I32GtU,  // Greater than (unsigned)
    I32LeS,  // Less than or equal (signed)
    I32LeU,  // Less than or equal (unsigned)
    I32GeS,  // Greater than or equal (signed)
    I32GeU,  // Greater than or equal (unsigned)
    I32Eqz,  // Equal to zero
    
    /// Control structures
    Block { label: u32 },
    Loop { label: u32 },
    If { label: u32 },
    Else,
    End,
    
    /// Stack manipulation
    Drop,
    Select,
}

/// WASM value types
#[derive(Clone, Copy, Debug)]
pub enum WasmType {
    I32,
    I64,
    F32,
    F64,
}

impl Instruction for WasmInst {
    fn is_move(&self) -> bool {
        matches!(self, WasmInst::LocalGet { .. } | WasmInst::LocalSet { .. })
    }
    
    fn size_hint(&self) -> Option<usize> {
        // Most WASM instructions are 2-5 bytes
        Some(match self {
            WasmInst::Const { .. } => 5,
            WasmInst::LocalGet { .. } | WasmInst::LocalSet { .. } => 2,
            _ => 3,
        })
    }
}

impl PhysicalInstruction for WasmInst {
    fn encode(&self, sink: &mut impl InstructionSink) -> Result<(), EncodeError> {
        // Simplified WASM encoding
        match self {
            WasmInst::Const { ty, value } => {
                match ty {
                    WasmType::I32 => {
                        sink.emit_bytes(&[0x41]); // i32.const
                        // LEB128 encode value
                        encode_leb128_u32(sink, *value as u32);
                    }
                    WasmType::I64 => {
                        sink.emit_bytes(&[0x42]); // i64.const
                        // LEB128 encode value
                        encode_leb128_u64(sink, *value);
                    }
                    _ => return Err(EncodeError::NotImplemented("float constants")),
                }
            }
            WasmInst::LocalGet { idx } => {
                sink.emit_bytes(&[0x20]); // local.get
                encode_leb128_u32(sink, *idx);
            }
            WasmInst::LocalSet { idx } => {
                sink.emit_bytes(&[0x21]); // local.set
                encode_leb128_u32(sink, *idx);
            }
            WasmInst::LocalTee { idx } => {
                sink.emit_bytes(&[0x22]); // local.tee
                encode_leb128_u32(sink, *idx);
            }
            WasmInst::Add { ty } => {
                match ty {
                    WasmType::I32 => sink.emit_bytes(&[0x6a]), // i32.add
                    WasmType::I64 => sink.emit_bytes(&[0x7c]), // i64.add
                    _ => return Err(EncodeError::NotImplemented("float add")),
                }
            }
            WasmInst::Sub { ty } => {
                match ty {
                    WasmType::I32 => sink.emit_bytes(&[0x6b]), // i32.sub
                    WasmType::I64 => sink.emit_bytes(&[0x7d]), // i64.sub
                    _ => return Err(EncodeError::NotImplemented("float sub")),
                }
            }
            WasmInst::Mul { ty } => {
                match ty {
                    WasmType::I32 => sink.emit_bytes(&[0x6c]), // i32.mul
                    WasmType::I64 => sink.emit_bytes(&[0x7e]), // i64.mul
                    _ => return Err(EncodeError::NotImplemented("float mul")),
                }
            }
            // Comparison operations
            WasmInst::I32Eq => sink.emit_bytes(&[0x46]),
            WasmInst::I32Ne => sink.emit_bytes(&[0x47]),
            WasmInst::I32LtS => sink.emit_bytes(&[0x48]),
            WasmInst::I32LtU => sink.emit_bytes(&[0x49]),
            WasmInst::I32GtS => sink.emit_bytes(&[0x4a]),
            WasmInst::I32GtU => sink.emit_bytes(&[0x4b]),
            WasmInst::I32LeS => sink.emit_bytes(&[0x4c]),
            WasmInst::I32LeU => sink.emit_bytes(&[0x4d]),
            WasmInst::I32GeS => sink.emit_bytes(&[0x4e]),
            WasmInst::I32GeU => sink.emit_bytes(&[0x4f]),
            WasmInst::I32Eqz => sink.emit_bytes(&[0x45]),
            WasmInst::Call { func_idx } => {
                sink.emit_bytes(&[0x10]); // call
                encode_leb128_u32(sink, *func_idx);
            }
            WasmInst::Return => {
                sink.emit_bytes(&[0x0f]); // return
            }
            // Control structures
            WasmInst::Block { .. } => {
                sink.emit_bytes(&[0x02, 0x40]); // block void
            }
            WasmInst::Loop { .. } => {
                sink.emit_bytes(&[0x03, 0x40]); // loop void
            }
            WasmInst::If { .. } => {
                sink.emit_bytes(&[0x04, 0x40]); // if void
            }
            WasmInst::Else => {
                sink.emit_bytes(&[0x05]); // else
            }
            WasmInst::End => {
                sink.emit_bytes(&[0x0b]); // end
            }
            WasmInst::Branch { target } => {
                sink.emit_bytes(&[0x0c]); // br
                encode_leb128_u32(sink, *target);
            }
            WasmInst::BranchIf { target } => {
                sink.emit_bytes(&[0x0d]); // br_if
                encode_leb128_u32(sink, *target);
            }
            _ => return Err(EncodeError::NotImplemented("instruction encoding")),
        }
        Ok(())
    }
}

fn encode_leb128_u32(sink: &mut impl InstructionSink, mut value: u32) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        if value == 0 {
            sink.emit_bytes(&[byte]);
            break;
        } else {
            sink.emit_bytes(&[byte | 0x80]);
        }
    }
}

fn encode_leb128_u64(sink: &mut impl InstructionSink, mut value: u64) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        if value == 0 {
            sink.emit_bytes(&[byte]);
            break;
        } else {
            sink.emit_bytes(&[byte | 0x80]);
        }
    }
}

// Dummy machine environment for WASM
use std::sync::LazyLock;
static DUMMY_MACHINE_ENV: LazyLock<regalloc2::MachineEnv> = LazyLock::new(|| {
    regalloc2::MachineEnv {
        preferred_regs_by_class: [vec![], vec![], vec![]],
        non_preferred_regs_by_class: [vec![], vec![], vec![]],
        scratch_by_class: [None; 3],
        fixed_stack_slots: vec![],
    }
});