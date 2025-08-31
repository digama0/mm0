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

impl From<WasmRegSet> for regalloc2::PRegSet {
    fn from(_: WasmRegSet) -> Self {
        regalloc2::PRegSet::empty()
    }
}

pub mod regalloc;
pub mod regalloc_impl;
pub mod module;
pub mod vcode;
pub mod vcode_impl;
pub mod lower;
pub mod arch_impl;
pub mod wat;

// Re-export instruction type as inst module
pub mod inst {
    pub use super::{WasmInst as Inst, WasmType};
}

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
    
    // SIMD 128-bit Instructions
    /// Push a v128 constant onto the stack
    V128Const { value: [u8; 16] },
    
    /// Load a v128 value from memory
    V128Load { offset: u32, align: u32 },
    /// Store a v128 value to memory
    V128Store { offset: u32, align: u32 },
    
    /// SIMD arithmetic - float operations
    F32x4Add,
    F32x4Sub,
    F32x4Mul,
    F32x4Div,
    F32x4Sqrt,
    F32x4Min,
    F32x4Max,
    
    /// SIMD arithmetic - integer operations
    I32x4Add,
    I32x4Sub,
    I32x4Mul,
    I16x8Add,
    I16x8Sub,
    I16x8Mul,
    I8x16Add,
    I8x16Sub,
    
    /// SIMD comparisons - float
    F32x4Eq,
    F32x4Ne,
    F32x4Lt,
    F32x4Gt,
    F32x4Le,
    F32x4Ge,
    
    /// SIMD comparisons - integer
    I32x4Eq,
    I32x4Ne,
    I32x4LtS,
    I32x4LtU,
    I32x4GtS,
    I32x4GtU,
    I32x4LeS,
    I32x4LeU,
    I32x4GeS,
    I32x4GeU,
    
    /// SIMD conversions
    I32x4TruncSatF32x4S,
    I32x4TruncSatF32x4U,
    F32x4ConvertI32x4S,
    F32x4ConvertI32x4U,
    
    /// SIMD shuffle and swizzle
    I8x16Shuffle { lanes: [u8; 16] },
    I8x16Swizzle,
    
    /// SIMD splat operations
    I32x4Splat,
    I16x8Splat,
    I8x16Splat,
    F32x4Splat,
    F64x2Splat,
    
    /// SIMD extract lane
    I32x4ExtractLane { lane: u8 },
    I16x8ExtractLane { lane: u8 },
    I8x16ExtractLane { lane: u8 },
    F32x4ExtractLane { lane: u8 },
    F64x2ExtractLane { lane: u8 },
    
    /// SIMD replace lane
    I32x4ReplaceLane { lane: u8 },
    I16x8ReplaceLane { lane: u8 },
    I8x16ReplaceLane { lane: u8 },
    F32x4ReplaceLane { lane: u8 },
    F64x2ReplaceLane { lane: u8 },
    
    /// SIMD bitwise operations
    V128And,
    V128Or,
    V128Xor,
    V128Not,
    V128Andnot,
    V128Bitselect,
    
    /// SIMD any/all true operations
    V128AnyTrue,
    I32x4AllTrue,
    I16x8AllTrue,
    I8x16AllTrue,
}

/// WASM value types
#[derive(Clone, Copy, Debug)]
pub enum WasmType {
    I32,
    I64,
    F32,
    F64,
    V128,
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
            // Memory operations
            WasmInst::Load { ty, offset, align } => {
                match ty {
                    WasmType::I32 => {
                        sink.emit_bytes(&[0x28]); // i32.load
                        encode_leb128_u32(sink, *align);
                        encode_leb128_u32(sink, *offset);
                    }
                    WasmType::I64 => {
                        sink.emit_bytes(&[0x29]); // i64.load
                        encode_leb128_u32(sink, *align);
                        encode_leb128_u32(sink, *offset);
                    }
                    _ => return Err(EncodeError::NotImplemented("float load")),
                }
            }
            WasmInst::Store { ty, offset, align } => {
                match ty {
                    WasmType::I32 => {
                        sink.emit_bytes(&[0x36]); // i32.store
                        encode_leb128_u32(sink, *align);
                        encode_leb128_u32(sink, *offset);
                    }
                    WasmType::I64 => {
                        sink.emit_bytes(&[0x37]); // i64.store
                        encode_leb128_u32(sink, *align);
                        encode_leb128_u32(sink, *offset);
                    }
                    _ => return Err(EncodeError::NotImplemented("float store")),
                }
            }
            // Stack manipulation
            WasmInst::Drop => sink.emit_bytes(&[0x1a]),
            WasmInst::Select => sink.emit_bytes(&[0x1b]),
            
            // SIMD instructions
            WasmInst::V128Const { value } => {
                sink.emit_bytes(&[0xfd, 0x0c]); // v128.const
                sink.emit_bytes(value);
            }
            WasmInst::V128Load { offset, align } => {
                sink.emit_bytes(&[0xfd, 0x00]); // v128.load
                encode_leb128_u32(sink, *align);
                encode_leb128_u32(sink, *offset);
            }
            WasmInst::V128Store { offset, align } => {
                sink.emit_bytes(&[0xfd, 0x0b]); // v128.store
                encode_leb128_u32(sink, *align);
                encode_leb128_u32(sink, *offset);
            }
            
            // SIMD arithmetic - float
            WasmInst::F32x4Add => sink.emit_bytes(&[0xfd, 0xe4]),
            WasmInst::F32x4Sub => sink.emit_bytes(&[0xfd, 0xe5]),
            WasmInst::F32x4Mul => sink.emit_bytes(&[0xfd, 0xe6]),
            WasmInst::F32x4Div => sink.emit_bytes(&[0xfd, 0xe7]),
            WasmInst::F32x4Sqrt => sink.emit_bytes(&[0xfd, 0xe3]),
            WasmInst::F32x4Min => sink.emit_bytes(&[0xfd, 0xe8]),
            WasmInst::F32x4Max => sink.emit_bytes(&[0xfd, 0xe9]),
            
            // SIMD arithmetic - integer
            WasmInst::I32x4Add => sink.emit_bytes(&[0xfd, 0xae]),
            WasmInst::I32x4Sub => sink.emit_bytes(&[0xfd, 0xb1]),
            WasmInst::I32x4Mul => sink.emit_bytes(&[0xfd, 0xb5]),
            WasmInst::I16x8Add => sink.emit_bytes(&[0xfd, 0x8e]),
            WasmInst::I16x8Sub => sink.emit_bytes(&[0xfd, 0x91]),
            WasmInst::I16x8Mul => sink.emit_bytes(&[0xfd, 0x95]),
            WasmInst::I8x16Add => sink.emit_bytes(&[0xfd, 0x6e]),
            WasmInst::I8x16Sub => sink.emit_bytes(&[0xfd, 0x71]),
            
            // SIMD comparisons - float
            WasmInst::F32x4Eq => sink.emit_bytes(&[0xfd, 0x41]),
            WasmInst::F32x4Ne => sink.emit_bytes(&[0xfd, 0x42]),
            WasmInst::F32x4Lt => sink.emit_bytes(&[0xfd, 0x43]),
            WasmInst::F32x4Gt => sink.emit_bytes(&[0xfd, 0x44]),
            WasmInst::F32x4Le => sink.emit_bytes(&[0xfd, 0x45]),
            WasmInst::F32x4Ge => sink.emit_bytes(&[0xfd, 0x46]),
            
            // SIMD comparisons - integer
            WasmInst::I32x4Eq => sink.emit_bytes(&[0xfd, 0x37]),
            WasmInst::I32x4Ne => sink.emit_bytes(&[0xfd, 0x38]),
            WasmInst::I32x4LtS => sink.emit_bytes(&[0xfd, 0x39]),
            WasmInst::I32x4LtU => sink.emit_bytes(&[0xfd, 0x3a]),
            WasmInst::I32x4GtS => sink.emit_bytes(&[0xfd, 0x3b]),
            WasmInst::I32x4GtU => sink.emit_bytes(&[0xfd, 0x3c]),
            WasmInst::I32x4LeS => sink.emit_bytes(&[0xfd, 0x3d]),
            WasmInst::I32x4LeU => sink.emit_bytes(&[0xfd, 0x3e]),
            WasmInst::I32x4GeS => sink.emit_bytes(&[0xfd, 0x3f]),
            WasmInst::I32x4GeU => sink.emit_bytes(&[0xfd, 0x40]),
            
            // SIMD conversions
            WasmInst::I32x4TruncSatF32x4S => sink.emit_bytes(&[0xfd, 0xf8]),
            WasmInst::I32x4TruncSatF32x4U => sink.emit_bytes(&[0xfd, 0xf9]),
            WasmInst::F32x4ConvertI32x4S => sink.emit_bytes(&[0xfd, 0xfa]),
            WasmInst::F32x4ConvertI32x4U => sink.emit_bytes(&[0xfd, 0xfb]),
            
            // SIMD shuffle and swizzle
            WasmInst::I8x16Shuffle { lanes } => {
                sink.emit_bytes(&[0xfd, 0x0d]);
                sink.emit_bytes(lanes);
            }
            WasmInst::I8x16Swizzle => sink.emit_bytes(&[0xfd, 0x0e]),
            
            // SIMD splat operations
            WasmInst::I32x4Splat => sink.emit_bytes(&[0xfd, 0x11]),
            WasmInst::I16x8Splat => sink.emit_bytes(&[0xfd, 0x10]),
            WasmInst::I8x16Splat => sink.emit_bytes(&[0xfd, 0x0f]),
            WasmInst::F32x4Splat => sink.emit_bytes(&[0xfd, 0x13]),
            WasmInst::F64x2Splat => sink.emit_bytes(&[0xfd, 0x14]),
            
            // SIMD extract lane
            WasmInst::I32x4ExtractLane { lane } => {
                sink.emit_bytes(&[0xfd, 0x1b]);
                sink.emit_bytes(&[*lane]);
            }
            WasmInst::I16x8ExtractLane { lane } => {
                sink.emit_bytes(&[0xfd, 0x18]);
                sink.emit_bytes(&[*lane]);
            }
            WasmInst::I8x16ExtractLane { lane } => {
                sink.emit_bytes(&[0xfd, 0x15]);
                sink.emit_bytes(&[*lane]);
            }
            WasmInst::F32x4ExtractLane { lane } => {
                sink.emit_bytes(&[0xfd, 0x1f]);
                sink.emit_bytes(&[*lane]);
            }
            WasmInst::F64x2ExtractLane { lane } => {
                sink.emit_bytes(&[0xfd, 0x21]);
                sink.emit_bytes(&[*lane]);
            }
            
            // SIMD replace lane
            WasmInst::I32x4ReplaceLane { lane } => {
                sink.emit_bytes(&[0xfd, 0x1c]);
                sink.emit_bytes(&[*lane]);
            }
            WasmInst::I16x8ReplaceLane { lane } => {
                sink.emit_bytes(&[0xfd, 0x1a]);
                sink.emit_bytes(&[*lane]);
            }
            WasmInst::I8x16ReplaceLane { lane } => {
                sink.emit_bytes(&[0xfd, 0x17]);
                sink.emit_bytes(&[*lane]);
            }
            WasmInst::F32x4ReplaceLane { lane } => {
                sink.emit_bytes(&[0xfd, 0x20]);
                sink.emit_bytes(&[*lane]);
            }
            WasmInst::F64x2ReplaceLane { lane } => {
                sink.emit_bytes(&[0xfd, 0x22]);
                sink.emit_bytes(&[*lane]);
            }
            
            // SIMD bitwise operations
            WasmInst::V128And => sink.emit_bytes(&[0xfd, 0x4e]),
            WasmInst::V128Or => sink.emit_bytes(&[0xfd, 0x50]),
            WasmInst::V128Xor => sink.emit_bytes(&[0xfd, 0x51]),
            WasmInst::V128Not => sink.emit_bytes(&[0xfd, 0x4d]),
            WasmInst::V128Andnot => sink.emit_bytes(&[0xfd, 0x4f]),
            WasmInst::V128Bitselect => sink.emit_bytes(&[0xfd, 0x52]),
            
            // SIMD any/all true operations
            WasmInst::V128AnyTrue => sink.emit_bytes(&[0xfd, 0x53]),
            WasmInst::I32x4AllTrue => sink.emit_bytes(&[0xfd, 0xa3]),
            WasmInst::I16x8AllTrue => sink.emit_bytes(&[0xfd, 0x83]),
            WasmInst::I8x16AllTrue => sink.emit_bytes(&[0xfd, 0x63]),
            
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