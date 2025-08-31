//! Architecture-independent code generation
//!
//! This module provides the abstraction layer for multi-architecture support.
//! It allows the compiler to generate code for different architectures without
//! hardcoding x86 assumptions throughout the codebase.

use std::io::Write;
use std::collections::HashMap;
use crate::types::mir;
use crate::types::vcode::{ProcAbi, ProcId};
use crate::types::IdxVec;
use crate::arch_pcode::ArchPCode;
use crate::mir_opt::storage::Allocations;
use crate::arch::target::{Target, TargetArch};
use crate::linker::ConstData;
use crate::{Symbol, Entity, LowerErr, LinkedCode};

/// Trait for architecture-specific code generation
pub trait ArchCodegen: Send + Sync {
    /// Build VCode from MIR for this architecture
    fn build_vcode(
        &self,
        names: &HashMap<Symbol, Entity>,
        funcs: &HashMap<Symbol, ProcId>,
        func_abi: &IdxVec<ProcId, ProcAbi>,
        consts: &ConstData,
        cfg: &mir::Cfg,
        allocs: &Allocations,
        ctx: crate::lower_shared::VCodeCtx<'_>,
    ) -> Result<Box<dyn VCodeTrait>, LowerErr>;
    
    /// Write executable for this architecture
    fn write_executable(&self, code: &LinkedCode, w: &mut dyn Write) -> std::io::Result<()>;
}

/// Trait for VCode that can be register allocated
pub trait VCodeTrait: Send {
    /// Perform register allocation
    fn regalloc(self: Box<Self>) -> (crate::types::vcode::ProcAbi, ArchPCode);
}

/// X86-64 code generator
pub struct X86Codegen;

impl ArchCodegen for X86Codegen {
    fn build_vcode(
        &self,
        names: &HashMap<Symbol, Entity>,
        funcs: &HashMap<Symbol, ProcId>,
        func_abi: &IdxVec<ProcId, ProcAbi>,
        consts: &ConstData,
        cfg: &mir::Cfg,
        allocs: &Allocations,
        ctx: crate::lower_shared::VCodeCtx<'_>,
    ) -> Result<Box<dyn VCodeTrait>, LowerErr> {
        #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
        {
            // Use the existing x86 build_vcode
            let vcode = crate::build_vcode::build_vcode(names, funcs, func_abi, consts, cfg, allocs, ctx)?;
            Ok(Box::new(vcode))
        }
        #[cfg(any(feature = "arm64-backend", feature = "wasm-backend"))]
        {
            // When building for ARM64/WASM, x86 build_vcode is not available
            Err(LowerErr::InfiniteOp(Default::default()))
        }
    }
    
    fn write_executable(&self, code: &LinkedCode, w: &mut dyn Write) -> std::io::Result<()> {
        // We need to pass a concrete type to write_elf
        // Create a wrapper that forwards to the dyn Write
        struct WriteWrapper<'a>(&'a mut dyn Write);
        impl<'a> Write for WriteWrapper<'a> {
            fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
                self.0.write(buf)
            }
            fn flush(&mut self) -> std::io::Result<()> {
                self.0.flush()
            }
        }
        code.write_elf(&mut WriteWrapper(w))
    }
}

/// ARM64 code generator
pub struct Arm64Codegen;

impl ArchCodegen for Arm64Codegen {
    fn build_vcode(
        &self,
        names: &HashMap<Symbol, Entity>,
        funcs: &HashMap<Symbol, ProcId>,
        func_abi: &IdxVec<ProcId, ProcAbi>,
        consts: &ConstData,
        cfg: &mir::Cfg,
        allocs: &Allocations,
        ctx: crate::lower_shared::VCodeCtx<'_>,
    ) -> Result<Box<dyn VCodeTrait>, LowerErr> {
        #[cfg(feature = "arm64-backend")]
        {
            eprintln!("ARM64 CODEGEN: build_vcode called! This is the ARM64 backend!");
            let vcode = crate::arch::arm64::lower::build_arm64_vcode(
                names, funcs, func_abi, consts, cfg, allocs, ctx
            )?;
            Ok(Box::new(vcode))
        }
        #[cfg(not(feature = "arm64-backend"))]
        {
            Err(LowerErr::InfiniteOp(Default::default()))
        }
    }
    
    fn write_executable(&self, code: &LinkedCode, w: &mut dyn Write) -> std::io::Result<()> {
        struct WriteWrapper<'a>(&'a mut dyn Write);
        impl<'a> Write for WriteWrapper<'a> {
            fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
                self.0.write(buf)
            }
            fn flush(&mut self) -> std::io::Result<()> {
                self.0.flush()
            }
        }
        code.write_elf(&mut WriteWrapper(w))
    }
}

/// WASM code generator
pub struct WasmCodegen;

impl ArchCodegen for WasmCodegen {
    fn build_vcode(
        &self,
        names: &HashMap<Symbol, Entity>,
        funcs: &HashMap<Symbol, ProcId>,
        func_abi: &IdxVec<ProcId, ProcAbi>,
        consts: &ConstData,
        cfg: &mir::Cfg,
        allocs: &Allocations,
        ctx: crate::lower_shared::VCodeCtx<'_>,
    ) -> Result<Box<dyn VCodeTrait>, LowerErr> {
        #[cfg(feature = "wasm-backend")]
        {
            eprintln!("WASM CODEGEN: build_vcode called! This is the WASM backend!");
            let vcode = crate::arch::wasm::lower::build_wasm_vcode(
                names, funcs, func_abi, consts, cfg, allocs, ctx
            )?;
            Ok(Box::new(vcode))
        }
        #[cfg(not(feature = "wasm-backend"))]
        {
            Err(LowerErr::InfiniteOp(Default::default()))
        }
    }
    
    fn write_executable(&self, code: &LinkedCode, w: &mut dyn Write) -> std::io::Result<()> {
        struct WriteWrapper<'a>(&'a mut dyn Write);
        impl<'a> Write for WriteWrapper<'a> {
            fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
                self.0.write(buf)
            }
            fn flush(&mut self) -> std::io::Result<()> {
                self.0.flush()
            }
        }
        code.write_elf(&mut WriteWrapper(w))
    }
}

/// Get code generator for target
pub fn get_codegen(target: Target) -> Box<dyn ArchCodegen> {
    eprintln!("get_codegen called with target: {:?}", target);
    match target.arch {
        TargetArch::X86_64 => {
            eprintln!("Selected X86_64 codegen");
            Box::new(X86Codegen)
        },
        TargetArch::Arm64 => {
            eprintln!("Selected ARM64 codegen!");
            Box::new(Arm64Codegen)
        },
        TargetArch::Wasm32 | TargetArch::Wasm64 => {
            eprintln!("Selected WASM codegen");
            Box::new(WasmCodegen)
        },
    }
}

// Implement VCodeTrait for x86 VCode
#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
impl VCodeTrait for crate::build_vcode::VCode {
    fn regalloc(self: Box<Self>) -> (ProcAbi, ArchPCode) {
        let (abi, pcode) = (*self).regalloc();
        (abi, ArchPCode::X86(pcode))
    }
}