//! Architecture-generic PCode wrapper
//!
//! This module provides an enum wrapper that allows LinkedCode to work with
//! any architecture's PCode type, solving the fundamental coupling issue.

use std::collections::HashMap;
use crate::types::{IdxVec, mir, vcode::{ProcAbi, BlockId, ChunkVec}};
#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
use crate::types::classify::Trace;
#[cfg(any(feature = "arm64-backend", feature = "wasm-backend"))]
use crate::types::vcode::Trace;
use crate::arch::target::TargetArch;

// Re-export PInstId so it's available everywhere
pub use crate::regalloc::PInstId;

/// Architecture-generic wrapper for PCode
#[derive(Clone, Debug)]
pub enum ArchPCode {
    /// x86-64 PCode
    #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
    X86(Box<crate::regalloc::PCode>),
    /// ARM64 PCode  
    #[cfg(feature = "arm64-backend")]
    Arm64(Box<crate::arch::arm64::regalloc::PCode>),
    /// WebAssembly PCode
    #[cfg(feature = "wasm-backend")]
    Wasm(Box<crate::arch::wasm::regalloc::PCode>),
}

impl ArchPCode {
    /// Get the architecture of this PCode
    #[allow(unreachable_patterns)]
    pub fn arch(&self) -> TargetArch {
        match self {
            #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
            ArchPCode::X86(_) => TargetArch::X86_64,
            #[cfg(feature = "arm64-backend")]
            ArchPCode::Arm64(_) => TargetArch::Arm64,
            #[cfg(feature = "wasm-backend")]
            ArchPCode::Wasm(_) => TargetArch::Wasm32,
            _ => unreachable!(),
        }
    }
    
    /// Get the block map
    #[allow(unreachable_patterns)]
    pub fn block_map(&self) -> &HashMap<mir::BlockId, BlockId> {
        match self {
            #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
            ArchPCode::X86(pcode) => &pcode.block_map,
            #[cfg(feature = "arm64-backend")]
            ArchPCode::Arm64(pcode) => &pcode.block_map,
            #[cfg(feature = "wasm-backend")]
            ArchPCode::Wasm(pcode) => &pcode.block_map,
            _ => unreachable!(),
        }
    }
    
    /// Get the blocks
    #[allow(unreachable_patterns)]
    pub fn blocks(&self) -> &IdxVec<BlockId, (mir::BlockId, PInstId, PInstId)> {
        match self {
            #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
            ArchPCode::X86(pcode) => &pcode.blocks,
            #[cfg(feature = "arm64-backend")]
            ArchPCode::Arm64(pcode) => &pcode.blocks,
            #[cfg(feature = "wasm-backend")]
            ArchPCode::Wasm(pcode) => &pcode.blocks,
            _ => unreachable!(),
        }
    }
    
    /// Get block addresses
    #[allow(unreachable_patterns)]
    pub fn block_addr(&self) -> &IdxVec<BlockId, u32> {
        match self {
            #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
            ArchPCode::X86(pcode) => &pcode.block_addr,
            #[cfg(feature = "arm64-backend")]
            ArchPCode::Arm64(pcode) => &pcode.block_addr,
            #[cfg(feature = "wasm-backend")]
            ArchPCode::Wasm(pcode) => &pcode.block_addr,
            _ => unreachable!(),
        }
    }
    
    /// Get trace information
    #[allow(unreachable_patterns)]
    pub fn trace(&self) -> &Trace {
        match self {
            #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
            ArchPCode::X86(pcode) => &pcode.trace,
            #[cfg(feature = "arm64-backend")]
            ArchPCode::Arm64(pcode) => &pcode.trace,
            #[cfg(feature = "wasm-backend")]
            ArchPCode::Wasm(pcode) => &pcode.trace,
            _ => unreachable!(),
        }
    }
    
    /// Get stack size
    #[allow(unreachable_patterns)]
    pub fn stack_size(&self) -> u32 {
        match self {
            #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
            ArchPCode::X86(pcode) => pcode.stack_size,
            #[cfg(feature = "arm64-backend")]
            ArchPCode::Arm64(pcode) => pcode.stack_size,
            #[cfg(feature = "wasm-backend")]
            ArchPCode::Wasm(pcode) => pcode.stack_size,
            _ => unreachable!(),
        }
    }
    
    /// Get total code length
    #[allow(unreachable_patterns)]
    pub fn len(&self) -> u32 {
        match self {
            #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
            ArchPCode::X86(pcode) => pcode.len,
            #[cfg(feature = "arm64-backend")]
            ArchPCode::Arm64(pcode) => pcode.len,
            #[cfg(feature = "wasm-backend")]
            ArchPCode::Wasm(pcode) => pcode.len,
            _ => unreachable!(),
        }
    }
    
    /// Check if code is empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    
    /// Get instruction count (architecture-specific)
    #[allow(unreachable_patterns)]
    pub fn inst_count(&self) -> usize {
        match self {
            #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
            ArchPCode::X86(pcode) => pcode.insts.len(),
            #[cfg(feature = "arm64-backend")]
            ArchPCode::Arm64(pcode) => pcode.insts.len(),
            #[cfg(feature = "wasm-backend")]
            ArchPCode::Wasm(pcode) => pcode.insts.len(),
            _ => unreachable!(),
        }
    }
    
    /// Architecture-specific operations that need the concrete type
    #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
    #[allow(unreachable_patterns)]
    pub fn with_x86<F, R>(&self, f: F) -> Option<R>
    where F: FnOnce(&crate::regalloc::PCode) -> R
    {
        match self {
            #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
            ArchPCode::X86(pcode) => Some(f(pcode)),
            _ => None,
        }
    }
    
    #[cfg(feature = "arm64-backend")]
    #[allow(unreachable_patterns)]
    pub fn with_arm64<F, R>(&self, f: F) -> Option<R>
    where F: FnOnce(&crate::arch::arm64::regalloc::PCode) -> R
    {
        match self {
            #[cfg(feature = "arm64-backend")]
            ArchPCode::Arm64(pcode) => Some(f(pcode)),
            _ => None,
        }
    }
    
    #[cfg(feature = "wasm-backend")]
    #[allow(unreachable_patterns)]
    pub fn with_wasm<F, R>(&self, f: F) -> Option<R>
    where F: FnOnce(&crate::arch::wasm::regalloc::PCode) -> R
    {
        match self {
            #[cfg(feature = "wasm-backend")]
            ArchPCode::Wasm(pcode) => Some(f(pcode)),
            _ => None,
        }
    }
}