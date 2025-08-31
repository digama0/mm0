//! WASM "register allocation" implementation
//!
//! WebAssembly is a stack machine, so it doesn't need traditional register
//! allocation. This module converts VCode to PCode with minimal changes.

use crate::types::{IdxVec, mir, vcode::*};
use super::vcode::VCode;
use super::WasmInst;
use super::regalloc::{PCode, PInstId};
use super::WasmType;
use std::collections::HashMap;

/// Simple allocation for WASM - mostly a direct copy since no registers
pub fn wasm_simple_alloc(vcode: VCode) -> PCode {
    super::regalloc::regalloc_wasm(&vcode).expect("WASM allocation should not fail")
}

