//! Dummy proof types for non-x86 architectures
//!
//! This module provides stub types to satisfy the compiler when building
//! for architectures that don't have proof support.

use crate::FileSpan;

/// Dummy instruction type
#[derive(Clone, Copy, Debug)]
pub struct Inst<'a> {
    pub inst: DummyInst,
    _phantom: std::marker::PhantomData<&'a ()>,
}

/// Dummy instruction
#[derive(Clone, Copy, Debug)]
pub struct DummyInst;

impl DummyInst {
    pub fn is_spill(&self) -> bool {
        false
    }
}

/// Dummy instruction iterator
#[derive(Clone, Debug)]
pub struct InstIter<'a> {
    _phantom: std::marker::PhantomData<&'a ()>,
}

impl<'a> Iterator for InstIter<'a> {
    type Item = Inst<'a>;
    
    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

/// Dummy constant for termination verification
pub const VERIFY_TERMINATION: bool = false;