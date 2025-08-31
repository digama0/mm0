//! Shared types and utilities for MIR to VCode lowering
//!
//! This module contains architecture-independent types that are used
//! by all architecture-specific lowering implementations.

use crate::types::{mir::{Arg, Ty}, VarId, Spanned};
use crate::{FileSpan, Symbol};

/// An error during lowering. This error means that the operation is not supported by the backend,
/// the main one is that a ghost variable is used in a computationally relevant position.
#[derive(Debug)]
pub enum LowerErr {
    /// A ghost variable was used in an operation that requires it to not be ghost.
    GhostVarUsed(Spanned<VarId>),
    /// An operation on unbounded integers was used and could not be optimized away.
    InfiniteOp(FileSpan),
    /// The entry point is unreachable, which means that there is an
    /// unconditional infinite loop in the function.
    EntryUnreachable(FileSpan),
}

/// The ABI expected by the caller.
#[derive(Clone, Copy, Debug)]
pub enum VCodeCtx<'a> {
    /// This is a regular procedure; the `&[Arg]` is the function returns.
    Proc(&'a [Arg]),
    /// This is the `start` function, which is called by the operating system and has a
    /// special stack layout.
    Start(&'a [(Symbol, bool, VarId, Ty)]),
}

impl<'a> From<&'a [Arg]> for VCodeCtx<'a> {
    fn from(v: &'a [Arg]) -> Self { Self::Proc(v) }
}