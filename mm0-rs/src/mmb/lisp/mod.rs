//! Serialize and deserialize the global lisp environment into the `Lisp` mmb
//! index table. See `mm0-rs/mmb-lisp.md`.

pub mod export;
pub mod import;

/// The `Lisp` table format version, written into the index entry's `data` field.
/// This crate implements version `0`.
pub const VERSION: u32 = 0;

/// Value-stream opcodes (see `mmb-lisp.md`).
mod op {
  pub(super) const END: u8 = 0x00;
  pub(super) const UNDEF: u8 = 0x01;
  pub(super) const FALSE: u8 = 0x02;
  pub(super) const TRUE: u8 = 0x03;
  pub(super) const ATOM: u8 = 0x04;
  pub(super) const ATOMZ: u8 = 0x05;
  pub(super) const STRING: u8 = 0x06;
  pub(super) const STRINGZ: u8 = 0x07;
  pub(super) const NUMBER: u8 = 0x08;
  pub(super) const SYNTAX: u8 = 0x09;
  pub(super) const BUILTIN: u8 = 0x0A;
  pub(super) const LIST: u8 = 0x0B;
  pub(super) const LIST_SAVE: u8 = 0x0C;
  pub(super) const DOTTED_LIST: u8 = 0x0D;
  pub(super) const DOTTED_LIST_SAVE: u8 = 0x0E;
  pub(super) const MAP: u8 = 0x0F;
  pub(super) const SPAN: u8 = 0x10;
  pub(super) const ANNOT: u8 = 0x11;
  pub(super) const SAVE: u8 = 0x12;
  pub(super) const REF: u8 = 0x13;
  pub(super) const NEW_REF: u8 = 0x14;
  pub(super) const LAMBDA: u8 = 0x16;
  pub(super) const CUSTOM_PROC: u8 = 0x17;
  pub(super) const CODE: u8 = 0x18;
  pub(super) const MVAR: u8 = 0x19;
  pub(super) const GOAL: u8 = 0x1A;
  pub(super) const DEAD_WEAK: u8 = 0x1B;
  pub(super) const SET_WEAK: u8 = 0x1C;
}

/// `Ir` sub-stream opcodes (see the `Ir` table in `mmb-lisp.md`). Its space is
/// independent of [`op`].
mod ir {
  pub(super) const UNDEF: u8 = 0x01;
  pub(super) const DUP: u8 = 0x02;
  pub(super) const FOCUS_FINISH: u8 = 0x03;
  pub(super) const TEST_PATTERN_RESUME: u8 = 0x04;
  pub(super) const MAP: u8 = 0x05;
  pub(super) const HAVE: u8 = 0x06;
  pub(super) const REFINE_RESUME: u8 = 0x07;
  pub(super) const ADD_THM: u8 = 0x08;
  pub(super) const MERGE_MAP: u8 = 0x09;
  pub(super) const ON_DECLS: u8 = 0x0A;
  pub(super) const PATTERN_UNDEF: u8 = 0x0B;
  pub(super) const PATTERN_GOAL: u8 = 0x0C;
  pub(super) const PATTERN_TEST_PAUSE: u8 = 0x0D;
  pub(super) const DROP: u8 = 0x0E;
  pub(super) const DROP_ABOVE: u8 = 0x0F;
  pub(super) const ASSERT_SCOPE: u8 = 0x10;
  pub(super) const END_SCOPE: u8 = 0x11;
  pub(super) const LOCAL: u8 = 0x12;
  pub(super) const DOTTED_LIST: u8 = 0x13;
  pub(super) const JUMP_UNLESS: u8 = 0x14;
  pub(super) const JUMP: u8 = 0x15;
  pub(super) const LOCAL_DEF: u8 = 0x16;
  pub(super) const PATTERN_ATOM: u8 = 0x17;
  pub(super) const PATTERN_EQ_ATOM: u8 = 0x18;
  pub(super) const PATTERN_DOTTED_LIST: u8 = 0x19;
  pub(super) const REFINE_GOAL: u8 = 0x1A;
  pub(super) const PATTERN_RESULT: u8 = 0x1B;
  pub(super) const PATTERN_BOOL: u8 = 0x1C;
  pub(super) const PATTERN_QUOTE_ATOM: u8 = 0x1D;
  pub(super) const PATTERN_QEXPR_ATOM: u8 = 0x1E;
  pub(super) const CONST: u8 = 0x1F;
  pub(super) const PATTERN_STRING: u8 = 0x20;
  pub(super) const PATTERN_NUMBER: u8 = 0x21;
  pub(super) const APP_HEAD: u8 = 0x22;
  pub(super) const FOCUS_START: u8 = 0x23;
  pub(super) const BRANCH_FAIL: u8 = 0x24;
  pub(super) const GLOBAL: u8 = 0x25;
  pub(super) const SET_MERGE_STRATEGY: u8 = 0x26;
  pub(super) const LIST: u8 = 0x27;
  pub(super) const GLOBAL_DEF: u8 = 0x28;
  pub(super) const SET_DOC: u8 = 0x29;
  pub(super) const APP: u8 = 0x2A;
  pub(super) const TAIL_APP: u8 = 0x2B;
  pub(super) const BUILTIN_APP: u8 = 0x2C;
  pub(super) const BUILTIN_TAIL_APP: u8 = 0x2D;
  pub(super) const ARITY_ERROR: u8 = 0x2E;
  pub(super) const BRANCH: u8 = 0x2F;
  pub(super) const PATTERN_LIST: u8 = 0x30;
  pub(super) const PATTERN_TRY: u8 = 0x31;
  pub(super) const PATTERN_MVAR: u8 = 0x32;
  pub(super) const LAMBDA: u8 = 0x33;
}

/// `CustomProc` `kind` bytes.
mod custom {
  pub(super) const MATCH_CONT: u8 = 0;
  pub(super) const REFINE_CALLBACK: u8 = 1;
  pub(super) const MERGE_MAP: u8 = 2;
  pub(super) const PROOF_THUNK: u8 = 3;
}

/// [`infer_target`](crate::elab::lisp::InferTarget) tags: the `u8` after an `MVar`.
mod infer {
  pub(super) const UNKNOWN: u8 = 0;
  pub(super) const PROVABLE: u8 = 1;
  pub(super) const BOUND: u8 = 2;
  pub(super) const REG: u8 = 3;
}

/// `PatternMVar` tags: the `Ir::PatternMVar` `data`.
mod pat_mvar {
  pub(super) const UNKNOWN: u8 = 0;
  pub(super) const ANY: u8 = 1;
  pub(super) const SIMPLE: u8 = 2;
}

/// `ProcSpec` kinds: the first byte of a `spec`.
mod spec {
  pub(super) const EXACT: u8 = 0;
  pub(super) const AT_LEAST: u8 = 1;
}

/// The bit of a `Lambda` command's `data` flags set for a named closure.
pub(super) const LAMBDA_NAMED: u32 = 1;
