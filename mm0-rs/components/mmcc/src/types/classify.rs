//! A high level classification of VCode emit patterns, used for relating MIR to VCode.
use super::{vcode::{BlockId, ChunkVec}, IdxVec};

/// A call to `get_place`, to resolve a place reference into a register or memory.
#[derive(Clone, Copy, Debug)]
pub struct Place {
  /// The number of projection entries, found in `Trace.projs`
  pub projs: u8,
}

/// A call to `get_const`, which resolves to a value or a constant in static memory.
#[derive(Clone, Copy, Debug)]
pub enum Const {
  /// A directly given value as a `u64`.
  Value,
  /// A larger or structured value stored in static memory.
  Ptr,
}

/// A call to `get_operand`.
#[derive(Clone, Copy, Debug)]
pub enum Operand {
  /// The operand is a place.
  Place(Place),
  /// The operand is a const.
  Const(Const),
}

/// A call to `into_reg`. The bool is true if a mov instruction was emitted.
#[derive(Clone, Copy, Debug)]
pub struct IntoReg(pub bool);

/// A call to `into_mem`. The bool is true if a mov instruction was emitted.
#[derive(Clone, Copy, Debug)]
pub struct IntoMem(pub bool);

/// A call to `into_rm`. The bool is true if a mov instruction was emitted.
#[derive(Clone, Copy, Debug)]
pub struct IntoRM(pub bool);

/// A call to `into_rmi_32`. The bool is true if a mov instruction was emitted.
#[derive(Clone, Copy, Debug)]
pub struct IntoRMI32(pub bool);

/// A call to `get_operand_reg`.
pub type OperandReg = (Operand, IntoReg);
/// A call to `get_operand_rm`.
pub type OperandRM = (Operand, IntoRM);
/// A call to `get_operand_32`.
pub type Operand32 = (Operand, IntoRMI32);

/// A call to `emit_copy`.
#[derive(Clone, Copy, Debug)]
pub enum Copy {
  /// One instruction was emitted (load or store or imm).
  One,
  /// Two instructions were emitted for a mem-mem move.
  Two,
}

/// A call to `build_move`.
#[derive(Clone, Copy, Debug)]
pub enum Move {
  /// A small (<= 8 byte) move, implemented via a copy.
  Small(Operand, Copy),
}

/// A `build_as` call.
#[derive(Clone, Copy, Debug)]
pub enum As {
  /// This is a truncating `as`, no sign extension is needed.
  Truncate(Copy),
  /// This is an extending `as`, with a zero/sign extension.
  Extend(Copy),
}

/// A `build_shift_or_zero` call.
#[derive(Clone, Copy, Debug)]
#[allow(variant_size_differences)]
pub enum Shift {
  /// The right operand is zero, so we read the left operand and write 0.
  Zero(OperandReg),
  /// The right operand is an immediate, so we read the left operand, shift, and write the result.
  Imm(OperandReg, Copy),
  /// The right operand is a variable, so we read the operands, shift, and write the result.
  Var(OperandReg, OperandReg, Copy),
}

/// A `build_rvalue` call.
#[derive(Clone, Copy, Debug)]
pub enum RValue {
  /// A `Use` statement
  Use(Move),
  /// A `Unop` statement, except `As`
  Unop(OperandReg, Copy),
  /// A `Unop(As)` statement
  As(OperandRM, As),
  /// A generic `Binop` statement
  Binop(OperandReg, Operand32, Copy),
  /// A `Binop(Mul)` statement
  Mul(OperandReg, OperandRM, Copy),
  /// A `Binop(Max)` statement
  Max(OperandReg, OperandReg, Copy),
  /// A `Binop(Min)` statement
  Min(OperandReg, OperandReg, Copy),
  /// A `Binop(Shl|Shr)` statement
  Shift(Shift),
  /// A `Binop(Eq|Ne|Lt|Le)` or `Eq` statement
  Cmp(OperandReg, Operand32, Copy),
  /// A `Pun` statement
  Pun(Place),
  /// A `Cast` statement
  Cast(OperandRM, As),
  /// A `List` statement. The arguments are stored in `Trace.lists`
  List(u32),
  /// A `Array` statement with one argument.
  Array1(Move),
  /// A `Array` statement. The arguments are stored in `Trace.lists`
  Array(u32),
  /// A `Borrow` statement
  Borrow(Place, Copy),
  /// A statement producing no code.
  Ghost,
}

/// A call to `add_scaled`.
#[derive(Clone, Copy, Debug)]
pub enum AddScaled {
  /// The address has no base and scale 1,
  /// so the address mode was updated and no code was emitted
  NoBase1,
  /// The address has scale 1/2/4/8,
  /// so the address mode was updated and no code was emitted
  Pow2,
  /// The address has no base and scale 3/5/9,
  /// so the address mode was updated and no code was emitted
  NoBasePow2Add,
  /// A LEA was emitted to reduce to the `Pow2` case, resulting in 1 instruction
  ComposePow2,
  /// The scale or base was not one of the easy cases, so IMM+MUL was emitted
  Large,
  /// A LEA was emitted to reduce to the `Large` case, resulting in 3 instructions
  ComposeLarge,
}

/// One projection in the `get_place` call.
#[derive(Clone, Copy, Debug)]
pub enum Projection {
  /// A `Deref` projection
  Deref(IntoReg),
  /// A `Proj(And|Sn)` projection
  Ghost,
  /// A `Proj(Array)` projection
  ProjArray,
  /// A `Proj(Struct)` projection
  ProjStruct,
  /// A `Index|Slice` projection
  IndexSlice(IntoReg, AddScaled),
}

  /// An operand element in `List`, `Array`, `Call` or `Return`
#[derive(Clone, Copy, Debug)]
pub enum Elem {
  /// A ghost element
  Ghost,
  /// The operand was evaluated
  Operand(Operand),
  /// The operand was evaluated and placed in a memory location
  Boxed(Operand, IntoMem),
  /// The operand was evaluated and placed in a memory location
  BoxedMem(Operand, IntoMem),
  /// The operand was moved
  Move(Move),
  /// A return value was placed in a register
  RetReg,
  /// A return value was placed in memory
  RetMem(Copy),
}

/// A statement.
#[derive(Clone, Copy, Debug)]
#[allow(variant_size_differences)]
pub enum Statement {
  /// A `Let` statement
  Let(RValue),
  /// An `Assign` statement
  Assign(Place, Move),
  /// A statement with no code
  Ghost,
}

/// A block terminator statement
#[derive(Clone, Copy, Debug)]
pub enum Terminator {
  /// A `Jump` statement. The arguments are stored in `Trace.lists`
  Jump(u32),
  /// A `Jump1` statement.
  Jump1,
  /// A `Return` statement. The arguments are stored in `Trace.lists`
  Return,
  /// An `Exit` statement.
  Exit,
  /// An `If` statement.
  If(OperandReg),
  /// An `Assert` statement.
  Assert(OperandReg),
  /// A `Call` statement. If the bool is true then the function returns
  Call(bool),
  /// An intrinsic `Call` statement. The Option is set if the return is not ignored
  SysCall(u32, Option<Copy>),
  /// An `Assert(false)` statement.
  Fail,
}

/// A classification of emitted instructions based on the input MIR.
#[derive(Clone, Debug, Default)]
pub struct Trace {
  pub(crate) stmts: ChunkVec<BlockId, Statement>,
  pub(crate) terms: IdxVec<BlockId, Terminator>,
  pub(crate) projs: Vec<Projection>,
  pub(crate) lists: Vec<Elem>,
}
