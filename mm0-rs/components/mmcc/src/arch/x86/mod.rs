//! x86-specific parts of the compiler.
pub mod proof;

use std::fmt::Debug;

use num::Zero;
use regalloc2::{MachineEnv, PReg, VReg, Operand};

use crate::codegen::InstSink;
use crate::LinkedCode;
use crate::types::{IdxVec, Size,
  vcode::{BlockId, GlobalId, SpillId, ProcId, InstId, Inst as VInst, VCode}};

const fn preg(i: usize) -> PReg { PReg::new(i, regalloc2::RegClass::Int) }

/// If true, then a REX byte is needed to encode this register
#[inline] fn large_preg(r: PReg) -> bool { r.hw_enc() & 8 != 0 }

const RAX: PReg = preg(0);
const RCX: PReg = preg(1);
const RDX: PReg = preg(2);
const RBX: PReg = preg(3);
pub(crate) const RSP: PReg = preg(4);
const RBP: PReg = preg(5);
const RSI: PReg = preg(6);
const RDI: PReg = preg(7);
const R8: PReg = preg(8);
const R9: PReg = preg(9);
const R10: PReg = preg(10);
const R11: PReg = preg(11);
const R12: PReg = preg(12);
const R13: PReg = preg(13);
const R14: PReg = preg(14);
const R15: PReg = preg(15);
pub(crate) const ARG_REGS: [PReg; 6] = [RDI, RSI, RDX, RCX, R8, R9];
pub(crate) const SYSCALL_ARG_REGS: (PReg, [PReg; 6]) = (RAX, [RDI, RSI, RDX, R10, R8, R9]);
pub(crate) const CALLER_SAVED: [PReg; 8] = [RAX, RDI, RSI, RDX, RCX, R8, R9, R10];
pub(crate) const CALLEE_SAVED: [PReg; 6] = [RBX, RBP, R12, R13, R14, R15];
pub(crate) const SCRATCH: PReg = R11;

pub(crate) fn callee_saved() -> impl DoubleEndedIterator<Item=PReg> + Clone {
  CALLEE_SAVED.iter().copied()
}
pub(crate) fn caller_saved() -> impl DoubleEndedIterator<Item=PReg> + Clone {
  CALLER_SAVED.iter().copied()
}
pub(crate) fn non_callee_saved() -> impl DoubleEndedIterator<Item=PReg> + Clone {
  caller_saved().chain([SCRATCH])
}

lazy_static! {
  pub(crate) static ref MACHINE_ENV: MachineEnv = {
    MachineEnv {
      preferred_regs_by_class: [CALLER_SAVED.into(), vec![]],
      non_preferred_regs_by_class: [CALLEE_SAVED.into(), vec![]],
      scratch_by_class: [SCRATCH, PReg::invalid()],
      regs: caller_saved().chain(callee_saved()).chain([SCRATCH]).collect(),
    }
  };
}

#[derive(Copy, Clone, Default)]
pub(crate) struct PRegSet(u16);
impl PRegSet {
  #[inline] pub(crate) fn insert(&mut self, r: PReg) { self.0 |= 1 << r.hw_enc() }
  #[inline] pub(crate) fn get(self, r: PReg) -> bool { self.0 & (1 << r.hw_enc()) != 0 }
}

/// These indicate the form of a scalar shift/rotate: left, signed right, unsigned right.
#[derive(Clone, Copy, Debug)]
pub enum ShiftKind {
  // Rol = 0,
  // Ror = 1,
  /// Left shift.
  Shl = 4,
  /// Logical right shift: Inserts zeros in the most significant bits.
  ShrL = 5,
  /// Arithmetic right shift: Replicates the sign bit in the most significant bits.
  ShrA = 7,
}

/// A binop which is used only for its effect on the flags.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Cmp {
  /// CMP instruction: compute `a - b` and set flags from result.
  Cmp,
  /// TEST instruction: compute `a & b` and set flags from result.
  Test,
}

/// These indicate ways of extending (widening) a value, using the Intel
/// naming: B(yte) = u8, W(ord) = u16, L(ong)word = u32, Q(uad)word = u64
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ExtMode {
  /// Byte (u8) -> Longword (u32).
  BL,
  /// Byte (u8) -> Quadword (u64).
  BQ,
  /// Word (u16) -> Longword (u32).
  WL,
  /// Word (u16) -> Quadword (u64).
  WQ,
  /// Longword (u32) -> Quadword (u64).
  LQ,
}

impl ExtMode {
  /// Calculate the `ExtMode` from passed bit lengths of the from/to types.
  #[must_use] pub fn new(from: Size, to: Size) -> Option<ExtMode> {
    match (from, to) {
      (Size::S8, Size::S16 | Size::S32) => Some(ExtMode::BL),
      (Size::S8, Size::S64) => Some(ExtMode::BQ),
      (Size::S16, Size::S32) => Some(ExtMode::WL),
      (Size::S16, Size::S64) => Some(ExtMode::WQ),
      (Size::S32, Size::S64) => Some(ExtMode::LQ),
      _ => None,
    }
  }

  /// Return the source register size in bytes.
  #[must_use] pub fn src(self) -> Size {
    match self {
      ExtMode::BL | ExtMode::BQ => Size::S8,
      ExtMode::WL | ExtMode::WQ => Size::S16,
      ExtMode::LQ => Size::S32,
    }
  }

  /// Return the destination register size in bytes.
  #[must_use] pub fn dst(self) -> Size {
    match self {
      ExtMode::BL | ExtMode::WL => Size::S32,
      ExtMode::BQ | ExtMode::WQ | ExtMode::LQ => Size::S64,
    }
  }
}

/// Condition code tests supported by the x86 architecture.
#[allow(clippy::upper_case_acronyms)]
#[derive(Copy, Clone, Debug)]
#[repr(u8)]
pub enum CC {
  ///  overflow
  O = 0,
  /// no overflow
  NO = 1,
  /// `<` unsigned (below, aka NAE = not above equal, C = carry)
  B = 2,
  /// `>=` unsigned (not below, aka AE = above equal, NC = no carry)
  NB = 3,
  /// zero (aka E = equal)
  Z = 4,
  /// not-zero (aka NE = not equal)
  NZ = 5,
  /// `<=` unsigned (below equal, aka NA = not above)
  BE = 6,
  /// `>` unsigned (not below equal, aka A = above)
  NBE = 7,
  /// negative (sign)
  S = 8,
  /// not-negative (no sign)
  NS = 9,
  // /// parity (aka PE = parity even)
  // P = 10,
  // /// not parity (aka PO = parity odd)
  // NP = 11,
  /// `<` signed (less, aka NGE = not greater equal)
  L = 12,
  /// `>=` signed (not less, aka GE = greater equal)
  NL = 13,
  /// `<=` signed (less equal, aka NG = not greater)
  LE = 14,
  /// `>` signed (not less equal, aka G = greater)
  NLE = 15,
}

impl CC {
  /// Invert the logical meaning of a condition code, e.g. `Z <-> NZ`, `LE <-> G` etc.
  #[must_use] pub fn invert(self) -> Self {
    match self {
      CC::O => CC::NO,
      CC::NO => CC::O,
      CC::B => CC::NB,
      CC::NB => CC::B,
      CC::Z => CC::NZ,
      CC::NZ => CC::Z,
      CC::BE => CC::NBE,
      CC::NBE => CC::BE,
      CC::S => CC::NS,
      CC::NS => CC::S,
      // CC::P => CC::NP,
      // CC::NP => CC::P,
      CC::L => CC::NL,
      CC::NL => CC::L,
      CC::LE => CC::NLE,
      CC::NLE => CC::LE,
    }
  }
}

/// Some basic ALU operations.
#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(u8)]
pub enum Binop {
  /// Addition
  Add = 0,
  /// Bitwise OR
  Or = 1,
  /// Addition with carry
  Adc = 2,
  /// Subtract with borrow
  Sbb = 3,
  /// Bitwise AND
  And = 4,
  /// Subtract
  Sub = 5,
  /// Bitwise XOR
  Xor = 6,
}

/// Some basic ALU operations.
#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(u8)]
pub enum Unop {
  /// Increment (add 1)
  Inc = 0,
  /// Decrement (subtract 1)
  Dec = 1,
  /// Bitwise NOT
  Not = 2,
  /// Signed integer negation
  Neg = 3,
}

/// A shift amount, which can be used as an addend in an addressing mode.
#[derive(Clone, Copy, Debug)]
pub struct ShiftIndex<Reg = VReg> {
  /// The reg will be shifted by `2 ^ shift`, where `shift in 0..3`
  pub shift: u8,
  /// The register value to shift
  pub index: Reg,
}

/// A base offset for an addressing mode.
#[derive(Clone, Copy)]
pub enum Offset<N = u32> {
  /// A real offset, relative to zero.
  Real(N),
  /// An offset relative to the given spill slot. `base` must be 0 in this case
  /// because it is pinned to `RSP`.
  Spill(SpillId, N),
  /// An offset into the given global (in the .data / .bss section).
  Global(GlobalId, N),
  /// An offset into the constant pool (the .rodata section).
  Const(N),
}

impl<N: Zero + Debug> Debug for Offset<N> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Real(n) => n.fmt(f),
      Self::Spill(i, n) if n.is_zero() => i.fmt(f),
      Self::Spill(i, n) => write!(f, "{:?} + {:?}", i, n),
      Self::Global(i, n) if n.is_zero() => i.fmt(f),
      Self::Global(i, n) => write!(f, "{:?} + {:?}", i, n),
      Self::Const(n) => write!(f, "const[{:?}]", n),
    }
  }
}

impl<N> From<N> for Offset<N> {
  fn from(n: N) -> Self { Self::Real(n) }
}
impl From<i32> for Offset {
  #[allow(clippy::cast_sign_loss)]
  fn from(n: i32) -> Self { Self::Real(n as u32) }
}

impl Offset {
  pub(crate) const ZERO: Self = Self::Real(0);
}
impl Offset<u64> {
  pub(crate) const ZERO64: Self = Self::Real(0);
}

impl From<Offset> for Offset<u64> {
  fn from(imm: Offset) -> Self {
    match imm {
      Offset::Real(i) => Offset::Real(i.into()),
      Offset::Spill(s, i) => Offset::Spill(s, i.into()),
      Offset::Global(g, i) => Offset::Global(g, i.into()),
      Offset::Const(i) => Offset::Const(i.into()),
    }
  }
}
impl TryFrom<Offset<u64>> for Offset {
  type Error = std::num::TryFromIntError;
  fn try_from(imm: Offset<u64>) -> Result<Self, Self::Error> {
    Ok(match imm {
      Offset::Real(i) => Offset::Real(u32::try_from(i)?),
      Offset::Spill(s, i) => Offset::Spill(s, u32::try_from(i)?),
      Offset::Global(g, i) => Offset::Global(g, u32::try_from(i)?),
      Offset::Const(i) => Offset::Const(u32::try_from(i)?),
    })
  }
}

impl<N: std::ops::Add<Output = N>> std::ops::Add<N> for Offset<N> {
  type Output = Offset<N>;
  fn add(self, n: N) -> Offset<N> {
    match self {
      Offset::Real(i) => Offset::Real(i + n),
      Offset::Spill(s, i) => Offset::Spill(s, i + n),
      Offset::Global(g, i) => Offset::Global(g, i + n),
      Offset::Const(i) => Offset::Const(i + n),
    }
  }
}

/// A trait to factor the commonalities of [`VReg`] and [`PReg`].
pub trait IsReg: Sized + Eq {
  /// A special value of the type representing the invalid value.
  fn invalid() -> Self;
  /// Is this value not the invalid values?
  fn is_valid(&self) -> bool { *self != Self::invalid() }
}
impl IsReg for VReg {
  fn invalid() -> Self { VReg::invalid() }
}
impl IsReg for PReg {
  fn invalid() -> Self { PReg::invalid() }
}

/// A memory address. This has the form `off+base+si`, where `off` is a base memory location
/// (a 32 bit address, or an offset from a stack slot, named global or named constant),
/// `base` is a register or 0, and `si` is a shifted register or 0.
/// Note that `base` must be 0 if `off` is `Spill(..)` because spill slots are RSP-relative,
/// so there is no space for a second register in the encoding.
#[derive(Clone, Copy)]
pub struct AMode<Reg = VReg> {
  /// A constant addend on the address
  pub off: Offset,
  /// `VReg::invalid` means no added register
  pub base: Reg,
  /// Optionally add a shifted register
  pub si: Option<ShiftIndex<Reg>>,
}

impl<Reg: IsReg + Debug> Debug for AMode<Reg> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "[{:?}", self.off)?;
    if self.base.is_valid() {
      write!(f, " + {:?}", self.base)?
    }
    if let Some(si) = &self.si {
      write!(f, " + {}*{:?}", 1 << si.shift, si.index)?
    }
    write!(f, "]")
  }
}

impl<Reg: IsReg> From<Offset> for AMode<Reg> {
  fn from(off: Offset) -> Self { Self { off, base: Reg::invalid(), si: None } }
}

impl<Reg: IsReg> AMode<Reg> {
  pub(crate) fn reg(r: Reg) -> Self { Self { off: Offset::ZERO, base: r, si: None } }
  pub(crate) fn spill(i: SpillId) -> Self { Offset::Spill(i, 0).into() }
  pub(crate) fn global(i: GlobalId) -> Self { Offset::Global(i, 0).into() }
  pub(crate) fn const_(i: u32) -> Self { Offset::Const(i).into() }
}

impl AMode {
  fn collect_operands(&self, args: &mut Vec<Operand>) {
    if self.base != VReg::invalid() { args.push(Operand::reg_use(self.base)) }
    if let Some(si) = &self.si { args.push(Operand::reg_use(si.index)) }
  }

  pub(crate) fn emit_load(&self, code: &mut VCode<Inst>, sz: Size) -> VReg {
    let dst = code.fresh_vreg();
    code.emit(Inst::load_mem(sz, dst, *self));
    dst
  }

  pub(crate) fn add_scaled(&self, code: &mut VCode<Inst>, sc: u64, reg: VReg) -> AMode {
    match (
      &self.si,
      self.base != VReg::invalid() || matches!(self.off, Offset::Spill(..)),
      sc
    ) {
      (_, false, 1) => AMode { off: self.off, base: reg, si: self.si },
      (None, _, 1 | 2 | 4 | 8) => {
        let shift = match sc { 1 => 0, 2 => 1, 4 => 2, 8 => 3, _ => unreachable!() };
        AMode { off: self.off, base: self.base, si: Some(ShiftIndex { shift, index: reg }) }
      }
      (None, false, 3 | 5 | 9) => {
        let shift = match sc { 3 => 1, 5 => 2, 9 => 3, _ => unreachable!() };
        AMode { off: self.off, base: reg, si: Some(ShiftIndex { index: reg, shift }) }
      }
      (Some(_), _, _) => AMode::reg(code.emit_lea(Size::S64, *self)).add_scaled(code, sc, reg),
      (None, _, _) => {
        let sc = code.emit_imm(Size::S64, sc);
        let mul = code.emit_mul(Size::S64, reg, sc).0;
        AMode { off: self.off, base: self.base, si: Some(ShiftIndex { shift: 0, index: mul }) }
      }
    }
  }
}

impl std::ops::Add<u32> for &AMode {
  type Output = AMode;
  fn add(self, n: u32) -> AMode {
    AMode {
      off: self.off + n,
      base: self.base,
      si: self.si
    }
  }
}

/// An operand which is either an integer Register or a value in Memory.  This can denote an 8, 16,
/// 32, 64, or 128 bit value.
#[allow(variant_size_differences)]
#[derive(Copy, Clone)]
pub enum RegMem<Reg = VReg> {
  /// A register
  Reg(Reg),
  /// A reference to a memory address
  Mem(AMode<Reg>),
}

impl<Reg: IsReg + Debug> Debug for RegMem<Reg> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      RegMem::Reg(r) => r.fmt(f),
      RegMem::Mem(a) => a.fmt(f),
    }
  }
}

impl<Reg> From<Reg> for RegMem<Reg> {
  fn from(r: Reg) -> Self { RegMem::Reg(r) }
}
impl<Reg> From<AMode<Reg>> for RegMem<Reg> {
  fn from(a: AMode<Reg>) -> Self { RegMem::Mem(a) }
}

impl RegMem {
  fn collect_operands(&self, args: &mut Vec<Operand>) {
    match *self {
      RegMem::Reg(reg) => args.push(Operand::reg_use(reg)),
      RegMem::Mem(ref addr) => addr.collect_operands(args),
    }
  }

  pub(crate) fn into_reg(self, code: &mut VCode<Inst>, sz: Size) -> VReg {
    match self {
      RegMem::Reg(r) => r,
      RegMem::Mem(a) => a.emit_load(code, sz),
    }
  }

  pub(crate) fn into_mem(self, code: &mut VCode<Inst>, sz: Size) -> AMode {
    match self {
      RegMem::Reg(r) => {
        let a = AMode::spill(code.fresh_spill(sz.bytes().expect("large reg").into()));
        code.emit_copy(sz, a.into(), r);
        a
      },
      RegMem::Mem(a) => a,
    }
  }

  pub(crate) fn emit_deref(&self, code: &mut VCode<Inst>, sz: Size) -> AMode {
    AMode::reg(self.into_reg(code, sz))
  }
}

/// An operand which is either an integer Register, a value in Memory or an Immediate.  This can
/// denote an 8, 16, 32 or 64 bit value.  For the Immediate form, in the 8- and 16-bit case, only
/// the lower 8 or 16 bits of `simm32` is relevant.  In the 64-bit case, the value denoted by
/// `simm32` is its sign-extension out to 64 bits.
#[derive(Copy, Clone)]
pub(crate) enum RegMemImm<N = u32> {
  Reg(VReg),
  Mem(AMode),
  Imm(N),
  Uninit,
}

impl<N: Zero + Debug> Debug for RegMemImm<N> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      RegMemImm::Reg(r) => r.fmt(f),
      RegMemImm::Mem(a) => a.fmt(f),
      RegMemImm::Imm(i) => i.fmt(f),
      RegMemImm::Uninit => "uninit".fmt(f),
    }
  }
}

impl<N> From<VReg> for RegMemImm<N> {
  fn from(r: VReg) -> Self { RegMemImm::Reg(r) }
}
impl<N> From<AMode> for RegMemImm<N> {
  fn from(a: AMode) -> Self { RegMemImm::Mem(a) }
}
impl<N> From<RegMem> for RegMemImm<N> {
  fn from(rm: RegMem) -> Self {
    match rm {
      RegMem::Reg(r) => RegMemImm::Reg(r),
      RegMem::Mem(a) => RegMemImm::Mem(a),
    }
  }
}
impl From<RegMemImm> for RegMemImm<u64> {
  fn from(rmi: RegMemImm) -> Self {
    match rmi {
      RegMemImm::Reg(r) => RegMemImm::Reg(r),
      RegMemImm::Mem(a) => RegMemImm::Mem(a),
      RegMemImm::Imm(i) => RegMemImm::Imm(i.into()),
      RegMemImm::Uninit => RegMemImm::Uninit,
    }
  }
}
impl From<u32> for RegMemImm {
  fn from(i: u32) -> Self { RegMemImm::Imm(i) }
}
impl From<u64> for RegMemImm<u64> {
  fn from(i: u64) -> Self { RegMemImm::Imm(i) }
}

impl<N> RegMemImm<N> {
  fn collect_operands(&self, args: &mut Vec<Operand>) {
    match *self {
      RegMemImm::Reg(reg) => args.push(Operand::reg_use(reg)),
      RegMemImm::Mem(ref addr) => addr.collect_operands(args),
      RegMemImm::Imm(_) |
      RegMemImm::Uninit => {}
    }
  }

  pub(crate) fn into_rm(self, code: &mut VCode<Inst>, sz: Size) -> RegMem
  where N: Into<u64> {
    match self {
      RegMemImm::Reg(r) => RegMem::Reg(r),
      RegMemImm::Mem(a) => RegMem::Mem(a),
      RegMemImm::Imm(i) => RegMem::Reg(code.emit_imm(sz, i)),
      RegMemImm::Uninit => RegMem::Reg(code.fresh_vreg()),
    }
  }

  pub(crate) fn into_reg(self, code: &mut VCode<Inst>, sz: Size) -> VReg
  where N: Into<u64> {
    match self {
      RegMemImm::Reg(r) => r,
      RegMemImm::Mem(a) => a.emit_load(code, sz),
      RegMemImm::Imm(i) => code.emit_imm(sz, i),
      RegMemImm::Uninit => code.fresh_vreg(),
    }
  }

  pub(crate) fn into_mem(self, code: &mut VCode<Inst>, sz: Size) -> AMode
  where N: Into<u64> {
    self.into_rm(code, sz).into_mem(code, sz)
  }
}

impl RegMemImm<u64> {
  pub(crate) fn into_rmi_32(self, code: &mut VCode<Inst>) -> RegMemImm {
    match self {
      RegMemImm::Reg(r) => RegMemImm::Reg(r),
      RegMemImm::Mem(a) => RegMemImm::Mem(a),
      RegMemImm::Imm(i) => match u32::try_from(i) {
        Ok(i) => RegMemImm::Imm(i),
        _ => RegMemImm::Reg(code.emit_imm(Size::S64, i))
      }
      RegMemImm::Uninit => RegMemImm::Uninit,
    }
  }
}

/// The available set of kernel calls that can be made through the `syscall` instruction.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub(crate) enum SysCall {
  /// `fd <- open(filename, flags, 0)`. `flags` must be one of:
  /// * `O_RDONLY = 0`
  /// * `O_WRONLY + O_CREAT + O_TRUNC = 1 + 1<<6 + 1<<9 = 577`
  Open = 2,
  /// `nread <- read(fd, buf, count)`.
  Read = 0,
  /// `nwrite <- write(fd, buf, count)`.
  Write = 1,
  /// `err <- fstat(fd, statbuf)`.
  FStat = 5,
  /// `p <- mmap(0, len, prot, flags, fd, 0)`.
  /// * If `fd == u32::MAX` then `flags = MAP_PRIVATE + MAP_ANONYMOUS = 2 + 32 = 34`
  /// * If `fd != u32::MAX` then `flags = MAP_PRIVATE = 2`
  MMap = 9,
  /// `! <- exit(exit_code)`.
  Exit = 0x3c,
}

impl SysCall {
  #[inline] pub(crate) fn returns(self) -> bool { self != Self::Exit }
}

#[derive(Debug)]
pub(crate) enum Inst {
  // /// A length 0 no-op instruction.
  // Nop,
  /// Jump to the given block ID. This is required to be the immediately following instruction,
  /// so no code need be emitted.
  Fallthrough { dst: BlockId },
  /// Integer arithmetic/bit-twiddling: `reg <- (add|sub|and|or|xor|adc|sbb) (32|64) reg rmi`
  Binop {
    op: Binop,
    sz: Size, // 4 or 8
    dst: VReg, // dst = src1
    src1: VReg,
    src2: RegMemImm,
  },
  /// Unary ALU operations: `reg <- (not|neg) (8|16|32|64) reg`
  Unop {
    op: Unop,
    sz: Size, // 1, 2, 4 or 8
    dst: VReg, // dst = src
    src: VReg,
  },
  /// Unsigned integer quotient and remainder pseudo-operation:
  // `RDX:RAX <- cdq RAX`
  // `RAX,RDX <- divrem RDX:RAX r/m.`
  DivRem {
    sz: Size, // 2, 4 or 8
    dst_div: VReg, // = RAX
    dst_rem: VReg, // = RDX
    src1: VReg, // = RAX
    src2: RegMem,
  },
  /// Unsigned integer quotient and remainder pseudo-operation:
  // `RDX:RAX <- cdq RAX`
  // `RAX,RDX <- divrem RDX:RAX r/m`.
  Mul {
    sz: Size, // 2, 4 or 8
    dst_lo: VReg, // = RAX
    dst_hi: VReg, // = RDX
    src1: VReg, // = RAX
    src2: RegMem,
  },
  // /// The high bits (RDX) of a (un)signed multiply: RDX:RAX := RAX * rhs.
  // MulHi {
  //   sz: Size, // 2, 4, or 8
  //   signed: bool,
  //   rhs: RegMem,
  // },
  // /// Do a sign-extend based on the sign of the value in rax into rdx: (cwd cdq cqo)
  // /// or al into ah: (cbw)
  // SignExtendData {
  //   sz: Size, // 1, 2, 4 or 8
  //   dst: VReg, // dst = RDX
  //   src: VReg, // src = RAX
  // },
  /// Constant materialization: `reg <- (imm32|imm64)`.
  /// Either: movl $imm32, %reg32 or movabsq $imm64, %reg32.
  Imm {
    sz: Size, // 4 or 8
    dst: VReg,
    src: u64,
  },
  /// GPR to GPR move: `reg <- mov (64|32) reg`. This is always a pure move,
  /// because we require that a 32 bit source register has zeroed high part.
  MovRR {
    sz: Size, // 4 or 8
    dst: VReg,
    src: VReg,
  },
  /// Move into a fixed reg: `preg <- mov (64|32) reg`.
  MovRP {
    sz: Size, // 4 or 8
    dst: (VReg, PReg),
    src: VReg,
  },
  /// Move from a fixed reg: `reg <- mov (64|32) preg`.
  MovPR {
    sz: Size, // 4 or 8
    dst: VReg,
    src: (VReg, PReg),
  },
  /// Zero-extended loads, except for 64 bits: `reg <- movz (bl|bq|wl|wq|lq) r/m`.
  /// Note that the lq variant doesn't really exist since the default zero-extend rule makes it
  /// unnecessary. For that case we emit the equivalent "movl AM, reg32".
  MovzxRmR {
    ext_mode: ExtMode,
    dst: VReg,
    src: RegMem,
  },
  /// A plain 64-bit integer load, since `MovzxRmR` can't represent that.
  Load64 {
    dst: VReg,
    src: AMode,
  },
  /// Load effective address: `dst <- addr`
  Lea {
    sz: Size, // 4 or 8
    dst: VReg,
    addr: AMode,
  },
  /// Sign-extended loads and moves: `reg <- movs (bl|bq|wl|wq|lq) [addr]`.
  MovsxRmR {
    ext_mode: ExtMode,
    dst: VReg,
    src: RegMem,
  },
  /// Integer stores: `[addr] <- mov (b|w|l|q) reg`.
  Store {
    sz: Size, // 1, 2, 4 or 8.
    dst: AMode,
    src: VReg,
  },
  /// Arithmetic shifts: `reg <- (shl|shr|sar) (b|w|l|q) reg, imm`.
  ShiftImm {
    sz: Size, // 1, 2, 4 or 8
    kind: ShiftKind,
    /// shift count: 0 .. #bits-in-type - 1
    num_bits: u8,
    dst: VReg, // dst = src
    src: VReg,
  },
  /// Arithmetic shifts: `reg <- (shl|shr|sar) (b|w|l|q) reg, CL`.
  ShiftRR {
    sz: Size, // 1, 2, 4 or 8
    kind: ShiftKind,
    dst: VReg, // dst = src
    src: VReg,
    src2: VReg, // src2 = CL
  },
  /// Integer comparisons/tests: `flags <- (cmp|test) (b|w|l|q) reg rmi`.
  Cmp {
    sz: Size, // 1, 2, 4 or 8
    op: Cmp,
    src1: VReg,
    src2: RegMemImm,
  },
  /// Materializes the requested condition code in the destination reg.
  /// `dst <- if cc { 1 } else { 0 }`
  SetCC { cc: CC, dst: VReg },
  /// Integer conditional move.
  /// Overwrites the destination register.
  CMov {
    sz: Size, // 2, 4, or 8
    cc: CC,
    dst: VReg, // dst = src1
    src1: VReg,
    src2: RegMem,
  },
  /// `pushq rmi`
  Push64 { src: RegMemImm },
  /// `popq reg`
  Pop64 { dst: VReg },
  /// Direct call: `call f`.
  CallKnown {
    f: ProcId,
    operands: Box<[Operand]>,
    /// If `clobbers = None` then this call does not return.
    clobbers: Option<Box<[PReg]>>,
  },
  // /// Indirect call: `callq r/m`.
  // CallUnknown {
  //   dest: RegMem,
  //   uses: Vec<VReg>,
  //   defs: Vec<VReg>,
  //   opcode: Opcode,
  // },
  /// Call to the operating system: `syscall`.
  SysCall {
    f: SysCall,
    operands: Box<[Operand]>,
  },
  /// Function epilogue placeholder.
  Epilogue { params: Box<[Operand]> },
  /// Jump to a known target: `jmp simm32`.
  /// The params are block parameters; they are turned into movs after register allocation.
  JmpKnown { dst: BlockId, params: Box<[Operand]> },
  /// Two-way conditional branch: `if cc { jmp taken } else { jmp not_taken }`.
  JmpCond {
    cc: CC,
    taken: BlockId,
    not_taken: BlockId,
  },
  // /// Indirect jump: `jmpq r/m`.
  // JmpUnknown { target: RegMem },
  /// Traps if the condition code is not set.
  Assert { cc: CC },
  /// An instruction that will always trigger the illegal instruction exception.
  Ud2,
}

impl VInst for Inst {
  fn is_call(&self) -> bool {
    matches!(self, Inst::CallKnown {..} | Inst::SysCall {..})
  }

  fn is_ret(&self) -> bool {
    matches!(self, Inst::Epilogue {..} | Inst::SysCall { f: SysCall::Exit, .. })
  }

  fn is_branch(&self) -> bool {
    matches!(self, Inst::JmpCond {..} | Inst::JmpKnown {..})
  }

  fn branch_blockparam_arg_offset(&self) -> usize { 0 }

  fn is_move(&self) -> Option<(Operand, Operand)> {
    match *self {
      Inst::MovRR { dst, src, .. } => Some((Operand::reg_use(src), Operand::reg_def(dst))),
      Inst::MovRP { dst, src, .. } =>
        Some((Operand::reg_use(src), Operand::reg_fixed_def(dst.0, dst.1))),
      Inst::MovPR { dst, src, .. } =>
        Some((Operand::reg_fixed_use(src.0, src.1), Operand::reg_def(dst))),
      _ => None
    }
  }

  fn collect_operands(&self, args: &mut Vec<Operand>) {
    match *self {
      Inst::Imm { dst, .. } |
      Inst::SetCC { dst, .. } |
      Inst::Pop64 { dst } => args.push(Operand::reg_def(dst)),
      Inst::Unop { dst, src, .. } |
      Inst::ShiftImm { dst, src, .. } => {
        args.push(Operand::reg_use(src));
        args.push(Operand::reg_reuse_def(dst, 0));
      }
      Inst::Binop { dst, src1, ref src2, .. } => {
        args.push(Operand::reg_use(src1));
        src2.collect_operands(args);
        args.push(Operand::reg_reuse_def(dst, 0));
      }
      Inst::Mul { sz, dst_lo, dst_hi, src1, ref src2 } => {
        args.push(Operand::reg_fixed_use(src1, RAX));
        src2.collect_operands(args);
        args.push(Operand::reg_fixed_def(dst_lo, RAX));
        args.push(Operand::reg_fixed_def(dst_hi, RDX));
      },
      Inst::DivRem { sz, dst_div, dst_rem, src1, ref src2 } => {
        args.push(Operand::reg_fixed_use(src1, RAX));
        src2.collect_operands(args);
        args.push(Operand::reg_fixed_def(dst_div, RAX));
        args.push(Operand::reg_fixed_def(dst_rem, RDX));
      },
      // Inst::SignExtendData { sz, dst, src } => todo!(),
      Inst::MovzxRmR { dst, ref src, .. } |
      Inst::MovsxRmR { dst, ref src, .. } => {
        src.collect_operands(args);
        args.push(Operand::reg_def(dst));
      }
      Inst::Load64 { dst, ref src } => {
        src.collect_operands(args);
        args.push(Operand::reg_def(dst));
      }
      Inst::Lea { dst, ref addr, .. } => {
        addr.collect_operands(args);
        args.push(Operand::reg_def(dst));
      }
      Inst::Store { ref dst, src, .. } => {
        args.push(Operand::reg_use(src));
        dst.collect_operands(args);
      }
      Inst::ShiftRR { dst, src, src2, .. } => {
        args.push(Operand::reg_use(src));
        args.push(Operand::reg_fixed_use(src2, RCX));
        args.push(Operand::reg_reuse_def(dst, 0));
      }
      Inst::Cmp { src1, ref src2, .. } => {
        args.push(Operand::reg_use(src1));
        src2.collect_operands(args);
      }
      Inst::CMov { dst, src1, ref src2, .. } => {
        args.push(Operand::reg_use(src1));
        src2.collect_operands(args);
        args.push(Operand::reg_reuse_def(dst, 0));
      }
      Inst::Push64 { ref src } => src.collect_operands(args),
      Inst::CallKnown { operands: ref params, .. } |
      Inst::SysCall { operands: ref params, .. } |
      Inst::JmpKnown { ref params, .. } |
      Inst::Epilogue { ref params } => args.extend_from_slice(params),
      // Inst::JmpUnknown { target } => target.collect_operands(args),
      // moves are handled specially by regalloc, we don't need operands
      Inst::MovRR { .. } | Inst::MovPR { .. } | Inst::MovRP { .. } |
      // Other instructions that have no operands
      Inst::Fallthrough { .. } |
      Inst::JmpCond { .. } |
      Inst::Assert { .. } |
      Inst::Ud2 => {}
    }
  }

  fn clobbers(&self) -> &[PReg] {
    match self {
      Inst::CallKnown { clobbers: Some(cl), .. } => cl,
      Inst::SysCall { f, .. } if f.returns() => &[RCX, R11],
      _ => &[],
    }
  }
}

impl Inst {
  pub(crate) fn load_mem(sz: Size, dst: VReg, src: AMode) -> Inst {
    match sz {
      Size::S8 => Inst::MovzxRmR { ext_mode: ExtMode::BQ, dst, src: RegMem::Mem(src) },
      Size::S16 => Inst::MovzxRmR { ext_mode: ExtMode::WQ, dst, src: RegMem::Mem(src) },
      Size::S32 => Inst::MovzxRmR { ext_mode: ExtMode::LQ, dst, src: RegMem::Mem(src) },
      Size::S64 => Inst::Load64 { dst, src },
      Size::Inf => panic!(),
    }
  }
}

#[must_use]
pub(crate) struct Flags<'a>(&'a mut VCode<Inst>, CC);

impl Flags<'_> {
  pub(crate) fn into_reg(self) -> VReg {
    let dst = self.0.fresh_vreg();
    self.0.emit(Inst::SetCC { cc: self.1, dst });
    dst
  }

  pub(crate) fn select(self, sz: Size, tru: impl Into<RegMem>, fal: VReg) -> VReg {
    let dst = self.0.fresh_vreg();
    self.0.emit(Inst::CMov { sz, cc: self.1, dst, src1: fal, src2: tru.into() });
    dst
  }

  pub(crate) fn assert(self) -> InstId {
    self.0.emit(Inst::Assert { cc: self.1 })
  }

  pub(crate) fn branch(self, tru: BlockId, fal: BlockId) -> InstId {
    self.0.emit(Inst::JmpCond { cc: self.1, taken: tru, not_taken: fal })
  }
}

impl VCode<Inst> {
  pub(crate) fn emit_lea(&mut self, sz: Size, addr: AMode) -> VReg {
    let dst = self.fresh_vreg();
    self.emit(Inst::Lea { sz, dst, addr });
    dst
  }

  pub(crate) fn emit_binop(&mut self, sz: Size, op: Binop, src1: VReg, src2: impl Into<RegMemImm>
  ) -> VReg {
    let dst = self.fresh_vreg();
    self.emit(Inst::Binop { sz, op, dst, src1, src2: src2.into() });
    dst
  }

  pub(crate) fn emit_unop(&mut self, sz: Size, op: Unop, src: VReg) -> VReg {
    let dst = self.fresh_vreg();
    self.emit(Inst::Unop { sz, op, dst, src });
    dst
  }

  pub(crate) fn emit_imm(&mut self, sz: Size, src: impl Into<u64>) -> VReg {
    let dst = self.fresh_vreg();
    self.emit(Inst::Imm { sz, dst, src: src.into() });
    dst
  }

  pub(crate) fn emit_mul(&mut self, sz: Size, src1: VReg, src2: impl Into<RegMem>) -> (VReg, VReg) {
    let dst_lo = self.fresh_vreg();
    let dst_hi = self.fresh_vreg();
    self.emit(Inst::Mul { sz, dst_lo, dst_hi, src1, src2: src2.into() });
    (dst_lo, dst_hi)
  }

  pub(crate) fn emit_shift(&mut self, sz: Size, kind: ShiftKind, src1: VReg, src2: Result<u8, VReg>
  ) -> VReg {
    let dst = self.fresh_vreg();
    self.emit(match src2 {
      Ok(num_bits) => Inst::ShiftImm { sz, kind, dst, src: src1, num_bits },
      Err(src2) => Inst::ShiftRR { sz, kind, dst, src: src1, src2 },
    });
    dst
  }

  pub(crate) fn emit_cmp(&mut self, sz: Size, op: Cmp, cc: CC, src1: VReg, src2: impl Into<RegMemImm>
  ) -> Flags<'_> {
    self.emit(Inst::Cmp { sz, op, src1, src2: src2.into() });
    Flags(self, cc)
  }

  #[inline] pub(crate) fn emit_copy(&mut self, sz: Size, dst: RegMem, src: impl Into<RegMemImm<u64>>) {
    fn copy(code: &mut VCode<Inst>, sz: Size, dst: RegMem, src: RegMemImm<u64>) {
      match (dst, src) {
        (_, RegMemImm::Uninit) => {}
        (RegMem::Reg(dst), RegMemImm::Reg(src)) => { code.emit(Inst::MovRR { sz, dst, src }); }
        (RegMem::Reg(dst), RegMemImm::Mem(src)) => { code.emit(Inst::load_mem(sz, dst, src)); }
        (RegMem::Reg(dst), RegMemImm::Imm(src)) => {
          code.emit(Inst::Imm { sz: sz.max(Size::S32), dst, src });
        }
        (RegMem::Mem(dst), RegMemImm::Reg(src)) => { code.emit(Inst::Store { sz, dst, src }); }
        _ => {
          let temp = code.fresh_vreg();
          copy(code, sz, temp.into(), src);
          copy(code, sz, dst, temp.into());
        }
      }
    }
    copy(self, sz, dst, src.into())
  }
}

/// A version of `ShiftIndex` post-register allocation.
pub(crate) type PShiftIndex = ShiftIndex<PReg>;

/// A version of `AMode` post-register allocation.
/// [`Offset::Spill`] is not permitted in a physical address.
pub(crate) type PAMode = AMode<PReg>;

/// A version of `RegMem` post-register allocation.
pub(crate) type PRegMem = RegMem<PReg>;

impl PAMode {
  pub(crate) fn base(&self) -> PReg {
    if let Offset::Spill(..) = self.off { RSP } else { self.base }
  }
}

/// A version of `RegMemImm` post-register allocation.
#[derive(Copy, Clone)]
#[allow(variant_size_differences)]
pub enum PRegMemImm {
  /// A register.
  Reg(PReg),
  /// A value stored at the given address.
  Mem(PAMode),
  /// An immediate (a constant value). This is usually sign extended,
  /// even though it is stored as `u32`.
  Imm(u32),
}

impl Debug for PRegMemImm {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      PRegMemImm::Reg(r) => r.fmt(f),
      PRegMemImm::Mem(a) => a.fmt(f),
      PRegMemImm::Imm(i) => i.fmt(f),
    }
  }
}

/// A representation of x86 assembly instructions.
#[derive(Clone, Copy, Debug)]
#[allow(missing_docs)]
pub enum PInst {
  // /// A length 0 no-op instruction.
  // Nop,
  /// Integer arithmetic/bit-twiddling: `reg <- (add|sub|and|or|xor|adc|sbb) (32|64) reg rmi`
  Binop {
    op: Binop,
    sz: Size, // 1, 2, 4 or 8
    dst: PReg,
    src: PRegMemImm,
  },
  /// Unary ALU operations: `reg <- (not|neg) (8|16|32|64) reg`
  Unop {
    op: Unop,
    sz: Size, // 1, 2, 4 or 8
    dst: PReg,
  },
  /// Unsigned integer double wide multiplication.
  // `RDX:RAX <- RAX * r/m`
  Mul {
    sz: Size, // 2, 4 or 8
    src: PRegMem,
  },
  /// Part of `DivRem` pseudo-operation. `RDX:RAX <- cdq RAX`
  Cdx {
    sz: Size, // 2, 4 or 8
  },
  /// Unsigned integer quotient and remainder operation: `RAX,RDX <- divrem RDX:RAX r/m.`
  DivRem {
    sz: Size, // 2, 4 or 8
    src: PRegMem,
  },
  // /// The high bits (RDX) of a (un)signed multiply: RDX:RAX := RAX * rhs.
  // MulHi {
  //   sz: Size, // 2, 4, or 8
  //   signed: bool,
  //   rhs: RegMem,
  // },
  // /// Do a sign-extend based on the sign of the value in rax into rdx: (cwd cdq cqo)
  // /// or al into ah: (cbw)
  // SignExtendData {
  //   sz: Size, // 1, 2, 4 or 8
  //   dst: PReg, // dst = RDX
  //   src: PReg, // src = RAX
  // },
  /// Constant materialization: `reg <- (imm32|imm64)`.
  /// Either: movl $imm32, %reg32 or movabsq $imm64, %reg32.
  Imm {
    sz: Size, // 4 or 8
    dst: PReg,
    src: u64,
  },
  /// GPR to GPR move: `reg <- mov (64|32) reg`. This is always a pure move,
  /// because we require that a 32 bit source register has zeroed high part.
  MovRR {
    sz: Size, // 4 or 8
    dst: PReg,
    src: PReg,
  },
  /// Zero-extended loads, except for 64 bits: `reg <- movz (bl|bq|wl|wq|lq) r/m`.
  /// Note that the lq variant doesn't really exist since the default zero-extend rule makes it
  /// unnecessary. For that case we emit the equivalent "movl AM, reg32".
  MovzxRmR {
    ext_mode: ExtMode,
    dst: PReg,
    src: PRegMem,
  },
  /// A plain 64-bit integer load, since `MovzxRmR` can't represent that.
  Load64 {
    dst: PReg,
    src: PAMode,
  },
  /// Load effective address: `dst <- addr`
  Lea {
    sz: Size, // 4 or 8
    dst: PReg,
    addr: PAMode,
  },
  /// Sign-extended loads and moves: `reg <- movs (bl|bq|wl|wq|lq) [addr]`.
  MovsxRmR {
    ext_mode: ExtMode,
    dst: PReg,
    src: PRegMem,
  },
  /// Integer stores: `[addr] <- mov (b|w|l|q) reg`.
  Store {
    sz: Size, // 1, 2, 4 or 8.
    dst: PAMode,
    src: PReg,
  },
  /// Arithmetic shifts: `reg <- (shl|shr|sar) (b|w|l|q) reg, imm/CL`.
  Shift {
    kind: ShiftKind,
    sz: Size, // 1, 2, 4 or 8
    dst: PReg,
    /// shift count: Some(0 .. #bits-in-type - 1), or None = CL
    num_bits: Option<u8>,
  },
  /// Integer comparisons/tests: `flags <- (cmp|test) (b|w|l|q) reg rmi`.
  Cmp {
    sz: Size, // 1, 2, 4 or 8
    op: Cmp,
    src1: PReg,
    src2: PRegMemImm,
  },
  /// Materializes the requested condition code in the destination reg.
  /// `dst <- if cc { 1 } else { 0 }`
  SetCC { cc: CC, dst: PReg },
  /// Integer conditional move.
  /// Overwrites the destination register.
  CMov {
    sz: Size, // 2, 4, or 8
    cc: CC,
    dst: PReg,
    src: PRegMem,
  },
  /// `pushq rmi`
  Push64 { src: PRegMemImm },
  /// `popq reg`
  Pop64 { dst: PReg },
  /// Direct call: `call f`.
  CallKnown { f: ProcId },
  // /// Indirect call: `callq r/m`.
  // CallUnknown {
  //   dest: PRegMem,
  //   uses: Vec<PReg>,
  //   defs: Vec<PReg>,
  //   opcode: Opcode,
  // },
  /// Call to the operating system: `syscall`.
  SysCall,
  /// Return.
  Ret,
  /// Jump to a known target: `jmp simm32`.
  /// The params are block parameters; they are turned into movs after register allocation.
  JmpKnown {
    dst: BlockId,
    /// True if we know that the branch can be encoded by a `RIP + i8` relative jump
    short: bool,
  },
  /// Conditional jump: `if cc { jmp dst }`.
  JmpCond {
    cc: CC,
    dst: BlockId,
    /// True if we know that the branch can be encoded by a `RIP + i8` relative jump
    short: bool,
  },
  // /// Indirect jump: `jmpq r/m`.
  // JmpUnknown { target: PRegMem },
  /// Traps if the condition code is not set.
  Assert { cc: CC },
  /// An instruction that will always trigger the illegal instruction exception.
  Ud2,
}

/// The layout of a displacement, used in [`ModRMLayout`].
#[derive(Clone, Copy, Debug)]
#[repr(u8)]
pub enum DispLayout {
  /// 0 byte immediate, `mm = 00`
  S0 = 0,
  /// 1 byte immediate, `mm = 01`
  S8 = 1,
  /// 4 byte immediate, `mm = 10`
  S32 = 2,
}

impl DispLayout {
  /// The length of the displacement value in bytes.
  #[allow(clippy::len_without_is_empty)]
  #[must_use] pub fn len(self) -> u8 {
    match self {
      Self::S0 => 0,
      Self::S8 => 1,
      Self::S32 => 4,
    }
  }
}

/// Layout of the Mod/RM and SIB bytes.
#[derive(Clone, Copy, Debug)]
#[allow(clippy::upper_case_acronyms)]
pub enum ModRMLayout {
  /// `11ooonnn` where `rn = o` and `rm = reg(n)`
  Reg,
  /// `00ooo101 + imm32` where `rn = o` and `rm = [RIP + imm32]`
  #[allow(unused)] RIP,
  /// `00ooo100 + ssiii101 + imm32` where `rn = o` and `rm = [0 + sc*ix + imm32]`
  Sib0,
  /// `mmooo100 + ssiiibbb + disp0/8/32` where `rn = o` and `rm = [reg(b) + sc*ix + disp]`
  SibReg(DispLayout),
  /// `mmooonnn + disp0/8/32` where `rn = o` and `rm = [reg(n) + disp]`
  Disp(DispLayout),
}

impl ModRMLayout {
  /// The length of the Mod/RM byte and everything after it.
  #[allow(clippy::len_without_is_empty)]
  #[must_use] pub fn len(self) -> u8 {
    match self {
      Self::Reg => 1, // ModRM
      Self::RIP => 5, // ModRM + imm32
      Self::Sib0 => 6, // ModRM + SIB + imm32
      Self::SibReg(disp) => 2 + disp.len(), // ModRM + SIB + disp0/8/32
      Self::Disp(disp) => 1 + disp.len(), // ModRM + disp0/8/32
    }
  }
}

/// The layout of the opcode byte and everything after it.
#[derive(Clone, Copy, Debug)]
pub enum OpcodeLayout {
  /// `decodeBinopRAX` layout: `00ooo01v + imm8/32`
  BinopRAX(bool),
  /// `decodeBinopImm` layout: `1000000v + modrm + imm8/32`
  BinopImm(bool, ModRMLayout),
  /// `decodeBinopImm8` layout: `0x83 + modrm + imm8`
  BinopImm8(ModRMLayout),
  /// `decodeBinopReg` layout: `00ooo0dv + modrm`
  BinopReg(ModRMLayout),
  /// `decodeBinopHi` layout: `1100000v + modrm + imm8`
  BinopHi(ModRMLayout),
  /// `decodeBinopHiReg` layout with immediate 1: `1101000v + modrm`
  BinopHi1(ModRMLayout),
  /// `decodeBinopHiReg` layout: `1101001v + modrm`
  BinopHiReg(ModRMLayout),
  /// `decodeMovSX` layout: `0x63 + modrm`
  MovSX(ModRMLayout),
  /// `decodeMovReg` layout: `100010dv + modrm`
  MovReg(ModRMLayout),
  /// `decodeMov64` layout, but for 32 bit: `1011vrrr + imm32`
  Mov32,
  /// `decodeMov64` layout: `1011vrrr + imm64`
  Mov64,
  /// `decodeMovImm` layout: `1100011v + modrm + imm32`
  MovImm(ModRMLayout),
  /// `decodePushImm` layout: `011010x0 + imm8/32`
  PushImm(bool),
  /// `decodePushReg` layout: `01010rrr`
  PushReg,
  /// `decodePopReg` layout: `01011rrr`
  PopReg,
  /// `decodeJump` layout: `111010x1 + imm8/32`
  Jump(bool),
  /// `decodeJCC8` layout: `0111cccc + imm8`
  Jcc8,
  /// `decodeCall` layout: `0xE8 + imm32`
  Call,
  /// `decodeRet` layout: `0xC3`
  Ret,
  /// `decodeCdx` layout: `0x99`
  Cdx,
  /// `decodeLea` layout: `0x8D + modrm`
  Lea(ModRMLayout),
  /// `decodeTest` layout: `1000010v + modrm`
  Test(ModRMLayout),
  /// `decodeTestRAX` layout: `1010100v + imm8/32`
  TestRAX(bool),
  /// `decodeHi` layout: `1111x11v + modrm`
  Hi(ModRMLayout),
  /// `decodeHi` layout for `Test`: `1111x11v + modrm + imm8/32`
  HiTest(bool, ModRMLayout),
  /// `decodeTwoSetCC` layout: `0x0F + 1001cccc + modrm`
  SetCC(ModRMLayout),
  /// `decodeTwoCMov` layout: `0x0F + 0100cccc + modrm`
  CMov(ModRMLayout),
  /// `decodeTwoMovX` layout: `0x0F + 1011s11v + modrm`
  MovX(ModRMLayout),
  /// `decodeTwoJCC` layout: `0x0F + 1000cccc + imm32`
  Jcc,
  /// `decodeTwoSysCall` layout: `0x0F 0x05`
  SysCall,
  /// `assert` pseudo-instruction: `jcc cond l; ud2; l:`
  Assert,
  /// `ud2` instruction: `0x0F 0x0B`
  Ud2,
}

impl OpcodeLayout {
  /// The length of the opcode byte and everything after it.
  #[allow(clippy::len_without_is_empty)]
  #[must_use] pub fn len(self) -> u8 {
    #[inline] fn sz32(sz32: bool) -> u8 { if sz32 { 4 } else { 1 } }
    match self {
      Self::Ret | Self::Cdx | Self::PushReg | Self::PopReg => 1, // opcode
      Self::BinopRAX(b) | Self::PushImm(b) |
      Self::Jump(b) | Self::TestRAX(b) => 1 + sz32(b), // opcode + imm8/32
      Self::Jcc8 | // opcode + imm8
      Self::Ud2 | Self::SysCall => 2, // 0F + opcode
      Self::Assert => 4, // jcc8 + ud2
      Self::Mov32 | Self::Call => 5, // opcode + imm32
      Self::Jcc => 6, // 0F + opcode + imm32
      Self::Mov64 => 9, // opcode + imm64
      Self::BinopReg(modrm) | Self::BinopHi1(modrm) | Self::BinopHiReg(modrm) |
      Self::MovSX(modrm) | Self::MovReg(modrm) |
      Self::Lea(modrm) | Self::Test(modrm) |
      Self::Hi(modrm) => 1 + modrm.len(), // opcode + modrm
      Self::BinopImm(b, modrm) |
      Self::HiTest(b, modrm) => 1 + sz32(b) + modrm.len(), // opcode + modrm + imm8/32
      Self::BinopImm8(modrm) | Self::BinopHi(modrm) | // opcode + modrm + imm8
      Self::SetCC(modrm) | Self::CMov(modrm) |
      Self::MovX(modrm) => 2 + modrm.len(), // 0F + opcode + modrm
      Self::MovImm(modrm) => 5 + modrm.len(), // opcode + modrm + imm32
    }
  }
}

/// The layout of an instruction, which is a broad categorization of
/// which of several encodings it falls into, including in particular
/// enough information to determine the byte length of the instruction.
#[derive(Clone, Copy)]
pub struct InstLayout {
  /// Does the instruction have a REX byte?
  pub rex: bool,
  /// The layout of the instruction itself.
  pub opc: OpcodeLayout,
}

impl Debug for InstLayout {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.rex { write!(f, "REX + {:?}", self.opc) } else { self.opc.fmt(f) }
  }
}

impl InstLayout {
  /// The byte length of any instruction with this layout.
  #[allow(clippy::len_without_is_empty)]
  #[must_use] pub fn len(self) -> u8 { self.rex as u8 + self.opc.len() }
}

#[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
fn layout_u32(n: u32) -> DispLayout {
  match n {
    0 => DispLayout::S0,
    _ if n as i8 as u32 == n => DispLayout::S8,
    _ => DispLayout::S32,
  }
}

fn layout_offset(off: &Offset) -> DispLayout {
  match *off {
    Offset::Real(n) => layout_u32(n),
    Offset::Spill(sp, off) => unreachable!(),
    _ => DispLayout::S32,
  }
}

fn layout_opc_reg(rex: &mut bool, rm: PReg) -> ModRMLayout {
  *rex |= large_preg(rm);
  ModRMLayout::Reg
}

fn layout_opc_mem(rex: &mut bool, a: &PAMode) -> ModRMLayout {
  if a.base.is_valid() { *rex |= large_preg(a.base) }
  if let Some(si) = a.si { *rex |= large_preg(si.index) }
  match a {
    _ if !a.base().is_valid() => ModRMLayout::Sib0,
    PAMode {off, si: None, ..} if a.base().hw_enc() & 7 != 4 =>
      ModRMLayout::Disp(layout_offset(off)),
    PAMode {off, base, ..} => match (*base, layout_offset(off)) {
      (RBP, DispLayout::S0) => ModRMLayout::SibReg(DispLayout::S8),
      (_, layout) => ModRMLayout::SibReg(layout)
    }
  }
}

fn layout_opc_rm(rex: &mut bool, rm: &PRegMem) -> ModRMLayout {
  match rm {
    PRegMem::Reg(r) => layout_opc_reg(rex, *r),
    PRegMem::Mem(a) => layout_opc_mem(rex, a),
  }
}

fn layout_opc_rmi(rex: &mut bool, rm: &PRegMemImm) -> ModRMLayout {
  match rm {
    PRegMemImm::Reg(r) => layout_opc_reg(rex, *r),
    PRegMemImm::Mem(a) => layout_opc_mem(rex, a),
    PRegMemImm::Imm(_) => unreachable!(),
  }
}

fn layout_reg(rex: &mut bool, r: PReg, rm: PReg) -> ModRMLayout {
  *rex |= large_preg(r);
  layout_opc_reg(rex, rm)
}

fn layout_mem(rex: &mut bool, r: PReg, a: &PAMode) -> ModRMLayout {
  *rex |= large_preg(r);
  layout_opc_mem(rex, a)
}

fn layout_rm(rex: &mut bool, r: PReg, rm: &PRegMem) -> ModRMLayout {
  *rex |= large_preg(r);
  layout_opc_rm(rex, rm)
}

fn layout_rmi(rex: &mut bool, r: PReg, rm: &PRegMemImm) -> ModRMLayout {
  *rex |= large_preg(r);
  layout_opc_rmi(rex, rm)
}

fn high_reg(rex: &mut bool, r: PReg) { *rex |= r.index() & 4 != 0 }

fn high_amode(rex: &mut bool, a: &PAMode) {
  if a.base.is_valid() { high_reg(rex, a.base) }
  if let Some(si) = &a.si { high_reg(rex, si.index) }
}

fn high_rm(rex: &mut bool, rm: &PRegMem) {
  match rm {
    &RegMem::Reg(r) => high_reg(rex, r),
    RegMem::Mem(a) => high_amode(rex, a)
  }
}

fn high_rmi(rex: &mut bool, rmi: &PRegMemImm) {
  match rmi {
    &PRegMemImm::Reg(r) => high_reg(rex, r),
    PRegMemImm::Mem(a) => high_amode(rex, a),
    PRegMemImm::Imm(_) => {}
  }
}

#[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
fn layout_binop_lo(sz: Size, dst: PReg, src: &PRegMemImm) -> InstLayout {
  let mut rex = sz == Size::S64;
  if sz == Size::S8 { high_reg(&mut rex, dst); high_rmi(&mut rex, src) }
  let mut opc = match *src {
    PRegMemImm::Imm(i) => match sz {
      Size::S8 => OpcodeLayout::BinopImm(false, layout_opc_reg(&mut rex, dst)),
      Size::S16 => unimplemented!(),
      _ if i as i8 as u32 == i => OpcodeLayout::BinopImm8(layout_opc_reg(&mut rex, dst)),
      _ => OpcodeLayout::BinopImm(true, layout_opc_reg(&mut rex, dst)),
    }
    _ => OpcodeLayout::BinopReg(layout_rmi(&mut rex, dst, src))
  };
  if dst == RAX && matches!(src, PRegMemImm::Imm(..)) {
    let rax = OpcodeLayout::BinopRAX(sz != Size::S8);
    if rax.len() <= opc.len() { opc = rax }
  }
  InstLayout { rex, opc }
}

impl PInst {
  pub(crate) fn len(&self) -> u8 { self.layout_inst().len() }

  #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
  pub(crate) fn layout_inst(&self) -> InstLayout {
    match *self {
      PInst::Binop { sz, dst, ref src, .. } => layout_binop_lo(sz, dst, src),
      PInst::Unop { sz, dst, .. } => {
        let mut rex = sz == Size::S64;
        if sz == Size::S8 { high_reg(&mut rex, dst) }
        InstLayout { opc: OpcodeLayout::Hi(layout_opc_reg(&mut rex, dst)), rex }
      }
      PInst::DivRem { sz, ref src } | PInst::Mul { sz, ref src } => {
        let mut rex = sz == Size::S64;
        InstLayout { opc: OpcodeLayout::Hi(layout_opc_rm(&mut rex, src)), rex }
      }
      PInst::Cdx { sz } => InstLayout { rex: sz == Size::S64, opc: OpcodeLayout::Cdx },
      PInst::Imm { sz, dst, src } => {
        let opc = match (sz, src) {
          (_, 0) => {
             // xor dst, dst
             return layout_binop_lo(sz.min(Size::S32), dst, &PRegMemImm::Reg(dst))
          }
          (Size::S64, _) if src as i32 as u64 == src =>
            OpcodeLayout::MovImm(layout_opc_reg(&mut true, dst)),
          (Size::S64, _) => OpcodeLayout::Mov64,
          _ => OpcodeLayout::Mov32,
        };
        InstLayout { rex: sz == Size::S64 || large_preg(dst), opc }
      }
      PInst::MovRR { sz, dst, src } => {
        let mut rex = sz == Size::S64;
        InstLayout { opc: OpcodeLayout::MovReg(layout_reg(&mut rex, dst, src)), rex }
      }
      PInst::MovzxRmR { ext_mode: ExtMode::LQ, dst, ref src } => {
        let mut rex = false;
        InstLayout { opc: OpcodeLayout::MovReg(layout_rm(&mut rex, dst, src)), rex }
      }
      PInst::MovsxRmR { ext_mode: ExtMode::LQ, dst, ref src } =>
        InstLayout { opc: OpcodeLayout::MovSX(layout_rm(&mut true, dst, src)), rex: true },
      PInst::MovzxRmR { ext_mode, dst, ref src } |
      PInst::MovsxRmR { ext_mode, dst, ref src } => {
        let mut rex = ext_mode.dst() == Size::S64;
        InstLayout { opc: OpcodeLayout::MovX(layout_rm(&mut rex, dst, src)), rex }
      }
      PInst::Load64 { dst, ref src } =>
        InstLayout { opc: OpcodeLayout::MovReg(layout_mem(&mut true, dst, src)), rex: true },
      PInst::Lea { sz, dst, ref addr } => {
        let mut rex = sz == Size::S64;
        InstLayout { opc: OpcodeLayout::Lea(layout_mem(&mut rex, dst, addr)), rex }
      }
      PInst::Store { sz, ref dst, src } => {
        let mut rex = sz == Size::S64;
        if sz == Size::S8 { high_amode(&mut rex, dst); high_reg(&mut rex, src) }
        InstLayout { opc: OpcodeLayout::MovReg(layout_mem(&mut rex, src, dst)), rex }
      }
      PInst::Shift { sz, dst, num_bits, .. } => {
        let mut rex = sz == Size::S64;
        if sz == Size::S8 { high_reg(&mut rex, dst) }
        let opc = match num_bits {
          None => OpcodeLayout::BinopHiReg(layout_opc_reg(&mut rex, dst)),
          Some(1) => OpcodeLayout::BinopHi1(layout_opc_reg(&mut rex, dst)),
          Some(_) => OpcodeLayout::BinopHi(layout_opc_reg(&mut rex, dst)),
        };
        InstLayout { rex, opc }
      }
      PInst::Cmp { sz, op: Cmp::Cmp, src1, ref src2 } => layout_binop_lo(sz, src1, src2),
      PInst::Cmp { sz, op: Cmp::Test, src1, ref src2 } => {
        let mut rex = sz == Size::S64;
        if sz == Size::S8 { high_reg(&mut rex, src1); high_rmi(&mut rex, src2) }
        let opc = match *src2 {
          PRegMemImm::Imm(i) => match src1 {
            RAX => OpcodeLayout::TestRAX(sz != Size::S8),
            _ => OpcodeLayout::HiTest(sz != Size::S8, layout_opc_reg(&mut rex, src1)),
          }
          _ => OpcodeLayout::Test(layout_rmi(&mut rex, src1, src2))
        };
        InstLayout { rex, opc }
      }
      PInst::SetCC { dst, .. } => {
        let mut rex = false;
        high_reg(&mut rex, dst);
        InstLayout { opc: OpcodeLayout::SetCC(layout_opc_reg(&mut rex, dst)), rex }
      }
      PInst::CMov { sz, cc, dst, ref src } => {
        let mut rex = sz == Size::S64;
        InstLayout { opc: OpcodeLayout::CMov(layout_rm(&mut rex, dst, src)), rex }
      }
      PInst::Push64 { ref src } => {
        let mut rex = false;
        let opc = match *src {
          PRegMemImm::Imm(i) => OpcodeLayout::PushImm(i as i8 as u32 != i),
          PRegMemImm::Reg(r) => { rex |= large_preg(r); OpcodeLayout::PushReg }
          PRegMemImm::Mem(ref a) => OpcodeLayout::Hi(layout_opc_mem(&mut rex, a))
        };
        InstLayout { rex, opc }
      }
      PInst::Pop64 { dst } => InstLayout { opc: OpcodeLayout::PopReg, rex: large_preg(dst) },
      PInst::CallKnown { .. } => InstLayout { opc: OpcodeLayout::Call, rex: false },
      PInst::SysCall => InstLayout { opc: OpcodeLayout::SysCall, rex: false },
      PInst::Ret => InstLayout { opc: OpcodeLayout::Ret, rex: false },
      PInst::JmpKnown { short, .. } => InstLayout { opc: OpcodeLayout::Jump(!short), rex: false },
      PInst::JmpCond { short: true, .. } => InstLayout { opc: OpcodeLayout::Jcc8, rex: false },
      PInst::JmpCond { short: false, .. } => InstLayout { opc: OpcodeLayout::Jcc, rex: false },
      PInst::Assert { .. } => InstLayout { opc: OpcodeLayout::Assert, rex: false },
      PInst::Ud2 => InstLayout { opc: OpcodeLayout::Ud2, rex: false },
    }
  }

  pub(crate) fn is_jump(&self) -> Option<BlockId> {
    if let PInst::JmpKnown { dst, .. } | PInst::JmpCond { dst, .. } = *self {
      Some(dst)
    } else {
      None
    }
  }
  pub(crate) fn shorten(&mut self) {
    if let PInst::JmpKnown { short, .. } | PInst::JmpCond { short, .. } = self {
      *short = true
    }
  }

  pub(crate) fn len_bound(&self) -> (u8, u8) {
    match *self {
      PInst::JmpKnown { dst, short: false } => (
        PInst::JmpKnown { dst, short: true }.len(),
        PInst::JmpKnown { dst, short: false }.len()
      ),
      PInst::JmpCond { cc, dst, short: false } => (
        PInst::JmpCond { cc, dst, short: true }.len(),
        PInst::JmpCond { cc, dst, short: false }.len()
      ),
      _ => { let len = self.len(); (len, len) }
    }
  }

  #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
  pub(crate) fn write(&self, buf: &mut InstSink<'_>) {
    const REX_W: u8 = 1 << 3;
    const REX_R: u8 = 1 << 2;
    const REX_X: u8 = 1 << 1;
    const REX_B: u8 = 1 << 0;

    fn op_size_w(rex: &mut u8, sz: Size) -> u8 {
      match sz {
        Size::S8 => 0,
        Size::S16 => unimplemented!(),
        Size::S32 => 1,
        Size::S64 => { *rex |= REX_W; 1 },
        Size::Inf => unreachable!(),
      }
    }

    fn get_binop(inst: &PInst) -> (Size, PReg, PRegMemImm, u8) {
      match *inst {
        PInst::Binop { sz, dst, src, op } => (sz, dst, src, op as u8),
        PInst::Cmp { sz, op: Cmp::Cmp, src1, src2 } => (sz, src1, src2, 7),
        PInst::Imm { sz, dst, src: 0 } =>
          (sz.min(Size::S32), dst, PRegMemImm::Reg(dst), Binop::Xor as u8),
        _ => unreachable!()
      }
    }

    fn to_rm(rmi: PRegMemImm) -> PRegMem {
      match rmi {
        PRegMemImm::Reg(r) => PRegMem::Reg(r),
        PRegMemImm::Mem(m) => PRegMem::Mem(m),
        PRegMemImm::Imm(_) => unreachable!(),
      }
    }

    #[inline] fn encode_reg8(n: u8, rex: &mut u8, x: u8) -> u8 {
      if n >= 8 { *rex |= x }
      n & 7
    }

    #[inline] fn encode_reg(preg: PReg, rex: &mut u8, x: u8) -> u8 {
      encode_reg8(preg.index() as u8, rex, x)
    }

    fn write_disp(disp: DispLayout, buf: &mut InstSink<'_>, n: u32) {
      match disp {
        DispLayout::S0 => assert!(n == 0),
        DispLayout::S8 => buf.push_u8(n as u8),
        DispLayout::S32 => buf.push_u32(n),
      }
    }

    fn encode_offset(buf: &InstSink<'_>, off: &Offset) -> u32 {
      match *off {
        Offset::Real(off) => off,
        Offset::Spill(..) => unreachable!("removed by regalloc"),
        Offset::Global(id, n) => buf[id] + n,
        Offset::Const(n) => buf.rodata_start + n,
      }
    }

    fn encode_si(si: Option<PShiftIndex>, rex: &mut u8) -> u8 {
      match si {
        Some(ShiftIndex { shift, index }) => (shift << 6) + (encode_reg(index, rex, REX_X) << 3),
        None => 4 << 3
      }
    }

    fn write_opc_modrm(modrm: ModRMLayout,
      rex: &mut u8, buf: &mut InstSink<'_>, arg1: u8, arg2: PRegMem
    ) {
      let opc = encode_reg8(arg1, rex, REX_R);
      match (modrm, arg2) {
        (ModRMLayout::Reg, PRegMem::Reg(rm2)) =>
          buf.push_u8((3 << 6) + (opc << 3) + encode_reg(rm2, rex, REX_B)),
        (ModRMLayout::Sib0, PRegMem::Mem(a)) => {
          buf.push_u8((opc << 3) + 4);
          buf.push_u8(encode_si(a.si, rex) + 5);
          let off = encode_offset(buf, &a.off);
          buf.push_u32(off);
        }
        (ModRMLayout::SibReg(disp), PRegMem::Mem(a)) => {
          buf.push_u8(((disp as u8) << 6) + (opc << 3) + 4);
          buf.push_u8(encode_si(a.si, rex) + encode_reg(a.base, rex, REX_B));
          let off = encode_offset(buf, &a.off);
          write_disp(disp, buf, off);
        }
        (ModRMLayout::Disp(disp), PRegMem::Mem(a)) => {
          buf.push_u8(((disp as u8) << 6) + (opc << 3) + encode_reg(a.base, rex, REX_B));
          let off = encode_offset(buf, &a.off);
          write_disp(disp, buf, off);
        }
        _ => unreachable!(),
      }
    }

    fn write_modrm(modrm: ModRMLayout,
      rex: &mut u8, buf: &mut InstSink<'_>, arg1: PReg, arg2: PRegMem
    ) {
      write_opc_modrm(modrm, rex, buf, arg1.index() as u8, arg2)
    }

    fn push_u8_u32(sz32: bool, buf: &mut InstSink<'_>, src: u32) {
      if sz32 { buf.push_u32(src) } else { buf.push_u8(src as u8) }
    }

    let layout = self.layout_inst();
    buf.update_rip(layout.len());
    if layout.rex { buf.push_u8(0) }
    let mut rex = 0;
    match (layout.opc, self) {
      (OpcodeLayout::BinopRAX(b), _) =>
        if let (sz, RAX, PRegMemImm::Imm(src), op) = get_binop(self) {
          buf.push_u8(0x04 + (op << 3) + op_size_w(&mut rex, sz));
          push_u8_u32(b, buf, src);
        } else { unreachable!() },
      (OpcodeLayout::BinopImm(b, modrm), _) =>
        if let (sz, dst, PRegMemImm::Imm(src), op) = get_binop(self) {
          buf.push_u8(0x80 + op_size_w(&mut rex, sz));
          write_opc_modrm(modrm, &mut rex, buf, op, PRegMem::Reg(dst));
          push_u8_u32(b, buf, src);
        } else { unreachable!() },
      (OpcodeLayout::BinopImm8(modrm), _) =>
        if let (sz, dst, PRegMemImm::Imm(src), op) = get_binop(self) {
          assert!(op_size_w(&mut rex, sz) == 1);
          buf.push_u8(0x83);
          write_opc_modrm(modrm, &mut rex, buf, op, PRegMem::Reg(dst));
          buf.push_u8(src as u8);
        } else { unreachable!() },
      (OpcodeLayout::BinopReg(modrm), _) => {
        let (sz, dst, src, op) = get_binop(self);
        buf.push_u8(0x02 + (op << 3) + op_size_w(&mut rex, sz));
        write_modrm(modrm, &mut rex, buf, dst, to_rm(src));
      }
      (OpcodeLayout::BinopHi(modrm), &PInst::Shift { kind, sz, dst, num_bits: Some(n) }) => {
        buf.push_u8(0xc0 + op_size_w(&mut rex, sz));
        write_opc_modrm(modrm, &mut rex, buf, kind as u8, PRegMem::Reg(dst));
        buf.push_u8(n);
      }
      (OpcodeLayout::BinopHi1(modrm), &PInst::Shift { kind, sz, dst, num_bits: Some(1) }) => {
        buf.push_u8(0xd0 + op_size_w(&mut rex, sz));
        write_opc_modrm(modrm, &mut rex, buf, kind as u8, PRegMem::Reg(dst));
      }
      (OpcodeLayout::BinopHiReg(modrm), &PInst::Shift { kind, sz, dst, num_bits: None }) => {
        buf.push_u8(0xd2 + op_size_w(&mut rex, sz));
        write_opc_modrm(modrm, &mut rex, buf, kind as u8, PRegMem::Reg(dst));
      }
      (OpcodeLayout::MovSX(modrm), &PInst::MovsxRmR { ext_mode: ExtMode::LQ, dst, src }) => {
        buf.push_u8(0x63); rex |= REX_W;
        write_modrm(modrm, &mut rex, buf, dst, src);
      }
      (OpcodeLayout::MovReg(modrm), _) => {
        let (op, r, rm) = match *self {
          PInst::MovRR { sz, dst, src } => (0x8a + op_size_w(&mut rex, sz), dst, src.into()),
          PInst::MovzxRmR { ext_mode: ExtMode::LQ, dst, src } => (0x8b, dst, src),
          PInst::Load64 { dst, src } => (0x8a + op_size_w(&mut rex, Size::S64), dst, src.into()),
          PInst::Store { sz, dst, src } => (0x88 + op_size_w(&mut rex, sz), src, dst.into()),
          _ => unreachable!(),
        };
        buf.push_u8(op);
        write_modrm(modrm, &mut rex, buf, r, rm);
      }
      (OpcodeLayout::Mov32, &PInst::Imm { sz: Size::S32, dst, src }) => {
        buf.push_u8(0xb8 + encode_reg(dst, &mut rex, REX_B));
        buf.push_u32(src as u32);
      }
      (OpcodeLayout::Mov64, &PInst::Imm { sz: Size::S64, dst, src }) => {
        buf.push_u8(0xb8 + encode_reg(dst, &mut rex, REX_B)); rex |= REX_W;
        buf.push_u64(src);
      }
      (OpcodeLayout::MovImm(modrm), &PInst::Imm { sz, dst, src }) => {
        buf.push_u8(0xc6 + op_size_w(&mut rex, sz));
        write_opc_modrm(modrm, &mut rex, buf, 0, PRegMem::Reg(dst));
        buf.push_u32(src as u32);
      }
      (OpcodeLayout::PushImm(b), &PInst::Push64 { src: PRegMemImm::Imm(src) }) => {
        buf.push_u8(0x68 + (((!b) as u8) << 2));
        push_u8_u32(b, buf, src);
      }
      (OpcodeLayout::PushReg, &PInst::Push64 { src: PRegMemImm::Reg(src) }) =>
        buf.push_u8(0x50 + encode_reg(src, &mut rex, REX_B)),
      (OpcodeLayout::PopReg, &PInst::Pop64 { dst }) =>
        buf.push_u8(0x58 + encode_reg(dst, &mut rex, REX_B)),
      (OpcodeLayout::Jump(b), &PInst::JmpKnown { short, dst }) => {
        let dst = buf.rip_relative_block(dst);
        assert!(short == !b);
        buf.push_u8(0xe9 + ((short as u8) << 2));
        push_u8_u32(b, buf, dst as u32);
      }
      (OpcodeLayout::Jcc8, &PInst::JmpCond { cc, short: true, dst }) => {
        let dst = buf.rip_relative_block(dst);
        buf.push_u8(0x70 + cc as u8);
        buf.push_u8(dst as u8);
      }
      (OpcodeLayout::Call, &PInst::CallKnown { f }) => {
        let dst = buf.rip_relative_proc(f);
        buf.push_u8(0xe8);
        buf.push_u32(dst as u32);
      }
      (OpcodeLayout::Ret, PInst::Ret) => buf.push_u8(0xc3),
      (OpcodeLayout::Lea(modrm), &PInst::Lea { sz, dst, addr }) => {
        assert!(op_size_w(&mut rex, sz) == 1);
        buf.push_u8(0x8d);
        write_modrm(modrm, &mut rex, buf, dst, RegMem::Mem(addr));
      }
      (OpcodeLayout::Test(modrm), &PInst::Cmp { sz, op: Cmp::Test, src1, src2 }) => {
        buf.push_u8(0x84 + op_size_w(&mut rex, sz));
        write_modrm(modrm, &mut rex, buf, src1, to_rm(src2));
      }
      (OpcodeLayout::TestRAX(b),
        &PInst::Cmp { sz, op: Cmp::Test, src1: RAX, src2: PRegMemImm::Imm(imm) }
      ) => {
        buf.push_u8(0xa8 + op_size_w(&mut rex, sz));
        push_u8_u32(b, buf, imm);
      }
      (OpcodeLayout::Hi(modrm), _) => {
        let (op1, op2, rm) = match *self {
          PInst::Unop { sz, op: Unop::Inc, dst } => (0xfe + op_size_w(&mut rex, sz), 0, dst.into()),
          PInst::Unop { sz, op: Unop::Dec, dst } => (0xfe + op_size_w(&mut rex, sz), 1, dst.into()),
          PInst::Unop { sz, op: Unop::Not, dst } => (0xf6 + op_size_w(&mut rex, sz), 2, dst.into()),
          PInst::Unop { sz, op: Unop::Neg, dst } => (0xf6 + op_size_w(&mut rex, sz), 3, dst.into()),
          PInst::Mul { sz, src } => (0xf6 + op_size_w(&mut rex, sz), 4, src),
          PInst::DivRem { sz, src } => (0xf6 + op_size_w(&mut rex, sz), 6, src),
          PInst::Push64 { src: PRegMemImm::Mem(a) } => (0xff, 6, a.into()),
          _ => unreachable!(),
        };
        buf.push_u8(op1);
        write_opc_modrm(modrm, &mut rex, buf, op2, rm);
      }
      (OpcodeLayout::HiTest(b, modrm),
        &PInst::Cmp { sz, op: Cmp::Test, src1, src2: PRegMemImm::Imm(imm) }
      ) => {
        buf.push_u8(0xf6 + op_size_w(&mut rex, sz));
        write_opc_modrm(modrm, &mut rex, buf, 0, src1.into());
        push_u8_u32(b, buf, imm);
      }
      (OpcodeLayout::SetCC(modrm), &PInst::SetCC { cc, dst }) => {
        buf.push_u8(0x0f);
        buf.push_u8(0x90 + cc as u8);
        write_opc_modrm(modrm, &mut rex, buf, 0, dst.into());
      }
      (OpcodeLayout::CMov(modrm), &PInst::CMov { sz, cc, dst, src }) => {
        assert!(op_size_w(&mut rex, sz) == 1);
        buf.push_u8(0x0f);
        buf.push_u8(0x40 + cc as u8);
        write_modrm(modrm, &mut rex, buf, dst, src);
      }
      (OpcodeLayout::MovX(modrm), _) => {
        let (opc, ext_mode, dst, src) = match *self {
          PInst::MovzxRmR { ext_mode, dst, src } => (0xb6, ext_mode, dst, src),
          PInst::MovsxRmR { ext_mode, dst, src } => (0xbe, ext_mode, dst, src),
          _ => unreachable!()
        };
        assert!(op_size_w(&mut rex, ext_mode.dst()) == 1);
        buf.push_u8(0x0f);
        buf.push_u8(opc + (ext_mode.src() == Size::S16) as u8);
        write_modrm(modrm, &mut rex, buf, dst, src);
      }
      (OpcodeLayout::Jcc, &PInst::JmpCond { cc, short: false, dst }) => {
        let dst = buf.rip_relative_block(dst);
        buf.push_u8(0x0f);
        buf.push_u8(0x80 + cc as u8);
        buf.push_u32(dst as u32);
      }
      (OpcodeLayout::SysCall, PInst::SysCall) => { buf.push_u8(0x0f); buf.push_u8(0x05); }
      (OpcodeLayout::Assert, &PInst::Assert { cc }) => {
        buf.push_u8(0x70 + cc as u8); buf.push_u8(2); // jcc cond +2
        buf.push_u8(0x0f); buf.push_u8(0x0b); // ud2
      }
      (OpcodeLayout::Ud2, PInst::Ud2) => { buf.push_u8(0x0f); buf.push_u8(0x0b); }
      _ => unreachable!(),
    }

    debug_assert!(usize::from(layout.len()) == buf.len());
    if layout.rex {
      buf.set_rex(0x40 + rex);
    } else {
      assert!(rex == 0);
    }
  }
}