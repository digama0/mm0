//! x86-specific parts of the compiler.

use std::{convert::TryFrom, fmt::Debug};

use num::Zero;
use regalloc2::{MachineEnv, PReg, VReg, Operand};

use crate::types::{Size,
  vcode::{BlockId, ConstId, GlobalId, SpillId, ProcId, InstId, Inst as VInst, VCode}};

const fn preg(i: usize) -> PReg { PReg::new(i, regalloc2::RegClass::Int) }

const RAX: PReg = preg(0);
const RCX: PReg = preg(1);
const RDX: PReg = preg(2);
const RBX: PReg = preg(3);
const RSP: PReg = preg(4);
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
const CALLER_SAVED: [PReg; 8] = [RAX, RDI, RSI, RDX, RCX, R8, R9, R10];
const CALLEE_SAVED: [PReg; 6] = [RBX, RBP, R12, R13, R14, R15];
const SCRATCH: PReg = R11;

lazy_static! {
  pub(crate) static ref MACHINE_ENV: MachineEnv = {
    MachineEnv {
      preferred_regs_by_class: [CALLER_SAVED.into(), vec![]],
      non_preferred_regs_by_class: [CALLEE_SAVED.into(), vec![]],
      scratch_by_class: [SCRATCH, PReg::invalid()],
      regs: CALLER_SAVED.iter().copied()
        .chain(CALLEE_SAVED.iter().copied())
        .chain([SCRATCH]).collect(),
    }
  };
}

/// What kind of division or remainer instruction this is?
#[derive(Clone, Debug)]
pub(crate) enum DivOrRemKind {
  SignedDiv,
  UnsignedDiv,
  SignedRem,
  UnsignedRem,
}

/// These indicate the form of a scalar shift/rotate: left, signed right, unsigned right.
#[derive(Clone, Copy, Debug)]
pub(crate) enum ShiftKind {
  Shl,
  /// Inserts zeros in the most significant bits.
  ShrL,
  /// Replicates the sign bit in the most significant bits.
  ShrA,
  Rol,
  Ror,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Cmp {
  /// CMP instruction: compute `a - b` and set flags from result.
  Cmp,
  /// TEST instruction: compute `a & b` and set flags from result.
  Test,
}

/// These indicate ways of extending (widening) a value, using the Intel
/// naming: B(yte) = u8, W(ord) = u16, L(ong)word = u32, Q(uad)word = u64
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum ExtMode {
  /// Byte -> Longword.
  BL,
  /// Byte -> Quadword.
  BQ,
  /// Word -> Longword.
  WL,
  /// Word -> Quadword.
  WQ,
  /// Longword -> Quadword.
  LQ,
}

impl ExtMode {
  /// Calculate the `ExtMode` from passed bit lengths of the from/to types.
  pub(crate) fn new(from: Size, to: Size) -> Option<ExtMode> {
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
  pub(crate) fn src(&self) -> Size {
    match self {
      ExtMode::BL | ExtMode::BQ => Size::S8,
      ExtMode::WL | ExtMode::WQ => Size::S16,
      ExtMode::LQ => Size::S32,
    }
  }

  /// Return the destination register size in bytes.
  pub(crate) fn dst(&self) -> Size {
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
pub(crate) enum CC {
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
  /// parity (aka PE = parity even)
  P = 10,
  /// not parity (aka PO = parity odd)
  NP = 11,
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
  pub(crate) fn invert(self) -> Self {
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
      CC::P => CC::NP,
      CC::NP => CC::P,
      CC::L => CC::NL,
      CC::NL => CC::L,
      CC::LE => CC::NLE,
      CC::NLE => CC::LE,
    }
  }
}

/// Some basic ALU operations.  TODO: maybe add Adc, Sbb.
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) enum Binop {
  Add = 0,
  Or = 1,
  Adc = 2,
  Sbb = 3,
  And = 4,
  Sub = 5,
  Xor = 6,
}

/// Some basic ALU operations.  TODO: maybe add Adc, Sbb.
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) enum Unop {
  Inc = 0,
  Dec = 1,
  Not = 2,
  Neg = 3,
}

/// A shift amount, which can be used as an addend in an addressing mode.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ShiftIndex<Reg = VReg> {
  pub(crate) index: Reg,
  pub(crate) shift: u8, /* 0 .. 3 only */
}

/// A base offset for an addressing mode.
#[derive(Clone, Copy)]
pub(crate) enum Imm<N = u32> {
  /// A real offset, relative to zero.
  Real(N),
  /// An offset relative to the given spill slot. `base` must be 0 in this case
  /// because it is pinned to `RSP`.
  Spill(SpillId, N),
  /// An offset into the given global (in the .data / .bss section).
  Global(GlobalId, N),
  /// An offset into the given constant (in the .rodata section).
  Const(ConstId, N),
}

impl<N: Zero + Debug> Debug for Imm<N> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Real(n) => n.fmt(f),
      Self::Spill(i, n) if n.is_zero() => i.fmt(f),
      Self::Spill(i, n) => write!(f, "{:?} + {:?}", i, n),
      Self::Global(i, n) if n.is_zero() => i.fmt(f),
      Self::Global(i, n) => write!(f, "{:?} + {:?}", i, n),
      Self::Const(i, n) if n.is_zero() => i.fmt(f),
      Self::Const(i, n) => write!(f, "{:?} + {:?}", i, n),
    }
  }
}

impl<N> From<N> for Imm<N> {
  fn from(n: N) -> Self { Self::Real(n) }
}

impl Imm {
  pub(crate) const ZERO: Self = Self::Real(0);
}
impl Imm<u64> {
  pub(crate) const ZERO64: Self = Self::Real(0);
}

impl From<Imm> for Imm<u64> {
  fn from(imm: Imm) -> Self {
    match imm {
      Imm::Real(i) => Imm::Real(i.into()),
      Imm::Spill(s, i) => Imm::Spill(s, i.into()),
      Imm::Global(g, i) => Imm::Global(g, i.into()),
      Imm::Const(c, i) => Imm::Const(c, i.into()),
    }
  }
}
impl TryFrom<Imm<u64>> for Imm {
  type Error = std::num::TryFromIntError;
  fn try_from(imm: Imm<u64>) -> Result<Self, Self::Error> {
    Ok(match imm {
      Imm::Real(i) => Imm::Real(u32::try_from(i)?),
      Imm::Spill(s, i) => Imm::Spill(s, u32::try_from(i)?),
      Imm::Global(g, i) => Imm::Global(g, u32::try_from(i)?),
      Imm::Const(c, i) => Imm::Const(c, u32::try_from(i)?),
    })
  }
}

impl<N: std::ops::Add<Output = N>> std::ops::Add<N> for Imm<N> {
  type Output = Imm<N>;
  fn add(self, n: N) -> Imm<N> {
    match self {
      Imm::Real(i) => Imm::Real(i + n),
      Imm::Spill(s, i) => Imm::Spill(s, i + n),
      Imm::Global(g, i) => Imm::Global(g, i + n),
      Imm::Const(c, i) => Imm::Const(c, i + n),
    }
  }
}

pub(crate) trait IsReg {
  fn invalid() -> Self;
  fn is_valid(&self) -> bool;
}
impl IsReg for VReg {
  fn invalid() -> Self { VReg::invalid() }
  fn is_valid(&self) -> bool { *self != VReg::invalid() }
}
impl IsReg for PReg {
  fn invalid() -> Self { PReg::invalid() }
  fn is_valid(&self) -> bool { *self != PReg::invalid() }
}

/// A memory address. This has the form `off+base+si`, where `off` is a base memory location
/// (a 32 bit address, or an offset from a stack slot, named global or named constant),
/// `base` is a register or 0, and `si` is a shifted register or 0.
/// Note that `base` must be 0 if `off` is `Spill(..)` because spill slots are RSP-relative,
/// so there is no space for a second register in the encoding.
#[derive(Clone, Copy)]
pub(crate) struct AMode<Reg = VReg> {
  pub(crate) off: Imm,
  /// `VReg::invalid` means no added register
  pub(crate) base: Reg,
  /// Optionally add a shifted register
  pub(crate) si: Option<ShiftIndex<Reg>>,
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

impl<Reg: IsReg> From<Imm> for AMode<Reg> {
  fn from(off: Imm) -> Self { Self { off, base: Reg::invalid(), si: None } }
}

impl<Reg: IsReg> AMode<Reg> {
  pub(crate) fn reg(r: Reg) -> Self { Self { off: Imm::ZERO, base: r, si: None } }
  pub(crate) fn spill(i: SpillId) -> Self { Imm::Spill(i, 0).into() }
  pub(crate) fn global(i: GlobalId) -> Self { Imm::Global(i, 0).into() }
  pub(crate) fn const_(i: ConstId) -> Self { Imm::Const(i, 0).into() }
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
      self.base != VReg::invalid() || matches!(self.off, Imm::Spill(..)),
      sc
    ) {
      (_, false, 1) => AMode { off: self.off, base: reg, si: self.si },
      (None, _, 1 | 2 | 4 | 8) => {
        let shift = match sc { 1 => 0, 2 => 1, 4 => 2, 8 => 3, _ => unreachable!() };
        AMode { off: self.off, base: self.base, si: Some(ShiftIndex { index: reg, shift }) }
      }
      (None, false, 3 | 5 | 9) => {
        let shift = match sc { 3 => 1, 5 => 2, 9 => 3, _ => unreachable!() };
        AMode { off: self.off, base: reg, si: Some(ShiftIndex { index: reg, shift }) }
      }
      (Some(_), _, _) => AMode::reg(code.emit_lea(*self)).add_scaled(code, sc, reg),
      (None, _, _) => {
        let sc = code.emit_imm(Size::S64, sc);
        let mul = code.emit_mul(Size::S64, reg, sc).0;
        AMode { off: self.off, base: self.base, si: Some(ShiftIndex { index: mul, shift: 0 }) }
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
pub(crate) enum RegMem<Reg = VReg> {
  Reg(Reg),
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
  Imm(Imm<N>),
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
impl<N> From<Imm<N>> for RegMemImm<N> {
  fn from(i: Imm<N>) -> Self { RegMemImm::Imm(i) }
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
      RegMemImm::Imm(i) => RegMemImm::Mem(i.into()),
      RegMemImm::Uninit => RegMemImm::Uninit,
    }
  }
}
impl From<u32> for RegMemImm {
  fn from(n: u32) -> Self { Imm::Real(n).into() }
}
impl From<u64> for RegMemImm<u64> {
  fn from(n: u64) -> Self { Imm::Real(n).into() }
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
  where Imm<N>: Into<Imm<u64>> {
    match self {
      RegMemImm::Reg(r) => RegMem::Reg(r),
      RegMemImm::Mem(a) => RegMem::Mem(a),
      RegMemImm::Imm(i) => RegMem::Reg(code.emit_imm(sz, i)),
      RegMemImm::Uninit => RegMem::Reg(code.fresh_vreg()),
    }
  }

  pub(crate) fn into_reg(self, code: &mut VCode<Inst>, sz: Size) -> VReg
  where Imm<N>: Into<Imm<u64>> {
    match self {
      RegMemImm::Reg(r) => r,
      RegMemImm::Mem(a) => a.emit_load(code, sz),
      RegMemImm::Imm(i) => code.emit_imm(sz, i),
      RegMemImm::Uninit => code.fresh_vreg(),
    }
  }

  pub(crate) fn into_mem(self, code: &mut VCode<Inst>, sz: Size) -> AMode
  where Imm<N>: Into<Imm<u64>> {
    self.into_rm(code, sz).into_mem(code, sz)
  }
}

impl RegMemImm<u64> {
  pub(crate) fn into_rmi_32(self, code: &mut VCode<Inst>) -> RegMemImm {
    match self {
      RegMemImm::Reg(r) => RegMemImm::Reg(r),
      RegMemImm::Mem(a) => RegMemImm::Mem(a),
      RegMemImm::Imm(i) => match Imm::try_from(i) {
        Ok(i) => RegMemImm::Imm(i),
        _ => RegMemImm::Reg(code.emit_imm(Size::S64, i))
      }
      RegMemImm::Uninit => RegMemImm::Uninit,
    }
  }
}

#[derive(Debug)]
pub(crate) enum Inst {
  // /// A length 0 no-op instruction.
  // Nop,
  /// Jump to the given block ID. This is required to be the immediately following instruction,
  /// so no code need be emitted.
  Fallthrough { dst: BlockId },
  /// Integer arithmetic/bit-twiddling: `reg <- (add|sub|and|or|xor|mul|adc|sbb) (32|64) reg rmi`
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
    src: Imm<u64>,
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
  Cmov {
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
  /// Return.
  Ret,
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
  /// Traps if the condition code is set.
  TrapIf { cc: CC },
  /// An instruction that will always trigger the illegal instruction exception.
  Ud2,
}

impl VInst for Inst {
  fn is_call(&self) -> bool {
    matches!(self, Inst::CallKnown {..})
  }

  fn is_ret(&self) -> bool {
    matches!(self, Inst::Ret {..})
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
      Inst::Lea { dst, ref addr } => {
        addr.collect_operands(args);
        args.push(Operand::reg_def(dst));
      }
      Inst::Store { sz, ref dst, src } => {
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
      Inst::Cmov { dst, src1, ref src2, .. } => {
        args.push(Operand::reg_use(src1));
        src2.collect_operands(args);
        args.push(Operand::reg_reuse_def(dst, 0));
      }
      Inst::Push64 { ref src } => src.collect_operands(args),
      Inst::CallKnown { operands: ref params, .. } |
      Inst::JmpKnown { ref params, .. } => args.extend_from_slice(params),
      // Inst::JmpUnknown { target } => target.collect_operands(args),
      // moves are handled specially by regalloc, we don't need operands
      Inst::MovRR { .. } | Inst::MovPR { .. } | Inst::MovRP { .. } |
      // Other instructions that have no operands
      Inst::Fallthrough { .. } |
      Inst::Ret |
      Inst::JmpCond { .. } |
      Inst::TrapIf { .. } |
      Inst::Ud2 => {}
    }
  }

  fn clobbers(&self) -> &[PReg] {
    if let Inst::CallKnown { clobbers: Some(cl), .. } = self { cl } else { &[] }
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
    self.0.emit(Inst::Cmov { sz, cc: self.1, dst, src1: fal, src2: tru.into() });
    dst
  }

  pub(crate) fn trap_if(self) -> InstId {
    self.0.emit(Inst::TrapIf { cc: self.1 })
  }

  pub(crate) fn branch(self, tru: BlockId, fal: BlockId) -> InstId {
    self.0.emit(Inst::JmpCond { cc: self.1, taken: tru, not_taken: fal })
  }
}

impl VCode<Inst> {
  pub(crate) fn emit_lea(&mut self, addr: AMode) -> VReg {
    let dst = self.fresh_vreg();
    self.emit(Inst::Lea { dst, addr });
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

  pub(crate) fn emit_imm(&mut self, sz: Size, src: impl Into<Imm<u64>>) -> VReg {
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
        (RegMem::Reg(dst), RegMemImm::Imm(src)) => { code.emit(Inst::Imm { sz, dst, src }); }
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
pub(crate) type PAMode = AMode<PReg>;

/// A version of `RegMem` post-register allocation.
pub(crate) type PRegMem = RegMem<PReg>;

/// A version of `RegMemImm` post-register allocation.
#[derive(Copy, Clone)]
pub(crate) enum PRegMemImm {
  Reg(PReg),
  Mem(PAMode),
  Imm(Imm),
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

#[derive(Debug)]
pub(crate) enum PInst {
  // /// A length 0 no-op instruction.
  // Nop,
  /// Integer arithmetic/bit-twiddling: `reg <- (add|sub|and|or|xor|mul|adc|sbb) (32|64) reg rmi`
  Binop {
    op: Binop,
    sz: Size, // 4 or 8
    dst: PReg,
    src: PRegMemImm,
  },
  /// Unary ALU operations: `reg <- (not|neg) (8|16|32|64) reg`
  Unop {
    op: Unop,
    sz: Size, // 1, 2, 4 or 8
    dst: PReg,
  },
  /// Unsigned integer quotient and remainder pseudo-operation:
  // `RDX:RAX <- cdq RAX`
  // `RAX,RDX <- divrem RDX:RAX r/m.`
  DivRem {
    sz: Size, // 2, 4 or 8
    src: PRegMem,
  },
  /// Unsigned integer quotient and remainder pseudo-operation:
  // `RDX:RAX <- cdq RAX`
  // `RAX,RDX <- divrem RDX:RAX r/m`.
  Mul {
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
    src: Imm<u64>,
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
    sz: Size, // 1, 2, 4 or 8
    kind: ShiftKind,
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
  Cmov {
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
  /// Traps if the condition code is set.
  TrapIf { cc: CC },
  /// An instruction that will always trigger the illegal instruction exception.
  Ud2,
}
