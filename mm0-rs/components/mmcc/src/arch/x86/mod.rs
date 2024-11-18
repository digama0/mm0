//! x86-specific parts of the compiler.

use std::fmt::{Debug, Display};

use num::Zero;
use once_cell::sync::Lazy;
use regalloc2::{MachineEnv, Operand};

use crate::codegen::InstSink;
use crate::types::{classify as cl, mir, Size,
  vcode::{BlockId, GlobalId, SpillId, ProcId, InstId, VReg, IsReg, Inst as VInst, VCode}};

/// A physical register. For x86, this is one of the 16 general purpose integer registers.
#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct PReg(pub regalloc2::PReg);

impl PReg {
  #[inline(always)]
  pub(crate) const fn new(reg: usize) -> Self {
    Self(regalloc2::PReg::new(reg, regalloc2::RegClass::Int))
  }

  /// The index of the register, a number from 0 to 15.
  #[allow(clippy::cast_possible_truncation)]
  #[inline(always)]
  #[must_use] pub fn index(self) -> u8 { self.0.hw_enc() as u8 }

  /// If true, then a REX byte is needed to encode this register
  #[inline] fn large(self) -> bool { self.index() & 8 != 0 }
}

impl IsReg for PReg {
  fn invalid() -> Self { Self(regalloc2::PReg::invalid()) }
}

impl Display for PReg {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match *self {
      RAX => write!(f, "rax"),
      RCX => write!(f, "rcx"),
      RDX => write!(f, "rdx"),
      RBX => write!(f, "rbx"),
      RSP => write!(f, "rsp"),
      RBP => write!(f, "rbp"),
      RSI => write!(f, "rsi"),
      RDI => write!(f, "rdi"),
      _ if self.is_valid() => write!(f, "r{}", self.index()),
      _ => write!(f, "r-")
    }
  }
}

impl Debug for PReg {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { Display::fmt(self, f) }
}

const RAX: PReg = PReg::new(0);
const RCX: PReg = PReg::new(1);
const RDX: PReg = PReg::new(2);
const RBX: PReg = PReg::new(3);
pub(crate) const RSP: PReg = PReg::new(4);
const RBP: PReg = PReg::new(5);
const RSI: PReg = PReg::new(6);
const RDI: PReg = PReg::new(7);
const R8: PReg = PReg::new(8);
const R9: PReg = PReg::new(9);
const R10: PReg = PReg::new(10);
const R11: PReg = PReg::new(11);
const R12: PReg = PReg::new(12);
const R13: PReg = PReg::new(13);
const R14: PReg = PReg::new(14);
const R15: PReg = PReg::new(15);
// pub(crate) const ARG_REGS: [PReg; 6] = [RDI, RSI, RDX, RCX, R8, R9];
pub(crate) const RET_AND_ARG_REGS: [PReg; 7] = [RAX, RDI, RSI, RDX, RCX, R8, R9];
pub(crate) const SYSCALL_ARG_REGS: (PReg, [PReg; 6]) = (RAX, [RDI, RSI, RDX, R10, R8, R9]);
pub(crate) const CALLER_SAVED: [PReg; 9] = [RAX, RDI, RSI, RDX, RCX, R8, R9, R10, R11];
pub(crate) const CALLEE_SAVED: [PReg; 6] = [RBX, RBP, R12, R13, R14, R15];

pub(crate) fn callee_saved() -> impl DoubleEndedIterator<Item=PReg> + Clone {
  CALLEE_SAVED.iter().copied()
}
pub(crate) fn caller_saved() -> impl DoubleEndedIterator<Item=PReg> + Clone {
  CALLER_SAVED.iter().copied()
}

pub(crate) static MACHINE_ENV: Lazy<MachineEnv> = Lazy::new(|| MachineEnv {
  preferred_regs_by_class: [CALLER_SAVED.map(|r| r.0).into(), vec![], vec![]],
  non_preferred_regs_by_class: [CALLEE_SAVED.map(|r| r.0).into(), vec![], vec![]],
  scratch_by_class: [None; 3],
  fixed_stack_slots: vec![],
});

/// A set of physical registers. For x86, this can be stored as a 16 bit bitfield.
#[derive(Copy, Clone, Default, Debug)]
pub struct PRegSet(u16);
impl PRegSet {
  #[inline] pub(crate) fn insert(&mut self, r: PReg) { self.0 |= 1 << r.index() }
  #[inline] pub(crate) fn get(self, r: PReg) -> bool { self.0 & (1 << r.index()) != 0 }
  #[inline] pub(crate) fn remove(&mut self, r: PReg) { self.0 &= !(1 << r.index()) }

  /// An iterator over the registers in the set.
  pub fn iter(self) -> impl Iterator<Item=PReg> {
    (0..16).map(PReg::new).filter(move |&r| self.get(r))
  }
}

impl std::ops::BitOrAssign for PRegSet {
  fn bitor_assign(&mut self, rhs: Self) {
    self.0 |= rhs.0
  }
}

impl From<PRegSet> for regalloc2::PRegSet {
  fn from(val: PRegSet) -> Self {
    let mut out = Self::empty();
    for i in 0..16 {
      let r = PReg::new(i);
      if val.get(r) {
        out.add(r.0)
      }
    }
    out
  }
}

impl FromIterator<PReg> for PRegSet {
  fn from_iter<T: IntoIterator<Item = PReg>>(iter: T) -> Self {
    let mut out = Self::default();
    for i in iter { out.insert(i); }
    out
  }
}

/// These indicate the form of a scalar shift/rotate: left, signed right, unsigned right.
#[derive(Clone, Copy)]
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

impl Display for ShiftKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Shl => write!(f, "shl"),
      Self::ShrL => write!(f, "shr"),
      Self::ShrA => write!(f, "sar"),
    }
  }
}

impl Debug for ShiftKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { Display::fmt(self, f) }
}

/// A binop which is used only for its effect on the flags.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Cmp {
  /// CMP instruction: compute `a - b` and set flags from result.
  Cmp,
  /// TEST instruction: compute `a & b` and set flags from result.
  Test,
}

impl Display for Cmp {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Cmp => write!(f, "cmp"),
      Self::Test => write!(f, "test"),
    }
  }
}

impl Debug for Cmp {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { Display::fmt(self, f) }
}

/// These indicate ways of extending (widening) a value, using the Intel
/// naming: B(yte) = u8, W(ord) = u16, L(ong)word = u32, Q(uad)word = u64
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
#[derive(Copy, Clone)]
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

impl Display for CC {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      CC::O => write!(f, "o"),
      CC::NO => write!(f, "no"),
      CC::B => write!(f, "b"),
      CC::NB => write!(f, "nb"),
      CC::Z => write!(f, "z"),
      CC::NZ => write!(f, "nz"),
      CC::BE => write!(f, "be"),
      CC::NBE => write!(f, "nbe"),
      CC::S => write!(f, "s"),
      CC::NS => write!(f, "ns"),
      CC::L => write!(f, "l"),
      CC::NL => write!(f, "nl"),
      CC::LE => write!(f, "le"),
      CC::NLE => write!(f, "nle"),
    }
  }
}

impl Debug for CC {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { Display::fmt(self, f) }
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
#[derive(Copy, Clone, PartialEq, Eq)]
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

impl Display for Binop {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Add => write!(f, "add"),
      Self::Or => write!(f, "or"),
      Self::Adc => write!(f, "adc"),
      Self::Sbb => write!(f, "sbb"),
      Self::And => write!(f, "and"),
      Self::Sub => write!(f, "sub"),
      Self::Xor => write!(f, "xor"),
    }
  }
}

impl Debug for Binop {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { Display::fmt(self, f) }
}

/// Some basic ALU operations.
#[derive(Copy, Clone, PartialEq, Eq)]
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

impl Display for Unop {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Inc => write!(f, "inc"),
      Self::Dec => write!(f, "dec"),
      Self::Not => write!(f, "not"),
      Self::Neg => write!(f, "neg"),
    }
  }
}

impl Debug for Unop {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { Display::fmt(self, f) }
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

impl<N: Default> Default for Offset<N> {
  fn default() -> Self { Self::Real(N::default()) }
}

impl<N: Zero + Debug> Debug for Offset<N> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Real(n) => n.fmt(f),
      Self::Spill(i, n) if n.is_zero() => i.fmt(f),
      Self::Spill(i, n) => write!(f, "{i:?} + {n:?}"),
      Self::Global(i, n) if n.is_zero() => i.fmt(f),
      Self::Global(i, n) => write!(f, "{i:?} + {n:?}"),
      Self::Const(n) => write!(f, "const[{n:?}]"),
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

/// A memory address.
///
/// This has the form `off+base+si`, where `off` is a base memory location
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

impl<Reg: IsReg> Default for AMode<Reg> {
  fn default() -> Self { Self { off: Offset::default(), base: Reg::invalid(), si: None } }
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

impl<Reg: IsReg + Display> Display for AMode<Reg> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "[{:?}", self.off)?;
    if self.base.is_valid() {
      write!(f, " + {}", self.base)?
    }
    if let Some(si) = &self.si {
      write!(f, " + {}*{}", 1 << si.shift, si.index)?
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
  fn on_regs(&self, mut f: impl FnMut(VReg)) {
    if self.base.is_valid() { f(self.base) }
    if let Some(si) = &self.si { f(si.index) }
  }

  fn collect_operands(&self, args: &mut Vec<Operand>) {
    self.on_regs(|v| args.push(Operand::reg_use(v.0)))
  }

  pub(crate) fn emit_load(&self, code: &mut VCode<Inst>, sz: Size) -> VReg {
    let dst = code.fresh_vreg();
    code.emit(Inst::load_mem(sz, dst, *self));
    dst
  }

  pub(crate) fn add_scaled(&self,
    code: &mut VCode<Inst>, sc: u64, reg: VReg
  ) -> (AMode, cl::AddScaled) {
    match (
      &self.si,
      self.base != VReg::invalid() || matches!(self.off, Offset::Spill(..)),
      sc
    ) {
      (_, false, 1) => (AMode { off: self.off, base: reg, si: self.si }, cl::AddScaled::NoBase1),
      (None, _, 1 | 2 | 4 | 8) => {
        let shift = match sc { 1 => 0, 2 => 1, 4 => 2, 8 => 3, _ => unreachable!() };
        let si = Some(ShiftIndex { shift, index: reg });
        (AMode { off: self.off, base: self.base, si }, cl::AddScaled::Pow2)
      }
      (None, false, 3 | 5 | 9) => {
        let shift = match sc { 3 => 1, 5 => 2, 9 => 3, _ => unreachable!() };
        let si = Some(ShiftIndex { index: reg, shift });
        (AMode { off: self.off, base: reg, si }, cl::AddScaled::NoBasePow2Add)
      }
      (Some(_), _, _) => {
        let (a, sc) = AMode::reg(code.emit_lea(Size::S64, *self)).add_scaled(code, sc, reg);
        (a, match sc {
          cl::AddScaled::Large => cl::AddScaled::ComposeLarge,
          cl::AddScaled::Pow2 => cl::AddScaled::ComposePow2,
          _ => unreachable!(),
        })
      }
      (None, _, _) => {
        let sc = code.emit_imm(Size::S64, sc);
        let mul = code.emit_mul(Size::S64, reg, sc).0;
        let si = Some(ShiftIndex { shift: 0, index: mul });
        (AMode { off: self.off, base: self.base, si }, cl::AddScaled::Large)
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

impl<Reg: IsReg> Default for RegMem<Reg> {
  fn default() -> Self { Self::Mem(AMode::default()) }
}

impl<Reg: IsReg + Display> Display for RegMem<Reg> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      RegMem::Reg(r) => r.fmt(f),
      RegMem::Mem(a) => a.fmt(f),
    }
  }
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
  fn on_regs(&self, mut f: impl FnMut(VReg)) {
    match *self {
      RegMem::Reg(reg) => f(reg),
      RegMem::Mem(ref addr) => addr.on_regs(f),
    }
  }

  fn collect_operands(&self, args: &mut Vec<Operand>) {
    self.on_regs(|v| args.push(Operand::reg_use(v.0)))
  }

  pub(crate) fn into_reg(self, code: &mut VCode<Inst>, sz: Size) -> (VReg, cl::IntoReg) {
    match self {
      RegMem::Reg(r) => (r, cl::IntoReg(false)),
      RegMem::Mem(a) => (a.emit_load(code, sz), cl::IntoReg(true))
    }
  }

  pub(crate) fn into_mem(self, code: &mut VCode<Inst>, sz: Size) -> (AMode, cl::IntoMem) {
    match self {
      RegMem::Reg(r) => {
        let a = AMode::spill(code.fresh_spill(sz.bytes().expect("large reg").into()));
        let _ = code.emit_copy(sz, a.into(), r);
        (a, cl::IntoMem(true))
      },
      RegMem::Mem(a) => (a, cl::IntoMem(false))
    }
  }

  pub(crate) fn emit_deref(&self, code: &mut VCode<Inst>, sz: Size) -> (AMode, cl::IntoReg) {
    let (reg, cl) = self.into_reg(code, sz);
    (AMode::reg(reg), cl)
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
}

impl<N: Zero + Debug> Debug for RegMemImm<N> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      RegMemImm::Reg(r) => Debug::fmt(r, f),
      RegMemImm::Mem(a) => Debug::fmt(a, f),
      RegMemImm::Imm(i) => Debug::fmt(i, f),
    }
  }
}

impl<N: Zero + Display> Display for RegMemImm<N> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      RegMemImm::Reg(r) => Display::fmt(r, f),
      RegMemImm::Mem(a) => Display::fmt(a, f),
      RegMemImm::Imm(i) => Display::fmt(i, f),
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
      RegMemImm::Reg(reg) => args.push(Operand::reg_use(reg.0)),
      RegMemImm::Mem(ref addr) => addr.collect_operands(args),
      RegMemImm::Imm(_) => {}
    }
  }

  pub(crate) fn into_rm(self, code: &mut VCode<Inst>, sz: Size) -> (RegMem, cl::IntoRM)
  where N: Into<u64> {
    match self {
      RegMemImm::Reg(r) => (RegMem::Reg(r), cl::IntoRM(false)),
      RegMemImm::Mem(a) => (RegMem::Mem(a), cl::IntoRM(false)),
      RegMemImm::Imm(i) => (RegMem::Reg(code.emit_imm(sz, i)), cl::IntoRM(true))
    }
  }

  pub(crate) fn into_reg(self, code: &mut VCode<Inst>, sz: Size) -> (VReg, cl::IntoReg)
  where N: Into<u64> {
    match self {
      RegMemImm::Reg(r) => (r, cl::IntoReg(false)),
      RegMemImm::Mem(a) => (a.emit_load(code, sz), cl::IntoReg(true)),
      RegMemImm::Imm(i) => (code.emit_imm(sz, i), cl::IntoReg(true)),
    }
  }

  pub(crate) fn into_mem(self, code: &mut VCode<Inst>, sz: Size) -> (AMode, cl::IntoMem)
  where N: Into<u64> {
    let (rm, cl) = self.into_rm(code, sz);
    let (a, cl2) = rm.into_mem(code, sz);
    (a, cl::IntoMem(cl.0 || cl2.0))
  }
}

impl RegMemImm<u64> {
  pub(crate) fn into_rmi_32(self, code: &mut VCode<Inst>) -> (RegMemImm, cl::IntoRMI32) {
    match self {
      RegMemImm::Reg(r) => (RegMemImm::Reg(r), cl::IntoRMI32(false)),
      RegMemImm::Mem(a) => (RegMemImm::Mem(a), cl::IntoRMI32(false)),
      RegMemImm::Imm(i) => match u32::try_from(i) {
        Ok(i) => (RegMemImm::Imm(i), cl::IntoRMI32(false)),
        _ => (RegMemImm::Reg(code.emit_imm(Size::S64, i)), cl::IntoRMI32(true)),
      }
    }
  }
}

/// The available set of kernel calls that can be made through the `syscall` instruction.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SysCall {
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

impl Debug for SysCall {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Open => write!(f, "open"),
      Self::Read => write!(f, "read"),
      Self::Write => write!(f, "write"),
      Self::FStat => write!(f, "fstat"),
      Self::MMap => write!(f, "mmap"),
      Self::Exit => write!(f, "exit"),
    }
  }
}

impl SysCall {
  #[inline] pub(crate) fn returns(self) -> bool { self != Self::Exit }
}

pub(crate) enum Inst {
  // /// A length 0 no-op instruction.
  // Nop,
  /// Jump to the given block ID. This is required to be the immediately following instruction,
  /// so no code need be emitted.
  Fallthrough { dst: BlockId },
  // /// Ghost instruction: Start of a let statement, together with the size of the data to transfer.
  // LetStart { size: u32 },
  // /// Ghost instruction: End of a let statement,
  // /// together with the register, just assigned, that corresponds to the new variable.
  // LetEnd { dst: RegMem },
  /// A ghost instruction at the start of a basic block to declare that a MIR variable
  /// lives at a certain machine location.
  BlockParam { var: mir::VarId, val: RegMem },
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
  // /// Unsigned integer quotient and remainder pseudo-operation:
  // /// `RDX:RAX <- cdq RAX`
  // /// `RAX,RDX <- divrem RDX:RAX r/m.`
  // DivRem {
  //   sz: Size, // 2, 4 or 8
  //   dst_div: VReg, // = RAX
  //   dst_rem: VReg, // = RDX
  //   src1: VReg, // = RAX
  //   src2: RegMem,
  // },
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
  /// (The 32 bit mov is used for all sizes <= 32)
  Imm {
    sz: Size,
    dst: VReg,
    src: u64,
  },
  /// GPR to GPR move: `reg <- movq reg`. This is always a pure move,
  /// because we require that a 32 bit source register has zeroed high part.
  MovRR {
    dst: VReg,
    src: VReg,
  },
  // /// Move into a fixed reg: `preg <- mov (64|32) reg`.
  // MovRP {
  //   dst: PReg,
  //   src: VReg,
  // },
  /// Move from a fixed reg: `reg <- mov (64|32) preg`.
  MovPR {
    dst: VReg,
    src: PReg,
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
  /// Direct call: `call f`.
  CallKnown {
    f: ProcId,
    operands: Box<[Operand]>,
    /// If `clobbers = None` then this call does not return.
    clobbers: Option<PRegSet>,
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
  JmpKnown { dst: BlockId, params: Box<[regalloc2::VReg]> },
  /// Two-way conditional branch: `if cc { jmp taken } else { jmp not_taken }`.
  JmpCond {
    cc: CC,
    taken: BlockId,
    not_taken: BlockId,
  },
  // /// Indirect jump: `jmpq r/m`.
  // JmpUnknown { target: RegMem },
  /// Traps if the condition code is not set.
  /// Otherwise, jumps to the target block.
  Assert { cc: CC, dst: BlockId },
  /// An instruction that will always trigger the illegal instruction exception.
  Ud2,
}

impl Debug for Inst {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use itertools::Itertools;
    struct PrintOperand(Operand);
    impl Display for PrintOperand {
      fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use regalloc2::{OperandKind, OperandConstraint};
        let vreg = VReg(self.0.vreg());
        match self.0.kind() {
          OperandKind::Def => write!(f, "out ")?,
          OperandKind::Use => {}
        }
        match self.0.constraint() {
          OperandConstraint::FixedReg(r) => write!(f, "{vreg} @ {}", PReg(r)),
          OperandConstraint::Reg => write!(f, "{vreg}"),
          _ => unreachable!(),
        }
      }
    }
    match self {
      Self::Fallthrough { dst } => write!(f, "fallthrough -> bb{}", dst.0),
      // Self::LetStart { size } => write!(f, "let_start[{}]", size),
      // Self::LetEnd { dst } => write!(f, "let_end {:?}", dst),
      Self::BlockParam { var, val } => write!(f, "param {var:?} @ {val}"),
      Self::Binop { op, sz, dst, src1, src2 } =>
        write!(f, "{dst} <- {op:?}.{} {src1}, {src2}", sz.bits0()),
      Self::Unop { op, sz, dst, src } =>
        write!(f, "{dst} <- {op:?}.{} {src}", sz.bits0()),
      Self::Mul { sz, dst_lo, dst_hi, src1, src2 } =>
        write!(f, "{dst_hi}:{dst_lo} <- mul.{} {src1}, {src2}", sz.bits0()),
      Self::Imm { sz, dst, src } => write!(f, "{dst} <- imm.{} {src}", sz.bits0()),
      Self::MovRR { dst, src } => write!(f, "{dst} <- mov.64 {src}"),
      Self::MovPR { dst, src } => write!(f, "{dst} <- mov.64 {src}"),
      Self::MovzxRmR { ext_mode, dst, src } =>
        write!(f, "{dst}.{} <- movz {src}.{}", ext_mode.dst().bits0(), ext_mode.src().bits0()),
      Self::Load64 { dst, src } => write!(f, "{dst} <- mov.64 {src}"),
      Self::Lea { sz, dst, addr } => write!(f, "{dst} <- lea.{} {addr}", sz.bits0()),
      Self::MovsxRmR { ext_mode, dst, src } =>
        write!(f, "{dst}.{} <- movs {src}.{}", ext_mode.dst().bits0(), ext_mode.src().bits0()),
      Self::Store { sz, dst, src } => write!(f, "{dst} <- mov.{} {src}", sz.bits0()),
      Self::ShiftImm { sz, kind, num_bits, dst, src } =>
        write!(f, "{dst} <- {kind:?}.{} {src}, {num_bits}", sz.bits0()),
      Self::ShiftRR { sz, kind, dst, src, src2 } =>
        write!(f, "{dst} <- {kind:?}.{} {src}, {src2}", sz.bits0()),
      Self::Cmp { sz, op, src1, src2 } => write!(f, "{op}.{} {src1}, {src2}", sz.bits0()),
      Self::SetCC { cc, dst } => write!(f, "{dst} <- set{cc}"),
      Self::CMov { sz, cc, dst, src1, src2 } =>
        write!(f, "{dst} <- cmov{cc}.{} {src1}, {src2}", sz.bits0()),
      Self::CallKnown { f: func, operands, .. } =>
        write!(f, "call {func:?}({})", operands.iter().map(|&x| PrintOperand(x)).format(", ")),
      Self::SysCall { f: func, operands } =>
        write!(f, "syscall {func:?}({})", operands.iter().map(|&x| PrintOperand(x)).format(", ")),
      Self::Epilogue { params } =>
        write!(f, "epilogue({})", params.iter().map(|&x| PrintOperand(x)).format(", ")),
      Self::JmpKnown { dst, params } =>
        write!(f, "jump -> bb{}({})", dst.0, params.iter().format(", ")),
      Self::JmpCond { cc, taken, not_taken } =>
        write!(f, "j{cc} -> bb{} else bb{}", taken.0, not_taken.0),
      Self::Assert { cc, dst } => write!(f, "assert{cc} -> bb{}", dst.0),
      Self::Ud2 => write!(f, "ud2"),
    }
  }
}

impl VInst for Inst {
  fn is_call(&self) -> bool {
    matches!(self, Inst::CallKnown {..} | Inst::SysCall {..})
  }

  fn is_ret(&self) -> bool {
    matches!(self, Inst::Epilogue {..} | Inst::SysCall { f: SysCall::Exit, .. })
  }

  fn is_branch(&self) -> bool {
    matches!(self,
      Inst::Fallthrough {..} | Inst::Assert {..} | Inst::JmpKnown {..} | Inst::JmpCond {..})
}

  fn branch_blockparams(&self, _: usize) -> &[regalloc2::VReg] {
    match self {
      Inst::JmpKnown { params, .. } => params,
      _ => &[]
    }
  }

  fn is_move(&self) -> Option<(Operand, Operand)> {
    if let Inst::MovRR { dst, src } = *self {
      Some((Operand::reg_use(src.0), Operand::reg_def(dst.0)))
    } else { None }
  }

  fn collect_operands(&self, args: &mut Vec<Operand>) {
    match *self {
      // Inst::LetEnd { dst } => dst.collect_operands(args),
      Inst::BlockParam { val, .. } =>
        val.on_regs(|r| args.push(Operand::new(r.0,
          // regalloc2::OperandConstraint::Any,
          regalloc2::OperandConstraint::Reg, // FIXME
          regalloc2::OperandKind::Use,
          regalloc2::OperandPos::Early,
        ))),
      Inst::Imm { dst, .. } |
      Inst::SetCC { dst, .. } => args.push(Operand::reg_def(dst.0)),
      Inst::Unop { dst, src, .. } |
      Inst::ShiftImm { dst, src, .. } => {
        args.push(Operand::reg_use(src.0));
        args.push(Operand::reg_reuse_def(dst.0, 0));
      }
      Inst::Binop { dst, src1, ref src2, .. } => {
        args.push(Operand::reg_use(src1.0));
        src2.collect_operands(args);
        args.push(Operand::reg_reuse_def(dst.0, 0));
      }
      Inst::Mul { dst_lo, dst_hi, src1, ref src2, .. } => {
        args.push(Operand::reg_fixed_use(src1.0, RAX.0));
        src2.collect_operands(args);
        args.push(Operand::reg_fixed_def(dst_lo.0, RAX.0));
        args.push(Operand::reg_fixed_def(dst_hi.0, RDX.0));
      },
      // Inst::DivRem { dst_div, dst_rem, src1, ref src2, .. } => {
      //   args.push(Operand::reg_fixed_use(src1, RAX));
      //   src2.collect_operands(args);
      //   args.push(Operand::reg_fixed_def(dst_div, RAX));
      //   args.push(Operand::reg_fixed_def(dst_rem, RDX));
      // },
      // Inst::MovRP { dst, src } => args.push(Operand::reg_fixed_use(src, dst)),
      Inst::MovPR { dst, src } => args.push(Operand::reg_fixed_def(dst.0, src.0)),
      Inst::MovzxRmR { dst, ref src, .. } |
      Inst::MovsxRmR { dst, ref src, .. } => {
        src.collect_operands(args);
        args.push(Operand::reg_def(dst.0));
      }
      Inst::Load64 { dst, ref src } => {
        src.collect_operands(args);
        args.push(Operand::reg_def(dst.0));
      }
      Inst::Lea { dst, ref addr, .. } => {
        addr.collect_operands(args);
        args.push(Operand::reg_def(dst.0));
      }
      Inst::Store { ref dst, src, .. } => {
        args.push(Operand::reg_use(src.0));
        dst.collect_operands(args);
      }
      Inst::ShiftRR { dst, src, src2, .. } => {
        args.push(Operand::reg_use(src.0));
        args.push(Operand::reg_fixed_use(src2.0, RCX.0));
        args.push(Operand::reg_reuse_def(dst.0, 0));
      }
      Inst::Cmp { src1, ref src2, .. } => {
        args.push(Operand::reg_use(src1.0));
        src2.collect_operands(args);
      }
      Inst::CMov { dst, src1, ref src2, .. } => {
        args.push(Operand::reg_use(src1.0));
        src2.collect_operands(args);
        args.push(Operand::reg_reuse_def(dst.0, 0));
      }
      Inst::CallKnown { operands: ref params, .. } |
      Inst::SysCall { operands: ref params, .. } |
      Inst::Epilogue { ref params } => args.extend_from_slice(params),
      // Inst::JmpUnknown { target } => target.collect_operands(args),
      // moves are handled specially by regalloc, we don't need operands
      Inst::MovRR { .. } |
      // Jumps have blockparams but no operands
      Inst::JmpKnown { .. } |
      // Other instructions that have no operands
      Inst::Fallthrough { .. } |
      // Inst::LetStart { .. } |
      Inst::JmpCond { .. } |
      Inst::Assert { .. } |
      Inst::Ud2 => {}
    }
  }

  fn clobbers(&self) -> PRegSet {
    match self {
      &Inst::CallKnown { clobbers: Some(cl), .. } => cl,
      Inst::SysCall { f, .. } if f.returns() => [RCX, R11].into_iter().collect(),
      _ => Default::default(),
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

  pub(crate) fn assert(self, dst: BlockId) -> InstId {
    self.0.emit(Inst::Assert { cc: self.1, dst })
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

  #[must_use]
  #[inline] pub(crate) fn emit_copy(&mut self,
    sz: Size, dst: RegMem, src: impl Into<RegMemImm<u64>>
  ) -> cl::Copy {
    fn copy(code: &mut VCode<Inst>, sz: Size, dst: RegMem, src: RegMemImm<u64>) -> cl::Copy {
      match (dst, src) {
        (RegMem::Reg(dst), RegMemImm::Reg(src)) => code.emit(Inst::MovRR { dst, src }),
        (RegMem::Reg(dst), RegMemImm::Mem(src)) => code.emit(Inst::load_mem(sz, dst, src)),
        (RegMem::Reg(dst), RegMemImm::Imm(src)) => code.emit(Inst::Imm { sz, dst, src }),
        (RegMem::Mem(dst), RegMemImm::Reg(src)) => code.emit(Inst::Store { sz, dst, src }),
        _ => {
          let temp = code.fresh_vreg();
          copy(code, sz, temp.into(), src);
          copy(code, sz, dst, temp.into());
          return cl::Copy::Two
        }
      };
      cl::Copy::One
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
pub type PRegMem = RegMem<PReg>;

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

impl Display for PRegMemImm {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      PRegMemImm::Reg(r) => Display::fmt(r, f),
      PRegMemImm::Mem(a) => Display::fmt(a, f),
      PRegMemImm::Imm(i) => Display::fmt(i, f),
    }
  }
}

impl Debug for PRegMemImm {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { Display::fmt(self, f) }
}

/// A representation of x86 assembly instructions.
#[derive(Clone, Copy)]
#[allow(missing_docs)]
pub enum PInst {
  // /// A length 0 no-op instruction.
  // Nop,
  /// Jump to the given block ID. This is required to be the immediately following instruction,
  /// so no code need be emitted.
  Fallthrough { dst: BlockId },
  // /// Ghost instruction: Start of a let statement, together with the size of the data to transfer,
  // /// and the register that will be assigned, that corresponds to the new variable.
  // LetStart { size: u32, dst: PRegMem },
  /// An eliminated identity move instruction.
  MovId,
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
  /// (The 32 bit mov is used for all sizes <= 32)
  Imm {
    sz: Size,
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
    /// True if this is a spill instruction
    spill: bool,
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
    /// True if this is a spill instruction
    spill: bool,
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
  /// Otherwise, jumps to the target block.
  Assert { cc: CC, dst: BlockId },
  /// An instruction that will always trigger the illegal instruction exception.
  Ud2,
}

impl Debug for PInst {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Fallthrough { dst } => write!(f, "fallthrough -> vb{}", dst.0),
      // Self::LetStart { size, dst } => write!(f, "let_start[{}] {:?}", size, dst),
      Self::MovId => write!(f, "mov_id"),
      Self::Binop { op, sz, dst, src } =>
        write!(f, "{dst} <- {op:?}.{} {dst}, {src}", sz.bits0()),
      Self::Unop { op, sz, dst } =>
        write!(f, "{dst} <- {op:?}.{} {dst}", sz.bits0()),
      Self::Mul { sz, src } => write!(f, "rdx:rax <- mul.{} rax, {src}", sz.bits0()),
      Self::Cdx { sz } => write!(f, "rdx:rax <- cdx.{} rax", sz.bits0()),
      Self::DivRem { sz, src } => write!(f, "rax,rdx <- divrem.{} rdx:rax, {src}", sz.bits0()),
      Self::Imm { sz, dst, src } => write!(f, "{dst} <- imm.{} {src}", sz.bits0()),
      Self::MovRR { sz, dst, src } => write!(f, "{dst} <- mov.{} {src}", sz.bits0()),
      Self::MovzxRmR { ext_mode, dst, src } =>
        write!(f, "{dst}.{} <- movz {src}.{}", ext_mode.dst().bits0(), ext_mode.src().bits0()),
      Self::Load64 { spill: false, dst, src } => write!(f, "{dst} <- mov.64 {src}"),
      Self::Load64 { spill: true, dst, src } => write!(f, "{dst} <- mov.64 {src} (spill)"),
      Self::Lea { sz, dst, addr } => write!(f, "{dst} <- lea.{} {addr}", sz.bits0()),
      Self::MovsxRmR { ext_mode, dst, src } =>
        write!(f, "{dst}.{} <- movs {src}.{}", ext_mode.dst().bits0(), ext_mode.src().bits0()),
      Self::Store { spill: false, sz, dst, src } =>
        write!(f, "{dst} <- mov.{} {src}", sz.bits0()),
      Self::Store { spill: true, sz, dst, src } =>
        write!(f, "{dst} <- mov.{} {src} (spill)", sz.bits0()),
      Self::Shift { sz, kind, num_bits: Some(num_bits), dst } =>
        write!(f, "{dst} <- {kind:?}.{} {dst}, {num_bits}", sz.bits0()),
      Self::Shift { sz, kind, num_bits: None, dst } =>
        write!(f, "{dst} <- {kind:?}.{} {dst}, cl", sz.bits0()),
      Self::Cmp { sz, op, src1, src2 } => write!(f, "{op}.{} {src1}, {src2}", sz.bits0()),
      Self::SetCC { cc, dst } => write!(f, "{dst} <- set{cc}"),
      Self::CMov { sz, cc, dst, src } =>
        write!(f, "{dst} <- cmov{cc}.{} {dst}, {src}", sz.bits0()),
      Self::Push64 { src } => write!(f, "push {src}"),
      Self::Pop64 { dst } => write!(f, "pop {dst}"),
      Self::CallKnown { f: func } => write!(f, "call {func:?}"),
      Self::SysCall => write!(f, "syscall"),
      Self::Ret => write!(f, "ret"),
      Self::JmpKnown { dst, short: true } => write!(f, "jump -> vb{}", dst.0),
      Self::JmpKnown { dst, short: false } => write!(f, "jump -> far vb{}", dst.0),
      Self::JmpCond { cc, dst, short: true } => write!(f, "j{cc} -> vb{}", dst.0),
      Self::JmpCond { cc, dst, short: false } => write!(f, "j{cc} -> far vb{}", dst.0),
      Self::Assert { cc, dst } => write!(f, "assert{cc} -> vb{}", dst.0),
      Self::Ud2 => write!(f, "ud2"),
    }
  }
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

impl PInst {
  /// Returns true if this is a spill instruction (added by regalloc)
  #[must_use] pub fn is_spill(&self) -> bool {
    matches!(self,
      Self::MovRR { .. } |
      Self::Load64 { spill: true, .. } |
      Self::Store { spill: true, .. })
  }
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
  /// No instruction.
  Ghost,
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
  /// `decodeMov64` layout: `1011vrrr + imm32/64` (32 bit if bool is false)
  Mov64(bool),
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
      Self::Ghost => 0,
      Self::Ret | Self::Cdx | Self::PushReg | Self::PopReg => 1, // opcode
      Self::BinopRAX(b) | Self::PushImm(b) |
      Self::Jump(b) | Self::TestRAX(b) => 1 + sz32(b), // opcode + imm8/32
      Self::Jcc8 | // opcode + imm8
      Self::Ud2 | Self::SysCall => 2, // 0F + opcode
      Self::Assert => 4, // jcc8 + ud2
      Self::Mov64(false) | Self::Call => 5, // opcode + imm32
      Self::Jcc => 6, // 0F + opcode + imm32
      Self::Mov64(true) => 9, // opcode + imm64
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
  #[must_use] pub fn len(self) -> u8 { u8::from(self.rex) + self.opc.len() }
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
    Offset::Spill(..) => unreachable!(),
    _ => DispLayout::S32,
  }
}

fn layout_opc_reg(rex: &mut bool, rm: PReg) -> ModRMLayout {
  *rex |= rm.large();
  ModRMLayout::Reg
}

fn layout_opc_mem(rex: &mut bool, a: &PAMode) -> ModRMLayout {
  if a.base.is_valid() { *rex |= a.base.large() }
  if let Some(si) = a.si { *rex |= si.index.large() }
  match a {
    _ if !a.base().is_valid() => ModRMLayout::Sib0,
    PAMode {off, si: None, ..} if a.base().index() & 7 != 4 =>
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
  *rex |= r.large();
  layout_opc_reg(rex, rm)
}

fn layout_mem(rex: &mut bool, r: PReg, a: &PAMode) -> ModRMLayout {
  *rex |= r.large();
  layout_opc_mem(rex, a)
}

fn layout_rm(rex: &mut bool, r: PReg, rm: &PRegMem) -> ModRMLayout {
  *rex |= r.large();
  layout_opc_rm(rex, rm)
}

fn layout_rmi(rex: &mut bool, r: PReg, rm: &PRegMemImm) -> ModRMLayout {
  *rex |= r.large();
  layout_opc_rmi(rex, rm)
}

fn high_reg(rex: &mut bool, r: PReg) { *rex |= r.index() & 4 != 0 }

fn high_amode(rex: &mut bool, a: &PAMode) {
  if a.base.is_valid() { high_reg(rex, a.base) }
  if let Some(si) = &a.si { high_reg(rex, si.index) }
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
    let rax_layout = OpcodeLayout::BinopRAX(sz != Size::S8);
    if rax_layout.len() <= opc.len() { opc = rax_layout }
  }
  InstLayout { rex, opc }
}

impl PInst {
  pub(crate) fn len(&self) -> u8 { self.layout_inst().len() }

  #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
  pub(crate) fn layout_inst(&self) -> InstLayout {
    match *self {
      PInst::Fallthrough { .. } |
      // PInst::LetStart { .. } |
      PInst::MovId => InstLayout { rex: false, opc: OpcodeLayout::Ghost },
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
             return layout_binop_lo(Size::S32, dst, &PRegMemImm::Reg(dst))
          }
          (Size::S64, _) if src as i32 as u64 == src =>
            OpcodeLayout::MovImm(layout_opc_reg(&mut true, dst)),
          _ => OpcodeLayout::Mov64(sz == Size::S64),
        };
        InstLayout { rex: sz == Size::S64 || dst.large(), opc }
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
      PInst::Load64 { spill: _, dst, ref src } =>
        InstLayout { opc: OpcodeLayout::MovReg(layout_mem(&mut true, dst, src)), rex: true },
      PInst::Lea { sz, dst, ref addr } => {
        let mut rex = sz == Size::S64;
        InstLayout { opc: OpcodeLayout::Lea(layout_mem(&mut rex, dst, addr)), rex }
      }
      PInst::Store { spill: _, sz, ref dst, src } => {
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
          PRegMemImm::Imm(_) => match src1 {
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
      PInst::CMov { sz, dst, ref src, .. } => {
        let mut rex = sz == Size::S64;
        InstLayout { opc: OpcodeLayout::CMov(layout_rm(&mut rex, dst, src)), rex }
      }
      PInst::Push64 { ref src } => {
        let mut rex = false;
        let opc = match *src {
          PRegMemImm::Imm(i) => OpcodeLayout::PushImm(i as i8 as u32 != i),
          PRegMemImm::Reg(r) => { rex |= r.large(); OpcodeLayout::PushReg }
          PRegMemImm::Mem(ref a) => OpcodeLayout::Hi(layout_opc_mem(&mut rex, a))
        };
        InstLayout { rex, opc }
      }
      PInst::Pop64 { dst } => InstLayout { opc: OpcodeLayout::PopReg, rex: dst.large() },
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
        PInst::Binop { op, sz, dst, src } => (sz, dst, src, op as u8),
        PInst::Cmp { sz, op: Cmp::Cmp, src1, src2 } => (sz, src1, src2, 7),
        PInst::Imm { sz: _, dst, src: 0 } =>
          (Size::S32, dst, PRegMemImm::Reg(dst), Binop::Xor as u8),
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
      encode_reg8(preg.index(), rex, x)
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
      write_opc_modrm(modrm, rex, buf, arg1.index(), arg2)
    }

    fn push_u8_u32(sz32: bool, buf: &mut InstSink<'_>, src: u32) {
      if sz32 { buf.push_u32(src) } else { buf.push_u8(src as u8) }
    }

    let layout = self.layout_inst();
    buf.update_rip(layout.len());
    if layout.rex { buf.push_u8(0) }
    let mut rex = 0;
    match (layout.opc, self) {
      (OpcodeLayout::Ghost, _) => {}
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
          PInst::Load64 { spill: _, dst, src } =>
            (0x8a + op_size_w(&mut rex, Size::S64), dst, src.into()),
          PInst::Store { spill: _, sz, dst, src } =>
            (0x88 + op_size_w(&mut rex, sz), src, dst.into()),
          _ => unreachable!(),
        };
        buf.push_u8(op);
        write_modrm(modrm, &mut rex, buf, r, rm);
      }
      (OpcodeLayout::Mov64(false), &PInst::Imm { sz: _, dst, src }) => {
        buf.push_u8(0xb8 + encode_reg(dst, &mut rex, REX_B));
        buf.push_u32(src as u32);
      }
      (OpcodeLayout::Mov64(true), &PInst::Imm { sz: Size::S64, dst, src }) => {
        buf.push_u8(0xb8 + encode_reg(dst, &mut rex, REX_B)); rex |= REX_W;
        buf.push_u64(src);
      }
      (OpcodeLayout::MovImm(modrm), &PInst::Imm { sz, dst, src }) => {
        buf.push_u8(0xc6 + op_size_w(&mut rex, sz.max(Size::S32)));
        write_opc_modrm(modrm, &mut rex, buf, 0, PRegMem::Reg(dst));
        buf.push_u32(src as u32);
      }
      (OpcodeLayout::PushImm(b), &PInst::Push64 { src: PRegMemImm::Imm(src) }) => {
        buf.push_u8(0x68 + (u8::from(!b) << 2));
        push_u8_u32(b, buf, src);
      }
      (OpcodeLayout::PushReg, &PInst::Push64 { src: PRegMemImm::Reg(src) }) =>
        buf.push_u8(0x50 + encode_reg(src, &mut rex, REX_B)),
      (OpcodeLayout::PopReg, &PInst::Pop64 { dst }) =>
        buf.push_u8(0x58 + encode_reg(dst, &mut rex, REX_B)),
      (OpcodeLayout::Jump(b), &PInst::JmpKnown { short, dst }) => {
        let dst = buf.rip_relative_block(dst);
        assert!(short != b);
        buf.push_u8(0xe9 + (u8::from(short) << 1));
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
        assert!(op_size_w(&mut rex, sz.max(Size::S32)) == 1);
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
        buf.push_u8(opc + u8::from(ext_mode.src() == Size::S16));
        write_modrm(modrm, &mut rex, buf, dst, src);
      }
      (OpcodeLayout::Jcc, &PInst::JmpCond { cc, short: false, dst }) => {
        let dst = buf.rip_relative_block(dst);
        buf.push_u8(0x0f);
        buf.push_u8(0x80 + cc as u8);
        buf.push_u32(dst as u32);
      }
      (OpcodeLayout::SysCall, PInst::SysCall) => { buf.push_u8(0x0f); buf.push_u8(0x05); }
      (OpcodeLayout::Assert, &PInst::Assert { cc, .. }) => {
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
