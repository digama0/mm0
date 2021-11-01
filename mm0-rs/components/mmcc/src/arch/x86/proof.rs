//! X86-specific types used in the proof API.

use crate::proof::Inst;

use super::CC;

impl<'a> Inst<'a> {
  /// The REX byte and the opcode portion of the instruction.
  pub fn layout(&self) -> InstLayout {
    self.layout.parse(&mut self.content())
  }
}

fn parse_arr<const N: usize>(p: &mut &[u8]) -> [u8; N] {
  let (start, rest) = p.split_at(N);
  *p = rest;
  start.try_into().expect("parse error")
}
fn parse_u8(p: &mut &[u8]) -> u8 { parse_arr::<1>(p)[0] }
fn parse_u32(p: &mut &[u8]) -> u32 { u32::from_le_bytes(parse_arr(p)) }
fn parse_u64(p: &mut &[u8]) -> u64 { u64::from_le_bytes(parse_arr(p)) }

/// The layout for an instruction.
#[derive(Clone, Copy, Debug)]
pub struct InstLayout {
  /// The REX byte, if present (`Some(0..16)` or `None`)
  pub rex: Option<u8>,
  /// The main layout,
  pub opc: OpcodeLayout,
}

impl super::InstLayout {
  fn parse(self, p: &mut &[u8]) -> InstLayout {
    InstLayout {
      rex: if self.rex { Some(parse_u8(p) & 15) } else { None },
      opc: self.opc.parse(p),
    }
  }
}

/// The layout of the opcode byte and everything after it.
#[derive(Clone, Copy, Debug)]
#[allow(missing_docs)]
pub enum OpcodeLayout {
  /// `decodeBinopRAX` layout for 8-bit operand: `00ooo01v + imm8`
  BinopRAX8 { opc: u8, v: bool, imm: u8 },
  /// `decodeBinopRAX` layout for 32-bit operand: `00ooo01v + imm32`
  BinopRAX32 { opc: u8, v: bool, imm: u32 },
  /// `decodeBinopImm` layout for 8-bit operand: `1000000v + modrm + imm8`
  BinopImmS8 { v: bool, modrm: ModRMLayout, imm: u8 },
  /// `decodeBinopImm` layout for 32-bit operand: `1000000v + modrm + imm32`
  BinopImmS32 { v: bool, modrm: ModRMLayout, imm: u32 },
  /// `decodeBinopImm8` layout: `0x83 + modrm + imm8`
  BinopImm8 { modrm: ModRMLayout, imm: u8 },
  /// `decodeBinopReg` layout: `00ooo0dv + modrm`
  BinopReg { opc: u8, d: bool, v: bool, modrm: ModRMLayout },
  /// `decodeBinopHi` layout: `1100000v + modrm + imm8`
  BinopHi { v: bool, modrm: ModRMLayout, imm: u8 },
  /// `decodeBinopHiReg` layout with immediate 1: `1101000v + modrm`
  BinopHi1 { v: bool, modrm: ModRMLayout },
  /// `decodeBinopHiReg` layout: `1101001v + modrm`
  BinopHiReg { v: bool, modrm: ModRMLayout },
  /// `decodeMovSX` layout: `0x63 + modrm`
  MovSX { modrm: ModRMLayout },
  /// `decodeMovReg` layout: `100010dv + modrm`
  MovReg { d: bool, v: bool, modrm: ModRMLayout },
  /// `decodeMov64` layout, but for 32 bit: `1011vrrr + imm32`
  Mov32 { v: bool, r: u8, imm: u32 },
  /// `decodeMov64` layout: `1011vrrr + imm64`
  Mov64 { v: bool, r: u8, imm: u64 },
  /// `decodeMovImm` layout: `1100011v + modrm + imm32`
  MovImm { v: bool, modrm: ModRMLayout, imm: u32 },
  /// `decodePushImm` layout with 8 bit immediate: `0x6A + imm8`
  PushImm8 { imm: u8 },
  /// `decodePushImm` layout with 32 bit immediate: `0x68 + imm32`
  PushImm32 { imm: u32 },
  /// `decodePushReg` layout: `01010rrr`
  PushReg { r: u8 },
  /// `decodePopReg` layout: `01011rrr`
  PopReg { r: u8 },
  /// `decodeJump` layout with 8 bit immediate: `0xEB + imm8`
  Jump8 { imm: u8 },
  /// `decodeJump` layout with 32 bit immediate: `0xE9 + imm32`
  Jump32 { imm: u32 },
  /// `decodeJCC8` layout: `0111cccc + imm8`
  Jcc8 { cc: u8, imm: u8 },
  /// `decodeCall` layout: `0xE8 + imm32`
  Call { imm: u32 },
  /// `decodeRet` layout: `0xC3`
  Ret,
  /// `decodeLea` layout: `0x8D + modrm`
  Lea { modrm: ModRMLayout },
  /// `decodeTest` layout: `1000010v + modrm`
  Test { v: bool, modrm: ModRMLayout },
  /// `decodeTestRAX` layout with 8 bit immediate: `1010100v + imm8`
  TestRAX8 { v: bool, imm: u8 },
  /// `decodeTestRAX` layout with 32 bit immediate: `1010100v + imm32`
  TestRAX32 { v: bool, imm: u32 },
  /// `decodeHi` layout: `1111x11v + modrm`
  Hi { x: bool, v: bool, modrm: ModRMLayout },
  /// `decodeHi` layout for `Test` with 8 bit immediate: `1111x11v + modrm + imm8`
  HiTest8 { x: bool, v: bool, modrm: ModRMLayout, imm: u8 },
  /// `decodeHi` layout for `Test` with 32 bit immediate: `1111x11v + modrm + imm32`
  HiTest32 { x: bool, v: bool, modrm: ModRMLayout, imm: u32 },
  /// `decodeTwoSetCC` layout: `0x0F + 1001cccc + modrm`
  SetCC { cc: u8, modrm: ModRMLayout },
  /// `decodeTwoCMov` layout: `0x0F + 0100cccc + modrm`
  CMov { cc: u8, modrm: ModRMLayout },
  /// `decodeTwoMovX` layout: `0x0F + 1011s11v + modrm`
  MovX { s: bool, v: bool, modrm: ModRMLayout },
  /// `decodeTwoJCC` layout: `0x0F + 1000cccc + imm32`
  Jcc { cc: u8, imm: u32 },
  /// `decodeTwoSysCall` layout: `0x0F 0x05`
  SysCall,
  /// `assert` pseudo-instruction: `jcc cond l; ud2; l:`
  Assert { cc: u8 },
  /// `ud2` instruction: `0x0F 0x0B`
  Ud2,
}

impl super::OpcodeLayout {
  /// The REX byte and the opcode portion of the instruction.
  fn parse(self, p: &mut &[u8]) -> OpcodeLayout {
    let opc = parse_u8(p);
    match self {
      Self::BinopRAX(false) =>
        OpcodeLayout::BinopRAX8 { opc: (opc >> 3) & 7, v: opc & 1 != 0, imm: parse_u8(p) },
      Self::BinopRAX(true) =>
        OpcodeLayout::BinopRAX32 { opc: (opc >> 3) & 7, v: opc & 1 != 0, imm: parse_u32(p) },
      Self::BinopImm(false, modrm) =>
        OpcodeLayout::BinopImmS8 { v: opc & 1 != 0, modrm: modrm.parse(p), imm: parse_u8(p) },
      Self::BinopImm(true, modrm) =>
        OpcodeLayout::BinopImmS32 { v: opc & 1 != 0, modrm: modrm.parse(p), imm: parse_u32(p) },
      Self::BinopImm8(modrm) =>
        OpcodeLayout::BinopImm8 { modrm: modrm.parse(p), imm: parse_u8(p) },
      Self::BinopReg(modrm) => OpcodeLayout::BinopReg {
        opc: (opc >> 3) & 7, d: opc & 2 != 0, v: opc & 1 != 0, modrm: modrm.parse(p)
      },
      Self::BinopHi(modrm) =>
        OpcodeLayout::BinopHi { v: opc & 1 != 0, modrm: modrm.parse(p), imm: parse_u8(p) },
      Self::BinopHi1(modrm) => OpcodeLayout::BinopHi1 { v: opc & 1 != 0, modrm: modrm.parse(p) },
      Self::BinopHiReg(modrm) =>
        OpcodeLayout::BinopHiReg { v: opc & 1 != 0, modrm: modrm.parse(p) },
      Self::MovSX(modrm) => OpcodeLayout::MovSX { modrm: modrm.parse(p) },
      Self::MovReg(modrm) =>
        OpcodeLayout::MovReg { d: opc & 2 != 0, v: opc & 1 != 0, modrm: modrm.parse(p) },
      Self::Mov32 => OpcodeLayout::Mov32 { v: opc & 8 != 0, r: opc & 7, imm: parse_u32(p) },
      Self::Mov64 => OpcodeLayout::Mov64 { v: opc & 8 != 0, r: opc & 7, imm: parse_u64(p) },
      Self::MovImm(modrm) =>
        OpcodeLayout::MovImm { v: opc & 1 != 0, modrm: modrm.parse(p), imm: parse_u32(p) },
      Self::PushImm(false) => OpcodeLayout::PushImm8 { imm: parse_u8(p) },
      Self::PushImm(true) => OpcodeLayout::PushImm32 { imm: parse_u32(p) },
      Self::PushReg => OpcodeLayout::PushReg { r: opc & 7 },
      Self::PopReg => OpcodeLayout::PopReg { r: opc & 7 },
      Self::Jump(false) => OpcodeLayout::Jump8 { imm: parse_u8(p) },
      Self::Jump(true) => OpcodeLayout::Jump32 { imm: parse_u32(p) },
      Self::Jcc8 => OpcodeLayout::Jcc8 { cc: opc & 15, imm: parse_u8(p) },
      Self::Call => OpcodeLayout::Call { imm: parse_u32(p) },
      Self::Ret => OpcodeLayout::Ret,
      Self::Lea(modrm) => OpcodeLayout::Lea { modrm: modrm.parse(p) },
      Self::Test(modrm) => OpcodeLayout::Test { v: opc & 1 != 0, modrm: modrm.parse(p) },
      Self::TestRAX(false) => OpcodeLayout::TestRAX8 { v: opc & 1 != 0, imm: parse_u8(p) },
      Self::TestRAX(true) => OpcodeLayout::TestRAX32 { v: opc & 1 != 0, imm: parse_u32(p) },
      Self::Hi(modrm) =>
        OpcodeLayout::Hi { x: opc & 8 != 0, v: opc & 1 != 0, modrm: modrm.parse(p) },
      Self::HiTest(false, modrm) => OpcodeLayout::HiTest8 {
        x: opc & 8 != 0, v: opc & 1 != 0, modrm: modrm.parse(p), imm: parse_u8(p)
      },
      Self::HiTest(true, modrm) => OpcodeLayout::HiTest32 {
        x: opc & 8 != 0, v: opc & 1 != 0, modrm: modrm.parse(p), imm: parse_u32(p)
      },
      Self::SetCC(modrm) => OpcodeLayout::SetCC { cc: opc & 15, modrm: modrm.parse(p) },
      Self::CMov(modrm) => OpcodeLayout::CMov { cc: opc & 15, modrm: modrm.parse(p) },
      Self::MovX(modrm) =>
        OpcodeLayout::MovX { s: opc & 8 != 0, v: opc & 1 != 0, modrm: modrm.parse(p) },
      Self::Jcc => OpcodeLayout::Jcc { cc: opc & 15, imm: parse_u32(p) },
      Self::SysCall => OpcodeLayout::SysCall,
      Self::Assert => OpcodeLayout::Assert { cc: opc & 15 },
      Self::Ud2 => OpcodeLayout::Ud2,
      _ => unreachable!(),
    }
  }
}

/// Layout of the Mod/RM and SIB bytes.
#[derive(Clone, Copy, Debug)]
#[allow(clippy::upper_case_acronyms, missing_docs)]
pub enum ModRMLayout {
  /// `11ooonnn` where `rn = o` and `rm = reg(n)`
  Reg { rn: u8, rm: u8 },
  /// `00ooo101 + imm32` where `rn = o` and `rm = [RIP + imm32]`
  RIP { rn: u8, imm: u32 },
  /// `00ooo100 + ssiii101 + imm32` where `rn = o` and `rm = [0 + sc*ix + imm32]`
  Sib0 { rn: u8, scale: u8, index: u8, imm: u32 },
  /// `mmooo100 + ssiiibbb + disp0/8/32` where `rn = o` and `rm = [reg(b) + sc*ix + disp]`
  SibReg { rn: u8, scale: u8, index: u8, base: u8, disp: DispLayout },
  /// `mmooonnn + disp0/8/32` where `rn = o` and `rm = [reg(n) + disp]`
  Disp { rn: u8, base: u8, disp: DispLayout },
}

impl super::ModRMLayout {
  fn parse(self, p: &mut &[u8]) -> ModRMLayout {
    let opc = parse_u8(p);
    let (rn, rm) = ((opc >> 3) & 7, opc & 7);
    match self {
      Self::Reg => ModRMLayout::Reg { rn, rm },
      Self::RIP => ModRMLayout::RIP { rn, imm: parse_u32(p) },
      Self::Sib0 => {
        let sib = parse_u8(p);
        ModRMLayout::Sib0 { rn, scale: sib >> 6, index: (sib >> 3) & 7, imm: parse_u32(p) }
      }
      Self::SibReg(disp) => {
        let sib = parse_u8(p);
        ModRMLayout::SibReg {
          rn, scale: sib >> 6, index: (sib >> 3) & 7, base: sib & 7, disp: disp.parse(p)
        }
      }
      Self::Disp(disp) => ModRMLayout::Disp { rn, base: rm, disp: disp.parse(p) },
    }
  }
}

/// The layout of a displacement, used in [`ModRMLayout`].
#[derive(Clone, Copy, Debug)]
#[repr(u8)]
#[allow(variant_size_differences)]
pub enum DispLayout {
  /// 0 byte immediate, `mm = 00`
  S0,
  /// 1 byte immediate, `mm = 01`
  S8(u8),
  /// 4 byte immediate, `mm = 10`
  S32(u32),
}

impl super::DispLayout {
  fn parse(self, p: &mut &[u8]) -> DispLayout {
    match self {
      Self::S0 => DispLayout::S0,
      Self::S8 => DispLayout::S8(parse_u8(p)),
      Self::S32 => DispLayout::S32(parse_u32(p)),
    }
  }
}

impl DispLayout {
  fn mod_(&self) -> u8 {
    match self {
      DispLayout::S0 => 0,
      DispLayout::S8(_) => 1,
      DispLayout::S32(_) => 2,
    }
  }
}
