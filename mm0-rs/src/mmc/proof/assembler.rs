#![warn(unused)]
use std::collections::HashMap;

use mmcc::{Symbol, TEXT_START, types::Size};
use mmcc::arch::{ExtMode, OpcodeLayout, PInst, PRegMemImm, Unop};
use mmcc::proof::{AssemblyItem, AssemblyItemIter, ElfProof, Inst, Proc};
use crate::{Elaborator, FileSpan, Modifiers, Span, TermId, ThmId, elab::Result, mmc::proof::Name};

use super::{Dedup, ExprDedup, Mangler, Predefs, ProofDedup, ProofId,
  norm_num::{HexCache, Num}, predefs::Rex};

struct BuildAssemblyProc<'a> {
  // elab: &'a mut Elaborator,
  thm: ProofDedup<'a>,
  hex: HexCache,
  start: Num,
}

impl<'a> std::ops::Deref for BuildAssemblyProc<'a> {
  type Target = ProofDedup<'a>;
  fn deref(&self) -> &Self::Target { &self.thm }
}
impl<'a> std::ops::DerefMut for BuildAssemblyProc<'a> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.thm }
}

fn parse_slice<'a>(p: &mut &'a [u8], n: usize) -> &'a [u8] {
  let (start, rest) = p.split_at(n);
  *p = rest;
  start
}
fn parse_arr<const N: usize>(p: &mut &[u8]) -> [u8; N] {
  parse_slice(p, N).try_into().expect("parse error")
}
fn parse_u8(p: &mut &[u8]) -> u8 { parse_arr::<1>(p)[0] }
fn parse_u32(p: &mut &[u8]) -> u32 { u32::from_le_bytes(parse_arr(p)) }

#[allow(clippy::cast_possible_wrap)]
fn parse_i8_64(p: &mut &[u8]) -> i64 { i64::from(parse_u8(p) as i8) }

#[allow(clippy::cast_possible_wrap)]
fn parse_i32_64(p: &mut &[u8]) -> i64 { i64::from(parse_u32(p) as i32) }

type P<A> = (A, ProofId);

impl BuildAssemblyProc<'_> {
  // fn pp(&mut self, i: ProofId) -> String {
  //   let mut s = String::new();
  //   self.thm.pp(self.elab, i, &mut s).expect("impossible");
  //   s
  // }

  fn bool(&mut self, b: bool) -> P<bool> {
    (b, if b { app!(self, (tru)) } else { app!(self, (fal)) })
  }

  fn dn(&mut self, i: u8) -> P<u8> { (i, app!(self, (dn[i]))) }
  fn xn(&mut self, i: u8) -> P<u8> { (i, app!(self, (h2n {self.hex[i]}))) }

  /// Proves `(a, |- bit x[hex] d[i] = d[a])`
  fn xbit(&mut self, hex: u8, i: u8) -> (P<u8>, ProofId) {
    let a = self.dn((hex >> i) & 1);
    (a, thm!(self.thm, CACHE[xbit[hex][i]]: (bit (h2n {self.hex[hex]}) (dn[i])) = {a.1}))
  }

  /// Proves `(a, |- a -ZN b = c)` given `b` and `c`.
  #[allow(clippy::cast_sign_loss)]
  fn znsub_left(&mut self, b: Num, c: i64) -> (Num, ProofId) {
    let a = self.hex.from_u64(&mut self.thm, b.val.wrapping_add(c as u64));
    if c < 0 {
      let c = self.hex.from_u64(&mut self.thm, !c as u64);
      let (_, h) = self.hex.adc(&mut self.thm, true, a, c);
      (a, thm!(self.thm, znsub_negZ(*a, *b, *c, h): (znsub {*a} {*b}) = (negZ {*c})))
    } else {
      let c = self.hex.from_u64(&mut self.thm, c as u64);
      let (_, h) = self.hex.add(&mut self.thm, b, c);
      (a, thm!(self.thm, znsub_posZ(*a, *b, *c, h): (znsub {*a} {*b}) = (posZ {*c})))
    }
  }

  /// Proves `(a, |- REX_[B/X/R/W] rex = d[a])`
  fn rex_val(&mut self, rex: P<Option<u8>>, val: Rex) -> (P<u8>, ProofId) {
    let i = val as u8;
    if let Some(n) = rex.0 {
      let srex = self.xn(n);
      let (a, th) = self.xbit(n, i);
      (a, thm!(self.thm, REX_Si[i](a.1, srex.1, th): ((REX[i]) {rex.1}) = {a.1}))
    } else {
      let a = self.dn(0);
      (a, thm!(self.thm, REX_0[i](): ((REX[i]) {rex.1}) = {a.1}))
    }
  }

  /// Proves `[a, |- opSize have_rex w v = a]`
  fn op_size(&mut self, have_rex: bool, w: P<u8>, v: P<u8>) -> [ProofId; 2] {
    let r = self.bool(have_rex);
    if v.0 == 0 {
      let a = app!(self, (wSz8 {r.1}));
      [a, thm!(self, opSize_8(r.1, w.1): (opSize {r.1} {w.1} {v.1}) = a)]
    } else if w.0 == 0 {
      let a = app!(self, (wSz32));
      [a, thm!(self, opSize_32(r.1): (opSize {r.1} {w.1} {v.1}) = a)]
    } else {
      let a = app!(self, (wSz64));
      [a, thm!(self, opSize_64(r.1): (opSize {r.1} {w.1} {v.1}) = a)]
    }
  }

  /// Proves `[a, |- opSizeW rex v = a]`
  fn op_size_w(&mut self, rex: P<Option<u8>>, v: P<u8>) -> [ProofId; 2] {
    if let Some(srex) = rex.0 {
      let (w, h1) = self.xbit(srex, 3);
      let srex = self.xn(srex);
      let [a, h2] = self.op_size(true, w, v);
      [a, thm!(self.thm, opSizeW_S(a, srex.1, v.1, w.1, h1, h2): (opSizeW {rex.1} {v.1}) = a)]
    } else {
      let [a, h] = self.op_size(false, (0, rex.1), v);
      [a, thm!(self.thm, opSizeW_0(a, v.1, h): (opSizeW {rex.1} {v.1}) = a)]
    }
  }

  /// Proves `[k, n, s, |- parseIBytesPos k n s]`.
  /// The bytes to parse come from the first `k+1` bytes of `p`.
  fn parse_ibytes_pos(&mut self, p: &mut &[u8], k: u8) -> [ProofId; 4] {
    let head = parse_slice(p, k.into());
    let byte = parse_u8(p);
    let k = app!(self.thm, (d0));
    let (a1, a0) = (byte >> 4, byte & 15);
    let (e1, e0) = (self.hex[a1], self.hex[a0]);
    let mut is_zero;
    let s = app!(self.thm, (s1 (ch e1 e0)));
    let mut out = if a1 == 0 {
      is_zero = a0 == 0;
      let n = app!(self.thm, (h2n e0));
      [k, n, s, thm!(self.thm, parseIBytesPos01(e0): (parseIBytesPos k n s))]
    } else {
      is_zero = false;
      assert!(a1 < 8);
      let n = app!(self.thm, (hex (h2n e1) e0));
      let th = thm!(self.thm, decltn[a1][8_usize](): (h2n e1) < (h2n {self.hex[8]}));
      [k, n, s, thm!(self.thm, parseIBytesPos02(e0, e1, th): (parseIBytesPos k n s))]
    };
    for &byte in head.iter().rev() {
      let [k, n, s, th] = out;
      let (a1, a0) = (byte >> 4, byte & 15);
      let (e1, e0) = (self.hex[a1], self.hex[a0]);
      let k2 = app!(self.thm, (suc k));
      let s2 = app!(self.thm, (scons (ch e1 e0) s));
      out = if is_zero {
        if a1 == 0 {
          is_zero &= a0 == 0;
          let n2 = app!(self.thm, (h2n e0));
          [k2, n2, s2, thm!(self.thm,
            parseIBytesPosS1(e0, k, s, th): (parseIBytesPos k2 n2 s2))]
        } else {
          is_zero = false;
          let n2 = app!(self.thm, (hex (h2n e1) e0));
          [k2, n2, s2, thm!(self.thm,
            parseIBytesPosS2(e0, e1, k, s, th): (parseIBytesPos k2 n2 s2))]
        }
      } else {
        let n2 = app!(self.thm, (hex (hex n e1) e0));
        [k2, n2, s2, thm!(self.thm,
          parseIBytesPosS(e0, e1, k, n, s, th): (parseIBytesPos k2 n2 s2))]
      }
    }
    out
  }

  /// Proves `[k, n, s, |- parseIBytesNeg k n s]`.
  /// The bytes to parse come from the first `k+1` bytes of `p`.
  fn parse_ibytes_neg(&mut self, p: &mut &[u8], k: u8) -> [ProofId; 4] {
    let head = parse_slice(p, k.into());
    let byte = parse_u8(p);
    let k = app!(self.thm, (d0));
    let xf = app!(self.thm, (h2n {self.hex[15]}));
    let (c1, c0, a1, a0) = (byte >> 4, byte & 15, !byte >> 4, !byte & 15);
    let (ec1, ec0, ea1, ea0) = (self.hex[c1], self.hex[c0], self.hex[a1], self.hex[a0]);
    let mut is_zero;
    let s = app!(self.thm, (s1 (ch ec1 ec0)));
    let th0 = thm!(self.thm, decaddn[a0][c0](): (ea0 + ec0) = xf);
    let mut out = if a1 == 0 {
      is_zero = a0 == 0;
      let n = app!(self.thm, (h2n ea0));
      [k, n, s, thm!(self.thm, parseIBytesNeg01(ea0, ec0, th0): (parseIBytesNeg k n s))]
    } else {
      is_zero = false;
      assert!(a1 < 8);
      let n = app!(self.thm, (hex (h2n ea1) ea0));
      let th1 = thm!(self.thm, decaddn[a1][c1](): (ea1 + ec1) = xf);
      let th = thm!(self.thm, decltn[a1][8_usize](): (h2n ea1) < (h2n {self.hex[8]}));
      [k, n, s, thm!(self.thm, parseIBytesNeg02(ea0, ea1, ec0, ec1, th0, th1, th):
        (parseIBytesNeg k n s))]
    };
    for &byte in head.iter().rev() {
      let [k, n, s, th] = out;
      let (c1, c0, a1, a0) = (byte >> 4, byte & 15, !byte >> 4, !byte & 15);
      let (ec1, ec0, ea1, ea0) = (self.hex[c1], self.hex[c0], self.hex[a1], self.hex[a0]);
      let k2 = app!(self.thm, (suc k));
      let s2 = app!(self.thm, (scons (ch ec1 ec0) s));
      let th0 = thm!(self.thm, decaddn[a0][c0](): (ea0 + ec0) = xf);
      let th1 = thm!(self.thm, decaddn[a1][c1](): (ea1 + ec1) = xf);
      out = if is_zero {
        if a1 == 0 {
          let n2 = app!(self.thm, (h2n ea0));
          if a0 == 0 {
            [k2, n2, s2, thm!(self.thm, parseIBytesNegS0(k, s, th): (parseIBytesNeg k2 n2 s2))]
          } else {
            is_zero = false;
            [k2, n2, s2, thm!(self.thm,
              parseIBytesNegS1(ea0, ec0, k, s, th0, th): (parseIBytesNeg k2 n2 s2))]
          }
        } else {
          is_zero = false;
          let n2 = app!(self.thm, (hex (h2n ea1) ea0));
          [k2, n2, s2, thm!(self.thm,
            parseIBytesNegS2(ea0, ea1, ec0, ec1, k, s, th0, th1, th): (parseIBytesNeg k2 n2 s2))]
        }
      } else {
        let n2 = app!(self.thm, (hex (hex n ea1) ea0));
        [k2, n2, s2, thm!(self.thm,
          parseIBytesNegS(ea0, ea1, ec0, ec1, k, n, s, th0, th1, th): (parseIBytesNeg k2 n2 s2))]
      }
    }
    out
  }

  /// Proves `[k, imm, s, |- parseImmN k imm s]`.
  /// The bytes to parse come from the first `k+1` bytes of `p`.
  fn parse_imm_n(&mut self, p: &mut &[u8], k: u8) -> [ProofId; 4] {
    if p[usize::from(k)] < 128 {
      let [k, imm, s, th] = self.parse_ibytes_pos(p, k);
      let imm2 = app!(self.thm, (posZ imm));
      [k, imm2, s, thm!(self.thm, parseImmN_pos(k, imm, s, th): (parseImmN k imm2 s))]
    } else {
      let [k, imm, s, th] = self.parse_ibytes_neg(p, k);
      let imm2 = app!(self.thm, (negZ imm));
      [k, imm2, s, thm!(self.thm, parseImmN_neg(k, imm, s, th): (parseImmN k imm2 s))]
    }
  }

  /// Proves `[imm, s, |- parseImm8 imm s]`
  fn parse_imm_8(&mut self, p: &mut &[u8]) -> [ProofId; 3] {
    let [_, imm, s, th] = self.parse_imm_n(p, 0);
    [imm, s, thm!(self.thm, parseImm8_I(imm, s, th): (parseImm8 imm s))]
  }

  /// Proves `[imm, s, |- parseImm32 imm s]`
  fn parse_imm_32(&mut self, p: &mut &[u8]) -> [ProofId; 3] {
    let [_, imm, s, th] = self.parse_imm_n(p, 3);
    [imm, s, thm!(self.thm, parseImm32_I(imm, s, th): (parseImm32 imm s))]
  }

  /// Proves `[imm, s, |- parseImm64 imm s]`
  fn parse_imm_64(&mut self, p: &mut &[u8]) -> [ProofId; 3] {
    let [_, imm, s, th] = self.parse_imm_n(p, 7);
    [imm, s, thm!(self.thm, parseImm64_I(imm, s, th): (parseImm64 imm s))]
  }

  /// Proves `[imm, s, |- parseImm sz imm s]`
  fn parse_imm(&mut self, p: &mut &[u8], sz: ProofId) -> [ProofId; 3] {
    app_match!(self.thm, sz => {
      (wSz8 r) => {
        let [imm, s, th] = self.parse_imm_8(p);
        [imm, s, thm!(self.thm, parseImm_8(imm, r, s, th): (parseImm sz imm s))]
      }
      (wSz32) => {
        let [imm, s, th] = self.parse_imm_32(p);
        [imm, s, thm!(self.thm, parseImm_32(imm, s, th): (parseImm sz imm s))]
      }
      (wSz64) => {
        let [imm, s, th] = self.parse_imm_32(p);
        [imm, s, thm!(self.thm, parseImm_64(imm, s, th): (parseImm sz imm s))]
      }
      !
    })
  }

  /// Proves `([imm, s, s2, |- parseImm8S imm s s2], r)`
  /// if `f` produces `(s2, r)`.
  fn parse_imm_8_then<R>(&mut self, p: &mut &[u8],
    f: impl FnOnce(&mut Self, &mut &[u8]) -> (ProofId, R)
  ) -> ([ProofId; 4], R) {
    let [_, imm, s, th] = self.parse_imm_n(p, 3);
    let c1 = app_match!(self.thm, s => { (s1 c1) => c1, ! });
    let (s2, ret) = f(self, p);
    let s = app!(self.thm, (scons c1 s2));
    let th = thm!(self.thm, parseImm8S_I(c1, imm, s2, th): (parseImm8S imm s s2));
    ([imm, s, s2, th], ret)
  }

  /// Proves `([imm, s, s2, |- parseImm32S imm s s2], r)`
  /// if `f` produces `(s2, r)`.
  fn parse_imm_32_then<R>(&mut self, p: &mut &[u8],
    f: impl FnOnce(&mut Self, &mut &[u8]) -> (ProofId, R)
  ) -> ([ProofId; 4], R) {
    let [_, imm, s, th] = self.parse_imm_n(p, 0);
    let (c1, c2, c3, c4) = app_match!(self.thm, s => {
      (scons c1 (scons c2 (scons c3 (s1 c4)))) => (c1, c2, c3, c4),
      !
    });
    let (s2, ret) = f(self, p);
    let s = app!(self.thm, (scons c1 (scons c2 (scons c3 (scons c4 s2)))));
    let th = thm!(self.thm, parseImm8S_I(c1, c2, c3, c4, imm, s2, th): (parseImm8S imm s s2));
    ([imm, s, s2, th], ret)
  }

  /// Proves `([disp, l, l2, |- parseDisplacement md disp l l2], r)`
  /// if `f` produces `(l2, r)`.
  fn parse_displacement_then<R>(&mut self, p: &mut &[u8], md: P<u8>,
    f: impl FnOnce(&mut Self, &mut &[u8]) -> (ProofId, R)
  ) -> ([ProofId; 4], R) {
    match md.0 {
      0 => {
        let a = app!(self.thm, (posZ (h2n {self.hex[0]})));
        let (s, ret) = f(self, p);
        let th = thm!(self, parseDisplacement_0(s): (parseDisplacement {md.1} a s s));
        ([a, s, s, th], ret)
      }
      1 => {
        let ([a, s, s2, h], ret) = self.parse_imm_8_then(p, f);
        let th = thm!(self, parseDisplacement_8(a, s, s2, h): (parseDisplacement {md.1} a s s2));
        ([a, s, s2, th], ret)
      }
      2 => {
        let ([a, s, s2, h], ret) = self.parse_imm_32_then(p, f);
        let th = thm!(self, parseDisplacement_32(a, s, s2, h): (parseDisplacement {md.1} a s s2));
        ([a, s, s2, th], ret)
      }
      _ => unreachable!()
    }
  }

  /// Proves `([rn, rm, l, l2, |- parseModRM rex rn rm l l2], r)`
  /// if `f` produces `(l2, r)`.
  fn parse_modrm_then<R>(&mut self, p: &mut &[u8],
    rex: P<Option<u8>>,
    f: impl FnOnce(&mut Self, &mut &[u8]) -> (ProofId, R)
  ) -> ([ProofId; 5], R) {
    // Get the ModRM byte
    let modrm = parse_u8(p);
    let (x, y) = (modrm >> 4, modrm & 15);
    let modrmch = self.hex.ch(&mut self.thm, modrm);
    let ([rm2, o], h1) = self.hex.split_bits_31(&mut self.thm, y);
    let ([pc, md], h2) = self.hex.split_bits_22(&mut self.thm, x);
    let (r, h3) = self.rex_val(rex, Rex::R);
    let (rn, h4) = self.hex.unsplit_bits_121(&mut self.thm, o.0, pc.0, r.0);

    // Division into parseModRM2 cases
    let (rm, l, l2, ret, h5) = if md.0 == 3 {
      // ModRMLayout::Reg = `11ooonnn` where `rn = o` and `rm = reg(n)`
      let (b, h1) = self.rex_val(rex, Rex::B);
      let (r, h2) = self.hex.unsplit_bits_31(&mut self.thm, rm2.0, b.0);
      let rm = app!(self.thm, (IRM_reg {r.1}));
      let (l, ret) = f(self, p);
      (rm, l, l, ret, thm!(self, (parseModRM2[rex.1, rm, rm2.1, md.1, l, l]) =>
        parseModRM2_reg(b.1, r.1, rex.1, rm2.1, l, h1, h2)))

    } else if rm2.0 == 5 && md.0 == 0 {
      // ModRMLayout::RIP = `00ooo101 + imm32` where `rn = o` and `rm = [RIP + imm32]`
      let ([a, l, l2, h1], ret) = self.parse_imm_32_then(p, f);
      let rm = app!(self.thm, (IRM_mem (d0) (base_RIP) a));
      (rm, l, l2, ret, thm!(self, (parseModRM2[rex.1, rm, rm2.1, md.1, l, l2]) =>
        parseModRM2_rip(a, l, l2, rex.1, h1)))

    } else if rm2.0 == 4 {
      // Get the SIB byte
      let sib = parse_u8(p);
      let (x, y) = (sib >> 4, sib & 15);
      let sibch = self.hex.ch(&mut self.thm, sib);
      let ([bs, ixl], h1) = self.hex.split_bits_31(&mut self.thm, y);
      let ([ixh, sc], h2) = self.hex.split_bits_22(&mut self.thm, x);
      let (rx, h3) = self.rex_val(rex, Rex::X);
      let (index, h4) = self.hex.unsplit_bits_121(&mut self.thm, ixl.0, ixh.0, rx.0);

      // Parse the scale/index bits
      let (osi, h5) = if index.0 == 4 {
        // no index. We assume the compiler also generates no scale in this case
        assert!(sc.0 == 0);
        let osi = app!(self.thm, (d0));
        (osi, thm!(self.thm, parseSI_n[index.0](): (parseSI {sc.1} {index.1} osi)))
      } else {
        // has a scale and index register
        let osi = app!(self.thm, (scaleReg {sc.1} {index.1}));
        (osi, thm!(self.thm, parseSI_n[index.0](sc.1): (parseSI {sc.1} {index.1} osi)))
      };

      let (rb, h6) = self.rex_val(rex, Rex::B);
      let (base, h7) = self.hex.unsplit_bits_31(&mut self.thm, bs.0, rb.0);
      if base.0 == 5 && md.0 == 0 {
        // ModRMLayout::Sib0:
        // `00ooo100 + ssiii101 + imm32` where `rn = o` and `rm = [0 + sc*ix + imm32]`
        let ([a, l, l2, h8], ret) = self.parse_imm_32_then(p, f);
        let rm = app!(self.thm, (IRM_mem osi (d0) a));
        let l_ = app!(self.thm, (scons sibch l));
        (rm, l_, l2, ret, thm!(self, (parseModRM2[rex.1, rm, rm2.1, md.1, l_, l2]) =>
          parseModRM2_sib0(a, bs.1, index.1, ixh.1, ixl.1, l, l2,
            osi, rb.1, rex.1, rx.1, sc.1, self.hex[x], self.hex[y],
            h1, h2, h3, h4, h5, h6, h7, h8)))

      } else {
        // ModRMLayout::SibReg:
        // `mmooo100 + ssiiibbb + disp0/8/32` where `rn = o` and `rm = [reg(b) + sc*ix + disp]`
        // we have to prove a side condition saying we aren't in any of the other cases
        let h8 = if base.0 == 5 {
          thm!(self, sibSideCond_M[md.0](base.1): (sibSideCond {rm2.1} {md.1}))
        } else {
          thm!(self, sibSideCond_B[base.0](md.1): (sibSideCond {rm2.1} {md.1}))
        };
        let ([a, l, l2, h9], ret) = self.parse_displacement_then(p, md, f);
        let rm = app!(self.thm, (IRM_mem osi (base_reg {base.1}) a));
        let l_ = app!(self.thm, (scons sibch l));
        (rm, l_, l2, ret, thm!(self, (parseModRM2[rex.1, rm, rm2.1, md.1, l_, l2]) =>
          parseModRM2_sibReg(a, base.1, bs.1, index.1, ixh.1, ixl.1, l, l2,
            md.1, osi, rb.1, rex.1, rx.1, sc.1, self.hex[x], self.hex[y],
            h1, h2, h3, h4, h5, h6, h7, h8, h9)))
      }

    } else {
      // ModRMLayout::Disp: `mmooonnn + disp0/8/32` where `rn = o` and `rm = [reg(n) + disp]`
      let (b, h1) = self.rex_val(rex, Rex::B);
      let (r, h2) = self.hex.unsplit_bits_31(&mut self.thm, rm2.0, b.0);
      // we have to prove a side condition saying we aren't in any of the other cases
      let h3 = if rm2.0 == 5 {
        thm!(self, modrmSideCond_m[md.0](): (modrmSideCond {rm2.1} {md.1}))
      } else {
        thm!(self, modrmSideCond_n[rm2.0](): (modrmSideCond {rm2.1} {md.1}))
      };
      let ([a, l, l2, h4], ret) = self.parse_displacement_then(p, md, f);
      let rm = app!(self.thm, (IRM_mem (d0) (base_reg {r.1}) a));
      (rm, l, l2, ret, thm!(self, (parseModRM2[rex.1, rm, rm2.1, md.1, l, l2]) =>
        parseModRM2_disp(b.1, a, l, l2, md.1, r.1, rex.1, rm2.1, h1, h2, h3, h4)))
    }; // finished parseModRM2

    // We have a final fixup if the ModRM byte had no following bytes,
    // since we don't want to end an instruction with `c ': s0`
    let (s, th) = if app_match!(self.thm, l => { (s0) => true, _ => false }) {
      let s = app!(self.thm, (s1 modrmch));
      (s, thm!(self, (parseModRM[rex.1, rn.1, rm, s, l2]) =>
        parseModRM_1(l2, md.1, o.1, pc.1, r.1, rex.1, rm, rm2.1,
          rn.1, self.hex[x], self.hex[y], h1, h2, h3, h4, h5)))
    } else {
      let s = app!(self.thm, (scons modrmch l));
      (s, thm!(self, (parseModRM[rex.1, rn.1, rm, s, l2]) =>
        parseModRM_S(l, l2, md.1, o.1, pc.1, r.1, rex.1, rm, rm2.1,
          rn.1, self.hex[x], self.hex[y], h1, h2, h3, h4, h5)))
    };
    ([rn.1, rm, s, l2, th], ret)
  }

  /// Proves `([rn, rm, l, |- parseModRM_N rex rn rm l s0], r)`
  /// if `f` produces `(l2, r)`.
  fn parse_modrm(&mut self, p: &mut &[u8], rex: P<Option<u8>>) -> [ProofId; 4] {
    let ([rn, rm, l, _, th], ()) = self.parse_modrm_then(p, rex, |this, _| {
      (app!(this, (s0)), ())
    });
    [rn, rm, l, th]
  }

  /// Proves `[I, |- parseBinop opc sz dst src I]`.
  fn parse_binop(&mut self, pinst: &PInst,
    op: ProofId, sz: ProofId, dst: ProofId, src: ProofId
  ) -> [ProofId; 2] {
    match pinst {
      PInst::Binop { .. } | PInst::Cmp { .. } => {
        let inst = app!(self.thm, (instBinop op sz dst src));
        [inst, thm!(self, parseBinopBinop(op, sz, dst, src): (parseBinop op sz dst src inst))]
      }
      PInst::Imm { sz: Size::S32, src: 0, .. } => {
        let inst = app!(self.thm, (instImm (wSz32) dst (posZ (h2n {self.hex[0]}))));
        [inst, thm!(self, parseBinopClear32(dst): (parseBinop op sz dst src inst))]
      }
      PInst::Imm { sz: Size::S64, src: 0, .. } => {
        let inst = app!(self.thm, (instImm (wSz64) dst (posZ (h2n {self.hex[0]}))));
        [inst, thm!(self, parseBinopClear64(dst): (parseBinop op sz dst src inst))]
      }
      _ => unreachable!()
    }
  }

  /// Proves `[b, |- hasREX rex b]`
  fn has_rex(&mut self, rex: P<Option<u8>>) -> [ProofId; 2] {
    if let Some(hrex) = rex.0 {
      let b = app!(self, (tru));
      [b, thm!(self, hasREXS(self.hex[hrex]): (hasREX {rex.1} b))]
    } else {
      let b = app!(self, (fal));
      [b, thm!(self, hasREX0(): (hasREX {rex.1} b))]
    }
  }

  /// Given `x`, proves `[s, opc, I, |- parseOpc start ip s rex opc I]` where
  /// `s` is generated from the instruction assembly.
  fn parse_opc(&mut self, pinst: &PInst,
    p: &mut &[u8], layout: OpcodeLayout, ip: Num, rex: P<Option<u8>>
  ) -> [ProofId; 4] {
    let opc = parse_u8(p);
    let (x, y) = (opc >> 4, opc & 15);
    let opch = self.hex.ch(&mut self.thm, opc);
    match layout {
      OpcodeLayout::BinopRAX(_) => {
        let ([v, _, o], h1) = self.hex.split_bits_121(&mut self.thm, y);
        let ([pc, _], h2) = self.hex.split_bits_22(&mut self.thm, x);
        let (opc, h3) = self.hex.unsplit_bits_121(&mut self.thm, o.0, pc.0, 0);
        let [sz, h4] = self.op_size_w(rex, v);
        let [src, l, h5] = self.parse_imm(p, sz);
        let esrc = app!(self.thm, (IRM_imm32 src));
        let dst = self.hex[0];
        let [inst, h6] = self.parse_binop(pinst, opc.1, sz, dst, esrc);
        let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
          parseBinopRAX(inst, *ip, l, o.1, opc.1, *self.start,
            pc.1, rex.1, src, sz, v.1, self.hex[x], self.hex[y], h1, h2, h3, h4, h5, h6));
        [l, opch, inst, th]
      }
      OpcodeLayout::BinopImm(..) => {
        let ([v, _], h1) = self.hex.split_bits_13(&mut self.thm, y);
        let [sz, h2] = self.op_size_w(rex, v);
        let ([opc, dst, l1, l2, h3], (src, h4)) = self.parse_modrm_then(p, rex, |this, p| {
          let [src, l2, h4] = this.parse_imm(p, sz);
          (l2, (src, h4))
        });
        let dst = app_match!(self, dst => { (IRM_reg dst) => dst, ! });
        let esrc = app!(self.thm, (IRM_imm32 src));
        let [inst, h5] = self.parse_binop(pinst, opc, sz, dst, esrc);
        let th = thm!(self, (parseOpc[*self.start, *ip, l1, rex.1, opch, inst]) =>
          parseBinopImm(inst, dst, *ip, l1, l2, opc, *self.start,
            rex.1, src, sz, v.1, self.hex[y], h1, h2, h3, h4, h5));
        [l1, opch, inst, th]
      }
      OpcodeLayout::BinopImm8(_) =>  {
        let v = self.dn(1);
        let [sz, h1] = self.op_size_w(rex, v);
        let ([opc, dst, l1, l2, h2], (src, h3)) = self.parse_modrm_then(p, rex, |this, p| {
          let [src, l2, h3] = this.parse_imm_8(p);
          (l2, (src, h3))
        });
        let dst = app_match!(self, dst => { (IRM_reg dst) => dst, ! });
        let esrc = app!(self.thm, (IRM_imm32 src));
        let [inst, h4] = self.parse_binop(pinst, opc, sz, dst, esrc);
        let th = thm!(self, (parseOpc[*self.start, *ip, l1, rex.1, opch, inst]) =>
          parseBinopImm(inst, dst, *ip, l1, l2, opc, *self.start,
            rex.1, src, sz, v.1, self.hex[y], h1, h2, h3, h4));
        [l1, opch, inst, th]
      }
      OpcodeLayout::BinopReg(_) => {
        let ([v, _, o], h1) = self.hex.split_bits_121(&mut self.thm, y);
        let ([pc, _], h2) = self.hex.split_bits_22(&mut self.thm, x);
        let (opc, h3) = self.hex.unsplit_bits_121(&mut self.thm, o.0, pc.0, 0);
        let [sz, h4] = self.op_size_w(rex, v);
        let [dst, src, l, h5] = self.parse_modrm(p, rex);
        let [inst, h6] = self.parse_binop(pinst, opc.1, sz, dst, src);
        let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
          parseBinopReg(inst, dst, *ip, l, o.1, opc.1, *self.start,
            pc.1, rex.1, src, sz, v.1, self.hex[x], self.hex[y], h1, h2, h3, h4, h5, h6));
        [l, opch, inst, th]
      }
      OpcodeLayout::BinopHi(_) => {
        let ([v, _], h1) = self.hex.split_bits_13(&mut self.thm, y);
        let [sz, h2] = self.op_size_w(rex, v);
        let ([opc, dst, l1, l2, h3], (src, h4)) = self.parse_modrm_then(p, rex, |this, p| {
          let [src, l2, h4] = this.parse_imm_8(p);
          (l2, (src, h4))
        });
        let inst = app!(self, (instShift opc sz dst (IRM_imm32 (posZ src))));
        let th = thm!(self, (parseOpc[*self.start, *ip, l1, rex.1, opch, inst]) =>
          parseBinopHi(dst, *ip, l1, l2, opc, *self.start,
            rex.1, src, sz, v.1, self.hex[y], h1, h2, h3, h4));
        [l1, opch, inst, th]
      }
      OpcodeLayout::BinopHi1(_) => {
        let ([v, _], h1) = self.hex.split_bits_13(&mut self.thm, y);
        let [sz, h2] = self.op_size_w(rex, v);
        let [opc, dst, l, h3] = self.parse_modrm(p, rex);
        let dst = app_match!(self, dst => { (IRM_reg dst) => dst, ! });
        let inst = app!(self, (instShift opc sz dst (IRM_imm32 (posZ (dn[1_usize])))));
        let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
          parseBinopHi1(dst, *ip, l, opc, *self.start,
            rex.1, sz, v.1, self.hex[y], h1, h2, h3));
        [l, opch, inst, th]
      }
      OpcodeLayout::BinopHiReg(_) => {
        let ([v, _], h1) = self.hex.split_bits_13(&mut self.thm, y);
        let [sz, h2] = self.op_size_w(rex, v);
        let [opc, dst, l, h3] = self.parse_modrm(p, rex);
        let inst = app!(self, (instShift opc sz dst (IRM_reg {self.hex[1]})));
        let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
          parseBinopHiReg(dst, *ip, l, opc, *self.start,
            rex.1, sz, v.1, self.hex[y], h1, h2, h3));
        [l, opch, inst, th]
      }
      OpcodeLayout::MovSX(_) => {
        let (_, h1) = self.rex_val(rex, Rex::W);
        let [dst, src, l, h2] = self.parse_modrm(p, rex);
        let inst = app!(self, (instMovSX (wSz64) dst (wSz32) src));
        let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
          parseMovSLQ(dst, *ip, l, *self.start, rex.1, src, h1, h2));
        [l, opch, inst, th]
      }
      OpcodeLayout::MovX(_) => {
        let opc2 = parse_u8(p);
        let [b, h1] = self.has_rex(rex);
        let v = self.dn(1);
        let [sz, h2] = self.op_size_w(rex, v);
        let [dst, src, l, h3] = self.parse_modrm(p, rex);
        let l2 = app!(self, (scons {self.hex.ch(&mut self.thm, opc2)} l));
        if opc2 & 8 == 0 {
          let inst = app!(self, (instMovZX sz dst (wSz8 b) src));
          let th = thm!(self, (parseOpc[*self.start, *ip, l2, rex.1, opch, inst]) =>
            parseMovZB(b, dst, *ip, l, *self.start, rex.1, src, sz, h1, h2, h3));
          [l2, opch, inst, th]
        } else {
          let inst = app!(self, (instMovSX sz dst (wSz8 b) src));
          let th = thm!(self, (parseOpc[*self.start, *ip, l2, rex.1, opch, inst]) =>
            parseMovSB(b, dst, *ip, l, *self.start, rex.1, src, sz, h1, h2, h3));
          [l2, opch, inst, th]
        }
      }
      OpcodeLayout::MovReg(_) => {
        let ([v, d], h1) = self.hex.split_bits_13(&mut self.thm, y);
        match (d.0 & 1 != 0, self.parse_modrm(p, rex), pinst) {
          (true, [dst, src, l, h2], PInst::MovzxRmR { ext_mode: ExtMode::LQ, .. }) => {
            let (_, h3) = self.rex_val(rex, Rex::W);
            let inst = app!(self, (instMovZX (wSz64) dst (wSz32) src));
            let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
              parseMovZLQ(dst, *ip, l, *self.start,
                rex.1, src, v.1, self.hex[y], h1, h2, h3));
            [l, opch, inst, th]
          }
          (true, [dst, src, l, h2], _) => {
            let [sz, h3] = self.op_size_w(rex, v);
            let inst = app!(self, (instMov sz (IRM_reg dst) src));
            let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
              parseMovLoad(dst, *ip, l, *self.start,
                rex.1, src, sz, v.1, self.hex[y], h1, h2, h3));
            [l, opch, inst, th]
          }
          (false, [src, dst, l, h2], _) => {
            let [sz, h3] = self.op_size_w(rex, v);
            let inst = app!(self, (instMov sz dst (IRM_reg src)));
            let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
              parseMovStore(dst, *ip, l, *self.start,
                rex.1, src, sz, v.1, self.hex[y], h1, h2, h3));
            [l, opch, inst, th]
          }
        }
      }
      OpcodeLayout::Mov64(sz64) => {
        let ([r, _], h1) = self.hex.split_bits_31(&mut self.thm, y);
        let (rb, h2) = self.rex_val(rex, Rex::B);
        let ((_, dst), h3) = self.hex.unsplit_bits_31(&mut self.thm, r.0, rb.0);
        let (_, h4) = self.rex_val(rex, Rex::W);
        if sz64 {
          let [src, l, h5] = self.parse_imm_64(p);
          let inst = app!(self, (instMov (wSz64) (IRM_reg dst) (IRM_imm64 src)));
          let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
            parseMov64(dst, *ip, l, *self.start,
              r.1, rb.1, rex.1, src, self.hex[y], h1, h2, h3, h4, h5));
          [l, opch, inst, th]
        } else {
          let [src, l, h5] = self.parse_imm_32(p);
          let inst = app!(self, (instMov (wSz32) (IRM_reg dst) (IRM_imm32 src)));
          let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
            parseMov32(dst, *ip, l, *self.start,
              r.1, rb.1, rex.1, src, self.hex[y], h1, h2, h3, h4, h5));
          [l, opch, inst, th]
        }
      }
      OpcodeLayout::MovImm(_) => {
        let ([v, _], h1) = self.hex.split_bits_13(&mut self.thm, y);
        let [sz, h2] = self.op_size_w(rex, v);
        let ([_, dst, l1, l2, h3], (src, h4)) = self.parse_modrm_then(p, rex, |this, p| {
          let [src, l2, h4] = this.parse_imm(p, sz);
          (l2, (src, h4))
        });
        let inst = app!(self, (instMov sz dst (IRM_imm32 src)));
        let th = thm!(self, (parseOpc[*self.start, *ip, l1, rex.1, opch, inst]) =>
          parseMovImm(dst, *ip, l1, l2, *self.start,
            rex.1, src, sz, v.1, self.hex[y], h1, h2, h3, h4));
        [l1, opch, inst, th]
      }
      OpcodeLayout::PushImm(sz32) => {
        let [src, l, h1] = if sz32 { self.parse_imm_32(p) } else { self.parse_imm_8(p) };
        let inst = app!(self, (instPush (IRM_imm32 src)));
        let tgt = app!(self, parseOpc[*self.start, *ip, l, rex.1, opch, inst]);
        let th = if sz32 {
          thm!(self, parsePushImm32(*ip, l, *self.start, rex.1, src, h1): tgt)
        } else {
          thm!(self, parsePushImm8(*ip, l, *self.start, rex.1, src, h1): tgt)
        };
        [l, opch, inst, th]
      }
      OpcodeLayout::PushReg | OpcodeLayout::PopReg => {
        let ([r, _], h1) = self.hex.split_bits_31(&mut self.thm, y);
        let (rb, h2) = self.rex_val(rex, Rex::B);
        let ((_, reg), h3) = self.hex.unsplit_bits_31(&mut self.thm, r.0, rb.0);
        let l = app!(self, (s0));
        if matches!(layout, OpcodeLayout::PushReg) {
          let inst = app!(self, (instPush (IRM_reg reg)));
          let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
            parsePushReg(*ip, *self.start, r.1, rb.1, rex.1, reg, self.hex[y], h1, h2, h3));
          [l, opch, inst, th]
        } else {
          let inst = app!(self, (instPop reg));
          let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
            parsePopReg(reg, *ip, *self.start, r.1, rb.1, rex.1, self.hex[y], h1, h2, h3));
          [l, opch, inst, th]
        }
      }
      OpcodeLayout::Jump(sz32) => {
        let (n, [imm, l, h2]) = if sz32 {
          (parse_i32_64(&mut {*p}), self.parse_imm_32(p))
        } else {
          (parse_i8_64(&mut {*p}), self.parse_imm_8(p))
        };
        let (tgt, h1) = self.znsub_left(ip, n);
        let inst = app!(self, (instJump {*tgt}));
        let tgt = app!(self, parseOpc[*self.start, *ip, l, rex.1, opch, inst]);
        let th = if sz32 {
          thm!(self, parseJump32(imm, *ip, l, *self.start, rex.1, tgt, h1, h2): tgt)
        } else {
          thm!(self, parseJump8(imm, *ip, l, *self.start, rex.1, tgt, h1, h2): tgt)
        };
        [l, opch, inst, th]
      }
      OpcodeLayout::Jcc8 => {
        let (tgt, h1) = self.znsub_left(ip, parse_i8_64(&mut {*p}));
        let [imm, l, h2] = self.parse_imm_8(p);
        let inst = app!(self, (instJCC {self.hex[y]} {*tgt}));
        let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
          parseJCC8(self.hex[y], imm, *ip, l, *self.start, rex.1, *tgt, h1, h2));
        [l, opch, inst, th]
      }
      OpcodeLayout::Jcc => {
        let opc2 = parse_u8(p);
        let (tgt, h1) = self.znsub_left(ip, parse_i32_64(&mut {*p}));
        let [imm, l, h2] = self.parse_imm_32(p);
        let c = self.hex[opc2 & 15];
        let l2 = app!(self, (scons {self.hex.ch(&mut self.thm, opc2)} l));
        let inst = app!(self, (instJCC c {*tgt}));
        let th = thm!(self, (parseOpc[*self.start, *ip, l2, rex.1, opch, inst]) =>
          parseJCCTwo(c, imm, *ip, l, *self.start, rex.1, *tgt, h1, h2));
        [l2, opch, inst, th]
      }
      OpcodeLayout::Call => {
        let (a, h1) = self.hex.add(&mut self.thm, self.start, ip);
        let (tgt, h2) = self.znsub_left(a, parse_i32_64(&mut {*p}));
        let [imm, l, h3] = self.parse_imm_32(p);
        let inst = app!(self, (instCall {*tgt}));
        let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
          parseCall(*a, imm, *ip, l, *self.start, rex.1, *tgt, h1, h2, h3));
        [l, opch, inst, th]
      }
      OpcodeLayout::Ret => {
        let l = app!(self, (s0));
        let inst = app!(self, (instRet));
        let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
          parseRet(*ip, *self.start, rex.1));
        [l, opch, inst, th]
      }
      OpcodeLayout::Cdx => {
        let (w, h1) = self.rex_val(rex, Rex::W);
        let l = app!(self, (s0));
        if w.0 == 0 {
          let inst = app!(self, (instCDX (wSz32)));
          let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
            parseCDQ(*ip, *self.start, rex.1, h1));
          [l, opch, inst, th]
        } else {
          let inst = app!(self, (instCDX (wSz64)));
          let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
            parseCQO(*ip, *self.start, rex.1, h1));
          [l, opch, inst, th]
        }
      }
      OpcodeLayout::Lea(_) => {
        let [dst, addr, l, h1] = self.parse_modrm(p, rex);
        let (si, base, off) = app_match!(self, addr => {
          (IRM_mem si base off) => (si, base, off),
          !
        });
        let (w, h2) = self.rex_val(rex, Rex::W);
        if w.0 == 0 {
          let inst = app!(self, (instLea (wSz32) dst si base off));
          let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
            parseLea32(base, dst, *ip, l, off, *self.start, rex.1, si, h1, h2));
          [l, opch, inst, th]
        } else {
          let inst = app!(self, (instLea (wSz64) dst si base off));
          let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
            parseLea64(base, dst, *ip, l, off, *self.start, rex.1, si, h1, h2));
          [l, opch, inst, th]
        }
      }
      OpcodeLayout::Test(_) => {
        let ([v, _], h1) = self.hex.split_bits_13(&mut self.thm, y);
        let [sz, h2] = self.op_size_w(rex, v);
        let [src2, src1, l, h3] = self.parse_modrm(p, rex);
        let inst = app!(self, (instTest sz src1 (IRM_reg src2)));
        let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
          parseTest(*ip, l, *self.start, rex.1, src1, src2, sz, v.1, self.hex[y], h1, h2, h3));
        [l, opch, inst, th]
      }
      OpcodeLayout::TestRAX(_) => {
        let ([v, _], h1) = self.hex.split_bits_13(&mut self.thm, y);
        let (w, h2) = self.rex_val(rex, Rex::W);
        let [sz, h3] = self.op_size(true, w, v);
        let [src, l, h4] = self.parse_imm(p, sz);
        let inst = app!(self, (instTest sz (IRM_reg {self.hex[0]}) src));
        let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
          parseTest(*ip, l, *self.start, rex.1, src, sz, v.1, w.1, self.hex[y], h1, h2, h3, h4));
        [l, opch, inst, th]
      }
      OpcodeLayout::HiTest(..) => {
        let ([v, _], h1) = self.hex.split_bits_13(&mut self.thm, y);
        let [sz, h2] = self.op_size_w(rex, v);
        let ([_, src1, l1, l2, h3], (src2, h4)) = self.parse_modrm_then(p, rex, |this, p| {
          let [src2, l2, h4] = this.parse_imm(p, sz);
          (l2, (src2, h4))
        });
        let inst = app!(self, (instTest sz src1 (IRM_imm32 src2)));
        let th = thm!(self, (parseOpc[*self.start, *ip, l1, rex.1, opch, inst]) =>
          parseTestHi(*ip, l1, l2, *self.start,
            rex.1, src1, src2, sz, v.1, self.hex[y], h1, h2, h3, h4));
        [l1, opch, inst, th]
      }
      OpcodeLayout::Hi(_) => match (pinst, self.parse_modrm(p, rex)) {
        (PInst::Unop { op, .. }, [_, dst, l, h3]) => {
          let ([v, _], h1) = self.hex.split_bits_13(&mut self.thm, y);
          let [sz, h2] = self.op_size_w(rex, v);
          let dst = app_match!(self, dst => { (IRM_reg dst) => dst, ! });
          macro_rules! op { ($inst:ident, $th:ident) => {{
            let inst = app!(self, (instUnop ($inst) sz dst));
            let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
              $th(dst, *ip, l, *self.start, rex.1, sz, v.1, self.hex[y], h1, h2, h3));
            [l, opch, inst, th]
          }}}
          match op {
            Unop::Inc => op!(unopInc, parseInc),
            Unop::Dec => op!(unopDec, parseDec),
            Unop::Not => op!(unopNot, parseNot),
            Unop::Neg => op!(unopNeg, parseNeg),
          }
        }
        (PInst::Mul { .. } | PInst::DivRem { .. }, [_, src, l, h3]) => {
          let ([v, _], h1) = self.hex.split_bits_13(&mut self.thm, y);
          let [sz, h2] = self.op_size_w(rex, v);
          if matches!(pinst, PInst::Mul { .. }) {
            let inst = app!(self, (instMul sz src));
            let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
              parseMul(*ip, l, *self.start, rex.1, src, sz, v.1, self.hex[y], h1, h2, h3));
            [l, opch, inst, th]
          } else {
            let inst = app!(self, (instDiv sz src));
            let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
              parseDiv(*ip, l, *self.start, rex.1, src, sz, v.1, self.hex[y], h1, h2, h3));
            [l, opch, inst, th]
          }
        }
        (PInst::Push64 { src: PRegMemImm::Mem(_) }, [_, src, l, h1]) => {
          let inst = app!(self, (instPush src));
          let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
            parsePushMem(*ip, l, *self.start, rex.1, src, h1));
          [l, opch, inst, th]
        }
        _ => unreachable!(),
      }
      OpcodeLayout::SetCC(_) => {
        let opc2 = parse_u8(p);
        let [b, h1] = self.has_rex(rex);
        let [_, dst, l, h2] = self.parse_modrm(p, rex);
        let dst = app_match!(self, dst => { (IRM_reg dst) => dst, ! });
        let c = self.hex[opc2 & 15];
        let l2 = app!(self, (scons {self.hex.ch(&mut self.thm, opc2)} l));
        let inst = app!(self, (instSetCC c b dst));
        let th = thm!(self, (parseOpc[*self.start, *ip, l2, rex.1, opch, inst]) =>
          parseSetCC(b, c, dst, *ip, l, *self.start, rex.1, h1, h2));
        [l2, opch, inst, th]
      }
      OpcodeLayout::CMov(_) =>  {
        let opc2 = parse_u8(p);
        let (w, h1) = self.rex_val(rex, Rex::W);
        let v = self.dn(1);
        let [sz, h2] = self.op_size(true, w, v);
        let [dst, src, l, h3] = self.parse_modrm(p, rex);
        let c = self.hex[opc2 & 15];
        let l2 = app!(self, (scons {self.hex.ch(&mut self.thm, opc2)} l));
        let inst = app!(self, (instCMov c sz (IRM_reg dst) src));
        let th = thm!(self, (parseOpc[*self.start, *ip, l2, rex.1, opch, inst]) =>
          parseCMov(c, dst, *ip, l, *self.start, rex.1, src, sz, w.1, h1, h2, h3));
        [l2, opch, inst, th]
      }
      OpcodeLayout::SysCall => {
        let l = app!(self, (s1 {self.hex.ch(&mut self.thm, 0x05)}));
        let inst = app!(self, (instSysCall));
        let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
          parseSysCall(*ip, *self.start, rex.1));
        [l, opch, inst, th]
      }
      OpcodeLayout::Assert => {
        let [c1, c2, c3] = [0x02, 0x0f, 0x0b].map(|c| self.hex.ch(&mut self.thm, c));
        let l = app!(self, (scons c1 (scons c2 (s1 c3))));
        let inst = app!(self, (instAssert {self.hex[y]}));
        let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
          parseAssert(self.hex[y], *ip, *self.start, rex.1));
        [l, opch, inst, th]
      }
      OpcodeLayout::Ud2 => {
        let l = app!(self, (s1 {self.hex.ch(&mut self.thm, 0x0b)}));
        let inst = app!(self, (instSysCall));
        let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
          parseSysCall(*ip, *self.start, rex.1));
        [l, opch, inst, th]
      }
    }
  }

  /// Proves `[s, inst, |- parseInst start ip s inst]` where
  /// `s` is generated from the instruction assembly.
  fn parse_inst(&mut self, inst: &Inst<'_>, ip: Num) -> [ProofId; 3] {
    let p = &mut inst.content();
    let short = inst.layout.opc.len() == 1;
    if inst.layout.rex {
      let rex = parse_u8(p) & 15;
      let hrex = self.hex[rex];
      let srex = (Some(rex), app!(self, (suc (h2n hrex))));
      let [s, opc, inst, th] = self.parse_opc(inst.inst, p, inst.layout.opc, ip, srex);
      if short {
        let s2 = app!(self, (scons (ch {self.hex[4]} hrex) (s1 opc)));
        let th = thm!(self, parseInst10(inst, *ip, opc, *self.start, hrex, th):
          parseInst[*self.start, *ip, s2, inst]);
        [s2, inst, th]
      } else {
        let s2 = app!(self, (scons (ch {self.hex[4]} hrex) (scons opc s)));
        let th = thm!(self, parseInst11(inst, *ip, opc, *self.start, hrex, s, th):
          parseInst[*self.start, *ip, s2, inst]);
        [s2, inst, th]
      }
    } else {
      let rex = app!(self, (d0));
      let [s, opc, inst, th] = self.parse_opc(inst.inst, p, inst.layout.opc, ip, (None, rex));
      if short {
        let s2 = app!(self, (s1 opc));
        let th = thm!(self, parseInst00(inst, *ip, opc, *self.start, th):
          parseInst[*self.start, *ip, s2, inst]);
        [s2, inst, th]
      } else {
        let s2 = app!(self, (scons opc s));
        let th = thm!(self, parseInst01(inst, *ip, opc, *self.start, s, th):
          parseInst[*self.start, *ip, s2, inst]);
        [s2, inst, th]
      }
    }
  }

  /// Given `x`, proves `(s, y, A, |- assemble start s x y A)`, using elements of the iterator
  /// `iter` in a balanced binary tree of `localAssembleA` nodes.
  /// The function `f` handles the base case of an individual item in the iterator.
  fn bisect<T>(&mut self,
    n: usize, iter: &mut impl Iterator<Item=T>, x: Num,
    f: &mut impl FnMut(&mut Self, T, Num) -> (ProofId, Num, ProofId, ProofId),
  ) -> (ProofId, Num, ProofId, ProofId) {
    if n <= 1 {
      assert!(n != 0);
      let item = iter.next().expect("iterator size lied");
      f(self, item, x)
    } else {
      let m = n >> 1;
      let (s, y, a, th1) = self.bisect(m, iter, x, f);
      let (t, z, b, th2) = self.bisect(n - m, iter, y, f);
      let st = app!(self, (sadd s t));
      let ab = app!(self, (localAssembleA a b));
      let th = thm!(self, localAssembleA_I(*self.start, s, t, *x, *y, *z, a, b, th1, th2):
        localAssemble[*self.start, st, *x, *z, ab]);
      (st, z, ab, th)
    }
  }

  /// Given a string `s` with `len s < 16`, proves `(i, |- len s = x[i])`
  fn strlen(&mut self, s: ProofId) -> (Num, ProofId) {
    let mut args = vec![];
    let mut x = s;
    loop {
      app_match!(self, x => {
        (scons c x2) => { args.push(c); x = x2 }
        (s1 a) => {
          args.push(a);
          #[allow(clippy::cast_possible_truncation)]
          let n = self.hex.h2n(&mut self.thm, args.len() as u8);
          let res = app!(self, (strlen s {*n}));
          let th = self.strlenn[args.len()];
          return (n, self.thm(th, &args, res))
        }
        (s0) => {
          assert!(args.is_empty());
          let n = self.hex.h2n(&mut self.thm, 0);
          return (n, thm!(self, strlenn[0_usize](): (strlen s {*n})))
        }
        _ => panic!("not a string literal"),
      })
    }
  }

  /// Given `x`, proves `(s, y, A, |- localAssemble start s x y A)` where
  /// `s` is generated from the assembly blocks.
  pub(super) fn blocks(&mut self, proc: &Proc<'_>) -> (ProofId, Num, ProofId, ProofId) {
    let mut iter = proc.assembly_blocks();
    let x = self.hex.h2n(&mut self.thm, 0);
    self.bisect(iter.len(), &mut iter, x, &mut |this, block, x| {
      let mut iter = block.insts();
      let (s, y, a, th) = this.bisect(iter.len(), &mut iter, x, &mut |this, inst, x| {
        let n = this.hex.from_u8(&mut this.thm, inst.layout.len());
        let (y, h2) = this.hex.add(&mut this.thm, x, n);
        let [s, inst, h3] = this.parse_inst(&inst, y);
        let (n2, h1) = this.strlen(s); assert!(n == n2);
        let th = thm!(this, parseInstE(*this.start, s, *x, *y, *n, inst, h1, h2, h3):
          localAssemble[*this.start, s, *x, *y, inst]);
        (s, y, inst, th)
      });

      if x.val == 0 {
        let a2 = app!(this.thm, (asmEntry {*this.start} a));
        let th = thm!(this.thm, asmEntryI(*this.start, s, *y, a, th):
          localAssemble[*this.start, s, *x, *y, a2]);
        (s, y, a2, th)
      } else {
        let a2 = app!(this.thm, (asmAt {*x} a));
        let th = thm!(this.thm, asmAtI(*this.start, s, *x, *y, a, th):
          localAssemble[*this.start, s, *x, *y, a2]);
        (s, y, a2, th)
      }
    })
  }
}

struct BuildAssembly<'a> {
  proc_asm: &'a mut HashMap<Option<Symbol>, (TermId, ThmId)>,
  mangler: &'a Mangler,
  elab: &'a mut Elaborator,
  pd: &'a Predefs,
  span: &'a FileSpan,
  asmd_lemmas: u32,
  full: Span,
  hex: HexCache,
  thm: ProofDedup<'a>,
}

impl<'a> BuildAssembly<'a> {
  /// Given `x`, proves `(s, y, A, |- assemble s x y A)`, using elements of the iterator `iter`
  /// in a balanced binary tree of `assembleA` nodes.
  /// The function `f` handles the base case of an individual item in the iterator.
  fn bisect<T>(&mut self,
    n: usize, iter: &mut impl Iterator<Item=T>, x: ProofId,
    f: &mut impl FnMut(&mut Self, T, ProofId) -> Result<(ProofId, Num, ProofId, ProofId)>,
  ) -> Result<(ProofId, Num, ProofId, ProofId)> {
    if n <= 1 {
      assert!(n != 0);
      let item = iter.next().expect("iterator size lied");
      f(self, item, x)
    } else {
      let m = n >> 1;
      let (s, y, a, th1) = self.bisect(m, iter, x, f)?;
      let (t, z, b, th2) = self.bisect(n - m, iter, *y, f)?;
      let st = app!(self.thm, (sadd s t));
      let ab = app!(self.thm, (assembleA a b));
      let th = thm!(self.thm, assembleA_I(s, t, x, *y, *z, a, b, th1, th2):
        assemble[st, x, *z, ab]);
      Ok((st, z, ab, th))
    }
  }

  fn assemble_proc(&mut self,
    proc: &Proc<'_>, global_start: ProofId
  ) -> Result<(ProofId, Num, ProofId, ProofId)> {
    let mut thm = ProofDedup::new(self.pd, &[]);
    let hex = HexCache::new(&mut thm);
    let start = hex.from_u64(&mut thm, proc.start.into());
    let mut build = BuildAssemblyProc { thm, hex, start };
    let (s, y, a, th) = build.blocks(proc);
    let (y2, th2) = build.hex.add(&mut build.thm, start, y);
    let start = *start;
    let a2 = app!(build, (asmProc start a));
    let th = thm!(build, asmProcI(s, start, *y, *y2, a, th, th2): (assemble s start {*y2} a2));
    let pad = proc.trailing_padding();
    let (s, Num {val: end_val, e: end}, th) = if pad.is_empty() { (s, y2, th) } else {
      let i = pad.len().try_into().expect("too much padding");
      let t = app!(build, (padn[i]));
      let st = app!(build, (sadd s t));
      let n = build.hex.h2n(&mut build.thm, i);
      let (z, h2) = build.hex.add(&mut build.thm, y2, n);
      let th = thm!(build, (assemble[st, start, *z, a2]) =>
        assemble_pad(a, *n, s, t, start, *y2, *z, th, h2)((strlen_padn[i](): (strlen t {*n}))));
      (st, z, th)
    };

    let code = self.mangler.mangle(self.elab, Name::ProcContent(proc.name()));
    let code = self.elab.env.add_term({
      let mut de = ExprDedup::new(self.pd, &[]);
      let e = build.thm.to_expr(&mut de, s);
      de.build_def0(code, Modifiers::LOCAL, self.span.clone(), self.full, e, self.pd.string)
    }).map_err(|e| e.into_elab_error(self.full))?;

    let asm = self.mangler.mangle(self.elab, Name::ProcAsm(proc.name()));
    let asm = self.elab.env.add_term({
      let mut de = ExprDedup::new(self.pd, &[]);
      let e = build.thm.to_expr(&mut de, a);
      de.build_def0(asm, Modifiers::LOCAL, self.span.clone(), self.full, e, self.pd.set)
    }).map_err(|e| e.into_elab_error(self.full))?;

    let th = thm!(build.thm, ((assemble ({code}) start end (asmProc start ({asm})))) =>
      CONV({th} => (assemble (UNFOLD({code}); s) start end (asmProc start (UNFOLD({asm}); a)))));
    let asm_thm = self.mangler.mangle(self.elab, Name::ProcAsmThm(proc.name()));
    let asm_thm = self.elab.env
      .add_thm(build.thm.build_thm0(asm_thm, Modifiers::empty(), self.span.clone(), self.full, th))
      .map_err(|e| e.into_elab_error(self.full))?;
    self.proc_asm.insert(proc.name(), (asm, ThmId(0)));

    // Import into the context of the global (Name::Content) proof
    let s = app!(self.thm, ({code}));
    let end = Num::new(end_val, build.to_expr(&mut self.thm, end));
    let a = app!(self.thm, (asmProc global_start ({asm})));
    Ok((s, end, a, thm!(self.thm, {asm_thm}(): (assemble s global_start {*end} a))))
  }

  fn assemble(&mut self, proof: &'a ElfProof<'a>) -> Result<()> {
    let mut iter = proof.assembly();
    let x = self.hex.from_u32(&mut self.thm, TEXT_START);
    let (c, y, a, h1) = self.bisect(iter.len(), &mut iter, *x, &mut |this, item, x| {
      match item {
        AssemblyItem::Proc(proc) => this.assemble_proc(&proc, x),
        AssemblyItem::Const(_) => todo!(),
      }
    })?;
    let h2 = HexCache::is_u64(&mut self.thm, *y);
    let th = thm!(self.thm, assembledI(a, c, *y, h1, h2): (assembled c a));

    let content = self.mangler.mangle(self.elab, Name::Content);
    let content = self.elab.env.add_term({
      let mut de = ExprDedup::new(self.pd, &[]);
      let e = self.thm.to_expr(&mut de, c);
      de.build_def0(content, Modifiers::LOCAL, self.span.clone(), self.full, e, self.pd.string)
    }).map_err(|e| e.into_elab_error(self.full))?;

    let th = thm!(self.thm, ((assembled ({content}) a)) =>
      CONV({th} => (assembled (UNFOLD({content}); c) a)));
    let asmd_thm = self.mangler.mangle(self.elab, Name::AsmdThm);
    let asmd_thm = self.elab.env
      .add_thm(self.thm.build_thm0(asmd_thm, Modifiers::empty(), self.span.clone(), self.full, th))
      .map_err(|e| e.into_elab_error(self.full))?;

    let mut iter = proof.assembly();
    self.prove_conjuncts(iter.len(), &mut iter, &|this, de| de.thm0(this.elab, asmd_thm))
  }

  fn mk_lemma(&mut self,
    mk_proof: &dyn Fn(&Self, &mut ProofDedup<'a>) -> ProofId
  ) -> Result<ThmId> {
    let mut de = ProofDedup::new(self.pd, &[]);
    let th = mk_proof(self, &mut de);
    let lem = self.mangler.mangle(self.elab, Name::AsmdThmLemma(self.asmd_lemmas));
    self.asmd_lemmas += 1;
    self.elab.env
      .add_thm(de.build_thm0(lem, Modifiers::empty(), self.span.clone(), self.full, th))
      .map_err(|e| e.into_elab_error(self.full))
  }

  fn prove_conjuncts(&mut self,
    n: usize, iter: &mut AssemblyItemIter<'a>,
    mk_proof: &dyn Fn(&Self, &mut ProofDedup<'a>) -> ProofId,
  ) -> Result<()> {
    if n <= 1 {
      assert!(n != 0);
      let item = iter.next().expect("iterator size lied");
      let mut de = ProofDedup::new(self.pd, &[]);
      let th = mk_proof(self, &mut de);
      match item {
        AssemblyItem::Proc(proc) => {
          let asmd_thm = self.mangler.mangle(self.elab, Name::ProcAsmdThm(proc.name()));
          let asmd_thm = self.elab.env
            .add_thm(de.build_thm0(asmd_thm, Modifiers::empty(), self.span.clone(), self.full, th))
            .map_err(|e| e.into_elab_error(self.full))?;
          self.proc_asm.get_mut(&proc.name()).expect("impossible").1 = asmd_thm;
        }
        AssemblyItem::Const(_) => todo!(),
      }
      Ok(())
    } else {
      let m = n >> 1;
      let left = |this: &Self, de: &mut ProofDedup<'a>| {
        let th = mk_proof(this, de);
        let (c, a, b) = app_match!(de, de.concl(th) => {
          (assembled c (assembleA a b)) => (c, a, b),
          !
        });
        thm!(de, assembled_l(a, b, c, th): (assembled c a))
      };
      let right = |this: &Self, de: &mut ProofDedup<'a>| {
        let th = mk_proof(this, de);
        let (c, a, b) = app_match!(de, de.concl(th) => {
          (assembled c (assembleA a b)) => (c, a, b),
          !
        });
        thm!(de, assembled_r(a, b, c, th): (assembled c b))
      };
      if n > 16 {
        let lem1 = self.mk_lemma(&left)?;
        self.prove_conjuncts(m, iter, &|this, de| de.thm0(this.elab, lem1))?;
        let lem2 = self.mk_lemma(&right)?;
        self.prove_conjuncts(n - m, iter, &|this, de| de.thm0(this.elab, lem2))
      } else {
        self.prove_conjuncts(m, iter, &left)?;
        self.prove_conjuncts(n - m, iter, &right)
      }
    }
  }
}

pub(super) fn assemble_proof(
  elab: &mut Elaborator,
  pd: &Predefs,
  proc_asm: &mut HashMap<Option<Symbol>, (TermId, ThmId)>,
  mangler: &Mangler,
  proof: &ElfProof<'_>,
  span: &FileSpan,
  full: Span,
) -> Result<()> {
  let mut thm = ProofDedup::new(pd, &[]);
  let mut build = BuildAssembly {
    proc_asm,
    mangler,
    elab,
    pd,
    span,
    full,
    hex: HexCache::new(&mut thm),
    thm,
    asmd_lemmas: 0,
  };
  build.assemble(proof)?;
  Ok(())
}
