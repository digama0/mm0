use mm0_util::{AtomId, FileSpan, Modifiers, Span};
use mmcc::{arch::{OpcodeLayout, PInst}, proof::{AssemblyBlocks, Inst, Proc}, types::Size};

use super::{ProofDedup, Predefs, predefs::Rex, ProofId, Dedup, norm_num::{HexCache, Num}};

pub(super) struct BuildAssemblyProc<'a> {
  pub(super) thm: ProofDedup<'a>,
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

enum DecodeResult {
  Reg,
  Jump { tgt: Num, c: ProofId, q: ProofId },
  Call { tgt: Num, q: ProofId }
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
fn parse_u64(p: &mut &[u8]) -> u64 { u64::from_le_bytes(parse_arr(p)) }

type P<A> = (A, ProofId);

impl BuildAssemblyProc<'_> {
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

  /// Proves `(a, |- REX_[B/X/R/W] rex = d[a])`
  fn rex_val(&mut self, rex: P<Option<u8>>, val: Rex) -> (P<u8>, ProofId) {
    let i = val as u8;
    if let Some(n) = rex.0 {
      let (a, th) = self.xbit(n, i);
      (a, thm!(self.thm, REX_Si[i](a.1, rex.1, th): ((REX[i]) {rex.1}) = {a.1}))
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
    if let Some(rex) = rex.0 {
      let (w, h1) = self.xbit(rex, 3);
      let rex = self.xn(rex);
      let [a, h2] = self.op_size(true, w, v);
      [a, thm!(self.thm, opSizeW_S(a, rex.1, v.1, w.1, h1, h2): (opSizeW {rex.1} {v.1}) = a)]
    } else {
      let [a, p] = self.op_size(false, (0, rex.1), v);
      [a, thm!(self.thm, opSizeW_0(a, v.1): (opSizeW {rex.1} {v.1}) = a)]
    }
  }

  /// Proves `[k, n, s, |- parseIBytesPos k n s]`.
  /// The bytes to parse come from the first `k+1` bytes of `p`.
  fn parse_ibytes_pos(&mut self, p: &mut &[u8], mut k: u8) -> [ProofId; 4] {
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
      let [k, imm, s, pr] = self.parse_ibytes_pos(p, k);
      let imm2 = app!(self.thm, (posZ imm));
      [k, imm2, s, thm!(self.thm, parseImmN_pos(k, imm, s, pr): (parseImm k imm2 s))]
    } else {
      let [k, imm, s, pr] = self.parse_ibytes_neg(p, k);
      let imm2 = app!(self.thm, (negZ imm));
      [k, imm2, s, thm!(self.thm, parseImmN_neg(k, imm, s, pr): (parseImm k imm2 s))]
    }
  }

  /// Proves `[imm, s, |- parseImm8 imm s]`
  fn parse_imm_8(&mut self, p: &mut &[u8]) -> [ProofId; 3] {
    let [_, imm, s, pr] = self.parse_imm_n(p, 0);
    [imm, s, thm!(self.thm, parseImm8_I(imm, s, pr): (parseImm8 imm s))]
  }

  /// Proves `[imm, s, |- parseImm32 imm s]`
  fn parse_imm_32(&mut self, p: &mut &[u8]) -> [ProofId; 3] {
    let [_, imm, s, pr] = self.parse_imm_n(p, 3);
    [imm, s, thm!(self.thm, parseImm32_I(imm, s, pr): (parseImm32 imm s))]
  }

  /// Proves `[imm, s, |- parseImm64 imm s]`
  fn parse_imm_64(&mut self, p: &mut &[u8]) -> [ProofId; 3] {
    let [_, imm, s, pr] = self.parse_imm_n(p, 7);
    [imm, s, thm!(self.thm, parseImm64_I(imm, s, pr): (parseImm64 imm s))]
  }

  /// Proves `[imm, s, |- parseImm sz imm s]`
  fn parse_imm(&mut self, p: &mut &[u8], sz: ProofId) -> [ProofId; 3] {
    app_match!(self.thm, sz => {
      (wSz8 r) => {
        let [imm, s, pr] = self.parse_imm_8(p);
        [imm, s, thm!(self.thm, parseImm_8(imm, r, s, pr): (parseImm sz imm s))]
      }
      (wSz32) => {
        let [imm, s, pr] = self.parse_imm_32(p);
        [imm, s, thm!(self.thm, parseImm_32(imm, s, pr): (parseImm sz imm s))]
      }
      (wSz64) => {
        let [imm, s, pr] = self.parse_imm_64(p);
        [imm, s, thm!(self.thm, parseImm_64(imm, s, pr): (parseImm sz imm s))]
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

  /// Proves `([rn, rm, l, l2, |- parseModRM_N rex rn rm l l2], r)`
  /// if `f` produces `(l2, r)`.
  fn parse_modrm_then<R>(&mut self, p: &mut &[u8],
    rex: P<Option<u8>>,
    f: impl FnOnce(&mut Self, &mut &[u8]) -> (ProofId, R)
  ) -> ([ProofId; 5], R) {
    /// Get the ModRM byte
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
            h1, h2, h3, h4, h5, h6, h7, h8)))
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
      (s, thm!(self, (parseModRM[rex.1, rn.1, rm, rm2.1, s, l2]) =>
        parseModRM_1(l2, md.1, o.1, pc.1, r.1, rex.1, rm, rm2.1,
          rn.1, self.hex[x], self.hex[y], h1, h2, h3, h4, h5)))
    } else {
      let s = app!(self.thm, (scons modrmch l));
      (s, thm!(self, (parseModRM[rex.1, rn.1, rm, rm2.1, s, l2]) =>
        parseModRM_S(l, l2, md.1, o.1, pc.1, r.1, rex.1, rm, rm2.1,
          rn.1, self.hex[x], self.hex[y], h1, h2, h3, h4, h5)))
    };
    ([rn.1, rm, s, l2, th], ret)
  }

  /// Proves `[I, |- parseBinop opc sz dst src I]`.
  fn parse_binop(&mut self, pinst: &PInst,
    op: u8, sz: ProofId, dst: u8, src: ProofId
  ) -> [ProofId; 2] {
    let (op, dst) = (self.hex[op], self.hex[dst]);
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
        let ([v, eq1, o], h1) = self.hex.split_bits_121(&mut self.thm, y);
        let ([pc, eq2], h2) = self.hex.split_bits_22(&mut self.thm, x);
        let opc = (opc >> 3) & 7;
        let ([eq3, eq4, eq5], h3) = self.hex.split_bits_121(&mut self.thm, opc);
        assert!((eq1.0, eq2.0, eq3, eq4, eq5.0) == (2, 0, o, pc, 0));
        let [sz, h4] = self.op_size_w(rex, v);
        let [src, l, h5] = self.parse_imm(p, sz);
        let esrc = app!(self.thm, (IRM_imm32 src));
        let [inst, h6] = self.parse_binop(pinst, opc, sz, 0, esrc);
        let th = thm!(self, (parseOpc[*self.start, *ip, l, rex.1, opch, inst]) =>
          parseBinopRAX(inst, *ip, l, o.1, self.hex[opc], *self.start,
            pc.1, rex.1, src, sz, v.1, self.hex[x], self.hex[y],
            h1, h2, h3, h4, h5, h6));
        [l, opch, inst, th]
      }
      OpcodeLayout::BinopImm(..) => todo!(),
      OpcodeLayout::BinopImm8(_) => todo!(),
      OpcodeLayout::BinopReg(_) => todo!(),
      OpcodeLayout::BinopHi(_) => todo!(),
      OpcodeLayout::BinopHi1(_) => todo!(),
      OpcodeLayout::BinopHiReg(_) => todo!(),
      OpcodeLayout::MovSX(_) => todo!(),
      OpcodeLayout::MovReg(_) => todo!(),
      OpcodeLayout::Mov32 => todo!(),
      OpcodeLayout::Mov64 => todo!(),
      OpcodeLayout::MovImm(_) => todo!(),
      OpcodeLayout::PushImm(_) => todo!(),
      OpcodeLayout::PushReg => todo!(),
      OpcodeLayout::PopReg => todo!(),
      OpcodeLayout::Jump(_) => todo!(),
      OpcodeLayout::Jcc8 => todo!(),
      OpcodeLayout::Call => todo!(),
      OpcodeLayout::Ret => todo!(),
      OpcodeLayout::Cdx => todo!(),
      OpcodeLayout::Lea(_) => todo!(),
      OpcodeLayout::Test(_) => todo!(),
      OpcodeLayout::TestRAX(_) => todo!(),
      OpcodeLayout::Hi(_) => todo!(),
      OpcodeLayout::HiTest(..) => todo!(),
      OpcodeLayout::SetCC(_) => todo!(),
      OpcodeLayout::CMov(_) => todo!(),
      OpcodeLayout::MovX(_) => todo!(),
      OpcodeLayout::Jcc => todo!(),
      OpcodeLayout::SysCall => todo!(),
      OpcodeLayout::Assert => todo!(),
      OpcodeLayout::Ud2 => todo!(),
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
      let [s, opc, inst, pr] = self.parse_opc(inst.inst, p, inst.layout.opc, ip, srex);
      if short {
        let s2 = app!(self, (scons (ch {self.hex[4]} hrex) (s1 opc)));
        let pr = thm!(self, parseInst10(inst, *ip, opc, *self.start, hrex, pr):
          parseInst[*self.start, *ip, s2, inst]);
        [inst, s2, pr]
      } else {
        let s2 = app!(self, (scons (ch {self.hex[4]} hrex) (scons opc s)));
        let pr = thm!(self, parseInst11(inst, *ip, opc, *self.start, hrex, s, pr):
          parseInst[*self.start, *ip, s2, inst]);
        [inst, s2, pr]
      }
    } else {
      let rex = app!(self, (d0));
      let [s, opc, inst, pr] = self.parse_opc(inst.inst, p, inst.layout.opc, ip, (None, rex));
      if short {
        let s2 = app!(self, (s1 opc));
        let pr = thm!(self, parseInst00(inst, *ip, opc, *self.start, pr):
          parseInst[*self.start, *ip, s2, inst]);
        [inst, s2, pr]
      } else {
        let s2 = app!(self, (scons opc s));
        let pr = thm!(self, parseInst01(inst, *ip, opc, *self.start, s, pr):
          parseInst[*self.start, *ip, s2, inst]);
        [inst, s2, pr]
      }
    }
  }

  fn bisect<T>(&mut self,
    n: usize, iter: &mut impl Iterator<Item=T>, x: Num, padding: Option<&[u8]>,
    f: &mut impl FnMut(&mut Self, T, Num, Option<&[u8]>) -> (ProofId, ProofId, Num, ProofId),
  ) -> (ProofId, ProofId, Num, ProofId) {
    if n <= 1 {
      assert!(n != 0);
      let item = iter.next().expect("iterator size lied");
      f(self, item, x, padding)
    } else {
      let m = n >> 1;
      let (s, a, y, pr1) = self.bisect(m, iter, x, None, f);
      let (t, b, z, pr2) = self.bisect(n - m, iter, y, padding, f);
      let st = app!(self, (sadd s t));
      let ab = app!(self, (asmp_A a b));
      let pr = thm!(self, is_asmp_A(*self.start, s, t, *x, *y, *z, a, b):
        is_asmp[*self.start, st, *x, *z, ab]);
      (st, ab, z, pr)
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
          let res = app!(self, (len s) = {*n});
          let th = self.strlenn[args.len()];
          return (n, self.thm(th, &args, res))
        }
        (s0) => {
          assert!(args.is_empty());
          let n = self.hex.h2n(&mut self.thm, 0);
          return (n, thm!(self, strlenn[0_usize](): (len s) = {*n}))
        }
        _ => panic!("not a string literal"),
      })
    }
  }

  /// Given `x`, proves `(s, A, y, |- is_asmp start s x y A)` where
  /// `s` is generated from the assembly blocks.
  pub(super) fn proc(&mut self, proc: &Proc<'_>) -> (ProofId, ProofId, Num, ProofId) {
    let mut iter = proc.assembly_blocks();
    let x = self.hex.h2n(&mut self.thm, 0);
    let pad = proc.trailing_padding();
    let pad = if pad.is_empty() { None } else { Some(pad) };
    self.bisect(iter.len(), &mut iter, x, pad, &mut |this, block, x, pad| {
      let mut iter = block.insts();
      let (s, a, y, pr) = this.bisect(iter.len(), &mut iter, x, None, &mut |this, inst, x, _| {
        let n = this.hex.from_u8(&mut this.thm, inst.layout.len());
        let (y, h2) = this.hex.add(&mut this.thm, x, n);
        let [s, inst, h3] = this.parse_inst(&inst, y);
        let (n2, h1) = this.strlen(s); assert!(n == n2);
        let pr = thm!(this, parseInstE(*this.start, s, *x, *y, *n, inst, h1, h2, h3):
          is_asmp[*this.start, s, *x, *y, inst]);
        (s, inst, y, pr)
      });

      let a2 = app!(this.thm, (asmp_at {*x} a));
      let pr = thm!(this.thm, is_asmp_at(*this.start, s, *x, *y, a):
        is_asmp[*this.start, s, *x, *y, a2]);
      if let Some(pad) = pad {
        let i = pad.len().try_into().expect("too much padding");
        let st = app!(this, (sadd s (padn[i])));
        let ab = app!(this, (asmp_A a (asmp_pad)));
        let n = this.hex.h2n(&mut this.thm, i);
        let (z, h2) = this.hex.add(&mut this.thm, y, n);
        let pr = thm!(this, is_asmp_A_padn[i](*this.start, s, *x, *y, *z, a, pr, h2):
          is_asmp[*this.start, st, *x, *z, ab]);
        (st, ab, z, pr)
      } else {
        (s, a2, y, pr)
      }
    })
  }
}

pub(super) fn assemble_proc(
  pd: &Predefs,
  name: AtomId,
  proc: &Proc<'_>,
  span: FileSpan,
  full: Span,
) -> crate::Thm {
  let mut thm = ProofDedup::new(pd, &[]);
  let hex = HexCache::new(&mut thm);
  let mut build = BuildAssemblyProc {
    start: hex.from_u64(&mut thm, proc.start.into()),
    hex,
    thm,
  };
  let pr = build.proc(proc).3;
  build.thm.build_thm0(name, Modifiers::empty(), span, full, pr)
}