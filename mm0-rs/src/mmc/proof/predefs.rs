use std::collections::HashSet;
use if_chain::if_chain;
use mm0_util::{AtomId, SortId, TermId, ThmId};
use debug_derive::EnvDebug;

use crate::{DeclKey, Environment};

fn mk_array<A, const N: usize>(mut f: impl FnMut(usize) -> A) -> [A; N] {
  let mut i = 0_usize;
  [(); N].map(|()| { let a = f(i); i += 1; a })
}

fn mk_remap<'a, A, const N: usize>(
  arr: &'a [A; N],
  mut f: impl FnMut(usize, &'a A) -> A
) -> [A; N] {
  let mut i = 0_usize;
  [(); N].map(|()| { let a = f(i, &arr[i]); i += 1; a })
}

fn get_sort(env: &Environment, s: &[u8]) -> SortId {
  if_chain! {
    if let Some(&a) = env.atoms.get(s);
    if let Some(sort) = env.data[a].sort;
    then { sort }
    else { panic!("sort {} not found", std::str::from_utf8(s).expect("utf8")) }
  }
}
fn get_term(env: &Environment, s: &[u8]) -> TermId {
  if_chain! {
    if let Some(&a) = env.atoms.get(s);
    if let Some(DeclKey::Term(t)) = env.data[a].decl;
    then { t }
    else { panic!("term {} not found", std::str::from_utf8(s).expect("utf8")) }
  }
}
fn get_thm(env: &Environment, s: &[u8]) -> ThmId {
  if_chain! {
    if let Some(&a) = env.atoms.get(s);
    if let Some(DeclKey::Thm(t)) = env.data[a].decl;
    then { t }
    else { panic!("thm {} not found", std::str::from_utf8(s).expect("utf8")) }
  }
}

trait PredefId<R>: Copy {
  fn premap(self, r: &mut R) -> Self { self }
}
impl PredefId<crate::Remapper> for AtomId {
  fn premap(self, r: &mut crate::Remapper) -> Self { use crate::Remap; self.remap(r) }
}
impl PredefId<crate::Remapper> for SortId {
  fn premap(self, r: &mut crate::Remapper) -> Self { use crate::Remap; self.remap(r) }
}
impl PredefId<crate::Remapper> for TermId {
  fn premap(self, r: &mut crate::Remapper) -> Self { use crate::Remap; self.remap(r) }
}
impl PredefId<crate::Remapper> for ThmId {
  fn premap(self, r: &mut crate::Remapper) -> Self { use crate::Remap; self.remap(r) }
}
impl crate::Remap for Predefs {
  type Target = Self;
  fn remap(&self, r: &mut crate::Remapper) -> Self { self.premap(r) }
}

macro_rules! make_predefs {
  (@ty $ty:tt $n:expr, $($ns:expr,)*) => {[make_predefs!(@ty $ty $($ns,)*); $n]};
  (@ty $ty:ident) => {$ty};
  (@new $ty:tt $env:expr, ($i:ident, $($is:ident,)*) $cond:tt $e:tt) => {
    mk_array(|$i| make_predefs!(@new $ty $env, ($($is,)*) $cond $e))
  };
  (@new $ty:ident $env:expr, () ($cond:expr) $e:tt) => {
    if $cond { make_predefs!(@new $ty $env, () () $e) } else { $ty::INVALID }
  };
  (@new $ty:ident $env:expr, () () ($base:ident)) => {
    make_predefs!(@new $ty $env, () () ($base => stringify!($base)))
  };
  (@new AtomId $env:expr, () () ($_:ident => $e:expr)) => { $env.get_atom($e.as_bytes()) };
  (@new SortId $env:expr, () () ($_:ident => $e:expr)) => { get_sort($env, $e.as_bytes()) };
  (@new TermId $env:expr, () () ($_:ident => $e:expr)) => { get_term($env, $e.as_bytes()) };
  (@new ThmId $env:expr, () () ($_:ident => $e:expr)) => { get_thm($env, $e.as_bytes()) };
  (@remap $ty:tt $self:expr, $r:expr, ($i:ident, $($is:ident,)*) $cond:tt) => {
    mk_remap($self, |$i, this| make_predefs!(@remap $ty this, $r, ($($is,)*) $cond))
  };
  (@remap $ty:ident $self:expr, $r:expr, () ($cond:expr)) => {
    if $cond { make_predefs!(@remap $ty $self, $r, () ()) } else { $ty::INVALID }
  };
  (@remap $ty:ident $self:expr, $r:expr, () ()) => {$self.premap($r)};
  {$($(#[$attr:meta])* $x:ident $([$i:ident: $n:expr])*:
      $ty:tt $(if $cond:expr)? $(=> $e:expr)?;)*} => {
    /// A predef is a name of an external constant, defined in `compiler.mm1` and required
    /// for proof output.
    #[derive(Copy, Clone, Debug, EnvDebug)]
    pub(crate) struct Predefs {
      $(
        #[allow(non_snake_case)] $(#[$attr])*
        pub(crate) $x: make_predefs!(@ty $ty $($n,)*),
      )*
    }
    #[cfg(feature = "memory")] mm0_deepsize::deep_size_0!(Predefs);

    impl Predefs {
      fn premap<R>(&self, r: &mut R) -> Self where
        AtomId: PredefId<R>,
        SortId: PredefId<R>,
        TermId: PredefId<R>,
        ThmId: PredefId<R>,
      {
        #[allow(unused)]
        Self { $($x: make_predefs!(@remap $ty &self.$x, r, ($($i,)*) ($($cond)?))),* }
      }
    }

    impl Predefs {
      /// Construct a `Predefs` from an environment.
      pub(crate) fn new(env: &mut crate::Environment) -> Self {
        #[allow(clippy::string_lit_as_bytes)]
        Self { $($x: make_predefs!(@new $ty env, ($($i,)*) ($($cond)?) ($x $(=> $e)?))),* }
      }
    }
  };
}

make_predefs! {
  /// `$F.$: wff`
  fal: TermId;
  /// `$T.$: wff`
  tru: TermId;
  /// `eq: nat > nat > wff`
  eq: TermId;
  /// `eq: nat > nat > wff`
  ne: TermId;
  /// `strict sort set;`
  set: SortId;
  /// `0: nat`
  d0: TermId;
  /// `suc: nat > nat`
  suc: TermId;
  /// `add: nat > nat > nat`
  add: TermId;
  /// `mul: nat > nat > nat`
  mul: TermId;
  /// `le: nat > nat > wff`
  le: TermId;
  /// `lt: nat > nat > wff`
  lt: TermId;
  /// `ltlei (h: $ a < b $): $ a <= b $`
  ltlei: ThmId;
  /// `ltnei (h: $ a < b $): $ a != b $`
  ltnei: ThmId;
  /// `ltneri (h: $ a < b $): $ b != a $`
  ltneri: ThmId;
  /// `leid: $ a <= a $`
  leid: ThmId;
  /// `znsub: `
  znsub: TermId;
  /// `pr: nat > nat > nat`
  pr: TermId;
  /// `cons: nat > nat > nat`
  cons: TermId;
  /// `strict sort string;`
  string: SortId;
  /// `sadd: string > string > string`
  sadd: TermId;
  /// `sadd: char > string > string`
  scons: TermId;
  /// `s0: string`
  s0: TermId;
  /// `s1: char > string`
  s1: TermId;
  /// `d[0..=f]: nat`
  dn[i: 17]: TermId => format!("d{i}");
  /// `x[0..=f]: hex`
  xn[i: 16]: TermId => format!("x{i:x}");
  /// `h2n: hex > nat`
  h2n: TermId;
  /// `hex: nat > hex > nat`
  hex: TermId;
  /// `ch: hex > hex > char`
  ch: TermId;
  /// `c2n: char > nat`
  c2n: TermId;
  /// `s2n: string > nat`
  s2n: TermId;
  /// `h2n[0..=f]: x[i] = d[i]`
  h2nn[i: 16]: ThmId => format!("h2n{i:x}");
  /// `decsucxf (a b c): suc a = b > suc (hex a xf) (hex b x0)`
  decsucxf: ThmId;
  /// `decsucx (a b c): suc b = c > suc (hex a b) (hex a c)`
  decsucx: ThmId;
  /// `decsuc[0..f]: suc x[a] = hex(a+1)`
  decsucn[i: 16]: ThmId => format!("decsuc{i:x}");
  /// `declt[0..f][0..=f]: x[a] < x[b]` for `a < b`
  decltn[a: 15][b: 16]: ThmId if a < b => format!("declt{a:x}{b:x}");
  /// `decltx1 (h: $ a < c $): $ a :x b < c :x d $`
  decltx1: ThmId;
  /// `decltx2 (h: $ b < c $): $ a :x b < a :x c $`
  decltx2: ThmId;
  /// `declt0x (h: $ x0 < b $): $ h2n a < b :x c $`
  declt0x: ThmId;
  /// `decadd[0..=f][0..=f]: x[a] + x[b] = hex(a+b)`
  decaddn[a: 16][b: 16]: ThmId => format!("decadd{a:x}{b:x}");
  /// `decadc[0..=f][0..=f]: suc (x[a] + x[b]) = hex(a+b+1)`
  decadcn[a: 16][b: 16]: ThmId => format!("decadc{a:x}{b:x}");

  // Theorems to compute `a + b = c` and `suc (a + b) = c`
  add_xx0: ThmId;
  add_xx1: ThmId;
  add_0x0: ThmId;
  add_0x1: ThmId;
  add_x00: ThmId;
  add_x01: ThmId;
  adc_xx0: ThmId;
  adc_xx1: ThmId;
  adc_0x0: ThmId;
  adc_0x1: ThmId;
  adc_x00: ThmId;
  adc_x01: ThmId;

  /// `bit: nat > nat > nat`
  bit: TermId;
  xbit[n: 16][i: 4]: ThmId => format!("xbit{n:x}{i:x}");

  /// `wSz8 (have_rex: wff): nat`
  wSz8: TermId;
  /// `wSz32: nat`
  wSz32: TermId;
  /// `wSz64: nat`
  wSz64: TermId;

  wsizeBytes: TermId;
  wSz8Bytesx: ThmId;
  wSz32Bytesx: ThmId;
  wSz64Bytesx: ThmId;

  opSize: TermId;
  opSize_64: ThmId;
  opSize_32: ThmId;
  opSize_8: ThmId;

  opSizeW: TermId;
  opSizeW_0: ThmId;
  opSizeW_S: ThmId;

  REX[i: 4]: TermId => ["REX_B", "REX_X", "REX_R", "REX_W"][i];
  REX_0[i: 4]: ThmId => ["REX_B_0", "REX_X_0", "REX_R_0", "REX_W_0"][i];
  REX_Si[i: 4]: ThmId => ["REX_B_Si", "REX_X_Si", "REX_R_Si", "REX_W_Si"][i];

  base_RIP: TermId;
  base_reg: TermId;

  unopInc: TermId;
  unopDec: TermId;
  unopNot: TermId;
  unopNeg: TermId;

  padn[i: 16]: TermId => format!("_x00x{i:x}");

  /// `strlen (s: string) (n: nat): wff`
  strlen: TermId;
  strlenn[i: 16]: ThmId => format!("strlen{i:x}");
  strlen_padn[i: 16]: ThmId if i != 0 => format!("strlen_x00x{i:x}");

  /// `assemble (s: string) (x y: nat) (P: set): wff`
  assemble: TermId;
  /// `assembleA (A B: set): set`
  assembleA: TermId;
  assembleA_I: ThmId;

  /// `ASM0: set`
  ASM0: TermId;
  /// `asmA (A B: set): set`
  ASM_A: TermId;

  /// `localAssemble (p: nat) (s: string) (x y: nat) (P: set): wff`
  localAssemble: TermId;
  localAssembleA_I: ThmId;

  /// `localAssemble0 (p: nat) (x: nat) (P: set): wff`
  localAssemble0: TermId;
  localAssemble0_0: ThmId;
  localAssemble0_l: ThmId;
  localAssemble0_r: ThmId;
  localAssemble0_A: ThmId;

  /// `asmAt (n: nat) (A: set): set`
  asmAt: TermId;
  asmAtI: ThmId;
  asmAt0: ThmId;

  /// `asmEntry (p: nat) (A: set): set`
  asmEntry: TermId;
  asmEntryI: ThmId;
  asmEntry0: ThmId;

  /// `asmProc (n: nat) (A: set): set`
  asmProc: TermId;
  asmProcI: ThmId;
  assemble_pad: ThmId;

  /// `assembled (c: string) (P: set): wff`
  assembled: TermId;
  assembledI: ThmId;
  assembled_l: ThmId;
  assembled_r: ThmId;

  /// `parseInst (p ip: nat) (s: string) (I: set): wff`
  parseInst: TermId;
  parseInstE: ThmId;
  parseInst01: ThmId;
  parseInst11: ThmId;
  parseInst00: ThmId;
  parseInst10: ThmId;

  /// `IRM_reg (reg: hex): nat`
  IRM_reg: TermId;
  /// `IRM_mem (si base off: nat): nat`
  IRM_mem: TermId;
  /// `IRM_imm32 (imm: nat): nat`
  IRM_imm32: TermId;
  /// `IRM_imm64 (imm: nat): nat`
  IRM_imm64: TermId;

  /// `isU64 (n: nat): wff`
  isU64: TermId;
  isU64n[i: 16]: ThmId => format!("isU64_{i:x}");

  /// `parseUBytes (k n: nat) (s: string): wff`
  parseUBytes: TermId;
  parseUBytesS: ThmId;
  parseUBytesS1: ThmId;
  parseUBytesS2: ThmId;
  parseUBytes01: ThmId;
  parseUBytes02: ThmId;

  parseUBytes_x00xn[i: 8]: ThmId if i != 0 => format!("parseUBytes_x00x{i:x}");

  /// `parseIBytesPos (k n: nat) (s: string): wff`
  parseIBytesPos: TermId;
  parseIBytesPosS: ThmId;
  parseIBytesPosS2: ThmId;
  parseIBytesPosS1: ThmId;
  parseIBytesPos02: ThmId;
  parseIBytesPos01: ThmId;

  /// `parseIBytesNeg (k n: nat) (s: string): wff`
  parseIBytesNeg: TermId;
  parseIBytesNegS: ThmId;
  parseIBytesNegS2: ThmId;
  parseIBytesNegS1: ThmId;
  parseIBytesNegS0: ThmId;
  parseIBytesNeg02: ThmId;
  parseIBytesNeg01: ThmId;

  /// `posZ: nat > nat` (the `nat > int` injection)
  posZ: TermId;
  /// `negZ: nat > nat` (semantically `nat > int`, maps `n: nat` to `-n-1: int` )
  negZ: TermId;
  znsub_posZ: ThmId;
  znsub_negZ: ThmId;

  /// `parseImmN (k imm: nat) (s: string): wff`
  parseImmN: TermId;
  parseImmN_pos: ThmId;
  parseImmN_neg: ThmId;

  /// `parseImm8 (imm: nat) (s: string): wff`
  parseImm8: TermId;
  parseImm8_I: ThmId;
  /// `parseImm32 (imm: nat) (s: string): wff`
  parseImm32: TermId;
  parseImm32_I: ThmId;
  /// `parseImm64 (imm: nat) (s: string): wff`
  parseImm64: TermId;
  parseImm64_I: ThmId;
  /// `parseImm8S (imm: nat) (s s2: string): wff`
  parseImm8S: TermId;
  parseImm8S_0: ThmId;
  parseImm8S_I: ThmId;
  /// `parseImm32S (imm: nat) (s s2: string): wff`
  parseImm32S: TermId;
  parseImm32S_0: ThmId;
  parseImm32S_I: ThmId;

  /// `parseImm (sz imm: nat) (s: string): wff`
  parseImm: TermId;
  parseImm_8: ThmId;
  parseImm_32: ThmId;
  parseImm_64: ThmId;

  splitBits[i: 5]: TermId => format!("splitBits{}", SPLIT_BITS_NAMES[i]);
  splitBitsn[i: 5][n: 16]: ThmId => format!("splitBits{}_{n:x}", SPLIT_BITS_NAMES[i]);

  /// `consStr (c: char) (l l2: nat): wff`
  consStr: TermId;
  consStr0: ThmId;
  consStrS: ThmId;

  /// `parseDisplacement (mod q: nat) (l l2: string): wff`
  parseDisplacement: TermId;
  parseDisplacement_0: ThmId;
  parseDisplacement_8: ThmId;
  parseDisplacement_32: ThmId;

  /// `scaleReg (sc: nat) (ix: hex): nat`
  scaleReg: TermId;

  /// `parseSI (sc: nat) (ix: hex) (osi: nat): wff`
  parseSI: TermId;
  parseSI_n[n: 16]: ThmId => format!("parseSI_{n:x}");

  /// `sibSideCond (base: hex) (md: nat): wff`
  sibSideCond: TermId;
  sibSideCond_M[m: 3]: ThmId if m != 0 => format!("sibSideCond_M{m}");
  sibSideCond_B[b: 16]: ThmId if b != 5 => format!("sibSideCond_B{b:x}");

  /// `modrmSideCond (base md: nat): wff`
  modrmSideCond: TermId;
  modrmSideCond_m[m: 3]: ThmId if m != 0 => format!("modrmSideCond_5{m}");
  modrmSideCond_n[n: 8]: ThmId if n != 4 && n != 5 => format!("modrmSideCond_{n:x}");

  /// `parseModRM2 (rex rm rm2 mod: nat) (l l2: string): wff`
  parseModRM2: TermId;
  parseModRM2_reg: ThmId;
  parseModRM2_rip: ThmId;
  parseModRM2_sib0: ThmId;
  parseModRM2_sibReg: ThmId;
  parseModRM2_disp: ThmId;

  /// `parseModRM (rex: nat) (rn: hex) (rm: nat) (l l2: string): wff`
  parseModRM: TermId;
  parseModRM_I: ThmId;

  /// `parseBinop (op: hex) (sz: nat) (dst: hex) (src: nat) (I: set): wff`
  parseBinop: TermId;
  parseBinopBinop: ThmId;
  parseBinopClear32: ThmId;
  parseBinopClear64: ThmId;

  /// `hasREX (rex: nat) (b: wff): wff`
  hasREX: TermId;
  hasREX0: ThmId;
  hasREXS: ThmId;

  /// `instBinop (opc: hex) (sz: nat) (dst: hex) (src: nat): set`
  instBinop: TermId;
  /// `instShift (opc: hex) (sz: nat) (dst: hex) (src: nat): set`
  instShift: TermId;
  /// `instImm (sz: nat) (dst: hex) (src: nat): set`
  instImm: TermId;
  /// `instMovSX (dst_sz: nat) (dst: hex) (src_sz src: nat): set`
  instMovSX: TermId;
  /// `instMovZX (dst_sz: nat) (dst: hex) (src_sz src: nat): set`
  instMovZX: TermId;
  /// `instMov (sz dst src: nat): set`
  instMov: TermId;
  /// `instPush (src: nat): set`
  instPush: TermId;
  /// `instPop (dst: hex): set`
  instPop: TermId;
  /// `instJump (tgt: nat): set`
  instJump: TermId;
  /// `instJCC (c: hex) (tgt: nat): set`
  instJCC: TermId;
  /// `instCall (tgt: nat): set`
  instCall: TermId;
  /// `instRet: set`
  instRet: TermId;
  /// `instCDX (sz: nat): set`
  instCDX: TermId;
  /// `instLea (sz dst si base off: nat): set`
  instLea: TermId;
  /// `instTest (sz src1 src2: nat): set`
  instTest: TermId;
  /// `instUnop (op sz: nat) (dst: hex): set`
  instUnop: TermId;
  /// `instMul (sz src: nat): set`
  instMul: TermId;
  /// `instDiv (sz src: nat): set`
  instDiv: TermId;
  /// `instSetCC (c: hex) (b: wff) (dst: hex): set`
  instSetCC: TermId;
  /// `instCMov (c: hex) (sz dst src: nat): set`
  instCMov: TermId;
  /// `instSysCall: set`
  instSysCall: TermId;
  /// `instUD2: set`
  instUD2: TermId;
  /// `instAssert (c: hex) (tgt: nat): set`
  instAssert: TermId;

  /// `parseOpc (p ip: nat) (s: string) (rex: nat) (opc: char) (I: set): wff`
  parseOpc: TermId;
  parseFallthrough: ThmId;
  parseBinopRAX: ThmId;
  parseBinopImm: ThmId;
  parseBinopImm8: ThmId;
  parseBinopReg: ThmId;
  parseBinopHi: ThmId;
  parseBinopHi1: ThmId;
  parseBinopHiReg: ThmId;
  parseMovSLQ: ThmId;
  parseMovSB: ThmId;
  parseMovZB: ThmId;
  parseMovStore: ThmId;
  parseMovLoad: ThmId;
  parseMovZLQ: ThmId;
  parseMov32: ThmId;
  parseMov64: ThmId;
  parseMovImm: ThmId;
  parsePushImm8: ThmId;
  parsePushImm32: ThmId;
  parsePushReg: ThmId;
  parsePushMem: ThmId;
  parsePopReg: ThmId;
  parseJump8: ThmId;
  parseJump32: ThmId;
  parseJCC8: ThmId;
  parseJCCTwo: ThmId;
  parseCall: ThmId;
  parseRet: ThmId;
  parseCDQ: ThmId;
  parseCQO: ThmId;
  parseLea32: ThmId;
  parseLea64: ThmId;
  parseTest: ThmId;
  parseTestRAX: ThmId;
  parseTestHi: ThmId;
  parseInc: ThmId;
  parseDec: ThmId;
  parseNot: ThmId;
  parseNeg: ThmId;
  parseMul: ThmId;
  parseDiv: ThmId;
  parseSetCC: ThmId;
  parseCMov: ThmId;
  parseSysCall: ThmId;
  parseUD2: ThmId;
  parseAssert: ThmId;

  mkGCtx: TermId;

  getContent: TermId;
  getContentGI: ThmId;

  resultUnit: TermId;

  getResult: TermId;
  getResultGI: ThmId;

  eVar: TermId;
  eInt: TermId;
  E0: TermId;
  eSn: TermId;
  eAppend: TermId;

  e_const: TermId;
  eInt_const: ThmId;

  e_len: TermId;
  e_len_reassoc: ThmId;

  pe0: TermId;
  peListP: TermId;
  peList: TermId;

  pe_layout: TermId;

  tyUnit: TermId;
  tyFalse: TermId;
  tyU8: TermId;
  tyU16: TermId;
  tyU32: TermId;
  tyU64: TermId;
  tyNat: TermId;
  tyI8: TermId;
  tyI16: TermId;
  tyI32: TermId;
  tyI64: TermId;
  tyInt: TermId;
  tyTyped: TermId;
  tyArray: TermId;
  tyNot: TermId;

  ty_sizeof: TermId;

  tyMoved: TermId;
  tyMoved_emp: ThmId;
  tyMoved_false: ThmId;
  tyMoved_u8: ThmId;
  tyMoved_u16: ThmId;
  tyMoved_u32: ThmId;
  tyMoved_u64: ThmId;
  tyMoved_i8: ThmId;
  tyMoved_i16: ThmId;
  tyMoved_i32: ThmId;
  tyMoved_i64: ThmId;
  tyMoved_typed: ThmId;
  tyMoved_array: ThmId;

  tyResult: TermId;
  tyResult_unit: ThmId;

  noRet: TermId;

  epiRet: TermId;
  epiFree: TermId;
  epiPop: TermId;

  mkPCtx1: TermId;
  mkPCtx: TermId;
  mkBCtx: TermId;
  mkTCtx: TermId;

  vctx0: TermId;
  vctxA: TermId;
  vVar: TermId;
  vHyp: TermId;

  okVCtxPush: TermId;
  okVCtxPush_1: ThmId;
  okVCtxPush_S: ThmId;
  okVCtxPush_R: ThmId;
  okVCtxPush_get: ThmId;

  okVCtxGet: TermId;
  okVCtxGet_R: ThmId;
  okVCtxGet_l: ThmId;
  okVCtxGet_r: ThmId;

  okVCtxTake: TermId;
  okVCtxTake_move_var: ThmId;
  okVCtxTake_ref_var: ThmId;
  okVCtxTake_move_hyp: ThmId;
  okVCtxTake_ref_hyp: ThmId;
  okVCtxTake_l: ThmId;
  okVCtxTake_r: ThmId;

  meTyped: TermId;
  mePart: TermId;

  me_sizeof: TermId;

  me_ty_sizeof: TermId;
  meTyped_ty_sizeof: ThmId;
  mePart_ty_sizeof: ThmId;

  e_reassoc: TermId;
  e_reassoc_id: ThmId;
  e_reassoc_assoc: ThmId;

  incMExpr: TermId;
  incMExpr_id: ThmId;
  incMExpr_tr: ThmId;
  incMExpr_nil: ThmId;
  incMExpr_list: ThmId;
  incMExpr_listS: ThmId;
  incMExpr_listC: ThmId;

  pushMExpr: TermId;
  pushMExpr_full: ThmId;
  pushMExpr_trL: ThmId;
  pushMExpr_trR: ThmId;
  pushMExpr_list: ThmId;
  pushMExpr_listS: ThmId;

  mctx0: TermId;
  FREE: TermId;
  stkFREE: TermId;
  REG: TermId;
  mVal: TermId;
  mSpill: TermId;
  mctxA: TermId;

  bddMCtx: TermId;
  bddMCtx_FREE: ThmId;
  bddMCtx_REG: ThmId;
  bddMCtx_A: ThmId;

  okMCtx: TermId;
  okMCtx_0: ThmId;
  okMCtx_S: ThmId;

  pushMCtx: TermId;
  pushMCtx_0: ThmId;
  pushMCtx_1L: ThmId;
  pushMCtx_1R: ThmId;
  pushMCtx_L: ThmId;
  pushMCtx_R: ThmId;
  pushMCtx_rotL: ThmId;
  pushMCtx_rotR: ThmId;

  getMCtxR: TermId;
  getMCtxR_reg: ThmId;
  getMCtxR_L: ThmId;
  getMCtxR_R: ThmId;

  getMCtxS: TermId;
  getMCtxS_val: ThmId;
  getMCtxS_spill: ThmId;
  getMCtxS_L: ThmId;
  getMCtxS_R: ThmId;

  replaceMCtxR: TermId;
  replaceMCtxR_free: ThmId;
  replaceMCtxR_reg: ThmId;
  replaceMCtxR_L: ThmId;
  replaceMCtxR_R: ThmId;
  replaceMCtxR_rotL: ThmId;
  replaceMCtxR_rotR: ThmId;

  replaceMCtxS: TermId;
  replaceMCtxS_split: ThmId;
  replaceMCtxS_startP: ThmId;
  replaceMCtxS_push: ThmId;
  replaceMCtxS_spill: ThmId;
  replaceMCtxS_respill: ThmId;
  replaceMCtxS_L: ThmId;
  replaceMCtxS_R: ThmId;
  replaceMCtxS_rotL: ThmId;
  replaceMCtxS_rotR: ThmId;

  ok0: TermId;

  labelA: TermId;
  label1: TermId;

  findLabel: TermId;
  findLabel_l: ThmId;
  findLabel_r: ThmId;
  findLabel_1: ThmId;

  labelGroup0: TermId;
  labelGroup: TermId;

  findLabels: TermId;
  findLabels_1: ThmId;
  findLabels_S: ThmId;

  okLabelGroups: TermId;
  okLabelGroupsI: ThmId;

  // okPushVar: TermId;
  // okPushVarI: ThmId;

  // okPushHyp: TermId;
  // okPushHypI: ThmId;

  // okReadHyp: TermId;
  // okReadHypHyp: ThmId;
  // okReadHypVar: ThmId;
  // okReadHyp_unit: ThmId;

  okCode: TermId;
  okCode_0: ThmId;
  okCode_id: ThmId;
  okCode_A: ThmId;
  okCode_0A: ThmId;
  okCode_tr: ThmId;
  okCode_trL: ThmId;

  okPrologue: TermId;
  okPrologue_push: ThmId;
  okPrologue_alloc0: ThmId;
  okPrologue_alloc: ThmId;

  okAssembled: TermId;
  okAssembledI: ThmId;
  okAssembled_l: ThmId;
  okAssembled_r: ThmId;

  aVar: TermId;
  aHyp: TermId;
  arg0: TermId;
  argS: TermId;

  accumArgs: TermId;
  accumArgs0: ThmId;
  accumArgsVar: ThmId;
  accumArgsHyp: ThmId;

  mkArgs: TermId;

  clob0: TermId;
  clobS: TermId;

  accumClob: TermId;
  accumClob_0: ThmId;
  accumClob_S: ThmId;

  okProc: TermId;
  okProcI: ThmId;

  buildStart: TermId;
  buildStartI: ThmId;

  okStart: TermId;
  okStartI: ThmId;

  okPushVariant: TermId;

  variantValue: TermId;

  addLabels: TermId;
  addLabels_A: ThmId;
  addLabels_1: ThmId;
  addLabels_0: ThmId;

  okLabels: TermId;
  okLabels_l: ThmId;
  okLabels_r: ThmId;
  okLabels_I: ThmId;
  okLabels_1: ThmId;

  okBlock: TermId;
  okBlock_weak: ThmId;
  okBlock_I: ThmId;
  okBlock_0: ThmId;
  okBlock_label: ThmId;

  checkRet: TermId;
  checkRetI: ThmId;

  okEpilogue: TermId;
  okEpilogue_ret: ThmId;
  okEpilogue_pop: ThmId;
  okEpilogue_free: ThmId;
  okEpilogue_E: ThmId;

  getEpi: TermId;
  getEpiI: ThmId;

  // Loc_reg: TermId;
  // Loc_local: TermId;

  // spillslot: TermId;

  // okRead: TermId;

  // okWrite: TermId;

  okConst: TermId;
  okConst_i8_pos: ThmId;
  okConst_i8_neg: ThmId;
  okConst_i32: ThmId;
  okConst_i64_32: ThmId;
  okConst_i64: ThmId;
  okConst_u8: ThmId;
  okConst_u32_pos: ThmId;
  okConst_u64_32_pos: ThmId;
  okConst_u64_pos: ThmId;
  okConst_u32_neg: ThmId;
  okConst_u64_neg: ThmId;

  withFlags: TermId;
  invertCond: TermId;
  flagCond: TermId;

  // okDefer: TermId;
  // okDeferI: ThmId;

  subst0: TermId;
  substS: TermId;

  substTy: TermId;

  buildSubst: TermId;
  buildSubst_0: ThmId;
  buildSubst_var: ThmId;
  buildSubst_hyp: ThmId;

  applyCall: TermId;
  applyCall_I: ThmId;

  applyCallG: TermId;
  applyCallG_I: ThmId;

  ok_movRR: ThmId;
  ok_load: ThmId;
  ok_load64: ThmId;
  ok_store: ThmId;
  ok_store64: ThmId;
  ok_jump: ThmId;
  ok_loadImm: ThmId;
  // ok_jcc: ThmId;
  // ok_jcc_invert: ThmId;
  ok_ud2: ThmId;
  // ok_assert: ThmId;
  ok_call_func: ThmId;
  ok_call_func_0: ThmId;
  ok_call_proc: ThmId;
  ok_fail: ThmId;
  ok_exit: ThmId;

  // basicElf_ok: ThmId;
  ELF_lit: TermId;
  okProg: TermId;
  okProgI: ThmId;

  sorry: ThmId; // delete me
}

impl Predefs {
  pub(crate) fn collect(&self, env: &crate::Environment, f: impl FnMut(AtomId)) {
    struct Collect<'a, F> {
      env: &'a crate::Environment,
      f: F,
    }
    impl<F: FnMut(AtomId)> PredefId<Collect<'_, F>> for AtomId {
      fn premap(self, r: &mut Collect<'_, F>) -> Self { (r.f)(self); self }
    }
    impl<F: FnMut(AtomId)> PredefId<Collect<'_, F>> for SortId {
      fn premap(self, r: &mut Collect<'_, F>) -> Self { (r.f)(r.env.sorts[self].atom); self }
    }
    impl<F: FnMut(AtomId)> PredefId<Collect<'_, F>> for TermId {
      fn premap(self, r: &mut Collect<'_, F>) -> Self { (r.f)(r.env.terms[self].atom); self }
    }
    impl<F: FnMut(AtomId)> PredefId<Collect<'_, F>> for ThmId {
      fn premap(self, r: &mut Collect<'_, F>) -> Self { (r.f)(r.env.thms[self].atom); self }
    }
    self.premap(&mut Collect { env, f });
  }
}

pub(crate) enum Rex {
  B = 0,
  X = 1,
  R = 2,
  W = 3,
}

const SPLIT_BITS_NAMES: [&str; 5] = ["13", "22", "31", "121", "1111"];
#[derive(Copy, Clone)]
pub(crate) enum SplitBits {
  Sb13 = 0,
  Sb22 = 1,
  Sb31 = 2,
  Sb121 = 3,
  Sb1111 = 4,
}
