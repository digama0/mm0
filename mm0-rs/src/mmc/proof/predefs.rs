use mm0_util::{TermId, ThmId};

use crate::{DeclKey, Environment};

fn mk_array<A, const N: usize>(mut f: impl FnMut(usize) -> A) -> [A; N] {
  let mut i = 0_usize;
  [(); N].map(|_| { let a = f(i); i += 1; a })
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

macro_rules! make_predefs {
  (@ty $ty:tt $n:expr, $($ns:expr,)*) => {[make_predefs!(@ty $ty $($ns,)*); $n]};
  (@ty $ty:ident) => {$ty};
  (@new $ty:tt $env:expr, ($i:ident, $($is:ident,)*) $cond:tt $e:expr) => {
    mk_array(|$i| make_predefs!(@new $ty $env, ($($is,)*) $cond $e))
  };
  (@new $ty:ident $env:expr, () ($cond:expr) $e:expr) => {
    if $cond { make_predefs!(@new $ty $env, () () $e) } else { $ty(0) }
  };
  (@new AtomId $env:expr, () () $e:expr) => { $env.get_atom($e) };
  (@new TermId $env:expr, () () $e:expr) => { get_term($env, $e) };
  (@new ThmId $env:expr, () () $e:expr) => { get_thm($env, $e) };
  {$($(#[$attr:meta])* $x:ident $([$i:ident: $n:expr])*:
      $ty:tt $(if $cond:expr)? => $e:expr;)*} => {
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

    impl crate::Remap for Predefs {
      type Target = Self;
      fn remap(&self, r: &mut crate::Remapper) -> Self {
        Self { $($x: self.$x.remap(r)),* }
      }
    }

    impl Predefs {
      /// Construct a `Predefs` from an environment.
      pub(crate) fn new(env: &mut crate::Environment) -> Self {
        #[allow(clippy::string_lit_as_bytes)]
        Self { $($x: make_predefs!(@new $ty env, ($($i,)*) ($($cond)?) $e.as_bytes())),* }
      }
    }
  };
}

make_predefs! {
  /// `$F.$: wff`
  fal: TermId => "fal";
  /// `$T.$: wff`
  tru: TermId => "tru";
  /// `eq: nat > nat > wff`
  eq: TermId => "eq";
  /// `eq: nat > nat > wff`
  ne: TermId => "ne";
  /// `0: nat`
  d0: TermId => "d0";
  /// `suc: nat > nat`
  suc: TermId => "suc";
  /// `add: nat > nat > nat`
  add: TermId => "add";
  /// `mul: nat > nat > nat`
  mul: TermId => "mul";
  /// `le: nat > nat > wff`
  le: TermId => "le";
  /// `lt: nat > nat > wff`
  lt: TermId => "lt";
  /// `ltlei (h: $ a < b $): $ a <= b $`
  ltlei: ThmId => "ltlei";
  /// `ltnei (h: $ a < b $): $ a != b $`
  ltnei: ThmId => "ltnei";
  /// `ltneri (h: $ a < b $): $ b != a $`
  ltneri: ThmId => "ltneri";
  /// `leid: $ a <= a $`
  leid: ThmId => "leid";
  /// `pr: nat > nat > nat`
  pr: TermId => "pr";
  /// `cons: nat > nat > nat`
  cons: TermId => "cons";
  /// `len: nat > nat`
  len: TermId => "len";
  /// `sadd: string > string > string`
  sadd: TermId => "sadd";
  /// `sadd: char > string > string`
  scons: TermId => "scons";
  /// `s0: string`
  s0: TermId => "s0";
  /// `s1: char > string`
  s1: TermId => "s1";
  /// `d[0..=f]: nat`
  dn[i: 17]: TermId => format!("d{}", i);
  /// `x[0..=f]: hex`
  xn[i: 16]: TermId => format!("x{:x}", i);
  /// `ch: hex > hex > char`
  ch: TermId => "ch";
  /// `c2n: char > nat`
  c2n: TermId => "c2n";
  /// `h2n: hex > nat`
  h2n: TermId => "h2n";
  /// `hex: nat > hex > nat`
  hex: TermId => "hex";
  /// `h2n[0..=f]: x[i] = d[i]`
  h2nn[i: 16]: ThmId => format!("h2n{:x}", i);
  /// `decsucxf (a b c): suc a = b > suc (hex a xf) (hex b x0)`
  decsucxf: ThmId => "decsucxf";
  /// `decsucx (a b c): suc b = c > suc (hex a b) (hex a c)`
  decsucx: ThmId => "decsucx";
  /// `decsuc[0..f]: suc x[a] = hex(a+1)`
  decsucn[i: 16]: ThmId => format!("decsuc{:x}", i);
  /// `declt[0..f][0..=f]: x[a] < x[b]` for `a < b`
  decltn[a: 15][b: 16]: ThmId if a < b => format!("declt{:x}{:x}", a, b);
  /// `decltx1 (h: $ a < c $): $ a :x b < c :x d $`
  decltx1: ThmId => "decltx1";
  /// `decltx2 (h: $ b < c $): $ a :x b < a :x c $`
  decltx2: ThmId => "decltx2";
  /// `declt0x (h: $ x0 < b $): $ h2n a < b :x c $`
  declt0x: ThmId => "declt0x";
  /// `decadd[0..=f][0..=f]: x[a] + x[b] = hex(a+b)`
  decaddn[a: 16][b: 16]: ThmId => format!("decadd{:x}{:x}", a, b);
  /// `decadc[0..=f][0..=f]: suc (x[a] + x[b]) = hex(a+b+1)`
  decadcn[a: 16][b: 16]: ThmId => format!("decadc{:x}{:x}", a, b);

  /// `add_xx0 (h1: $ a + c = e $) (h2: $ b + d = f $): $ a :x b + c :x d = e :x f $`
  add_xx0: ThmId => "add_xx0";
  /// `add_xx1 (h1: $ suc (a + c) = e $) (h2: $ b + d = x1 :x f $): $ a :x b + c :x d = e :x f $`
  add_xx1: ThmId => "add_xx1";
  /// `adc_xx0 (h1: $ a + c = e $) (h2: $ suc (b + d) = f $): $ suc (a :x b + c :x d) = e :x f $`
  adc_xx0: ThmId => "adc_xx0";
  /// `adc_xx1 (h1: $ suc (a + c) = e $) (h2: $ suc (b + d) = x1 :x f $):
  ///   $ suc (a :x b + c :x d) = e :x f $`
  adc_xx1: ThmId => "adc_xx1";
  /// `add_0x0 (h: $ a + c = d $): $ h2n a + b :x c = b :x d $`
  add_0x0: ThmId => "add_0x0";
  /// `add_0x1 (h1: $ suc b = d $) (h2: $ a + c = x1 :x e $): $ h2n a + b :x c = d :x e $`
  add_0x1: ThmId => "add_0x1";
  /// `adc_0x0 (h: $ suc (a + c) = d $): $ suc (h2n a + b :x c) = b :x d $`
  adc_0x0: ThmId => "adc_0x0";
  /// `adc_0x1 (h1: $ suc b = d $) (h2: $ suc (a + c) = x1 :x e $):
  ///   $ suc (h2n a + b :x c) = d :x e $`
  adc_0x1: ThmId => "adc_0x1";
  /// `add_x00 (h: $ b + c = d $): $ a :x b + h2n c = a :x d $`
  add_x00: ThmId => "add_x00";
  /// `add_x01 (h1: $ suc a = d $) (h2: $ b + c = x1 :x e $): $ a :x b + h2n c = d :x e $`
  add_x01: ThmId => "add_x01";
  /// `adc_x00 (h: $ suc (b + c) = d $): $ suc (a :x b + h2n c) = a :x d $`
  adc_x00: ThmId => "adc_x00";
  /// `adc_x01 (h1: $ suc a = d $) (h2: $ suc (b + c) = x1 :x e $):
  ///   $ suc (a :x b + h2n c) = d :x e $`
  adc_x01: ThmId => "adc_x01";

  sub64: TermId => "sub64";

  /// `bit: nat > nat > nat`
  bit: TermId => "bit";
  xbit[n: 16][i: 4]: ThmId => format!("xbit{:x}{:x}", n, i);
  xsplitBits[i: 5][n: 16]: ThmId => {
    let mut s = format!("xsplitBits_{:x}", n);
    for &a in SPLIT_BITS_PART[i] { s.push((b'0' + a).into()) }
    s
  };

  /// `wSz8 (have_rex: wff): nat`
  wSz8: TermId => "wSz8";
  /// `wSz32: nat`
  wSz32: TermId => "wSz32";
  /// `wSz64: nat`
  wSz64: TermId => "wSz64";

  opSize: TermId => "opSize";
  opSize_64: ThmId => "opSize_64";
  opSize_32: ThmId => "opSize_32";
  opSize_8: ThmId => "opSize_8";

  opSizeW: TermId => "opSizeW";
  opSizeW_0: ThmId => "opSizeW_0";
  opSizeW_S: ThmId => "opSizeW_S";

  xastJCC: TermId => "xastJCC";
  decode: TermId => "decode";
  decodeAux: TermId => "decodeAux";
  decode0I: ThmId => "decode0I";
  decode1I: ThmId => "decode1I";

  /// `asmp_A: set > set > set`
  asmp_A: TermId => "asmp_A";
  /// `is_asmp_A (p s t x y z A B)
  ///   (h1: $ is_asmp p s x y A $) (h2: $ is_asmp p t y z B $):
  ///   $ is_asmp p s x z (asmp_A A B) $`
  is_asmp: TermId => "is_asmp";
  /// `is_asmp_A (p s t x y z A B)
  ///   (h1: $ is_asmp p s x y A $) (h2: $ is_asmp p t y z B $):
  ///   $ is_asmp p s x z (asmp_A A B) $`
  is_asmp_A: ThmId => "is_asmp_A";
  asmp_at: TermId => "asmp_at";
  is_asmp_at: ThmId => "is_asmp_at";
  // asmi: TermId => "asmi";
  // asmiI: ThmId => "asmiI";
  // asmJCC: TermId => "asmJCC";
  // asmJCC_I: ThmId => "asmJCC_I";
  // asmCall: TermId => "asmCall";
  // asmCallI: ThmId => "asmCallI";
  strlenn[i: 16]: ThmId => format!("strlen{:x}", i);

  basicElf_ok: ThmId => "basicElf_ok";
}

const SPLIT_BITS_PART: [&[u8]; 5] = [&[1, 3], &[2, 2], &[3, 1], &[1, 2, 1], &[1, 1, 1, 1]];
#[derive(Copy, Clone)]
pub(crate) enum SplitBits {
  Sb13 = 0,
  Sb22 = 1,
  Sb31 = 2,
  Sb121 = 3,
  Sb1111 = 4,
}
impl SplitBits {
  pub(crate) const fn part(self) -> &'static [u8] { SPLIT_BITS_PART[self as usize] }
}

