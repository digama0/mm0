use arrayvec::ArrayVec;
use mmcc::Idx;

use super::{Dedup, ProofDedup, ProofId, predefs::SplitBits};


pub(super) struct HexCache<Id = ProofId> {
  pub(super) hex: [Id; 16],
}

impl<Id> std::ops::Index<u8> for HexCache<Id> {
  type Output = Id;
  fn index(&self, i: u8) -> &Self::Output { &self.hex[usize::from(i)] }
}

impl<Id: Idx> HexCache<Id> {
  pub(super) fn new<'a, D: Dedup<'a, Id=Id>>(de: &mut D) -> Self {
    Self { hex: de.xn.map(|a| de.app(a, &[])) }
  }
  pub(super) fn h2n<'a, D: Dedup<'a, Id=Id>>(&self, de: &mut D, i: u8) -> Num<Id> {
    Num::new(i.into(), app!(de, h2n[self[i]]))
  }
  pub(super) fn hex<'a, D: Dedup<'a, Id=Id>>(&self, de: &mut D, n: Num<Id>, i: u8) -> Num<Id> {
    Num::new((n.val << 4) | u64::from(i), app!(de, hex[n.e, self[i]]))
  }
  pub(super) fn ch<'a, D: Dedup<'a, Id=Id>>(&self, de: &mut D, c: u8) -> Id {
    app!(de, ch[self[c >> 4], self[c & 15]])
  }
  pub(super) fn c2nch<'a, D: Dedup<'a, Id=Id>>(&self, de: &mut D, c: u8) -> Id {
    app!(de, c2n[self.ch(de, c)])
  }
}

macro_rules! mk_from_int {($($num:ident, $f:ident: $ty:ty,)*) => {
  $(
    /// Returns the number of `hex` nodes in a representation of the given integer.
    /// `0, 1, ..., 0xf -> 0`, `0x10, ..., 0xff -> 1`, `0x100, ..., 0xfff -> 2`, etc.
    #[inline] pub(super) fn $num(n: $ty) -> u32 {
      (<$ty>::BITS - n.leading_zeros()).saturating_sub(1) >> 2
    }
  )*
  impl<Id: Idx> HexCache<Id> {
    $(pub(super) fn $f<'a, D: Dedup<'a, Id=Id>>(&self, de: &mut D, n: $ty) -> Num<Id> {
      let size = $num(n);
      let x = n >> (4 * size);
      let mut e = de.app(de.h2n, &[self.hex[x as usize]]);
      for shift in (0..size).rev() {
        e = de.app(de.hex, &[e, self.hex[((n >> (4 * shift)) & 15) as usize]]);
      }
      Num::new(n.into(), e)
    })*
  }
}}

mk_from_int! {
  num_digits, from_u64: u64,
  num_digits_u32, from_u32: u32,
  num_digits_u8, from_u8: u8,
}

#[derive(Clone, Copy)]
pub(super) struct Num<Id = ProofId> {
  pub(super) val: u64,
  pub(super) e: Id,
}

impl<Id> std::ops::Deref for Num<Id> {
  type Target = Id;
  fn deref(&self) -> &Self::Target { &self.e }
}

impl PartialEq for Num {
  fn eq(&self, other: &Self) -> bool { self.val == other.val }
}
impl Eq for Num {}
impl PartialOrd for Num {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    self.val.partial_cmp(&other.val)
  }
  fn lt(&self, other: &Self) -> bool { self.val < other.val }
  fn le(&self, other: &Self) -> bool { self.val <= other.val }
  fn gt(&self, other: &Self) -> bool { self.val > other.val }
  fn ge(&self, other: &Self) -> bool { self.val >= other.val }
}
impl Ord for Num {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.val.cmp(&other.val)
  }
}

pub(super) enum NumKind<Id> {
  Hex(Num<Id>, u8),
  H2n(u8),
}
impl<Id: Idx> Num<Id> {
  pub(super) fn new(val: u64, e: Id) -> Self { Self { val, e } }
  #[inline] pub(super) fn len(&self) -> u32 { num_digits(self.val) }
  #[allow(clippy::cast_possible_truncation)]
  #[inline] pub(super) fn digit(&self, i: u32) -> u8 {
    ((self.val >> (4 * i)) & 15) as u8
  }

  #[allow(clippy::cast_possible_truncation)]
  pub(super) fn cases<'a, D: Dedup<'a, Id=Id>>(self, de: &D) -> NumKind<Id> {
    app_match!(de, self.e => {
      (hex a _) => NumKind::Hex(Num::new(self.val >> 4, a), (self.val & 15) as u8),
      (h2n _) => NumKind::H2n(self.val as u8),
      v => panic!("not a number"),
    })
  }
}

impl HexCache {
  /// Returns `(n', |- suc n = n')` where `n' = n+1`
  pub(super) fn suc(&self, de: &mut ProofDedup<'_>, n: Num) -> (Num, ProofId) {
    match n.cases(de) {
      NumKind::Hex(a, 15) => {
        let (b, pr) = self.suc(de, a);
        let r = self.hex(de, b, 0);
        (r, thm!(de, decsucxf(*a, *b, pr): (suc {*n}) = {*r}))
      }
      NumKind::Hex(a, i) => {
        let (b, c) = (self[i], self[i+1]);
        let r = self.hex(de, a, i+1);
        let pr = thm!(de, decsucn[i](): (suc (h2n b)) = (h2n c));
        (r, thm!(de, decsucx(*a, b, c, pr): (suc {*n}) = {*r}))
      }
      NumKind::H2n(i) => {
        let r = self.from_u8(de, i+1);
        (r, thm!(de, decsucn[i](): (suc {*n}) = {*r}))
      }
    }
  }

  /// Returns `|- a < b` assuming `a < b`
  pub(super) fn lt(&self, de: &mut ProofDedup<'_>, x: Num, y: Num) -> ProofId {
    match (x.cases(de), y.cases(de)) {
      (NumKind::Hex(a, b), NumKind::Hex(c, d)) if a < c => {
        let (eb, ed) = (self[b], self[d]);
        thm!(de, decltx1(*a, eb, *c, ed, self.lt(de, a, c)): {*x} < {*y})
      }
      (NumKind::Hex(a, b), NumKind::Hex(_a, c)) if b < c => {
        let (eb, ec) = (self[b], self[c]);
        thm!(de, decltx2(*a, eb, ec)((decltn[b][c](): eb < ec)): {*x} < {*y})
      }
      (NumKind::H2n(a), NumKind::Hex(b, c)) => {
        let z = if a == 0 { x } else { self.h2n(de, 0) };
        thm!(de, declt0x(self[a], *b, self[c], self.lt(de, z, b)): {*x} < {*y})
      }
      (NumKind::H2n(a), NumKind::H2n(b)) if a < b =>
        thm!(de, decltn[a][b](): {*x} < {*y}),
      _ => panic!("lt precondition fail"),
    }
  }

  /// Returns `|- a <= b` assuming `a <= b`
  pub(super) fn le(&self, de: &mut ProofDedup<'_>, x: Num, y: Num) -> ProofId {
    if x == y { thm!(de, leid(*x): {*x} <= {*y}) }
    else { thm!(de, ltlei(*x, *y, self.lt(de, x, y)): {*x} <= {*y}) }
  }

  /// Returns `|- a != b` assuming `a != b`
  pub(super) fn ne(&self, de: &mut ProofDedup<'_>, x: Num, y: Num) -> ProofId {
    if x < y { thm!(de, ltnei(*x, *y, self.lt(de, x, y)): {*x} != {*y}) }
    else { thm!(de, ltneri(*y, *x, self.lt(de, y, x)): {*x} != {*y}) }
  }
  /// Returns `(c, |- a + b = c)`
  #[inline] pub(super) fn add(&self, de: &mut ProofDedup<'_>, x: Num, y: Num) -> (Num, ProofId) {
    self.adc(de, false, x, y)
  }

  /// Returns `(c, |- a + b = c)` or `(c, |- suc (a + b) = c)` depending on `carry`
  pub(super) fn adc(&self, de: &mut ProofDedup<'_>, carry: bool, x: Num, y: Num) -> (Num, ProofId) {
    macro_rules! thm_carry {
      ($de:expr, $th:ident/$thc:ident $([$idx:expr])*($($args:tt)*):
        $a:tt + $carry:ident = $b:tt) => {
        if $carry { thm!($de, $thc$([$idx])*($($args)*): (suc $a) = $b) }
        else { thm!($de, $th$([$idx])*($($args)*): $a = $b) }
      }
    }
    fn decadd(hex: &HexCache, de: &mut ProofDedup<'_>, carry: bool, b: u8, d: u8
    ) -> (bool, u8, ProofId, ProofId, ProofId, (Num, ProofId)) {
      let f = b + d + (carry as u8);
      let carryout = f >= 16;
      let f = f & 15;
      let (eb, ed, ef) = (hex[b], hex[d], hex[f]);
      let r = if carryout { let one = hex.h2n(de, 1); hex.hex(de, one, f) } else { hex.h2n(de, f) };
      let p = thm_carry!(de, decaddn/decadcn[b][d](): ((h2n eb) + (h2n ed)) + carry = {*r});
      (carryout, f, eb, ed, ef, (r, p))
    }
    match (x.cases(de), y.cases(de)) {
      (NumKind::Hex(a, b), NumKind::Hex(c, d)) => match decadd(self, de, carry, b, d) {
        (true, f, eb, ed, ef, (_, p2)) => {
          let (e, p1) = self.adc(de, true, a, c);
          let r = self.hex(de, e, f);
          (r, thm_carry!(de, add_xx1/adc_xx1(*a, eb, *c, ed, *e, ef, p1, p2):
            ({*x} + {*y}) + carry = {*r}))
        }
        (false, f, eb, ed, ef, (_, p2)) => {
          let (e, p1) = self.adc(de, false, a, c);
          let r = self.hex(de, e, f);
          (r, thm_carry!(de, add_xx0/adc_xx0(*a, eb, *c, ed, *e, ef, p1, p2):
            ({*x} + {*y}) + carry = {*r}))
        }
      }
      (NumKind::H2n(b), NumKind::Hex(c, d)) => match decadd(self, de, carry, b, d) {
        (true, f, eb, ed, ef, (_, p2)) => {
          let (e, p1) = self.suc(de, c);
          let r = self.hex(de, e, f);
          (r, thm_carry!(de, add_0x1/adc_0x1(eb, *c, ed, *e, ef, p1, p2):
            ({*x} + {*y}) + carry = {*r}))
        }
        (false, f, eb, ed, ef, (_, p2)) => {
          let r = self.hex(de, c, f);
          (r, thm_carry!(de, add_0x0/adc_0x0(eb, *c, ed, ef, p2):
            ({*x} + {*y}) + carry = {*r}))
        }
      }
      (NumKind::Hex(a, b), NumKind::H2n(d)) => match decadd(self, de, carry, b, d) {
        (true, f, eb, ed, ef, (_, p2)) => {
          let (e, p1) = self.suc(de, a);
          let r = self.hex(de, e, f);
          (r, thm_carry!(de, add_x01/adc_x01(*a, eb, ed, *e, ef, p1, p2):
            ({*x} + {*y}) + carry = {*r}))
        }
        (false, f, eb, ed, ef, (_, p2)) => {
          let r = self.hex(de, a, f);
          (r, thm_carry!(de, add_x00/adc_x00(*a, eb, ed, ef, p2):
            ({*x} + {*y}) + carry = {*r}))
        }
      }
      (NumKind::H2n(b), NumKind::H2n(d)) => decadd(self, de, carry, b, d).5
    }
  }

  pub(super) fn is_u64(de: &mut ProofDedup<'_>, a: ProofId) -> ProofId {
    let mut args = vec![];
    let mut x = a;
    loop {
      app_match!(de, x => {
        (hex a c) => { args.push(c); x = a }
        (h2n c) => {
          let i = args.len();
          args.push(c);
          let res = app!(de, (isU64 a));
          return de.thm(de.isU64n[i], &args, res)
        }
        v => panic!("not a number"),
      })
    }
  }
}

macro_rules! norm_split_bits {
  (@split $de:ident $arg:tt ($($out:expr,)*) ($x:expr) ($($stk:tt)*) $n:literal $($rest:tt)*) => {
    let x = $x;
    let n: u8 = $n;
    let a = x & ((1 << n) - 1);
    let ea = app!($de, (dn[a]));
    norm_split_bits!{@split $de $arg ($($out,)* (a, ea),) (x >> n)
        ($($stk)* ea) $($rest)*}
  };
  (@split $de:ident ($a:expr, $x:ident, $e:expr) ($($out:expr,)*) $y:tt ($($stk:tt)*)) => {
    ([$($out),*], thm!($de, splitBitsn[$a][$x](): (splitBits[$a]) $($stk)* {$e}))
  };
  (@unsplit_push ($($params:ident)*) ($($vals:tt)*) $n:literal $($rest:tt)*) => {
    norm_split_bits!{@unsplit_push ($($params)* a) ((a $n) $($vals)*) $($rest)*}
  };
  (@unsplit_push ($f:ident $g:ident $($params:ident)*) ($($args:tt)*)) => {
    pub(super) fn $g(&self, de: &mut ProofDedup<'_>,
      $($params: u8,)*
    ) -> ((u8, ProofId), ProofId) {
      let x = norm_split_bits!(@unsplit_build $($args)*);
      ((x, self.hex[usize::from(x)]), self.$f(de, x).1)
    }
  };
  (@unsplit_build ($a:ident $n:literal)) => { $a };
  (@unsplit_build ($a:ident $n:literal) ($b:ident $m:literal) $($rest:tt)*) => {
    ($a << $m) | norm_split_bits!(@unsplit_build ($b $m) $($rest)*)
  };
  ($(fn $f:ident, fn $g:ident ($a:ident: $($n:literal),*);)*) => {
    impl HexCache {
      $(pub(super) fn $f(&self,
        de: &mut ProofDedup<'_>, x: u8
      ) -> ([(u8, ProofId); [$($n),*].len()], ProofId) {
        norm_split_bits! {@split de (SplitBits::$a as usize, x, self[x]) () (x) () $($n)* }
      })*

      $(norm_split_bits! {@unsplit_push ($f $g) () $($n)* })*

      pub(super) fn split_bits(&self, de: &mut ProofDedup<'_>, sb: SplitBits, x: u8
      ) -> (ArrayVec<(u8, ProofId), 4>, ProofId) {
        match sb {
          $(SplitBits::$a => {
            let (xs, pr) = self.$f(de, x);
            (xs.into_iter().collect(), pr)
          })*
        }
      }
    }
  }
}
norm_split_bits! {
  fn split_bits_13, fn unsplit_bits_13(Sb13: 1, 3);
  fn split_bits_22, fn unsplit_bits_22(Sb22: 2, 2);
  fn split_bits_31, fn unsplit_bits_31(Sb31: 3, 1);
  fn split_bits_121, fn unsplit_bits_121(Sb121: 1, 2, 1);
  fn split_bits_1111, fn unsplit_bits_1111(Sb1111: 1, 1, 1, 1);
}
