//! The compiler lemmas we need from `compiler.mm1`
#![allow(clippy::many_single_char_names, clippy::similar_names, clippy::equatable_if_let)]
#![allow(unused, clippy::unused_self, clippy::diverging_sub_expression)]
#![allow(non_snake_case)]

use std::collections::HashMap;
use std::marker::PhantomData;

use mm0_util::{AtomId, Modifiers, Span, TermId, ThmId};
use mmcc::Idx;
use mmcc::proof::{AssemblyBlocks, AssemblyItem, ElfProof, Inst, Proc};

use crate::elab::Result;
use crate::{DeclKey, ElabError, Elaborator, Environment, ExprNode, Proof, ProofNode, Remap, Remapper, Thm, ThmKind, Type};
use crate::elab::proof::{self, IDedup};

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
  (@new $ty:tt $env:expr, ($i:ident, $($is:ident,)*) $e:expr) => {
    mk_array(|$i| make_predefs!(@new $ty $env, ($($is,)*) $e))
  };
  (@new AtomId $env:expr, () $e:expr) => { $env.get_atom($e) };
  (@new TermId $env:expr, () $e:expr) => { get_term($env, $e) };
  (@new ThmId $env:expr, () $e:expr) => { get_thm($env, $e) };
  {$($(#[$attr:meta])* $x:ident $([$i:ident: $n:expr])*: $ty:tt = $e:expr;)*} => {
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

    impl Remap for Predefs {
      type Target = Self;
      fn remap(&self, r: &mut Remapper) -> Self {
        Self { $($x: self.$x.remap(r)),* }
      }
    }

    impl Predefs {
      /// Construct a `Predefs` from an environment.
      pub(crate) fn new(env: &mut crate::Environment) -> Self {
        #[allow(clippy::string_lit_as_bytes)]
        Self { $($x: make_predefs!(@new $ty env, ($($i,)*) $e.as_bytes())),* }
      }
    }
  };
}

make_predefs! {
  /// `eq: nat > nat > wff`
  eq: TermId = "eq";
  /// `suc: nat > nat`
  suc: TermId = "suc";
  /// `sadd: string > string > string`
  sadd: TermId = "sadd";
  /// `x[0..=f]: hex`
  xi[i: 16]: TermId = format!("x{:x}", i);
  /// `ch: hex > hex > char`
  ch: TermId = "ch";
  /// `c2n: char > nat`
  c2n: TermId = "c2n";
  /// `h2n: hex > nat`
  h2n: TermId = "h2n";
  /// `hex: nat > hex > nat`
  hex: TermId = "hex";
  /// `h2n[0..=f]: x[i] = d[i]`
  h2ni[i: 16]: ThmId = format!("h2n{:x}", i);
  /// `decsucxf (a b c): suc a = b > suc (hex a xf) (hex b x0)`
  decsucxf: ThmId = "decsucxf";
  /// `decsucx (a b c): suc b = c > suc (hex a b) (hex a c)`
  decsucx: ThmId = "decsucx";
  /// `decsuc[0..=f] (a b c): suc b = c > suc (hex a b) (hex a c)`
  decsuci[i: 16]: ThmId = format!("decsuc{:x}", i);

  xbit[n: 16][i: 4]: ThmId = format!("xbit{:x}{:x}", n, i);
  asmp_A: TermId = "asmp_A";
  is_asmp: TermId = "is_asmp";
  is_asmp_A: ThmId = "is_asmp_A";
  asmp_at: TermId = "asmp_at";
  is_asmp_at: ThmId = "is_asmp_at";
  basicElf_ok: ThmId = "basicElf_ok";
}

macro_rules! app {
  ($de:expr, $pd:expr, {$($e:tt)*}) => { {$($e)*} };
  ($de:expr, $pd:expr, ($id:ident $($e:tt)*)) => {{
    let args = &[$(app!($de, $pd, $e)),*];
    $de.app($pd.$id, args)
  }};
  ($de:expr, $pd:expr, [$($e:tt)*]) => { app!($de, $pd, $($e)*) };
  ($de:expr, $pd:expr, $id:ident[$($e:expr),*]) => {{
    let args = &[$($e),*];
    $de.app($pd.$id, args)
  }};
  ($de:expr, $pd:expr, $e:tt = $e2:tt) => {app!($de, $pd, (eq $e $e2))};
  ($de:expr, $pd:expr, ($id:ident$([$ix:expr])+) $($e:tt)*) => {{
    let args = &[$(app!($de, $pd, $e)),*];
    $de.app($pd.$id$([$ix])*, args)
  }};
  ($de:expr, $pd:expr, $e:ident) => {{$e}};
  ($de:expr, $pd:expr, $($e:tt)*) => {{$($e)*}};
}

macro_rules! thm {
  ($de:expr, $pd:expr, $thm:ident$([$ix:expr])*($($args:expr),*): $($e:tt)*) => {{
    let res = app!($de, $pd, $($e)*);
    $de.thm($pd.$thm$([$ix])*, &[$($args),*], res)
  }};
}

macro_rules! app_match {
  (@build ((($args:tt $rhs1:expr) $($rest:tt)+) ($($vars:ident)*)) $out:expr,) => {
    if let Some(($($vars,)*)) = $out { $rhs1 } else {
      app_match!(@arms $args $($rest)+)
    }
  };
  (@build $args:tt $out:expr, (let $var:ident = $e:expr) $($stk:tt)*) => {
    app_match!(@build $args { let $var = $e; $out }, $($stk)*)
  };
  (@build (((($de:expr, $pd:expr, $e1:expr) $rhs1:expr) $($rest1:tt)+) ($($vars:ident)*))
    $out:expr, (match $c:ident ($e:expr) $($x:ident)*) $($stk:tt)*) => {
    app_match!(@build (((($de, $pd, $e1) $rhs1) $($rest1)+) ($($vars)*))
      if let Some(&[$($x),*]) = $de.is_app_of($e, $pd.$c) { $out } else { None },
      $($stk)*)
  };
  (@build (((($de:expr, $pd:expr, $e1:expr) $rhs1:expr) $($rest1:tt)+) ($($vars:ident)*))
    $out:expr, (match ($c:ident $([$ix:expr])*) ($e:expr) $($x:ident)*) $($stk:tt)*) => {
    app_match!(@build (((($de, $pd, $e1) $rhs1) $($rest1)+) ($($vars)*))
      if let Some(&[$($x),*]) = $de.is_app_of($e, $pd.$c$([$ix])*) { $out } else { None },
      $($stk)*)
  };
  (@build (((($de:expr, $pd:expr, $e1:expr) $rhs1:expr) $($rest1:tt)+) ($($vars:ident)*))
    $out:expr, (match {$c:expr} ($e:expr) $($x:ident)*) $($stk:tt)*) => {
    app_match!(@build (((($de, $pd, $e1) $rhs1) $($rest1)+) ($($vars)*))
      if let Some(&[$($x),*]) = $de.is_app_of($e, $c) { $out } else { None },
      $($stk)*)
  };
  (@pat $args:tt () ($($vars:ident)*) ($($stk:tt)*)) => {
    app_match!(@build ($args ($($vars)*)) Some(($($vars,)*)), $($stk)*)
  };
  (@pat $args:tt ($e:expr, $($es:tt)*) ($($vars:ident)*) ($($stk:tt)*) _ $($rest:tt)*) => {
    app_match!(@pat $args ($($es)*) ($($vars)*) ($($stk)*) $($rest)*)
  };
  (@pat $args:tt ($e:expr, $($es:tt)*) ($($vars:ident)*) ($($stk:tt)*) $v:ident $($rest:tt)*) => {
    app_match!(@pat $args ($($es)*) ($($vars)* $v) ((let $v = $e) $($stk)*) $($rest)*)
  };
  (@pat $args:tt ($e:expr, $($es:tt)*) $vars:tt $stk:tt ($c:tt $($pats:tt)*) $($rest:tt)*) => {
    app_match!(@gensyms ($args ($($es)*) $vars $stk ($e) $c $($rest)*) () $($pats)*)
  };
  (@gensyms $args:tt ($($out:tt)*) $pat:tt $($pats:tt)*) => {
    app_match!(@gensyms $args ($($out)* (x $pat)) $($pats)*)
  };
  (@gensyms (((($de:expr, $pd:expr, $e1:expr) $rhs1:expr) $($rest1:tt)+) ($($es:tt)*) $vars:tt
    ($($stk:tt)*) ($e:expr) $c:tt $($rest:tt)*) ($(($x:ident $pats:tt))*)) => {
    app_match!(@pat ((($de, $pd, $e1) $rhs1) $($rest1)+) ($($de.do_from_usize($x),)* $($es)*) $vars
      ((match $c ($e) $($x)*) $($stk)*) $($pats)* $($rest)*)
  };
  (@arms ($de:expr, $pd:expr, $e:expr) $pat1:tt => $rhs1:expr, $($rest:tt)+) => {
    app_match!(@pat ((($de, $pd, $e) $rhs1) $($rest)+) ($e,) () () $pat1)
  };
  (@arms ($de:expr, $pd:expr, $e:expr) $x:pat => $rhs:expr,) => {{ let $x = $e; $rhs }};
  ($de:expr, $pd:expr, $e:expr => { $($pat:tt => $rhs:expr,)* }) => {{
    let e = $e;
    app_match!(@arms ($de, $pd, e) $($pat => $rhs,)*)
  }};
}

trait Dedup {
  type Node;
  type Hash;
  type Id: Idx;
  fn new(args: &[(Option<AtomId>, Type)]) -> Self;
  fn add(&mut self, h: Self::Hash) -> Self::Id;
  fn reuse(&mut self, i: Self::Id) -> Self::Id;
  fn add_r(&mut self, h: Self::Hash) -> Self::Id {
    let i = self.add(h);
    self.reuse(i)
  }
  fn get(&self, i: Self::Id) -> &Self::Hash;
  fn build0(&self, i: Self::Id) -> (Box<[Self::Node]>, Self::Node);
  const APP: fn(t: TermId, args: Box<[usize]>) -> Self::Hash;
  fn app1(&mut self, t: TermId, args: &[Self::Id]) -> Self::Id {
    self.add(Self::APP(t, args.iter().map(|x| x.into_usize()).collect()))
  }
  fn app(&mut self, t: TermId, args: &[Self::Id]) -> Self::Id {
    self.add_r(Self::APP(t, args.iter().map(|x| x.into_usize()).collect()))
  }
  fn is_app_of(&self, i: Self::Id, t: TermId) -> Option<&[usize]>;
  #[inline] fn mk_eq(&mut self, pd: &Predefs, a: Self::Id, b: Self::Id) -> Self::Id {
    app!(self, pd, a = b)
  }
  #[inline] fn do_from_usize(&self, i: usize) -> Self::Id { Idx::from_usize(i) }
}

macro_rules! make_dedup {
  ($($dedup:ident, $hash:ident, $node:ty, $id:ident, $app:ident;)*) => {$(
    #[derive(Clone, Copy, PartialEq, Eq)]
    struct $id(usize);
    impl Idx for $id {
      fn into_usize(self) -> usize { self.0 }
      fn from_usize(n: usize) -> Self { Self(n) }
    }
    struct $dedup(proof::Dedup<proof::$hash>);
    impl Dedup for $dedup {
      type Node = $node;
      type Hash = proof::$hash;
      type Id = $id;
      fn new(args: &[(Option<AtomId>, Type)]) -> Self { Self(proof::Dedup::new(args)) }
      fn add(&mut self, h: proof::$hash) -> $id { $id(self.0.add_direct(h)) }
      fn reuse(&mut self, i: $id) -> $id { $id(self.0.reuse(i.0)) }
      fn build0(&self, i: $id) -> (Box<[$node]>, $node) {
        let (mut ids, heap) = proof::build(&self.0);
        (heap, ids[i.0].take())
      }
      fn get(&self, i: Self::Id) -> &Self::Hash { &self.0[i.0] }
      const APP: fn(t: TermId, args: Box<[usize]>) -> Self::Hash = proof::$hash::$app;
      fn is_app_of(&self, i: Self::Id, t: TermId) -> Option<&[usize]> {
        if let proof::$hash::$app(t2, args) = self.get(i) {
          if *t2 == t { return Some(&args) }
        }
        None
      }
    }
  )*}
}
make_dedup! {
  ExprDedup, ExprHash, ExprNode, ExprId, App;
  ProofDedup, ProofHash, ProofNode, ProofId, Term;
}

impl ProofDedup {
  fn thm(&mut self, t: ThmId, args: &[ProofId], res: ProofId) -> ProofId {
    self.add(proof::ProofHash::Thm(t, args.iter().map(|x| x.0).collect(), res.0))
  }
  fn thm_r(&mut self, t: ThmId, args: &[ProofId], res: ProofId) -> ProofId {
    self.add_r(proof::ProofHash::Thm(t, args.iter().map(|x| x.0).collect(), res.0))
  }
  fn thm_app(&mut self, th: ThmId, args: &[ProofId], t: TermId, es: &[ProofId]) -> ProofId {
    let res = self.app1(t, es);
    self.thm(th, args, res)
  }
}

struct HexCache<'a, D: Dedup = ProofDedup> {
  pd: &'a Predefs,
  hex: [D::Id; 16],
  _de: PhantomData<D>,
}

impl<D: Dedup> std::ops::Index<u8> for HexCache<'_, D> {
  type Output = D::Id;
  fn index(&self, i: u8) -> &Self::Output { &self.hex[usize::from(i)] }
}

struct Num<D: Dedup = ProofDedup> {
  val: u64,
  e: D::Id,
  _de: PhantomData<D>,
}
impl<D: Dedup> Clone for Num<D> {
  fn clone(&self) -> Self { Self { val: self.val, e: self.e, _de: PhantomData } }
}
impl<D: Dedup> Copy for Num<D> {}

impl<D: Dedup> std::ops::Deref for Num<D> {
  type Target = D::Id;
  fn deref(&self) -> &Self::Target { &self.e }
}

enum NumKind<D: Dedup> {
  Hex(Num<D>, u8),
  H2n(u8),
}
impl<D: Dedup> Num<D> {
  fn new(val: u64, e: D::Id) -> Self { Self { val, e, _de: PhantomData } }
  #[inline] fn len(&self) -> u32 { num_digits(self.val) }
  #[allow(clippy::cast_possible_truncation)]
  #[inline] fn digit(&self, i: u32) -> u8 {
    ((self.val >> (4 * i)) & 15) as u8
  }

  #[allow(clippy::cast_possible_truncation)]
  fn cases(self, de: &D, pd: &Predefs) -> NumKind<D> {
    app_match!(de, pd, self.e => {
      (hex a _) => NumKind::Hex(Num::new(self.val >> 4, a), (self.val & 15) as u8),
      (h2n _) => NumKind::H2n(self.val as u8),
      v => panic!("not a number"),
    })
  }
}

impl<'a, D: Dedup> HexCache<'a, D> {
  fn new(pd: &'a Predefs, de: &mut D) -> Self {
    Self { pd, hex: pd.xi.map(|a| de.app(a, &[])), _de: PhantomData }
  }
  fn h2n(&self, de: &mut D, i: u8) -> Num<D> {
    Num::new(i.into(), app!(de, self.pd, h2n[self[i]]))
  }
  fn hex(&self, de: &mut D, n: Num<D>, i: u8) -> Num<D> {
    Num::new((n.val << 4) | u64::from(i), app!(de, self.pd, hex[n.e, self[i]]))
  }
  fn ch(&self, de: &mut D, c: u8) -> D::Id {
    app!(de, self.pd, ch[self[c >> 4], self[c & 15]])
  }
  fn c2nch(&self, de: &mut D, c: u8) -> D::Id {
    app!(de, self.pd, c2n[self.ch(de, c)])
  }
}

impl<'a> HexCache<'a> {
  fn suc(&self, de: &mut ProofDedup, mut n: Num) -> (Num, ProofId) {
    match n.cases(de, self.pd) {
      NumKind::Hex(a, 15) => {
        let (b, pr) = self.suc(de, a);
        let r = self.hex(de, b, 0);
        (r, thm!(de, self.pd, decsucxf(*a, *b, pr): (suc {*n}) = {*r}))
      }
      NumKind::Hex(a, i) => {
        let (b, c) = (self[i], self[i+1]);
        let r = self.hex(de, a, i+1);
        let pr = thm!(de, self.pd, decsuci[usize::from(i)](): (suc b) = c);
        (r, thm!(de, self.pd, decsucx(*a, b, c, pr): (suc {*n}) = {*r}))
      }
      NumKind::H2n(i) => {
        let r = self.from_u8(de, i+1);
        (r, thm!(de, self.pd, decsuci[usize::from(i)](): (suc {*n}) = {*r}))
      }
    }
  }
}

macro_rules! mk_from_int {($($num:ident, $f:ident: $ty:ty,)*) => {
  $(
    /// Returns the number of `hex` nodes in a representation of the given integer.
    /// `0, 1, ..., 0xf -> 0`, `0x10, ..., 0xff -> 1`, `0x100, ..., 0xfff -> 2`, etc.
    #[inline] fn $num(n: $ty) -> u32 {
      (<$ty>::BITS - n.leading_zeros()).saturating_sub(1) >> 2
    }
  )*
  impl<'a, D: Dedup> HexCache<'a, D> {
    $(fn $f(&self, de: &mut D, n: $ty) -> Num<D> {
      let size = $num(n);
      let x = n >> (4 * size);
      let mut e = de.app(self.pd.h2n, &[self.hex[x as usize]]);
      for shift in (0..size).rev() {
        e = de.app(self.pd.hex, &[e, self.hex[((n >> (4 * shift)) & 15) as usize]]);
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

struct BuildAssemblyProc<'a> {
  thm: ProofDedup,
  hex: HexCache<'a>,
  start: ProofId,
}

fn assemble_block(iter: &mut AssemblyBlocks<'_>) {

}

impl BuildAssemblyProc<'_> {
  fn bisect<T>(&mut self,
    n: usize, iter: &mut impl Iterator<Item=T>, x: Num,
    f: &mut impl FnMut(&mut Self, T, Num) -> (ProofId, ProofId, Num, ProofId),
  ) -> (ProofId, ProofId, Num, ProofId) {
    if n <= 1 {
      assert!(n != 0);
      let item = iter.next().expect("iterator size lied");
      f(self, item, x)
    } else {
      let m = n >> 1;
      let (s, a, y, pr1) = self.bisect(m, iter, x, f);
      let (t, b, z, pr2) = self.bisect(n - m, iter, y, f);
      // axiom is_asmp_A (p s t x y z A B)
      //   (h1: $ is_asmp p s x y A $) (h2: $ is_asmp p t y z B $): $ is_asmp p s x z A $;
      let st = self.thm.app(self.hex.pd.sadd, &[s, t]);
      let ab = self.thm.app(self.hex.pd.asmp_A, &[a, b]);
      let pr = self.thm.thm_app(
        self.hex.pd.is_asmp_A, &[self.start, s, t, *x, *y, *z, a, b],
        self.hex.pd.is_asmp, &[self.start, st, *x, *z, ab]);
      (st, ab, z, pr)
    }
  }

  /// Given `x`, proves `(s, A, y, is_asmp p s x y A)` where
  /// `s` is generated from the instruction assembly.
  fn inst(&mut self, inst: &Inst<'_>, x: ProofId) -> (ProofId, ProofId, Num, ProofId) {
    todo!()
  }

  /// Given `x`, proves `(s, A, y, is_asmp p s x y A)` where
  /// `s` is generated from the assembly blocks.
  fn proc(&mut self, proc: &Proc<'_>) -> (ProofId, ProofId, Num, ProofId) {
    let mut iter = proc.assembly_blocks();
    let x = self.hex.h2n(&mut self.thm, 0);
    self.bisect(iter.len(), &mut iter, x, &mut |this, block, x| {
      let mut iter = block.insts();
      let (s, a, y, pr) = this.bisect(iter.len(), &mut iter, x, &mut |this, inst, x| {
        todo!()
      });
      // axiom is_asmp_at (p s x y A)
      //   (h1: $ is_asmp p s x y A $): $ is_asmp p s x y (asmp_at x A) $;
      let a2 = this.thm.app(this.hex.pd.asmp_at, &[*x, a]);
      let pr = this.thm.thm_app(
        this.hex.pd.is_asmp_at, &[this.start, s, *x, *y, a],
        this.hex.pd.is_asmp, &[this.start, s, *x, *y, a2]);
      (s, a2, y, pr)
    })
  }
}

pub(crate) fn render_proof(
  pd: &Predefs, elab: &mut Elaborator, sp: Span,
  name: AtomId, proof: &ElfProof<'_>
) -> Result<()> {
  let name_str = elab.data[name].name.clone();
  let name_str = name_str.as_str();
  macro_rules! atom {($lit:literal $(, $e:expr)*) => {
    elab.get_atom(format!(concat!("{}_", $lit), name_str $(, $e)*).as_bytes())
  }}

  let mut proc_asm = HashMap::new();

  for item in proof.assembly() {
    match item {
      AssemblyItem::Proc(proc) => {
        let name = proc.name();
        let mut thm = ProofDedup::new(&[]);
        let hex = HexCache::new(pd, &mut thm);
        hex.from_u64(&mut thm, proc.start());
        let mut build = BuildAssemblyProc {
          start: *hex.from_u64(&mut thm, proc.start()),
          hex,
          thm,
        };
        let (s, a, y, pr) = build.proc(&proc);
        let (heap, head) = build.thm.build0(pr);
        elab.env.add_thm(Thm {
          atom: *proc_asm.entry(name).or_insert_with(|| match name {
            Some(name) => atom!("{}_asm", name),
            None => atom!("_start_asm"),
          }),
          span: elab.fspan(sp),
          vis: Modifiers::empty(),
          full: sp,
          doc: None,
          args: Box::new([]),
          heap: todo!(),
          hyps: Box::new([]),
          ret: todo!(),
          kind: ThmKind::Thm(Some(Proof {
            heap,
            hyps: Box::new([]),
            head,
          })),
        }).map_err(|e| e.into_elab_error(sp))?;
        todo!()
      }
      AssemblyItem::Const(_) |
      AssemblyItem::Padding(_, _) => todo!(),
    }
  }
  elab.report(ElabError::info(sp, format!("{:#?}", proof)));
  Ok(())
}
