#![allow(clippy::cast_possible_truncation)]

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::ops::{Deref, DerefMut};
use std::marker::PhantomData;

use mmcc::Idx;
use mmcc::types::classify::TraceIter;
use mmcc::types::mir::{Cfg, Contexts, CtxBufId, CtxId, ExprKind, Statement, Terminator, VarId,
  LetKind, Ty, TyKind, RValue, Operand, Place, ConstKind, Constant};
use mmcc::types::vcode::{ProcAbi, ArgAbi};
use mmcc::{Symbol, TEXT_START, types::{Size, IdxVec, classify as cl}};
use mmcc::arch::{ExtMode, OpcodeLayout, PInst, PRegMemImm, Unop, RegMem};
use mmcc::proof::{AssemblyBlocks, AssemblyItem, AssemblyItemIter, BlockId, BlockProof,
  BlockProofTree, BlockTreeIter, ElfProof, Inst, InstIter, PReg, Proc, VBlockId, ProcId};
use crate::LispVal;
use crate::lisp::print::Print;
use crate::{Elaborator, FileSpan, Modifiers, Span, TermId, ThmId, elab::Result, mmc::proof::Name};

use super::{Dedup, ExprDedup, Mangler, Predefs, ProofDedup, ProofId,
  norm_num::{HexCache, Num}, predefs::Rex};

const BLOCK_PROOFS: bool = false; // TODO

pub(super) fn mk_result<'a, D: Dedup<'a>>(de: &mut D, proof: &ElfProof<'_>) -> D::Id {
  app!(de, (tyUnit)) // TODO
}

fn format_to_string(f: impl FnOnce(&mut String) -> std::fmt::Result) -> String {
  let mut s = String::new();
  f(&mut s).expect("impossible");
  s
}

type P<A> = (A, ProofId);

struct Ctx {
  t_gctx: TermId,
  gctx: ProofId,
  ret: ProofId,
  se: ProofId,
  epi: ProofId,
  sp_max: Num,
  pctx1: ProofId,
  pctx: ProofId,
  labs: ProofId,
  bctx: ProofId,
  ok0: ProofId,
  asm0: ProofId,
}

impl Ctx {
  fn new(de: &mut ProofDedup<'_>, hex: &HexCache, proc: &Proc<'_>, t_gctx: TermId) -> Ctx {
    let ok0 = app!(de, (ok0));
    let asm0 = app!(de, (ASM0));
    let gctx = app!(de, ({t_gctx}));
    let ret = app!(de, (noRet)); // TODO
    let se = app!(de, (tru)); // TODO
    let mut epi = app!(de, (epiRet));
    for &reg in proc.saved_regs() {
      epi = app!(de, epiPop[hex[reg.index()], epi]);
    }
    let sp_max = hex.from_u32(de, proc.stack_size());
    if sp_max.val != 0 { epi = app!(de, epiFree[*sp_max, epi]) }
    let pctx1 = app!(de, mkPCtx1[ret, epi, se]);
    let pctx = app!(de, mkPCtx[gctx, pctx1]);
    let labs = app!(de, (labelGroup0));
    let bctx = app!(de, mkBCtx[pctx, labs]);
    Ctx { t_gctx, gctx, ret, se, epi, sp_max, pctx1, pctx, labs, bctx, ok0, asm0 }
  }
}

mmcc::mk_id! { VCtxId, }

impl VCtxId {
  /// A sentinel value used in [`VCtx::parent`] to indicate the root context.
  const ROOT: Self = Self(u32::MAX);
}

#[derive(Clone, Copy)]
enum VarKind { Var, Hyp, Typed }

impl std::fmt::Display for VarKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      VarKind::Var => "var",
      VarKind::Hyp => "hyp",
      VarKind::Typed => "typed",
    }.fmt(f)
  }
}

#[derive(Clone)]
struct VCtxVar {
  var: VarId,
  e: ProofId,
  kind: VarKind,
}

/// This function produces the following sequence:
///
/// | p \ n | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 |
/// | ----- | - | - | - | - | - | - | - | - | - | - | -- | -- | -- | -- | -- | -- | -- | -- | -- |
/// | false | ! | 0 | 0 | 1 | 0 | 1 | 0 | 2 | 0 | 1 | 0  | 2  | 0  | 1  | 0  | 3  | 0  | 1  | 0  |
/// | true  | 0 | 1 | 0 | 2 | 0 | 1 | 0 | 3 | 0 | 1 | 0  | 2  | 0  | 1  | 0  | 4  | 0  | 1  | 0  |
///
/// * `rotation_sequence(n, false) + 1` is <https://oeis.org/A091090>
/// * `rotation_sequence(n, true)` is <https://oeis.org/A007814>
///
/// This represents the number of rotations to put after each insertion to balance a binary tree
/// which looks like this:
///
/// | n | T(n,false)    | r(n,false) | T(n,true)       | r(n,true) |
/// | - | ------------- | ---------- | --------------- | --------- |
/// | 0 | N/A                  | N/A | a                       | 0 |
/// | 1 | x                    | 0   | ax                      | 1 |
/// | 2 | xx                   | 0   | a(xx)                   | 0 |
/// | 3 | (xx)x                | 1   | (a(xx))x                | 2 |
/// | 4 | (xx)(xx)             | 0   | a((xx)(xx))             | 0 |
/// | 5 | ((xx)(xx))x          | 1   | (a((xx)(xx)))x          | 1 |
/// | 6 | ((xx)(xx))(xx)       | 0   | (a((xx)(xx)))(xx)       | 0 |
/// | 7 | (((xx)(xx))(xx))x    | 2   | ((a((xx)(xx)))(xx))x    | 3 |
/// | 8 | ((xx)(xx))((xx)(xx)) | 0   | a(((xx)(xx))((xx)(xx))) | 0 |
///
/// Following the left spine results in a sequence of perfect binary trees, going up the binary
/// representation of `n`, i.e. `n = 19 = 2^4 + 2^2 + 2^0` is translated to `(T_4 T_2) T_0` or
/// `((a T_4) T_2) T_0` depending on whether we have parent `a` or not, where `T_n` is the perfect
/// binary tree on `2^n` leaves.
#[inline] fn rotation_sequence(mut n: u32, parent: bool) -> u32 {
  if !parent { n -= ((n >> 1) + 1).next_power_of_two() }
  n.trailing_ones()
}

/// A `VarCache` stores the information for a variable access in a context.
/// The first part is the size of the smallest prefix of the context that contains this variable.
/// (So the first variable has index 1.) This is a "global" counter, i.e. it includes `base`.
///
/// The second part is a cache of various local sizes (not including `base`) and a proof
/// that from the prefix of `vars` of that length, `|- okVCtxGet vctx var`.
///
/// The cached indices follow a particular pattern: If `n` is the size of the context
/// as of the last access, then we store caches for `n`, `n` with the lowest nonzero bit cleared
/// (i.e. `n & (n - 1)`), repeating the lowest bit clear operation until 0 or we go past the index
/// of the variable. For example, if `n = 19` then we will store caches for `16, 18, 19`;
/// if the variable has index `18` then we will store only `18, 19` since `16` is not valid.
type VarCache = (u32, Vec<(u32, ProofId)>);

#[derive(Clone)]
struct VCtx {
  e: ProofId,
  base: u32,
  vars: Vec<VCtxVar>,
  nvars: Num,
  access_cache: RefCell<HashMap<VarId, VarCache>>,
  parent: VCtxId,
}

impl VCtx {
  fn pp(&self, thm: &ProofDedup<'_>, elab: &mut Elaborator,
    vctxs: &IdxVec<VCtxId, VCtx>,
    f: &mut impl std::fmt::Write
  ) -> std::fmt::Result {
    if self.parent != VCtxId::ROOT {
      vctxs[self.parent].pp(thm, elab, vctxs, f)?;
    }
    for v in &self.vars {
      write!(f, "{} {:?}: ", v.kind, v.var)?;
      thm.pp(elab, v.e, f)?;
      writeln!(f)?
    }
    Ok(())
  }

  fn to_string(&self,
    thm: &ProofDedup<'_>, elab: &mut Elaborator, vctxs: &IdxVec<VCtxId, VCtx>
  ) -> String {
    let mut s = String::new();
    self.pp(thm, elab, vctxs, &mut s).expect("format string");
    s
  }

  /// Build the root context. Note that variables can be added to the root context with `add`
  fn root(de: &mut ProofDedup<'_>, hex: &HexCache) -> impl Fn() -> Self + Copy + use<> {
    let e = app!(de, (vctx0));
    let nvars = hex.h2n(de, 0);
    move || Self {
      e,
      base: 0,
      vars: vec![],
      nvars,
      access_cache: Default::default(),
      parent: VCtxId::ROOT,
    }
  }

  /// Allocate a new context ID for this context, and store it in the context list.
  /// `self` is modified to derive from the new context. This is roughly equivalent to
  /// `clone()`, but it moves the data into `vctxs` instead of doing a deep copy.
  fn share(&mut self, vctxs: &mut IdxVec<VCtxId, VCtx>) -> impl Fn() -> Self + Copy + use<> {
    let Self { e, base, ref vars, nvars, parent, .. } = *self;
    let (push, parent, base) = match vars.len() as u32 {
      0 => (false, parent, base),
      len => (true, vctxs.peek(), base + len),
    };
    let f = move || VCtx {
      e, base, vars: vec![], nvars,
      access_cache: Default::default(),
      parent
    };
    if push { vctxs.push(std::mem::replace(self, f())); }
    f
  }

  /// Get the number of variables added since the last `share`.
  fn len(&self) -> u32 { self.vars.len() as u32 }

  /// Push a new variable to the context. Returns a proof of `|- okVCtxPush old v new`,
  /// where `old` is the original `self.e` and `new` is `self.e` after the modification.
  fn push(&mut self, de: &mut ProofDedup<'_>, var: VarId, kind: VarKind, v: ProofId) -> ProofId {
    self.vars.push(VCtxVar { var, e: v, kind });
    let old = self.e;
    let len = self.vars.len() as u32;
    let (mut th, mut new);
    if self.parent == VCtxId::ROOT && len == 1 {
      self.e = v; new = v;
      th = thm!(de, okVCtxPush_1(v): (okVCtxPush old v new))
    } else {
      let (mut l, mut r) = (old, v);
      new = app!(de, (vctxA l r));
      th = thm!(de, okVCtxPush_S(v, old): (okVCtxPush old v new));
      for _ in 0..rotation_sequence(len, self.parent != VCtxId::ROOT) {
        app_match!(de, let (vctxA a b) = l);
        let c = r;
        l = a; r = app!(de, (vctxA b c)); new = app!(de, (vctxA l r));
        th = thm!(de, okVCtxPush_R(a, b, c, v, old): (okVCtxPush old v new));
      }
      self.e = new;
    }
    self.access_cache.get_mut().insert(var, (self.base + len, vec![
      (self.base + len, thm!(de, okVCtxPush_get(v, old, new): (okVCtxGet new v)))
    ]));
    th
  }

  /// Add a new proof to the context without changing the set of assumptions.
  /// This is used to be able to reference derived theorems that appear in the MIR by `VarId`,
  /// but do not actually require extending the logical context.
  /// If `or_parent` is true (the default), the proof is inserted to the parent context if
  /// possible, including even the root context.
  fn add(&self, vctxs: &IdxVec<VCtxId, VCtx>, or_parent: bool, var: VarId, th: ProofId) {
    let len = self.len();
    if or_parent && len == 0 {
      vctxs[self.parent].add(vctxs, self.parent != VCtxId::ROOT, var, th)
    } else {
      self.access_cache.borrow_mut().insert(var, (self.base + len, vec![(len, th)]));
    }
  }

  /// Get a stored variable assumption from the context. Returns `(i, v, |- okVCtxGet vctx v)`
  /// where `i` is the index of the variable (the length of the smallest context prefix that
  /// validates the hypothesis).
  fn get(&self,
    de: &mut ProofDedup<'_>, vctxs: &IdxVec<VCtxId, VCtx>, v: VarId
  ) -> (u32, ProofId, ProofId) {
    fn build_cut(de: &mut ProofDedup<'_>,
      [base, src, tgt, cut]: [u32; 4], [l, r, v, th]: [ProofId; 4]) -> ProofId {
      debug_assert!(src < tgt && cut > 0);
      if src <= tgt - cut {
        let th = build(de, base, src, tgt - cut, l, v, th);
        return thm!(de, okVCtxGet_l(l, r, v, th): (okVCtxGet (vctxA l r) v))
      }
      app_match!(de, let (vctxA b c) = r);
      let l2 = app!(de, (vctxA l b));
      let th = build_cut(de, [base, src, tgt, cut >> 1], [l2, c, v, th]);
      thm!(de, okVCtxGet_R(l, b, c, v, th): (okVCtxGet (vctxA l r) v))
    }

    fn build(de: &mut ProofDedup<'_>,
      base: u32, src: u32, tgt: u32, e: ProofId, v: ProofId, th: ProofId,
    ) -> ProofId {
      debug_assert!(src <= tgt);
      if src == tgt { return th }
      let mut cut = 1 << tgt.trailing_zeros();
      if base == 0 && cut == tgt { cut >>= 1 }
      app_match!(de, let (vctxA a b) = e);
      build_cut(de, [base, src, tgt, cut], [a, b, v, th])
    }

    let mut cache = self.access_cache.borrow_mut();
    let (i, ref mut cache) = *cache.entry(v).or_insert_with(|| {
      assert!(self.parent != VCtxId::ROOT, "variable not found");
      let (i, _, th) = vctxs[self.parent].get(de, vctxs, v);
      (i, vec![(0, th)])
    });
    let mut last = cache.last_mut().expect("impossible");
    let len = self.len();
    app_match!(de, let (okVCtxGet _ v) = de.concl(last.1));
    if last.0 == len { return (i, v, last.1) }

    let bound = i.saturating_sub(self.base);
    let mut cur = len;
    let mut stack = vec![];
    let mut e = self.e;
    while last.0 != cur {
      if last.0 > cur {
        cache.pop();
        last = cache.last_mut().expect("impossible");
      } else {
        let cur2 = cur & (cur - 1);
        if cur2 < bound {
          let th = build(de, self.base, last.0, cur, e, v, last.1);
          *last = (cur, th);
          break
        }
        cur = cur2;
        app_match!(de, let (vctxA e2 _) = e);
        stack.push((len, std::mem::replace(&mut e, e2)));
      }
    }
    let mut th = last.1;
    for (cur2, e2) in stack.into_iter().rev() {
      th = build(de, self.base, cur, cur2, e2, v, th);
      cache.push((cur2, th));
      cur = cur2;
    }
    (i, v, th)
  }
}

trait NodeKind: Sized + std::fmt::Debug {
  type Context;
  type Key: Ord + std::fmt::Debug;
  type Node: std::fmt::Debug;
  type Leaf: std::fmt::Debug;
  fn node(de: &mut ProofDedup<'_>, a: &P<MCtxNode<Self>>, b: &P<MCtxNode<Self>>) -> Self::Node;
  fn p_node(de: &mut ProofDedup<'_>, bal: Ordering,
    a: P<MCtxNode<Self>>, b: P<MCtxNode<Self>>
  ) -> P<MCtxNode<Self>> {
    let e = Self::mk(de, a.1, b.1);
    (MCtxNode::Node(bal, Self::node(de, &a, &b), Box::new((a, b))), e)
  }
  fn leaf_key(ctx: &Self::Context, k: &Self::Leaf) -> Self::Key;
  fn node_key(ctx: &Self::Context, k: &Self::Node) -> Self::Key;
  fn key(ctx: &Self::Context, k: &MCtxNode<Self>) -> Self::Key {
    match k {
      MCtxNode::Zero => unreachable!(),
      MCtxNode::One(l) => Self::leaf_key(ctx, l),
      MCtxNode::Node(_, n, _) => Self::node_key(ctx, n),
    }
  }
  fn ctx_left(
    ctx: Self::Context, _a: &P<MCtxNode<Self>>, _b: &P<MCtxNode<Self>>
  ) -> Self::Context { ctx }
  fn ctx_right(
    ctx: Self::Context, _a: &P<MCtxNode<Self>>, _b: &P<MCtxNode<Self>>
  ) -> Self::Context { ctx }

  /// Constructs a node `(a, b)`
  fn mk(de: &mut ProofDedup<'_>, a: ProofId, b: ProofId) -> ProofId { app!(de, (mctxA a b)) }
}

#[allow(clippy::type_complexity)]
#[derive(Debug, Default)]
enum MCtxNode<N: NodeKind> {
  #[default] Zero,
  One(N::Leaf),
  Node(Ordering, N::Node, Box<(P<MCtxNode<N>>, P<MCtxNode<N>>)>),
}

#[derive(Debug)]
struct RegKind<L>(PhantomData<L>);

impl<L: std::fmt::Debug> NodeKind for RegKind<L> {
  type Context = ();
  type Key = u8;
  type Node = u8;
  type Leaf = (u8, L);
  fn node(_: &mut ProofDedup<'_>, a: &P<MCtxNode<Self>>, _: &P<MCtxNode<Self>>) -> Self::Node {
    match a.0 {
      MCtxNode::Zero => unreachable!(),
      MCtxNode::One((k, _)) | MCtxNode::Node(_, k, _) => k
    }
  }
  fn leaf_key((): &(), &(k, _): &(u8, L)) -> u8 { k }
  fn node_key((): &(), &k: &u8) -> u8 { k }
}

#[derive(Debug)]
struct StackKind<L>(PhantomData<L>);

impl<L: std::fmt::Debug> StackKind<L> {
  fn get_key(node: &MCtxNode<Self>) -> u32 {
    match *node {
      MCtxNode::Zero => unreachable!(),
      MCtxNode::One((k, _)) | MCtxNode::Node(_, k, _) => k
    }
  }
}
impl<L: std::fmt::Debug> NodeKind for StackKind<L> {
  type Context = u32;
  type Key = u32;
  type Node = u32;
  type Leaf = (u32, L);
  fn node(_: &mut ProofDedup<'_>, a: &P<MCtxNode<Self>>, _: &P<MCtxNode<Self>>) -> Self::Node {
    Self::get_key(&a.0)
  }
  fn leaf_key(ctx: &u32, _: &(u32, L)) -> u32 { *ctx }
  fn node_key(ctx: &u32, _: &u32) -> u32 { *ctx }
  fn ctx_right(ctx: u32, a: &P<MCtxNode<Self>>, _: &P<MCtxNode<Self>>) -> u32 {
    ctx + Self::get_key(&a.0)
  }
}

trait NodeInsert<N: NodeKind> {
  /// Proves `|- insert mctx0 t = t`
  fn zero(de: &mut ProofDedup<'_>, t: ProofId) -> ProofId;
  /// Proves `|- insert a t = (t, a)`
  fn one_lt(de: &mut ProofDedup<'_>, a: ProofId, t: ProofId) -> ProofId;
  /// Proves `|- insert a t = t`
  fn one_eq(de: &mut ProofDedup<'_>, a: ProofId, t: ProofId) -> ProofId;
  /// Proves `|- insert a t = (a, t)`
  fn one_gt(de: &mut ProofDedup<'_>, a: ProofId, t: ProofId) -> ProofId;
  /// Given `|- insert a t = a2` proves `|- insert (a, b) t = (a2, b)`
  fn node_lt(de: &mut ProofDedup<'_>, a_b_t_a2_th: [ProofId; 5]) -> ProofId;
  /// Given `|- insert b t = b2` proves `|- insert (a, b) t = (a, b2)`
  fn node_gt(de: &mut ProofDedup<'_>, a_b_t_b2_th: [ProofId; 5]) -> ProofId;

  /// Given `|- insert x t = (a, (b, c))` proves `|- insert x t = ((a, b), c)`
  fn rotate_left(_de: &mut ProofDedup<'_>, _x_t_a_b_c_th: [ProofId; 6]) -> ProofId { panic!() }
  /// Given `|- insert x t = ((a, b), c)` proves `|- insert x t = (a, (b, c))`
  fn rotate_right(_de: &mut ProofDedup<'_>, _x_t_a_b_c_th: [ProofId; 6]) -> ProofId { panic!() }

  /// Given `|- insert x t = (b, c)` proves `|- insert (a, x) t = ((a, b), c)`
  fn single_left(de: &mut ProofDedup<'_>, [x, t, a, b, c, th]: [ProofId; 6]) -> ProofId {
    let bc = N::mk(de, b, c);
    let th = Self::node_gt(de, [a, x, t, bc, th]); // insert (a, x) t = (a, (b, c))
    let ax = N::mk(de, a, x);
    Self::rotate_left(de, [ax, t, a, b, c, th]) // insert (a, x) t = ((a, b), c)
  }

  /// Given `|- insert x t = (a, b)` proves `|- insert (x, c) t = (a, (b, c))`
  fn single_right(de: &mut ProofDedup<'_>, [x, t, a, b, c, th]: [ProofId; 6]) -> ProofId {
    let ab = N::mk(de, a, b);
    let th = Self::node_lt(de, [x, c, t, ab, th]); // insert (x, c) t = ((a, b), c)
    let xc = N::mk(de, x, c);
    Self::rotate_right(de, [xc, t, a, b, c, th]) // insert (x, c) t = (a, (b, c))
  }

  /// Given `|- insert x t = ((b, c), d)` proves `|- insert (a, x) t = ((a, b), (c, d))`
  fn double_left(de: &mut ProofDedup<'_>, [x, t, a, b, c, d, th]: [ProofId; 7]) -> ProofId {
    let th = Self::rotate_right(de, [x, t, b, c, d, th]); // insert x t = (b, (c, d))
    let cd = N::mk(de, c, d); let bcd = N::mk(de, b, cd);
    let th = Self::node_gt(de, [a, x, t, bcd, th]); // insert (a, x) t = (a, (b, (c, d)))
    let ax = N::mk(de, a, x);
    Self::rotate_left(de, [ax, t, a, b, cd, th]) // insert (a, x) t = ((a, b), (c, d))
  }

  /// Given `|- insert x t = (a, (b, c))` proves `|- insert (x, d) t = ((a, b), (c, d))`
  fn double_right(de: &mut ProofDedup<'_>, [x, t, a, b, c, d, th]: [ProofId; 7]) -> ProofId {
    let th = Self::rotate_left(de, [x, t, a, b, c, th]); // insert x t = ((a, b), c)
    let ab = N::mk(de, a, b); let abc = N::mk(de, ab, c);
    let th = Self::node_lt(de, [x, d, t, abc, th]); // insert (x, d) t = (((a, b), c), d)
    let xd = N::mk(de, x, d);
    Self::rotate_right(de, [xd, t, ab, c, d, th]) // insert (x, d) t = ((a, b), (c, d))
  }

  fn insert(de: &mut ProofDedup<'_>, node: &mut P<MCtxNode<N>>,
    ctx: N::Context, key: &N::Key, t: P<N::Leaf>
  ) -> P<bool> {
    macro_rules! a {() => {(std::mem::take(&mut node.0), node.1)}}
    macro_rules! b {() => {(MCtxNode::One(t.0), t.1)}}
    match &mut node.0 {
      MCtxNode::Zero => { *node = b!(); (true, Self::zero(de, node.1)) }
      MCtxNode::One(l) => match key.cmp(&N::leaf_key(&ctx, l)) {
        Ordering::Less => {
          let th = Self::one_lt(de, node.1, t.1);
          *node = N::p_node(de, Ordering::Equal, b!(), a!()); (true, th)
        }
        Ordering::Equal => {
          let th = Self::one_eq(de, node.1, t.1);
          *node = b!(); (false, th)
        }
        Ordering::Greater => {
          let th = Self::one_gt(de, node.1, t.1);
          *node = N::p_node(de, Ordering::Equal, a!(), b!()); (true, th)
        }
      }
      MCtxNode::Node(bal, n, ns) => {
        let ns = &mut **ns; let ((_, a), (_, b)) = *ns; let et = t.1;
        if *key < N::key(&ctx, &ns.1.0) {
          let ctx = N::ctx_left(ctx, &ns.0, &ns.1);
          let (grew, th) = Self::insert(de, &mut ns.0, ctx, key, t);
          let rotate_right = grew && match bal {
            Ordering::Less => { *bal = Ordering::Equal; false }
            Ordering::Equal => { *bal = Ordering::Greater; false }
            Ordering::Greater => true
          };
          if rotate_right {
            let MCtxNode::Node(bal1, _, ns1) = std::mem::take(&mut ns.0.0) else { unreachable!() };
            let nb = std::mem::take(&mut ns.1.0);
            let (al, ar) = *ns1;
            match bal1 {
              Ordering::Greater => {
                let th = Self::single_right(de, [a, et, al.1, ar.1, b, th]);
                let n = N::p_node(de, Ordering::Equal, ar, (nb, b));
                *node = N::p_node(de, Ordering::Equal, al, n);
                (false, th)
              }
              Ordering::Equal => {
                let th = Self::single_right(de, [a, et, al.1, ar.1, b, th]);
                let n = N::p_node(de, Ordering::Greater, ar, (nb, b));
                *node = N::p_node(de, Ordering::Less, al, n);
                (true, th)
              }
              Ordering::Less => {
                let MCtxNode::Node(bal2, _, ns2) = ar.0 else { unreachable!() };
                let (arl, arr) = *ns2;
                let (bal_new, bal2_new) = match bal2 {
                  Ordering::Less => (Ordering::Greater, Ordering::Equal),
                  Ordering::Equal => (Ordering::Equal, Ordering::Equal),
                  Ordering::Greater => (Ordering::Equal, Ordering::Less),
                };
                let th = Self::double_right(de, [a, et, al.1, arl.1, arr.1, b, th]);
                let n1 = N::p_node(de, bal_new, al, arl);
                let n2 = N::p_node(de, bal2_new, arr, (nb, b));
                *node = N::p_node(de, Ordering::Equal, n1, n2);
                (false, th)
              }
            }
          } else {
            let th = Self::node_lt(de, [a, b, et, ns.0.1, th]);
            node.1 = N::mk(de, ns.0.1, b);
            *n = N::node(de, &ns.0, &ns.1); (grew && *bal == Ordering::Greater, th)
          }
        } else {
          let ctx = N::ctx_right(ctx, &ns.0, &ns.1);
          let (grew, th) = Self::insert(de, &mut ns.1, ctx, key, t);
          let rotate_left = grew && match bal {
            Ordering::Less => true,
            Ordering::Equal => { *bal = Ordering::Less; false }
            Ordering::Greater => { *bal = Ordering::Equal; false }
          };
          if rotate_left {
            let MCtxNode::Node(bal1, _, ns1) = std::mem::take(&mut ns.1.0) else { unreachable!() };
            let na = std::mem::take(&mut ns.0.0);
            let (bl, br) = *ns1;
            match bal1 {
              Ordering::Less => {
                let th = Self::single_left(de, [b, et, a, bl.1, br.1, th]);
                let n = N::p_node(de, Ordering::Equal, (na, a), bl);
                *node = N::p_node(de, Ordering::Equal, n, br);
                (false, th)
              }
              Ordering::Equal => {
                let th = Self::single_left(de, [b, et, a, bl.1, br.1, th]);
                let n = N::p_node(de, Ordering::Greater, (na, a), bl);
                *node = N::p_node(de, Ordering::Less, n, br);
                (true, th)
              }
              Ordering::Greater => {
                let MCtxNode::Node(bal2, _, ns2) = bl.0 else { unreachable!() };
                let (bll, blr) = *ns2;
                let (bal_new, bal2_new) = match bal2 {
                  Ordering::Less => (Ordering::Greater, Ordering::Equal),
                  Ordering::Equal => (Ordering::Equal, Ordering::Equal),
                  Ordering::Greater => (Ordering::Equal, Ordering::Less),
                };
                let th = Self::double_left(de, [b, et, a, bll.1, blr.1, br.1, th]);
                let n1 = N::p_node(de, bal_new, (na, a), bll);
                let n2 = N::p_node(de, bal2_new, blr, br);
                *node = N::p_node(de, Ordering::Equal, n1, n2);
                (false, th)
              }
            }
          } else {
            let th = Self::node_gt(de, [a, b, et, ns.1.1, th]);
            node.1 = N::mk(de, a, ns.1.1);
            *n = N::node(de, &ns.0, &ns.1); (grew && *bal == Ordering::Less, th)
          }
        }
      }
    }
  }
}

struct PushMCtx;
impl<N: NodeKind> NodeInsert<N> for PushMCtx {
  fn zero(de: &mut ProofDedup<'_>, t: ProofId) -> ProofId {
    thm!(de, pushMCtx_0(t): (pushMCtx (mctx0) t t))
  }

  fn one_lt(de: &mut ProofDedup<'_>, a: ProofId, t: ProofId) -> ProofId {
    thm!(de, pushMCtx_1L(a, t): (pushMCtx a t (mctxA t a)))
  }

  fn one_eq(_: &mut ProofDedup<'_>, _: ProofId, _: ProofId) -> ProofId {
    unreachable!("inserting twice in the same mctx")
  }

  fn one_gt(de: &mut ProofDedup<'_>, a: ProofId, t: ProofId) -> ProofId {
    thm!(de, pushMCtx_1R(a, t): (pushMCtx a t (mctxA a t)))
  }

  fn node_lt(de: &mut ProofDedup<'_>, [a, b, t, a2, th]: [ProofId; 5]) -> ProofId {
    thm!(de, pushMCtx_L(a, a2, b, t, th): (pushMCtx (mctxA a b) t (mctxA a2 b)))
  }

  fn node_gt(de: &mut ProofDedup<'_>, [a, b, t, b2, th]: [ProofId; 5]) -> ProofId {
    thm!(de, pushMCtx_R(a, b, b2, t, th): (pushMCtx (mctxA a b) t (mctxA a b2)))
  }

  fn rotate_left(de: &mut ProofDedup<'_>, [x, t, a, b, c, th]: [ProofId; 6]) -> ProofId {
    thm!(de, pushMCtx_rotL(a, b, c, x, t, th): (pushMCtx x t (mctxA (mctxA a b) c)))
  }

  fn rotate_right(de: &mut ProofDedup<'_>, [x, t, a, b, c, th]: [ProofId; 6]) -> ProofId {
    thm!(de, pushMCtx_rotR(a, b, c, x, t, th): (pushMCtx x t (mctxA a (mctxA b c))))
  }
}

struct NoProof;
impl<N: NodeKind> NodeInsert<N> for NoProof {
  fn zero(_: &mut ProofDedup<'_>, _: ProofId) -> ProofId { ProofId::INVALID }
  fn one_lt(_: &mut ProofDedup<'_>, _: ProofId, _: ProofId) -> ProofId { ProofId::INVALID }
  fn one_eq(_: &mut ProofDedup<'_>, _: ProofId, _: ProofId) -> ProofId { ProofId::INVALID }
  fn one_gt(_: &mut ProofDedup<'_>, _: ProofId, _: ProofId) -> ProofId { ProofId::INVALID }
  fn node_lt(_: &mut ProofDedup<'_>, _: [ProofId; 5]) -> ProofId { ProofId::INVALID }
  fn node_gt(_: &mut ProofDedup<'_>, _: [ProofId; 5]) -> ProofId { ProofId::INVALID }
  fn rotate_left(_: &mut ProofDedup<'_>, _: [ProofId; 6]) -> ProofId { ProofId::INVALID }
  fn rotate_right(_: &mut ProofDedup<'_>, _: [ProofId; 6]) -> ProofId { ProofId::INVALID }
  fn single_left(_: &mut ProofDedup<'_>, _: [ProofId; 6]) -> ProofId { ProofId::INVALID }
  fn single_right(_: &mut ProofDedup<'_>, _: [ProofId; 6]) -> ProofId { ProofId::INVALID }
  fn double_left(_: &mut ProofDedup<'_>, _: [ProofId; 7]) -> ProofId { ProofId::INVALID }
  fn double_right(_: &mut ProofDedup<'_>, _: [ProofId; 7]) -> ProofId { ProofId::INVALID }
}

#[derive(Debug)]
enum Expr {
  Var(VarId),
}

#[derive(Debug)]
enum MCtxRegValue {
  Free,
  Expr(P<Expr>),
}

#[derive(Debug)]
enum MCtxStkValue {
  Free
}

type MCtxRegKind = RegKind<MCtxRegValue>;
type MCtxStkKind = StackKind<MCtxStkValue>;
#[derive(Debug)]
struct MCtx {
  regs: P<MCtxNode<MCtxRegKind>>,
  stack: Option<P<MCtxNode<MCtxStkKind>>>,
}

impl MCtxNode<MCtxRegKind> {
  /// Returns `(a, b, |- bddMCtx mctx a b)`
  fn bdd(this: &P<Self>, de: &mut ProofDedup<'_>) -> (P<u8>, P<u8>, ProofId) {
    match this.0 {
      MCtxNode::Zero => unreachable!(),
      MCtxNode::One((k, _)) => {
        app_match!(de, this.1 => {
          (FREE r) => ((k, r), (k, r), thm!(de, bddMCtx_FREE(r): bddMCtx[this.1, r, r])),
          (REG r v) => ((k, r), (k, r), thm!(de, bddMCtx_REG(r, v): bddMCtx[this.1, r, r])),
        })
      }
      MCtxNode::Node(_, _, ref ns) => {
        let (n1, n2) = &**ns;
        let (a, b, h1) = Self::bdd(n1, de);
        let (c, d, h2) = Self::bdd(n2, de);
        let h3 = thm!(de, decltn[b.0][c.0](): (h2n {b.1}) < (h2n {c.1}));
        (a, d, thm!(de, (bddMCtx[this.1, a.1, d.1]) =>
          bddMCtx_A(n1.1, n2.1, a.1, b.1, c.1, d.1, h1, h2, h3)))
      }
    }
  }

  /// Returns `|- okMCtx mctx`
  fn ok(this: &P<Self>, de: &mut ProofDedup<'_>) -> ProofId {
    if let MCtxNode::Zero = this.0 {
      thm!(de, okMCtx_0(): (okMCtx (mctx0)))
    } else {
      let (a, b, th) = Self::bdd(this, de);
      thm!(de, okMCtx_S(a.1, b.1, this.1, th): okMCtx[this.1])
    }
  }
}

impl MCtx {
  fn new(de: &mut ProofDedup<'_>) -> P<Self> {
    let a = app!(de, (mctx0));
    (Self { regs: (MCtxNode::Zero, a), stack: None }, a)
  }

  fn push_reg<I: NodeInsert<MCtxRegKind>>(this: &mut P<Self>, de: &mut ProofDedup<'_>,
    ((reg, value), t): P<(u8, MCtxRegValue)>
  ) -> ProofId {
    let a = this.1;
    let (_, th) = I::insert(de, &mut this.0.regs, (), &reg, ((reg, value), t));
    if let Some((_, stk)) = this.0.stack {
      let a2 = this.0.regs.1;
      this.1 = app!(de, mctxA[a2, stk]);
      I::node_lt(de, [a, stk, t, a2, th])
    } else {
      this.1 = this.0.regs.1;
      th
    }
  }

  fn add_stack(this: &mut P<Self>, de: &mut ProofDedup<'_>, off: Num, n: Num) {
    let e = app!(de, (stkFREE {*off} {*n}));
    assert!(this.0.stack.replace((MCtxNode::One((n.val as u32, MCtxStkValue::Free)), e)).is_none());
    this.1 = app!(de, mctxA[this.1, e]);
  }

  fn mk(&self, de: &mut ProofDedup<'_>) -> ProofId {
    match self.stack {
      Some((_, stk)) => app!(de, mctxA[self.regs.1, stk]),
      None => self.regs.1,
    }
  }

  /// Returns `|- okMCtx mctx`
  fn ok(&self, de: &mut ProofDedup<'_>) -> ProofId {
    assert!(self.stack.is_none());
    MCtxNode::ok(&self.regs, de)
  }
}

struct TCtx {
  vctx: VCtx,
  mctx: P<MCtx>,
}

type PTCtx = P<Box<TCtx>>;

impl TCtx {
  /// Given `ty`, returns `(n, (tctx2, |- okPushVar tctx ty tctx2))`,
  /// where `tctx2` is the result of adding `vVar n ty` to `tctx`
  fn push_var(
    &mut self, tctx: ProofId, de: &mut ProofDedup<'_>, hex: &HexCache, var: VarId, ty: ProofId,
  ) -> (Num, (ProofId, ProofId)) {
    let n = self.vctx.nvars;
    let e = app!(de, (vVar {*n} ty));
    let old = self.vctx.e;
    let h1 = self.vctx.push(de, var, VarKind::Var, e);
    let (n2, h2) = hex.suc(de, n);
    self.vctx.nvars = n2;
    let tctx2 = self.mk(de);
    // let th = thm!(de, ((okPushVar tctx {*n2} tctx2)) =>
    //   okPushVarI(self.mctx.1, self.mctx.1, *n, *n2, ty, old, self.vctx.e, h1, h2));
    let th = ProofId::INVALID;
    (n, (tctx2, th))
  }

  /// Given `ty`, returns `(tctx2, |- okPushVar tctx ty tctx2)`,
  /// where `tctx2` is the result of adding `vHyp ty` to `tctx`
  fn push_hyp(
    &mut self, tctx: ProofId, de: &mut ProofDedup<'_>, var: VarId, kind: VarKind,
    ty: ProofId,
  ) -> (ProofId, ProofId) {
    let e = app!(de, (vHyp ty));
    let old = self.vctx.e;
    let h1 = self.vctx.push(de, var, kind, e);
    let tctx2 = self.mk(de);
    // let th = thm!(de, ((okPushVar tctx {*self.vctx.nvars} tctx2)) =>
    //   okPushHypI(self.mctx.1, *self.vctx.nvars, ty, old, self.vctx.e, h1));
    let th = ProofId::INVALID;
    (tctx2, th)
  }

  fn mk(&self, de: &mut ProofDedup<'_>) -> ProofId {
    app!(de, mkTCtx[self.vctx.e, *self.vctx.nvars, self.mctx.1])
  }
}

struct ProcProver<'a> {
  elf_proof: &'a ElfProof<'a>,
  proc: &'a Proc<'a>,
  proc_asm: &'a HashMap<Option<ProcId>, (TermId, ThmId)>,
  proc_proof: &'a mut HashMap<Option<ProcId>, ThmId>,
  /// Contains a map from a vblock id to `(asm, |- okAssembled pctx asm)`
  vblock_asm: HashMap<VBlockId, (ProofId, ProofId)>,
  /// Contains a map from a block id to
  /// `[labs, ip, lctx, |- okBlock (mkBCtx pctx labs) ip lctx]`
  block_proof: HashMap<BlockId, [ProofId; 4]>,
  vctxs: IdxVec<VCtxId, VCtx>,
  elab: &'a mut Elaborator,
  hex: HexCache,
  thm: ProofDedup<'a>,
  ctx: Ctx,
}

#[derive(Clone, Copy)]
enum Loc {
  Reg(P<u8>),
  Local(ProofId),
}

impl Loc {
  // fn as_expr(self, thm: &mut ProofDedup<'_>) -> P<Self> {
  //   let e = match self {
  //     Loc::Reg(n) => app!(thm, Loc_reg[n.1]),
  //     Loc::Local(n) => app!(thm, Loc_local[n]),
  //   };
  //   (self, e)
  // }
}

#[derive(Clone, Copy)]
enum Value {
  Reg,
  SpillSlot(ProofId),
}

enum ConstantVal {
  Zst,
  // (e, |- HasType e ty)
  Value(ProofId, ProofId),
}

impl std::ops::Deref for ProcProver<'_> {
  type Target = Ctx;
  fn deref(&self) -> &Self::Target { &self.ctx }
}

impl ProcProver<'_> {
  fn pp(&mut self, i: ProofId) -> String {
    format_to_string(|s| self.thm.pp(self.elab, i, s))
  }

  fn push_label_group(&mut self, var: ProofId, ls: ProofId) -> [ProofId; 2] {
    let old = [self.labs, self.bctx];
    self.ctx.labs = app!(self.thm, labelGroup[var, ls, self.labs]);
    self.ctx.bctx = app!(self.thm, mkBCtx[self.pctx, self.labs]);
    old
  }

  fn split_asm(&self, code: ProofId) -> (ProofId, ProofId) {
    app_match!(self.thm, code => {
      (ASM_A a b) => (a, b),
      (ASM0) => (code, code),
    })
  }

  fn pop_label_group(&mut self, [labs, bctx]: [ProofId; 2]) {
    self.ctx.labs = labs;
    self.ctx.bctx = bctx;
  }

  fn prove_vblock_asm(&mut self, iter: &mut AssemblyBlocks<'_>, a: ProofId, th: ProofId) {
    app_match!(self.thm, a => {
      (ASM_A a b) => {
        let th1 = thm!(self.thm, okAssembled_l(a, b, self.pctx, th): okAssembled[self.pctx, a]);
        self.prove_vblock_asm(iter, a, th1);
        let th2 = thm!(self.thm, okAssembled_r(a, b, self.pctx, th): okAssembled[self.pctx, b]);
        self.prove_vblock_asm(iter, b, th2);
      }
      _ => {
        let block = iter.next().expect("impossible");
        self.vblock_asm.insert(block.id, (a, th));
      }
    })
  }

  /// Returns the `tctx` type state for the entry of a block.
  fn block_tctx(&mut self, bl: BlockProof<'_>, vctx: VCtx, base: CtxId) -> PTCtx {
    let mut tctx = Box::new(TCtx {
      vctx,
      mctx: MCtx::new(&mut self.thm), // TODO
    });
    let mut l = tctx.mk(&mut self.thm);
    for (v, _, (e, ty)) in self.proc.cfg.ctxs.iter_range(base..bl.block().ctx) {
      let (l2, th) = match e {
        Some(e) if match **e {
          ExprKind::Var(u) if u == v.k => false,
          ExprKind::Unit => false,
          _ => true,
        } => {
          let ty = app!(self.thm, (ok0)); // TODO
          tctx.push_hyp(l, &mut self.thm, v.k, VarKind::Hyp, ty)
        }
        _ => {
          let ty = app!(self.thm, (ok0)); // TODO
          tctx.push_var(l, &mut self.thm, &self.hex, v.k, ty).1
        }
      };
      l = l2;
    }
    (tctx, l)
  }

  /// Given `[l1, l2, l3, code, |- okCode bctx l1 code1 l2, |- okCode bctx l2 code2 l3]`,
  /// proves `|- okCode bctx l1 code tctx`
  /// if `code = code1 +asm code2` or `code, code1, code2 = ASM0`
  fn ok_code_join(&mut self, [l1, l2, l3, code, h1, h2]: [ProofId; 6]) -> ProofId {
    app_match!(self.thm, code => {
      (ASM_A code1 code2) => thm!(self.thm, (okCode[self.bctx, l1, code, l3]) =>
        okCode_A(self.bctx, code1, code2, l1, l2, l3, h1, h2)),
      (ASM0) => thm!(self.thm, (okCode[self.bctx, l1, code, l3]) =>
        okCode_tr(self.bctx, l1, l2, l3, h1, h2)),
    })
  }

  /// Returns
  /// * `(ip, |- okBlock bctx (suc ip) tctx)` or
  /// * `(INVALID, |- okCode bctx tctx ASM0 ok0)`
  ///
  /// for the given block, starting from the given `tctx`.
  fn ok_block_opt(&mut self, (tctx, l1): P<&mut TCtx>, tgt: BlockId) -> (ProofId, ProofId) {
    if let Some(vid) = self.proc.vblock_id(tgt) {
      let (a, h1) = self.vblock_asm[&vid];
      app_match!(self.thm, let (asmAt ip code) = a);
      let h2 = self.ok_stmts(self.proc.block(tgt), code, (tctx, l1));
      (ip, thm!(self.thm, ((okBlock {self.bctx} (suc ip) l1)) =>
        okBlockI(self.labs, code, ip, self.pctx, l1, h1, h2)))
    } else {
      (ProofId::INVALID, self.ok_stmts(self.proc.block(tgt), self.asm0, (tctx, l1)))
    }
  }

  /// Returns `(ip, |- okBlock bctx ip tctx)`
  /// for the given block, starting from the given `tctx`.
  fn ok_block(&mut self, (tctx, l1): P<&mut TCtx>, tgt: BlockId) -> (ProofId, ProofId) {
    let (ip, th) = self.ok_block_opt((tctx, l1), tgt);
    if ip == ProofId::INVALID {
      let ip = app!(self.thm, (d0));
      (ip, thm!(self.thm, okBlock0(self.bctx, l1, th): okBlock[self.bctx, ip, l1]))
    } else {
      (app!(self.thm, (suc ip)), th)
    }
  }

  /// Returns `|- okReadHyp tctx ty2` if `th: |- okReadHyp tctx ty`
  fn read_hyp_coerce(&mut self, ty: ProofId, th: ProofId, ty2: ProofId) -> ProofId {
    // TODO
    assert!(ty == ty2, "failed to coerce {} to {}", self.pp(ty), self.pp(ty2));
    th
  }

  /// Returns `(ty, |- okReadHyp tctx ty)`
  fn read_hyp_tctx_var(&mut self, (tctx, l1): P<&TCtx>, v: VarId) -> (ProofId, ProofId) {
    // eprintln!("get {:?} in\n{}", v,
    //   format_to_string(|s| vctx.pp(&self.thm, self.elab, &self.vctxs, s)));
    let (_, val, h1) = tctx.vctx.get(&mut self.thm, &self.vctxs, v);
    app_match!(self.thm, let (mkTCtx vctx n mctx) = l1);
    app_match!(self.thm, val => {
      (vHyp ty) => (ty,
          // thm!(self.thm, okReadHypHyp(mctx, n, ty, vctx, h1): okReadHyp[l1, ty])
          ProofId::INVALID
        ),
      (vVar v ty) =>
        (ty,
          // thm!(self.thm, okReadHypVar(mctx, n, ty, v, vctx, h1): okReadHyp[l1, ty])
          ProofId::INVALID
        ),
    })
  }

  /// Returns `(ty, |- okReadHyp tctx ty)`
  fn read_hyp_tctx_place(&mut self, tctx: P<&TCtx>, p: &Place) -> (ProofId, ProofId) {
    assert!(p.proj.is_empty()); // TODO
    self.read_hyp_tctx_var(tctx, p.local)
  }

  fn mk_type(&mut self, ty: &Ty) -> ProofId {
    match &**ty {
      TyKind::Unit => app!(self.thm, (tyUnit)),
      TyKind::True => todo!(),
      TyKind::False => todo!(),
      TyKind::Bool => todo!(),
      TyKind::Var(_) => todo!(),
      TyKind::Int(ity) => todo!(),
      TyKind::Array(ty_kind, expr_kind) => todo!(),
      TyKind::Own(ty_kind) => todo!(),
      TyKind::Shr(lifetime, ty_kind) => todo!(),
      TyKind::Ref(lifetime, ty_kind) => todo!(),
      TyKind::RefSn(eplace_kind) => todo!(),
      TyKind::Sn(expr_kind, ty_kind) => todo!(),
      TyKind::Struct(args) => todo!(),
      TyKind::All(var_id, ty_kind, ty_kind1) => todo!(),
      TyKind::Imp(ty_kind, ty_kind1) => todo!(),
      TyKind::Wand(ty_kind, ty_kind1) => todo!(),
      TyKind::Not(ty_kind) => todo!(),
      TyKind::And(ty_kinds) => todo!(),
      TyKind::Or(ty_kinds) => todo!(),
      TyKind::If(expr_kind, ty_kind, ty_kind1) => todo!(),
      TyKind::Ghost(ty_kind) => todo!(),
      TyKind::Uninit(ty_kind) => todo!(),
      TyKind::Pure(expr_kind) => todo!(),
      TyKind::User(symbol, ty_kinds, expr_kinds) => todo!(),
      TyKind::Heap(expr_kind, expr_kind1, ty_kind) => todo!(),
      TyKind::HasTy(expr_kind, ty_kind) => todo!(),
      TyKind::Input => todo!(),
      TyKind::Output => todo!(),
      TyKind::Moved(ty_kind) => todo!(),
    }
  }

  fn constant(&self, c: &Constant) -> ConstantVal {
    match c.k {
      ConstKind::Unit |
      ConstKind::ITrue => ConstantVal::Zst,
      ConstKind::Bool => todo!(),
      ConstKind::Int => {
        let Some(e) = &c.ety.0 else { unreachable!() };
        let ExprKind::Int(n) = &**e else { unreachable!() };
        let TyKind::Int(ity) = *c.ety.1 else { unreachable!() };
        let n = ity.zero_extend_as_u64(n).expect("impossible");
        todo!("int constant")
      }
      ConstKind::Uninit => todo!(),
      ConstKind::Const(symbol) => todo!(),
      ConstKind::Sizeof => todo!(),
      ConstKind::Mm0Proof(proof_id) => todo!(),
      ConstKind::Contra(block_id, var_id) => todo!(),
      ConstKind::As(_) => todo!(),
    }
  }

  /// Returns `(ty, |- okReadHyp tctx ty)`
  fn read_hyp_operand(&mut self, (tctx, l1): P<&TCtx>, op: &Operand) -> (ProofId, ProofId) {
    match op.place() {
      Ok(p) => self.read_hyp_tctx_place((tctx, l1), p),
      Err(c) => match c.k {
        ConstKind::Unit => {
          let ty = app!(self.thm, (tyUnit));
          (ty,
            // thm!(self.thm, okReadHyp_unit(l1): okReadHyp[l1, ty])
            ProofId::INVALID
          )
        }
        ConstKind::ITrue => todo!(),
        ConstKind::Bool => todo!(),
        ConstKind::Int => todo!(),
        ConstKind::Uninit => todo!(),
        ConstKind::Const(_) => todo!(),
        ConstKind::Sizeof => todo!(),
        ConstKind::Mm0Proof(_) => todo!(),
        ConstKind::Contra(_, _) => todo!(),
        ConstKind::As(_) => todo!(),
      }
    }
  }

  /// Returns `(args, mctx, |- accumArgs args vctx n)`
  fn accum_args(&mut self, vctx: &mut VCtx,
    bl_ctx: CtxId, abi: &[ArgAbi]
  ) -> (ProofId, P<MCtx>, ProofId) {
    let mut args = app!(self.thm, (arg0));
    let mut th = thm!(self.thm, accumArgs0(): (accumArgs args {vctx.e} {*vctx.nvars}));
    let mut mctx = MCtx::new(&mut self.thm);
    for ((v, _, (e, ty)), abi) in self.proc.cfg.ctxs.iter(..bl_ctx).zip(abi) {
      let (vctx1, n1) = (vctx.e, vctx.nvars);
      let args2;
      th = match e {
        Some(e) if match **e {
          ExprKind::Var(u) if u == v.k => false,
          ExprKind::Unit => false,
          _ => true,
        } => {
          let ty = app!(self.thm, (ok0)); // TODO
          let e = app!(self.thm, (vHyp ty));
          let h2 = vctx.push(&mut self.thm, v.k, VarKind::Hyp, e);
          args2 = app!(self.thm, (argS args (aHyp ty)));
          thm!(self.thm, ((accumArgs args2 {vctx.e} {*vctx.nvars})) =>
            accumArgsHyp(args, *n1, ty, vctx1, vctx.e, th, h2))
        }
        _ => {
          match abi {
            ArgAbi::Ghost => {}
            ArgAbi::Reg(r, _) => {
              let r = r.index();
              let var = app!(self.thm, (eVar {*n1}));
              let value = MCtxRegValue::Expr((Expr::Var(v.k), var));
              let t = app!(self.thm, REG[self.hex[r], var]);
              MCtx::push_reg::<NoProof>(&mut mctx, &mut self.thm, ((r, value), t));
            }
            ArgAbi::Mem { .. } => todo!(),
            ArgAbi::Boxed { .. } => todo!(),
            ArgAbi::BoxedMem { .. } => todo!(),
          }
          let ty = app!(self.thm, (ok0)); // TODO
          let e = app!(self.thm, (vVar {*n1} ty));
          let h2 = vctx.push(&mut self.thm, v.k, VarKind::Var, e);
          let (n2, h3) = self.hex.suc(&mut self.thm, n1);
          vctx.nvars = n2;
          args2 = app!(self.thm, (argS args (aVar {*n1} ty)));
          thm!(self.thm, ((accumArgs args2 {vctx.e} {*vctx.nvars})) =>
            accumArgsVar(args, *n1, *vctx.nvars, ty, vctx1, vctx.e, th, h2, h3))
        }
      };
      args = args2;
    }
    (args, mctx, th)
  }

  /// Returns `(clob, |- accumClob clob mctx mctx2)`
  fn accum_clob(&mut self, mctx: &mut P<MCtx>,
    mut iter: impl Iterator<Item=u8>
  ) -> (ProofId, ProofId) {
    if let Some(r) = iter.next() {
      let mctx1 = mctx.1;
      let er = self.hex[r];
      let t = ((r, MCtxRegValue::Free), app!(self.thm, (FREE er)));
      let h1 = MCtx::push_reg::<PushMCtx>(mctx, &mut self.thm, t);
      let mctx2 = mctx.1;
      let (clob, h2) = self.accum_clob(mctx, iter);
      let clob2 = app!(self.thm, (clobS er clob));
      (clob2, thm!(self.thm, (accumClob[clob2, mctx1, mctx.1]) =>
        accumClobS(clob, mctx1, mctx2, mctx.1, er, h1, h2)))
    } else {
      let clob = app!(self.thm, (clob0));
      (clob, thm!(self.thm, accumClob0(mctx.1): accumClob[clob, mctx.1, mctx.1]))
    }
  }

  /// Returns `|- okPrologue epiRet mctx1 code epi mctx2`
  fn ok_prologue(&mut self, mctx: &mut P<MCtx>, mut code: ProofId) -> ProofId {
    let mut epi = app!(self.thm, (epiRet));
    let mut stack = vec![];
    for &reg in self.proc.saved_regs() {
      let r = reg.index(); let er = self.hex[r];
      app_match!(self.thm, let (ASM_A _ code2) = code);
      let mctx1 = mctx.1;
      let t = ((r, MCtxRegValue::Free), app!(self.thm, (FREE er)));
      let h1 = MCtx::push_reg::<PushMCtx>(mctx, &mut self.thm, t);
      stack.push([code, code2, epi, mctx1, mctx.1, er, h1]);
      epi = app!(self.thm, epiPop[er, epi]);
      code = code2;
    }
    let h1 = mctx.0.ok(&mut self.thm);
    let mctx1 = mctx.1;
    let mut th = if self.sp_max.val == 0 {
      thm!(self.thm, (okPrologue[epi, mctx1, code, epi, mctx1]) =>
        okPrologue_alloc0(epi, mctx1, h1))
    } else {
      let off = self.hex.h2n(&mut self.thm, 0);
      MCtx::add_stack(mctx, &mut self.thm, off, self.ctx.sp_max);
      let max = self.hex.from_u32(&mut self.thm, (1 << 12) - 8);
      let h2 = self.hex.le(&mut self.thm, self.ctx.sp_max, max);
      thm!(self.thm, (okPrologue[epi, mctx1, code, self.epi, mctx.1]) =>
        okPrologue_alloc(epi, mctx1, *self.sp_max, h1, h2))
    };
    for [code, code2, epi1, mctx1, mctx2, er, h1] in stack.into_iter().rev() {
      th = thm!(self.thm, (okPrologue[epi1, mctx1, code, epi, mctx.1]) =>
        okPrologue_push(code2, epi1, epi, mctx1, mctx2, mctx.1, er, h1, th))
    }
    th
  }

  /// Returns `|- okEpilogue epi code`
  fn ok_epilogue(&mut self, epi: ProofId, code: ProofId) -> ProofId {
    app_match!(self.thm, epi => {
      (epiPop r epi2) => {
        app_match!(self.thm, let (ASM_A _ code2) = code);
        let th = self.ok_epilogue(epi2, code2);
        thm!(self.thm, okEpilogue_pop(code2, epi2, r, th): okEpilogue[epi, code])
      }
      (epiFree n epi2) => {
        app_match!(self.thm, let (ASM_A _ code2) = code);
        let th = self.ok_epilogue(epi2, code2);
        thm!(self.thm, okEpilogue_free(code2, epi2, n, th): okEpilogue[epi, code])
      }
      (epiRet) => thm!(self.thm, okEpilogue_ret(): okEpilogue[epi, code]),
    })
  }

  /// Returns `|- getEpi bctx ret code`
  fn get_epi(&mut self, code: ProofId) -> ProofId {
    let h = self.ok_epilogue(self.epi, code);
    thm!(self.thm, (getEpi[self.bctx, self.ret, code]) =>
      getEpiI(code, self.epi, self.gctx, self.labs, self.ret, self.se, h))
  }

  /// Returns `(tctx, |- buildStart gctx pctx tctx)`
  fn build_start(&mut self, bl: BlockProof<'_>, root: VCtx) -> (PTCtx, ProofId) {
    let (tctx, l1) = self.block_tctx(bl, root, CtxId::ROOT);
    ((tctx, l1), thm!(self.thm, buildStartI(self.gctx): buildStart[self.gctx, self.pctx, l1]))
  }

  // /// Returns `(v, |- okRead tctx loc v)`
  // fn read(&mut self, tctx: &P<&mut TCtx>, loc: &P<Loc>) -> (P<Value>, ProofId) {
  //   let v = app!(self.thm, (d0)); // TODO
  //   let ret = app!(self.thm, okRead[tctx.1, loc.1, v]);
  //   ((Value::Reg, v), thm!(self.thm, sorry(ret): ret)) // TODO
  // }

  // /// Returns `(tctx', |- okWrite tctx loc v tctx')`
  // fn write(&mut self, tctx: &P<&mut TCtx>, loc: &P<Loc>, v: &P<Value>) -> ProofId {
  //   let l1 = tctx.1;
  //   // tctx.1 = l1;
  //   let ret = app!(self.thm, okWrite[l1, loc.1, v.1, tctx.1]);
  //   thm!(self.thm, sorry(ret): ret) // TODO
  // }

  /// Returns `|- okCode bctx tctx code tctx'` for a regalloc operation.
  fn ok_spill_op(&self, tctx: &P<&mut TCtx>, inst: &PInst, code: ProofId) -> ProofId {
    let l1 = tctx.1;
    app_match!(self.thm, let (instMov _ dst src) = code);
    let reg_or_mem = |arg| app_match!(self.thm, arg => {
      (IRM_reg reg) => Ok(reg),
      (IRM_mem _ _ (posZ off)) => Err(off),
    });
    match (reg_or_mem(dst), reg_or_mem(src), inst) {
      (Ok(edst), Ok(esrc), &PInst::MovRR { dst, src, .. }) => {
        // let lsrc = Loc::Reg((src.index(), esrc)).as_expr(&mut self.thm);
        // let ldst = Loc::Reg((dst.index(), edst)).as_expr(&mut self.thm);
        // let ((Value::Reg, v), h1) = self.read(tctx, &lsrc) else { unreachable!() };
        // let h2 = self.write(tctx, &ldst, &(Value::Reg, v));
        // thm!(self.thm, (okCode[self.bctx, l1, code, tctx.1]) =>
        //   ok_movRR(self.bctx, edst, esrc, l1, tctx.1, v, h1, h2))
        todo!("movRR")
      }
      (Ok(edst), Err(esrc), &PInst::Load64 { dst, .. }) => {
        // let lsrc = Loc::Local(esrc).as_expr(&mut self.thm);
        // let ldst = Loc::Reg((dst.index(), edst)).as_expr(&mut self.thm);
        // let ((Value::SpillSlot(v), _), h1) = self.read(tctx, &lsrc) else { unreachable!() };
        // let h2 = self.write(tctx, &ldst, &(Value::Reg, v));
        // thm!(self.thm, (okCode[self.bctx, l1, code, tctx.1]) =>
        //   ok_unspill(self.bctx, edst, esrc, l1, tctx.1, v, h1, h2))
        todo!("unspill")
      }
      (Err(edst), Ok(esrc), &PInst::Store { src, .. }) => {
        // let lsrc = Loc::Reg((src.index(), esrc)).as_expr(&mut self.thm);
        // let ldst = Loc::Local(edst).as_expr(&mut self.thm);
        // let ((Value::Reg, v), h1) = self.read(tctx, &lsrc) else { unreachable!() };
        // let ss = app!(self.thm, (spillslot v));
        // let h2 = self.write(tctx, &ldst, &(Value::SpillSlot(v), ss));
        // thm!(self.thm, (okCode[self.bctx, l1, code, tctx.1]) =>
        //   ok_spill(self.bctx, edst, esrc, l1, tctx.1, v, h1, h2))
        todo!("spill")
      }
      _ => unreachable!()
    }
  }

  /// Returns `(T, |- getResult gctx T)`
  fn get_result(&mut self) -> (ProofId, ProofId) {
    let u_gctx = self.thm.get_def0(self.elab, self.t_gctx);
    app_match!(self.thm, let (mkGCtx c fs ms ty) = u_gctx);
    let th = thm!(self.thm, getResultGI(ty, c, fs, ms): getResult[u_gctx, ty]);
    (ty, thm!(self.thm, (getResult[self.gctx, ty]) =>
      CONV({th} => (getResult (UNFOLD({self.t_gctx}); u_gctx) ty))))
  }

  /// Returns `|- checkRet bctx tctx ret`
  fn check_ret(&mut self,
    tctx: &mut P<&mut TCtx>, outs: &[VarId], args: &[(VarId, bool, Operand)]
  ) -> ProofId {
    // let th = thm!(self.thm, (checkRet[self.bctx, tctx.1, self.ret]) =>
    //   checkRetI(self.bctx, self.ret, tctx.1));
    let ret = app!(self.thm, checkRet[self.bctx, tctx.1, self.ret]);
    let th = thm!(self.thm, sorry(ret): ret); // TODO
    tctx.1 = self.ok0;
    th
  }

  /// Returns `(tctx2, |- applyCall tctx1 args ret clob tctx2)`,
  /// or `(tctx2, |- applyCallG tctx1 args ret tctx2)` if `rel` is false
  #[allow(clippy::too_many_arguments)]
  fn apply_call(&mut self,
    tctx: &P<&mut TCtx>,
    abi: &ProcAbi,
    args: ProofId,
    ret: ProofId,
    clob: ProofId,
    rel: bool,
  ) -> ProofId {
    if !abi.args.is_empty() || !abi.rets.is_empty() { todo!() }
    let l1 = tctx.1;
    let l2 = tctx.1;
    if rel {
      let ret = app!(self.thm, applyCall[l1, args, ret, clob, l2]);
      thm!(self.thm, sorry(ret): ret) // TODO
    } else {
      let ret = app!(self.thm, applyCallG[l1, args, ret, l2]);
      thm!(self.thm, sorry(ret): ret) // TODO
    }
  }

  /// Proves `|- okProc gctx start args ret clob se`,
  /// or `|- okStart gctx fs ms` for the start procedure
  fn prove_proc(&mut self, root: VCtx) -> ProofId {
    let (asm, asmd_thm) = self.proc_asm[&self.proc.id];
    let (x, th) = self.thm.thm0(self.elab, asmd_thm);
    app_match!(self.thm, let (assembled g (asmProc p a)) = x);
    let th = thm!(self.thm, okAssembledI(a, g, self.pctx1, p, th): okAssembled[self.pctx, a]);
    let a2 = self.thm.get_def0(self.elab, asm);
    let th = thm!(self.thm, (okAssembled[self.pctx, a2]) =>
      CONV({th} => SYM (okAssembled (REFL {self.pctx}) (UNFOLD({asm}); a2))));
    self.prove_vblock_asm(&mut self.proc.assembly_blocks(), a2, th);
    let (a, h1) = self.vblock_asm[&self.proc.vblock_id(BlockId::ENTRY).expect("ghost function")];
    app_match!(self.thm, let (asmEntry start (ASM_A prol code)) = a);
    let bl = self.proc.block(BlockId::ENTRY);
    if let Some(proc_id) = self.proc.id {
      let abi = self.elf_proof.proc_abi(proc_id);
      let mut vctx = root;
      let (args, mut mctx, h2) = self.accum_args(&mut vctx, bl.block().ctx, &abi.args);
      let (vctx1, sz1) = (vctx.e, *vctx.nvars);
      let mctx1 = mctx.1;
      let args2 = app!(self.thm, (mkArgs args mctx1));
      let (clob, h3) = self.accum_clob(&mut mctx, abi.clobbers.iter().map(PReg::index));
      let mctx2 = mctx.1;
      let h4 = self.ok_prologue(&mut mctx, prol);
      let mctx3 = mctx.1;
      let tctx = &mut TCtx { vctx, mctx };
      let l2 = tctx.mk(&mut self.thm);
      let h5 = self.ok_stmts(bl, code, (tctx, l2));
      thm!(self.thm, (okProc[self.gctx, start, args2, self.ret, clob, self.se]) =>
        okProcI(args, clob, code, self.epi, self.gctx, mctx1, mctx2, mctx3,
          prol, self.ret, self.se, start, sz1, vctx1, h1, h2, h3, h4, h5))
    } else {
      let ((mut tctx, l1), h2) = self.build_start(bl, root);
      let h3 = self.ok_stmts(bl, code, (&mut *tctx, l1));
      thm!(self.thm, okStartI(code, self.gctx, self.pctx, l1, h1, h2, h3): okStart[self.gctx])
    }
  }
}

#[derive(Debug, Default)]
enum StmtState<'a> {
  #[default] None,
  Call {
    f: ProcId, abi: &'a ProcAbi, args: &'a [(bool, Operand)],
    reach: bool, rets: &'a [(bool, VarId)], se: bool,
  },
}

enum InstState {
  None,
  StartSkip,
  Skip,
  Call,
  Load(ConstantVal),
  Move,
  Fallthrough(BlockId),
}

#[derive(Debug)]
enum Parent {
  /// `code1 +asm code2, code2`
  Left(ProofId, ProofId),
  /// `code1 +asm code2, l1, |- okCode bctx l1 code1 l2`
  Right(ProofId, ProofId, ProofId),
}

struct BlockProofVisitor<'a, 'b> {
  proc: &'b mut ProcProver<'a>,
  /// The id of the current block
  block_id: BlockId,
  /// The id of the current physical block
  vblock_id: Option<VBlockId>,
  tctx: P<&'b mut TCtx>,
  // /// Stack of `n` corresponding to binary subtrees of `code`
  // /// that have not been broken down and consumed yet.
  // binary: Vec<usize>,
  /// The data for the current statement
  stmt_state: StmtState<'a>,
  /// The path to the current position in the tree
  /// * `Left(code1 +asm code2, code2)` or
  /// * `Right((code1 +asm code2), l1, |- okCode bctx l1 code1 l2)`
  stack: Vec<Parent>,
  /// The current position in the tree
  code: ProofId,
  /// The `tctx` prior to executing `code`
  lhs_tctx: ProofId,
  /// Must be set before calling `do_inst`
  inst_state: InstState,
  /// Set prior to lists for position dependent handling
  arg_count: usize,
  /// Set at the end of the block
  out: ProofId,
}

impl<'a> Deref for BlockProofVisitor<'a, '_> {
  type Target = ProcProver<'a>;
  fn deref(&self) -> &Self::Target { self.proc }
}
impl DerefMut for BlockProofVisitor<'_, '_> {
  fn deref_mut(&mut self) -> &mut Self::Target { self.proc }
}

impl<'a> ProcProver<'a> {
  fn ok_stmts(&mut self, bl: BlockProof<'a>, code: ProofId, tctx: P<&mut TCtx>) -> ProofId {
    // eprintln!("\n{:?}: {:?}", bl.id, bl.vblock().map(|bl| bl.insts));
    if BLOCK_PROOFS {
      // let n = bl.block().stmts.len();
      let mut visitor = BlockProofVisitor {
        proc: self,
        block_id: bl.id,
        vblock_id: bl.vblock_id(),
        lhs_tctx: tctx.1,
        tctx,
        // binary: if n == 0 { vec![] } else { vec![n] },
        stmt_state: StmtState::None,
        stack: vec![],
        code: ProofId::INVALID,
        inst_state: InstState::None,
        arg_count: 0,
        out: ProofId::INVALID,
      };
      visitor.set_code(code);
      // if n != 0 { visitor.split() }
      bl.visit(&mut visitor);
      assert!(visitor.out != ProofId::INVALID, "{:?}", visitor.stack);
      visitor.out
    } else {
      let ret = app!(self.thm, (okCode {self.bctx} {tctx.1} code (ok0)));
      thm!(self.thm, sorry(ret): ret) // TODO
    }
  }
}

impl<'a> BlockProofVisitor<'a, '_> {
  fn pp(&mut self) {
    eprintln!("BlockProofVisitor {{");
    eprintln!("  block: {:?}", self.proc.proc.block(self.block_id).block());
    if let Some(id) = self.vblock_id {
      eprintln!("  vblock:");
      for i in self.proc.proc.vblock(id).insts {
        eprintln!("    {i:?}");
      }
    } else {
      eprintln!("  vblock: None");
    }
    eprintln!("  lhs_tctx: {}", self.proc.pp(self.lhs_tctx));
    eprintln!("  code: {}", self.proc.pp(self.code));
    // eprintln!("  stack:");
    // for p in self.stack.iter().rev() {
    //   match *p {
    //     Parent::Left(code, ..) => eprintln!("    L {}", self.proc.pp(code)),
    //     Parent::Right(code, ..) => eprintln!("    R {}", self.proc.pp(code)),
    //   }
    // }
    eprintln!("}}");
  }
  // /// Assuming a `|- code1 +asm code2` proof obligation, pops this and
  // /// adds two `|- code1`, `|- code2` proof obligations. (See `finish`)
  // fn split(&mut self) {
  //   let (code1, code2) = self.proc.split_asm(self.code);
  //   // eprintln!("split {}, {}", self.pp(code1), self.pp(code2));
  //   self.stack.push(Parent::Left(self.code, code2));
  //   self.code = code1;
  // }

  fn set_code(&mut self, mut code: ProofId) {
    loop {
      app_match!(self.thm, code => {
        (ASM_A a b) => { self.stack.push(Parent::Left(code, b)); code = a },
        (ASM0) => { self.finish_id(); return },
        _ => { self.code = code; return }
      })
    }
  }

  /// Closes a `|- okCode bctx lhs_tctx code tctx` proof obligation.
  /// Advances the state to the next unproven right sibling `code`,
  /// or sets `out` if the tree is complete
  fn finish(&mut self, mut th: ProofId) {
    // eprintln!("finish {}", self.proc.pp(self.code));
    while let Some(parent) = self.stack.pop() {
      match parent {
        Parent::Left(code, code2) => {
          self.stack.push(Parent::Right(code, self.lhs_tctx, th));
          self.lhs_tctx = self.tctx.1;
          self.set_code(code2);
          return
        }
        Parent::Right(code, l1, h1) => {
          th = self.proc.ok_code_join([l1, self.lhs_tctx, self.tctx.1, code, h1, th]);
          self.lhs_tctx = l1;
        }
      }
    }
    self.out = th
  }

  /// Closes a proof where `code = ASM0` using the identity
  fn finish_id(&mut self) {
    let l = self.tctx.1;
    let th = thm!(self.thm, okCode_id(self.bctx, l): okCode[self.bctx, l, self.asm0, l]);
    self.finish(th)
  }

  // fn start_binary(&mut self) {
  //   let mut n = self.binary.pop().expect("underflow");
  //   while n > 1 {
  //     let m = n >> 1;
  //     self.binary.push(n - m);
  //     self.split();
  //     n = m;
  //   }
  // }

  #[allow(clippy::too_many_arguments)]
  fn call(&mut self,
    f: ProcId, abi: &'a ProcAbi, _args: &'a [(bool, Operand)],
    _reach: bool, _rets: &'a [(bool, VarId)], se: bool,
    inst: Option<&Inst<'a>>,
  ) {
    let proc = &mut *self.proc;
    let proc_thm = *proc.proc_proof.get(&Some(f))
      .unwrap_or_else(|| unimplemented!("recursive function"));
    let (x, h1) = proc.thm.thm0(proc.elab, proc_thm);
    app_match!(proc.thm, let (okProc _ tgt args ret clob _) = x);
    let rel = inst.is_some();
    let l1 = self.tctx.1;
    let h2 = proc.apply_call(&self.tctx, abi, args, ret, clob, rel);
    let l2 = self.tctx.1;
    let th = match (rel, se) {
      (true, true) => thm!(self.thm, (okCode[self.bctx, l1, self.code, l2]) =>
        ok_call_proc(args, clob, self.epi, self.gctx, self.labs, ret, self.ret,
          l1, l2, tgt, h1, h2)),
      (true, false) => thm!(self.thm, (okCode[self.bctx, l1, self.code, l2]) =>
        ok_call_func(args, clob, self.gctx, self.labs, self.pctx1, ret,
          l1, l2, tgt, h1, h2)),
      (false, false) => thm!(self.thm, (okCode[self.bctx, l1, self.code, l2]) =>
        ok_call_func_0(args, clob, self.gctx, self.labs, self.pctx1, ret,
          l1, l2, tgt, h1, h2)),
      (false, true) => unreachable!("side effecting function must have control flow"),
    };
    self.finish(th)
  }

  #[allow(clippy::too_many_arguments)]
  fn fallthrough(&mut self, tgt: BlockId) {
    let l1 = self.tctx.1;
    let bctx = self.bctx;
    let (ip, mut th) = self.proc.ok_block_opt((self.tctx.0, l1), tgt);
    // eprintln!("returning to {:?}", self.block_id);
    if ip != ProofId::INVALID {
      th = thm!(self.thm, ok_jump(bctx, l1, ip, th): okCode[bctx, l1, self.code, self.ok0]);
    }
    self.tctx.1 = self.ok0;
    self.finish(th)
  }
}

impl<'a> cl::Visitor<'a> for BlockProofVisitor<'a, '_> {
  fn on_inst(&mut self, _: &TraceIter<'a>, spill: bool, inst: &Inst<'a>) {
    if spill {
      match self.inst_state {
        InstState::None => panic!("unexpected instruction: {:?}", inst.inst),
        InstState::Skip => panic!("unexpected spill instruction"),
        _ => {}
      }
      // self.split();
      let th = self.proc.ok_spill_op(&self.tctx, inst.inst, self.code);
      self.finish(th);
    } else {
      match self.inst_state {
        InstState::None => panic!("unexpected instruction: {:?}", inst.inst),
        InstState::StartSkip => self.inst_state = InstState::Skip,
        InstState::Skip => {}
        InstState::Call => {
          let StmtState::Call { f, abi, args, reach, rets, se } = self.stmt_state else {
            unreachable!()
          };
          self.call(f, abi, args, reach, rets, se, Some(inst));
          self.inst_state = InstState::None
        }
        InstState::Load(_) => todo!("{:?}", inst.inst),
        InstState::Move => todo!("{:?}", inst.inst),
        InstState::Fallthrough(tgt) => {
          self.fallthrough(tgt);
          self.inst_state = InstState::None
        }
      }
    }
  }

  fn before_operand(&mut self, _: &TraceIter<'_>, o: &Operand, cl: cl::Operand) {
    let InstState::None = self.inst_state else { unreachable!() };
    self.inst_state = InstState::Load(match o {
        Operand::Const(constant) => self.constant(constant),
        _ => todo!(),
    })
  }

  fn before_copy(&mut self, _: &TraceIter<'a>, cl: cl::Copy) {
    // if matches!(cl, cl::Copy::Two) { self.split() }
  }
  fn after_copy(&mut self, _: &TraceIter<'a>, _: cl::Copy) {
    self.inst_state = InstState::None
  }

  fn before_prologue(&mut self, _: &TraceIter<'a>,
    _: &'a [PReg], _: u32, _: &'a [ArgAbi], _: Option<&'a [ArgAbi]>,
  ) { self.inst_state = InstState::Skip }

  fn after_prologue(&mut self, _: &TraceIter<'a>,
    _: &'a [PReg], _: u32, _: &'a [ArgAbi], _: Option<&'a [ArgAbi]>,
  ) { self.inst_state = InstState::None }

  fn before_epilogue(&mut self, _: &cl::TraceIter<'_>) { self.inst_state = InstState::StartSkip }

  fn before_stmt(&mut self, _: &TraceIter<'_>, stmt: &Statement, cl: &cl::Statement) {
    // let mut n = self.binary.pop().expect("underflow");
    // while n > 1 {
    //   let m = n >> 1;
    //   self.binary.push(n - m);
    //   self.split();
    //   n = m;
    // }
    self.pp();
    self.stmt_state = match stmt {
      Statement::Let(..) => StmtState::None,
      Statement::Assign(_, _, _, _) => todo!(),
      Statement::LabelGroup(_, _) => todo!(),
      Statement::PopLabelGroup => todo!(),
      Statement::DominatedBlock(_, _) => todo!(),
    }
  }

  fn after_stmt(&mut self, _: &TraceIter<'_>, stmt: &Statement, _: &cl::Statement) {
    let th = match stmt {
      Statement::Let(_, _, _, _) => todo!(),
      Statement::Assign(_, _, _, _) => todo!(),
      Statement::LabelGroup(_, _) => todo!(),
      Statement::PopLabelGroup => todo!(),
      Statement::DominatedBlock(_, _) => todo!(),
    };
    self.finish(th)
  }

  fn before_rvalue(&mut self, _: &TraceIter<'_>, ty: &Ty, rv: &RValue, _: &cl::RValue) {
    // let th = match rv {
    //   RValue::Use(operand) => todo!(),
    //   RValue::Unop(unop, operand) => todo!(),
    //   RValue::Binop(binop, operand, operand1) => todo!(),
    //   RValue::Eq(ty_kind, _, operand, operand1) => todo!(),
    //   RValue::Pun(pun_kind, place) => todo!(),
    //   RValue::Cast(cast_kind, operand, ty_kind) => todo!(),
    //   RValue::List(os) => todo!(),
    //   RValue::Array(os) => todo!(),
    //   RValue::Ghost(operand) => todo!(),
    //   RValue::Borrow(place) => todo!(),
    //   RValue::Mm0(lambda_id, operands) => todo!(),
    //   RValue::Typeof(operand) => todo!(),
    // };
  }

  fn after_rvalue(&mut self, _: &TraceIter<'_>, ty: &Ty, rv: &RValue, _: &cl::RValue) {

  }

  fn before_call_args(&mut self, _: &TraceIter<'a>,
    _: ProcId, _: &ProcAbi, args: &[(bool, Operand)]
  ) {
    self.arg_count = args.len();
    if self.arg_count == 0 { self.finish_id() }
  }

  fn before_call_arg(&mut self, _: &TraceIter<'a>,
    _: bool, _: &'a Operand, _: &'a ArgAbi, _: &'a cl::Elem
  ) {
    self.arg_count -= 1;
    // if self.arg_count != 0 { self.split() }
  }

  fn after_call_arg(&mut self, _: &TraceIter<'a>,
    _: bool, _: &'a Operand, _: &'a ArgAbi, _: &'a cl::Elem
  ) {
    self.finish(todo!());
  }

  fn after_call_args(&mut self, _: &TraceIter<'a>,
    _: ProcId, _: &ProcAbi, _: &[(bool, Operand)]
  ) { self.inst_state = InstState::Call }

  fn before_call_retargs(&mut self, _: &TraceIter<'a>,
    _: ProcId, _: &'a ProcAbi, rets: &'a [(bool, VarId)],
  ) {
    self.arg_count = rets.len();
    // self.split();
    if self.arg_count == 0 { self.finish_id() }
  }

  fn before_call_retarg(&mut self, _: &TraceIter<'a>, _: cl::IntoMem, _: &'a ArgAbi) {
    self.arg_count -= 1;
    // if self.arg_count != 0 { self.split() }
  }

  fn after_call_retarg(&mut self, _: &TraceIter<'a>, _: cl::IntoMem, _: &'a ArgAbi) {
    self.finish(todo!())
  }

  fn after_call_retargs(&mut self, _: &TraceIter<'a>,
    _: ProcId, _: &'a ProcAbi, _: &'a [(bool, VarId)],
  ) {
    // self.split()
  }

  fn before_call_ret(&mut self, _: &TraceIter<'a>, _: &'a ArgAbi, _: &'a cl::Elem) {
    // self.split()
  }

  fn after_call_ret(&mut self, _: &TraceIter<'a>, _: &'a ArgAbi, _: &'a cl::Elem) {
    self.finish(todo!());
  }

  // override the main handling
  fn do_call_rets(&mut self,
    boxes: u8, retabi: &'a [ArgAbi], rets: &'a [(bool, VarId)], tgt: BlockId,
    it: &mut TraceIter<'a>,
  ) {
    // eprintln!("before_call_rets");
    for (arg, &(vr, _)) in retabi.iter().zip(rets) {
      if !vr { continue }
      self.do_call_ret(arg, it.next_list_elem(), it)
    }
    for _ in 0..boxes { self.do_copy(cl::Copy::One, it) }
    self.inst_state = InstState::Fallthrough(tgt);
    self.do_inst(it);
    // eprintln!("after_call_rets");
  }

  fn before_call(&mut self, _: &TraceIter<'a>,
    f: ProcId, abi: &'a ProcAbi, args: &'a [(bool, Operand)],
    reach: bool, rets: &'a [(bool, VarId)], se: bool, _: BlockId,
  ) {
    self.stmt_state = StmtState::Call { f, abi, args, reach, rets, se };
    // self.split();
  }

  fn after_call(&mut self, _: &TraceIter<'a>,
    _: ProcId, _: &ProcAbi, _: &[(bool, Operand)],
    _: bool, _: &[(bool, VarId)], _: bool, _: BlockId,
  ) {
  }

  fn before_terminator(&mut self, _: &TraceIter<'a>,
    _: &IdxVec<ProcId, ProcAbi>, _: Option<&[ArgAbi]>,
    term: &'a Terminator, _: &cl::Terminator
  ) {
    match term {
      Terminator::Jump(_, _, _) => todo!(),
      Terminator::Jump1(_, _) => todo!(),
      Terminator::Return(..) => {}
      Terminator::Unreachable(_) => todo!(),
      Terminator::If(_, _, _) => todo!(),
      Terminator::Assert(_, _, _) => todo!(),
      Terminator::Call { .. } => {}
      Terminator::Fail |
      Terminator::Exit(_) => self.inst_state = InstState::StartSkip,
      Terminator::Dead => unreachable!(),
    }
  }

  fn after_terminator(&mut self, _: &TraceIter<'a>,
    _: &IdxVec<ProcId, ProcAbi>, _: Option<&[ArgAbi]>,
    term: &Terminator, cl: &cl::Terminator
  ) {
    // let (l1, code) = self.stmt_in.take().expect("nesting fail");
    match term {
      Terminator::Jump(_, _, _) => todo!(),
      Terminator::Jump1(_, _) => todo!(),
      Terminator::Return(outs, args) => {
        assert!(!matches!(cl, cl::Terminator::Ghost), "ghost return not allowed, I think");
        self.inst_state = InstState::None;
        let proc = &mut *self.proc;
        let h1 = proc.get_epi(self.code);
        let h2 = proc.check_ret(&mut self.tctx, outs, args);
        let th = thm!(proc.thm, (okCode[proc.bctx, self.lhs_tctx, self.code, proc.ok0]) =>
          okEpilogue_E(proc.bctx, self.code, proc.ret, self.lhs_tctx, h1, h2));
        self.finish(th)
      }
      Terminator::Unreachable(_) => todo!(),
      Terminator::If(_, _, _) => todo!(),
      Terminator::Assert(_, _, _) => todo!(),
      Terminator::Fail => {
        let l1 = self.tctx.1;
        let th = thm!(self.thm, (okCode[self.bctx, l1, self.code, self.ok0]) =>
          ok_fail(self.bctx, l1));
        self.finish(th)
      }
      Terminator::Call { .. } => {}
      Terminator::Exit(op) => {
        let proc = &mut *self.proc;
        let (ty, h1) = proc.get_result();
        let l1 = self.tctx.1;
        let (ty2, h2) = proc.read_hyp_operand((self.tctx.0, l1), op);
        let h2 = proc.read_hyp_coerce(ty2, h2, ty);
        // let th = thm!(proc.thm, (okCode[proc.bctx, l1, self.code, proc.ok0]) =>
        //   ok_exit(ty, proc.gctx, proc.labs, proc.pctx1, l1, h1, h2));
        let th = todo!("exit");
        self.finish(th)
      }
      Terminator::Dead => unreachable!(),
    }
  }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn compile_proof(
  elab: &mut Elaborator,
  pd: &Predefs,
  proc_asm: &HashMap<Option<ProcId>, (TermId, ThmId)>,
  mangler: &Mangler,
  proof: &ElfProof<'_>,
  span: &FileSpan,
  full: Span,
  gctx: TermId,
) -> Result<ThmId> {
  let mut proc_proof = HashMap::new();
  for proc in proof.proc_proofs() {
    let mut thm = ProofDedup::new(pd, &[]);
    let hex = HexCache::new(&mut thm);
    let root = VCtx::root(&mut thm, &hex);
    let mut build = ProcProver {
      elf_proof: proof,
      proc: &proc,
      proc_asm,
      proc_proof: &mut proc_proof,
      vblock_asm: Default::default(),
      block_proof: Default::default(),
      elab,
      ctx: Ctx::new(&mut thm, &hex, &proc, gctx),
      vctxs: vec![root()].into(),
      hex,
      thm,
    };
    let th = build.prove_proc(root());
    let (ok_thm, doc) = mangler.get_data(build.elab,
      proc.name().map_or(Name::StartOkThm, Name::ProcOkThm));
    let (ok_thm, _) = build.elab.env
      .add_thm(build.thm.build_thm0(ok_thm, Modifiers::empty(), span.clone(), full, Some(doc), th))
      .map_err(|e| e.into_elab_error(full))?;
    proc_proof.insert(proc.id, ok_thm);
  }
  Ok(*proc_proof.get(&None).expect("missing start procedure"))
}
