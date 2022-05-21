#![allow(clippy::cast_possible_truncation)]

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::marker::PhantomData;

use mmcc::Idx;
use mmcc::types::IdxVec;
use mmcc::types::mir::{Cfg, Contexts, CtxBufId, CtxId, ExprKind, Statement, Terminator, VarId,
  Operand, Place, ConstKind};
use mmcc::types::vcode::{ProcAbi, ArgAbi};
use mmcc::{Symbol, TEXT_START, types::Size};
use mmcc::arch::{ExtMode, OpcodeLayout, PInst, PRegMemImm, Unop};
use mmcc::proof::{AssemblyBlocks, AssemblyItem, AssemblyItemIter, BlockId, BlockProof,
  BlockProofTree, BlockTreeIter, ElfProof, Inst, InstIter, PReg, Proc, VBlockId, ProcId};
use crate::LispVal;
use crate::lisp::print::Print;
use crate::{Elaborator, FileSpan, Modifiers, Span, TermId, ThmId, elab::Result, mmc::proof::Name};

use super::{Dedup, ExprDedup, Mangler, Predefs, ProofDedup, ProofId,
  norm_num::{HexCache, Num}, predefs::Rex};

pub(super) fn mk_result<'a, D: Dedup<'a>>(de: &mut D, proof: &ElfProof<'_>) -> D::Id {
  app!(de, (tyUnit)) // TODO
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
}

impl Ctx {
  fn new(de: &mut ProofDedup<'_>, hex: &HexCache, proc: &Proc<'_>, t_gctx: TermId) -> Ctx {
    let ok0 = app!(de, (ok0));
    let gctx = app!(de, ({t_gctx}));
    let ret = app!(de, (ok0)); // TODO
    let se = app!(de, (tru)); // TODO
    let mut epi = app!(de, (epiRet));
    #[allow(clippy::cast_possible_truncation)]
    for &reg in proc.saved_regs() {
      epi = app!(de, epiPop[hex[reg.index()], epi]);
    }
    let sp_max = hex.from_u32(de, proc.stack_size());
    if sp_max.val != 0 { epi = app!(de, epiFree[*sp_max, epi]) }
    let pctx1 = app!(de, mkPCtx1[ret, epi, se]);
    let pctx = app!(de, mkPCtx[gctx, pctx1]);
    let labs = app!(de, (labelGroup0));
    let bctx = app!(de, mkBCtx[pctx, labs]);
    Ctx { t_gctx, gctx, ret, se, epi, sp_max, pctx1, pctx, labs, bctx, ok0 }
  }
}

mmcc::mk_id! { VCtxId, }

impl VCtxId {
  const ROOT: Self = Self(0);
}

#[derive(Clone, Copy)]
enum VarKind { Var, Hyp, Typed }

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
  /// Build the root context. Note that variables can be added to the root context with `add`
  fn root(de: &mut ProofDedup<'_>, hex: &HexCache) -> impl Fn() -> Self + Copy {
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
  fn share(&mut self, vctxs: &mut IdxVec<VCtxId, VCtx>) -> impl Fn() -> Self + Copy {
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
        let (a, b) = app_match!(de, l => { (vctxA a b) => (a, b), ! });
        let c = r;
        l = a; r = app!(de, (vctxA b c)); new = app!(de, (vctxA l r));
        th = thm!(de, okVCtxPush_R(a, b, c, v, old): (okVCtxPush old v new));
      }
      self.e = new;
    };
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
      app_match!(de, r => {
        (vctxA b c) => {
          let l2 = app!(de, (vctxA l b));
          let th = build_cut(de, [base, src, tgt, cut >> 1], [l2, c, v, th]);
          thm!(de, okVCtxGet_R(l, b, c, v, th): (okVCtxGet (vctxA l r) v))
        },
        !
      })
    }

    fn build(de: &mut ProofDedup<'_>,
      base: u32, src: u32, tgt: u32, e: ProofId, v: ProofId, th: ProofId,
    ) -> ProofId {
      debug_assert!(src <= tgt);
      if src == tgt { return th }
      let mut cut = 1 << tgt.trailing_zeros();
      if base == 0 && cut == tgt { cut >>= 1 }
      app_match!(de, e => {
        (vctxA a b) => build_cut(de, [base, src, tgt, cut], [a, b, v, th]),
        !
      })
    }

    let mut cache = self.access_cache.borrow_mut();
    let (i, ref mut cache) = *cache.entry(v).or_insert_with(|| {
      assert!(self.parent != VCtxId::ROOT, "variable not found");
      let (i, _, th) = vctxs[self.parent].get(de, vctxs, v);
      (i, vec![(0, th)])
    });
    let mut last = cache.last_mut().expect("impossible");
    let len = self.len();
    let v = app_match!(de, de.concl(last.1) => { (okVCtxGet _ v) => v, ! });
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
        let e2 = app_match!(de, e => { (vctxA a _) => a, ! });
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

trait NodeKind: Sized {
  type Context;
  type Key: Ord;
  type Node;
  type Leaf;
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
    ctx: Self::Context, a: &P<MCtxNode<Self>>, b: &P<MCtxNode<Self>>
  ) -> Self::Context { ctx }
  fn ctx_right(
    ctx: Self::Context, a: &P<MCtxNode<Self>>, b: &P<MCtxNode<Self>>
  ) -> Self::Context { ctx }

  /// Constructs a node `(a, b)`
  fn mk(de: &mut ProofDedup<'_>, a: ProofId, b: ProofId) -> ProofId { app!(de, (mctxA a b)) }
}

#[allow(clippy::type_complexity)]
enum MCtxNode<N: NodeKind> {
  Zero,
  One(N::Leaf),
  Node(Ordering, N::Node, Box<(P<MCtxNode<N>>, P<MCtxNode<N>>)>),
}

impl<N: NodeKind> Default for MCtxNode<N> {
  fn default() -> Self { Self::Zero }
}

struct RegKind<L>(PhantomData<L>);
impl<L> NodeKind for RegKind<L> {
  type Context = ();
  type Key = u8;
  type Node = u8;
  type Leaf = (u8, L);
  fn node(de: &mut ProofDedup<'_>, a: &P<MCtxNode<Self>>, b: &P<MCtxNode<Self>>) -> Self::Node {
    match a.0 {
      MCtxNode::Zero => unreachable!(),
      MCtxNode::One((k, _)) | MCtxNode::Node(_, k, _) => k
    }
  }
  fn leaf_key(_: &(), k: &(u8, L)) -> u8 { k.0 }
  fn node_key(_: &(), k: &u8) -> u8 { *k }
}

struct StackKind<L>(PhantomData<L>);
impl<L> StackKind<L> {
  fn get_key(node: &MCtxNode<Self>) -> u32 {
    match *node {
      MCtxNode::Zero => unreachable!(),
      MCtxNode::One((k, _)) | MCtxNode::Node(_, k, _) => k
    }
  }
}
impl<L> NodeKind for StackKind<L> {
  type Context = u32;
  type Key = u32;
  type Node = u32;
  type Leaf = (u32, L);
  fn node(de: &mut ProofDedup<'_>, a: &P<MCtxNode<Self>>, b: &P<MCtxNode<Self>>) -> Self::Node {
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
  fn rotate_left(de: &mut ProofDedup<'_>, x_t_a_b_c_th: [ProofId; 6]) -> ProofId { panic!() }
  /// Given `|- insert x t = ((a, b), c)` proves `|- insert x t = (a, (b, c))`
  fn rotate_right(de: &mut ProofDedup<'_>, x_t_a_b_c_th: [ProofId; 6]) -> ProofId { panic!() }

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
        if *key < N::key(&ctx, &ns.1 .0) {
          let ctx = N::ctx_left(ctx, &ns.0, &ns.1);
          let (grew, th) = Self::insert(de, &mut ns.0, ctx, key, t);
          let rotate_right = grew && match bal {
            Ordering::Less => { *bal = Ordering::Equal; false }
            Ordering::Equal => { *bal = Ordering::Greater; false }
            Ordering::Greater => true
          };
          if rotate_right {
            let_unchecked!((bal1, ns1) as MCtxNode::Node(bal1, _, ns1) =
              std::mem::take(&mut ns.0 .0));
            let nb = std::mem::take(&mut ns.1 .0);
            let (al, ar) = *ns1;
            match bal1 {
              Ordering::Less => {
                let th = Self::single_right(de, [a, et, al.1, ar.1, b, th]);
                let n = N::p_node(de, Ordering::Equal, ar, (nb, b));
                *node = N::p_node(de, Ordering::Equal, al, n);
                (false, th)
              }
              Ordering::Equal => {
                let th = Self::single_right(de, [a, et, al.1, ar.1, b, th]);
                let n = N::p_node(de, Ordering::Less, ar, (nb, b));
                *node = N::p_node(de, Ordering::Greater, al, n);
                (true, th)
              }
              Ordering::Greater => {
                let_unchecked!((bal2, ns2) as MCtxNode::Node(bal2, _, ns2) = ar.0);
                let (arl, arr) = *ns2;
                let (bal_new, bal2_new) = match bal2 {
                  Ordering::Less => (Ordering::Equal, Ordering::Greater),
                  Ordering::Equal => (Ordering::Equal, Ordering::Equal),
                  Ordering::Greater => (Ordering::Less, Ordering::Equal),
                };
                let th = Self::double_right(de, [a, et, al.1, arl.1, arr.1, b, th]);
                let n1 = N::p_node(de, bal_new, al, arl);
                let n2 = N::p_node(de, bal2_new, arr, (nb, b));
                *node = N::p_node(de, Ordering::Equal, n1, n2);
                (false, th)
              }
            }
          } else {
            let th = Self::node_lt(de, [a, b, et, ns.0 .1, th]);
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
            let_unchecked!((bal1, ns1) as MCtxNode::Node(bal1, _, ns1) =
              std::mem::take(&mut ns.1 .0));
            let na = std::mem::take(&mut ns.0 .0);
            let (bl, br) = *ns1;
            match bal1 {
              Ordering::Greater => {
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
              Ordering::Less => {
                let_unchecked!((bal2, ns2) as MCtxNode::Node(bal2, _, ns2) = bl.0);
                let (bll, blr) = *ns2;
                let (bal_new, bal2_new) = match bal2 {
                  Ordering::Less => (Ordering::Equal, Ordering::Greater),
                  Ordering::Equal => (Ordering::Equal, Ordering::Equal),
                  Ordering::Greater => (Ordering::Less, Ordering::Equal),
                };
                let th = Self::double_left(de, [b, et, a, bll.1, blr.1, br.1, th]);
                let n1 = N::p_node(de, bal_new, (na, a), bll);
                let n2 = N::p_node(de, bal2_new, blr, br);
                *node = N::p_node(de, Ordering::Equal, n1, n2);
                (false, th)
              }
            }
          } else {
            let th = Self::node_lt(de, [a, b, et, ns.0 .1, th]);
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
    thm!(de, pushMCtx0(t): (pushMCtx (mctx0) t t))
  }

  fn one_lt(de: &mut ProofDedup<'_>, a: ProofId, t: ProofId) -> ProofId {
    thm!(de, pushMCtx1L(a, t): (pushMCtx a t (mctxA t a)))
  }

  fn one_eq(de: &mut ProofDedup<'_>, a: ProofId, t: ProofId) -> ProofId { unreachable!() }

  fn one_gt(de: &mut ProofDedup<'_>, a: ProofId, t: ProofId) -> ProofId {
    thm!(de, pushMCtx1R(a, t): (pushMCtx a t (mctxA a t)))
  }

  fn node_lt(de: &mut ProofDedup<'_>, [a, b, t, a2, th]: [ProofId; 5]) -> ProofId {
    thm!(de, pushMCtxL(a, a2, b, t, th): (pushMCtx (mctxA a b) t (mctxA a2 b)))
  }

  fn node_gt(de: &mut ProofDedup<'_>, [a, b, t, b2, th]: [ProofId; 5]) -> ProofId {
    thm!(de, pushMCtxR(a, b, b2, t, th): (pushMCtx (mctxA a b) t (mctxA a b2)))
  }

  fn rotate_left(de: &mut ProofDedup<'_>, [x, t, a, b, c, th]: [ProofId; 6]) -> ProofId {
    thm!(de, pushMCtxRotL(a, b, c, x, t, th): (pushMCtx x t (mctxA (mctxA a b) c)))
  }

  fn rotate_right(de: &mut ProofDedup<'_>, [x, t, a, b, c, th]: [ProofId; 6]) -> ProofId {
    thm!(de, pushMCtxRotR(a, b, c, x, t, th): (pushMCtx x t (mctxA a (mctxA b c))))
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

enum Expr {
  Var(VarId),
}

enum MCtxRegValue {
  Free,
  Expr(P<Expr>),
}

enum MCtxStkValue {
  Free
}

type MCtxRegKind = RegKind<MCtxRegValue>;
type MCtxStkKind = StackKind<MCtxStkValue>;
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
          (REG r v) => ((k, r), (k, r), thm!(de, bddMCtx_REG(r): bddMCtx[this.1, r, r])),
          !
        })
      }
      MCtxNode::Node(_, _, ref ns) => {
        let (n1, n2) = &**ns;
        let (a, b, h1) = Self::bdd(n1, de);
        let (c, d, h2) = Self::bdd(n2, de);
        let h3 = thm!(de, decltn[b.0][c.0](): {b.1} < {c.1});
        (a, d, thm!(de, (bddMCtx[this.1, a.1, d.1]) =>
          bddMCtx_A(n1.1, n2.1, a.1, b.1, c.1, d.1, h1, h2, h3)))
      }
    }
  }

  /// Returns `|- okMCtx mctx`
  fn ok(this: &P<Self>, de: &mut ProofDedup<'_>) -> ProofId {
    if let MCtxNode::Zero = this.0 {
      thm!(de, okMCtx0(): (okMCtx (mctx0)))
    } else {
      let (a, b, th) = Self::bdd(this, de);
      thm!(de, okMCtxS(a.1, b.1, this.1, th): okMCtx[this.1])
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
    match this.0.stack {
      Some((_, stk)) => I::node_lt(de, [a, stk, t, this.1, th]),
      None => th
    }
  }

  fn add_stack(this: &mut P<Self>, de: &mut ProofDedup<'_>, n: Num) {
    let e = app!(de, (stkFREE {*n}));
    assert!(this.0.stack.replace((MCtxNode::One((n.val as u32, MCtxStkValue::Free)), e)).is_none());
    this.1 = app!(de, mctxA[this.1, e]);
  }

  fn mk(&self, de: &mut ProofDedup<'_>) -> ProofId {
    match self.stack {
      Some((_, stk)) => app!(de, (mctxA {self.regs.1} stk)),
      None => self.regs.1,
    }
  }

  /// Returns `|- okMCtx mctx`
  fn ok(&self, de: &mut ProofDedup<'_>) -> ProofId {
    assert!(self.stack.is_none());
    MCtxNode::ok(&self.regs, de)
  }
}

enum DeferredKind<'a> {
  Exit(&'a Operand)
}

enum StatementIterKind<'a> {
  Start,
  PostCall(BlockId, &'a [(bool, VarId)]),
  Jump1(BlockId),
  Defer(u8, ProofId, DeferredKind<'a>),
}

struct StatementIter<'a> {
  stmts: std::slice::Iter<'a, Statement>,
  term: Option<&'a Terminator>,
  kind: StatementIterKind<'a>,
}

struct TCtx<'a> {
  viter: StatementIter<'a>,
  piter: Option<std::iter::Peekable<InstIter<'a>>>,
  vctx: VCtx,
  mctx: P<MCtx>,
}

type PTCtx<'a> = P<Box<TCtx<'a>>>;

impl<'a> TCtx<'a> {
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
    (n, (tctx2, thm!(de, ((okPushVar tctx {*n2} tctx2)) =>
      okPushVarI(self.mctx.1, self.mctx.1, *n, *n2, ty, old, self.vctx.e))))
  }

  /// Given `ty`, returns `(tctx2, |- okPushVar tctx ty tctx2)`,
  /// where `tctx2` is the result of adding `vHyp ty` to `tctx`
  fn push_hyp(
    &mut self, tctx: ProofId, de: &mut ProofDedup<'_>, hex: &HexCache, var: VarId, kind: VarKind,
    ty: ProofId,
  ) -> (ProofId, ProofId) {
    let e = app!(de, (vHyp ty));
    let old = self.vctx.e;
    let h1 = self.vctx.push(de, var, kind, e);
    let tctx2 = self.mk(de);
    (tctx2, thm!(de, ((okPushVar tctx {*self.vctx.nvars} tctx2)) =>
      okPushVarI(self.mctx.1, *self.vctx.nvars, ty, old, self.vctx.e)))
  }

  fn mk(&self, de: &mut ProofDedup<'_>) -> ProofId {
    app!(de, mkTCtx[self.vctx.e, *self.vctx.nvars, self.mctx.1])
  }

  /// Resets the iterators to point at a new block, without changing the variable context.
  fn retarget(&mut self, bl: BlockProof<'a>) {
    self.viter = StatementIter {
      stmts: bl.block().stmts.iter(),
      term: Some(bl.block().terminator()),
      kind: StatementIterKind::Start,
    };
    self.piter = bl.vblock().map(|vbl| vbl.insts().peekable());
  }
}

struct Prologue<'a> {
  epi: ProofId,
  sp: Num,
  mctx: P<MCtx>,
  iter: std::slice::Iter<'a, PReg>,
  prol: ProofId,
  viter: StatementIter<'a>,
  piter: InstIter<'a>,
  vctx: VCtx,
}

enum LCtx<'a> {
  Dead,
  Prologue(Box<Prologue<'a>>),
  Reg(Box<TCtx<'a>>),
  Epilogue(ProofId),
}

impl Default for LCtx<'_> {
  fn default() -> Self { Self::Dead }
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
  fn as_expr(self, thm: &mut ProofDedup<'_>) -> P<Self> {
    let e = match self {
      Loc::Reg(n) => app!(thm, Loc_reg[n.1]),
      Loc::Local(n) => app!(thm, Loc_local[n]),
    };
    (self, e)
  }
}

#[derive(Clone, Copy)]
enum Value {
  Reg,
  SpillSlot(ProofId),
}

impl<'a> std::ops::Deref for ProcProver<'a> {
  type Target = Ctx;
  fn deref(&self) -> &Self::Target { &self.ctx }
}

impl<'a> ProcProver<'a> {
  fn pp(&mut self, i: ProofId) -> String {
    let mut s = String::new();
    self.thm.pp(self.elab, i, &mut s).expect("impossible");
    s
  }

  fn push_label_group(&mut self, var: ProofId, ls: ProofId) -> [ProofId; 2] {
    let old = [self.labs, self.bctx];
    self.ctx.labs = app!(self.thm, labelGroup[var, ls, self.labs]);
    self.ctx.bctx = app!(self.thm, mkBCtx[self.pctx, self.labs]);
    old
  }

  fn pop_label_group(&mut self, [labs, bctx]: [ProofId; 2]) {
    self.ctx.labs = labs;
    self.ctx.bctx = bctx;
  }

  fn prove_vblock_asm(&mut self, iter: &mut AssemblyBlocks<'_>, a: ProofId, th: ProofId) {
    app_match!(self.thm, a => {
      (localAssembleA a b) => {
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
  fn block_tctx(&mut self, bl: BlockProof<'a>, vctx: VCtx, base: CtxId) -> PTCtx<'a> {
    let mut tctx = Box::new(TCtx {
      viter: StatementIter {
        stmts: bl.block().stmts.iter(),
        term: Some(bl.block().terminator()),
        kind: StatementIterKind::Start,
      },
      piter: bl.vblock().map(|vbl| vbl.insts().peekable()),
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
          tctx.push_hyp(l, &mut self.thm, &self.hex, v.k, VarKind::Typed, ty)
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

  /// Returns `|- okReadHyp tctx ty2` if `th: |- okReadHyp tctx ty`
  fn read_hyp_coerce(&mut self, ty: ProofId, th: ProofId, ty2: ProofId) -> ProofId {
    // TODO
    assert!(ty == ty2, "failed to coerce {} to {}", self.pp(ty), self.pp(ty2));
    th
  }

  /// Returns `(ty, |- okReadHyp vctx ty)`
  fn read_hyp_var(&mut self, vctx: &VCtx, v: VarId) -> (ProofId, ProofId) {
    let (_, val, h1) = vctx.get(&mut self.thm, &self.vctxs, v);
    app_match!(self.thm, val => {
      (vHyp ty) => (ty, thm!(self.thm, okReadHypI(ty, vctx.e, h1): okReadHyp[vctx.e, ty])),
      (vVar v ty) => (ty, thm!(self.thm, okReadHypVar(ty, v, vctx.e, h1): okReadHyp[vctx.e, ty])),
      !
    })
  }

  /// Returns `(ty, |- okReadHyp vctx ty)`
  fn read_hyp_place(&mut self, vctx: &VCtx, p: &Place) -> (ProofId, ProofId) {
    assert!(p.proj.is_empty()); // TODO
    self.read_hyp_var(vctx, p.local)
  }

  /// Returns `|- okReadHyp tctx ty`
  fn read_hyp_wrapper(&mut self, (tctx, l1): P<&TCtx<'a>>, ty: ProofId, th: ProofId) -> ProofId {
    app_match!(self.thm, l1 => {
      (mkTCtx vctx n mctx) => thm!(self.thm,
        okReadHypTCtx(mctx, n, ty, vctx, th): okReadHyp[l1, ty]),
      !
    })
  }

  /// Returns `(ty, |- okReadHyp tctx ty)`
  fn read_hyp_operand(&mut self, (tctx, l1): P<&TCtx<'a>>, op: &Operand) -> (ProofId, ProofId) {
    match op.place() {
      Ok(p) => {
        let (ty, th) = self.read_hyp_place(&tctx.vctx, p);
        (ty, self.read_hyp_wrapper((tctx, l1), ty, th))
      }
      Err(c) => match c.k {
        ConstKind::Unit => {
          let ty = app!(self.thm, (tyUnit));
          (ty, thm!(self.thm, okReadHyp_unit(l1): okReadHyp[l1, ty]))
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
        accumClobS(clob, mctx1, mctx2, mctx.1, h1, h2)))
    } else {
      let clob = app!(self.thm, (clob0));
      (clob, thm!(self.thm, accumClob0(mctx.1): accumClob[clob, mctx.1, mctx.1]))
    }
  }

  /// Returns `(tctx, |- buildStart pctx tctx)`
  fn build_start(&mut self, root: VCtx) -> (PTCtx<'a>, ProofId) {
    let tctx = self.block_tctx(self.proc.block(BlockId::ENTRY), root, CtxId::ROOT);
    let bproc = app!(self.thm, buildStart[self.pctx, tctx.1]);
    (tctx, thm!(self.thm, sorry(bproc): bproc)) // TODO
  }

  /// Returns `(v, |- okRead tctx loc v)`
  fn read(&mut self, tctx: P<&TCtx<'a>>, loc: &P<Loc>) -> (P<Value>, ProofId) {
    let v = app!(self.thm, (d0)); // TODO
    let ret = app!(self.thm, okRead[tctx.1, loc.1, v]);
    ((Value::Reg, v), thm!(self.thm, sorry(ret): ret)) // TODO
  }

  /// Returns `(tctx', |- okWrite tctx loc v tctx')`
  fn write(&mut self,
    (tctx, l1): P<&mut TCtx<'a>>, loc: &P<Loc>, v: &P<Value>
  ) -> (ProofId, ProofId) {
    let v = app!(self.thm, (d0)); // TODO
    let l2 = l1;
    let ret = app!(self.thm, okWrite[l1, loc.1, v, l2]);
    (l2, thm!(self.thm, sorry(ret): ret)) // TODO
  }

  /// Returns `(tctx', |- okCode bctx tctx code tctx')` for a regalloc operation.
  fn ok_spill_op(&mut self,
    (tctx, l1): P<&mut TCtx<'a>>, inst: &PInst, code: ProofId
  ) -> (ProofId, ProofId) {
    let (dst, src) = app_match!(self.thm, code => { (instMov _ dst src) => (dst, src), ! });
    let reg_or_mem = |arg| app_match!(self.thm, arg => {
      (IRM_reg reg) => Ok(reg),
      (IRM_mem _ _ (posZ off)) => Err(off),
      !
    });
    match (reg_or_mem(dst), reg_or_mem(src), inst) {
      (Ok(edst), Ok(esrc), &PInst::MovRR { dst, src, .. }) => {
        let lsrc = Loc::Reg((src.index(), esrc)).as_expr(&mut self.thm);
        let ldst = Loc::Reg((dst.index(), edst)).as_expr(&mut self.thm);
        let (v, h1) = match self.read((tctx, l1), &lsrc) {
          ((Value::Reg, v), h1) => (v, h1),
          _ => unreachable!(),
        };
        let (l2, h2) = self.write((tctx, l1), &ldst, &(Value::Reg, v));
        (l2, thm!(self.thm, (okCode[self.bctx, l1, code, l2]) =>
          ok_movRR(self.bctx, edst, esrc, l1, l2, v, h1, h2)))
      }
      (Ok(edst), Err(esrc), &PInst::Load64 { dst, .. }) => {
        let lsrc = Loc::Local(esrc).as_expr(&mut self.thm);
        let ldst = Loc::Reg((dst.index(), edst)).as_expr(&mut self.thm);
        let (v, h1) = match self.read((tctx, l1), &lsrc) {
          ((Value::SpillSlot(v), _), h1) => (v, h1),
          _ => unreachable!(),
        };
        let (l2, h2) = self.write((tctx, l1), &ldst, &(Value::Reg, v));
        (l2, thm!(self.thm, (okCode[self.bctx, l1, code, l2]) =>
          ok_unspill(self.bctx, edst, esrc, l1, l2, v, h1, h2)))
      }
      (Err(edst), Ok(esrc), &PInst::Store { src, .. }) => {
        let lsrc = Loc::Reg((src.index(), esrc)).as_expr(&mut self.thm);
        let ldst = Loc::Local(edst).as_expr(&mut self.thm);
        let (v, h1) = match self.read((tctx, l1), &lsrc) {
          ((Value::Reg, v), h1) => (v, h1),
          _ => unreachable!(),
        };
        let ss = app!(self.thm, (spillslot v));
        let (l2, h2) = self.write((tctx, l1), &ldst, &(Value::SpillSlot(v), ss));
        (l2, thm!(self.thm, (okCode[self.bctx, l1, code, l2]) =>
          ok_spill(self.bctx, edst, esrc, l1, l2, v, h1, h2)))
      }
      _ => unreachable!()
    }
  }

  /// Returns `|- getEpi bctx ret epi`
  fn get_epi(&mut self) -> ProofId {
    thm!(self.thm, (getEpi[self.bctx, self.ret, self.epi]) =>
      getEpiI(self.epi, self.gctx, self.labs, self.ret, self.se))
  }

  /// Returns `|- checkRet bctx tctx ret`
  fn check_ret(&mut self,
    tctx: PTCtx<'a>, out: &[VarId], args: &[(VarId, bool, Operand)]
  ) -> ProofId {
    drop(tctx.0);
    thm!(self.thm, (checkRet[self.bctx, tctx.1, self.ret]) =>
      checkRetI(self.bctx, self.ret, tctx.1))
  }

  /// Returns `(tctx2, |- applyCall tctx1 args ret clob tctx2)`,
  /// or `(tctx2, |- applyCallG tctx1 args ret tctx2)` if `rel` is false
  #[allow(clippy::too_many_arguments)]
  fn apply_call(&mut self,
    (tctx, l1): P<&mut TCtx<'a>>,
    abi: &'a ProcAbi,
    args: ProofId,
    ret: ProofId,
    clob: ProofId,
    rel: bool,
  ) -> (ProofId, ProofId) {
    let l2 = l1;
    if rel {
      let ret = app!(self.thm, applyCall[l1, args, ret, clob, l2]);
      (l2, thm!(self.thm, sorry(ret): ret)) // TODO
    } else {
      let ret = app!(self.thm, applyCallG[l1, args, ret, l2]);
      (l2, thm!(self.thm, sorry(ret): ret)) // TODO
    }
  }

  /// Returns `(lctx', |- okCode bctx tctx code lctx')`
  /// or `(lctx', |- okWeak bctx lctx lctx')` in the regular case, assuming
  /// regalloc moves have already been handled and `code` is atomic.
  fn ok_code_reg(&mut self, (lctx, l1): P<&mut LCtx<'a>>, code: Option<ProofId>) -> (ProofId, ProofId) {
    let tctx = if let LCtx::Reg(tctx) = lctx { &mut **tctx } else { unreachable!() };
    // println!("ok_code_reg");
    // dbg!(self.pp(l1), code.map(|code| self.pp(code)));
    loop {
      return match tctx.viter.kind {
        StatementIterKind::Start => if let Some(stmt) = tctx.viter.stmts.next() {
          // dbg!(stmt);
          // if let Some(iter) = &mut tctx.piter {
          //   if let Some(inst) = iter.peek() {
          //     dbg!(inst.inst);
          //   }
          // }
          match stmt {
            Statement::Let(lk, r, ty, rv) => todo!(),
            Statement::Assign(_, _, _, _) => todo!(),
            Statement::LabelGroup(..) => todo!(),
            Statement::PopLabelGroup => todo!(),
            Statement::DominatedBlock(_, _) => todo!(),
          }
        } else if let Some(x) = tctx.viter.term.take() {
          match x {
            Terminator::Jump(_, _, _) => todo!(),
            &Terminator::Jump1(_, tgt) => {
              tctx.viter.kind = StatementIterKind::Jump1(tgt);
              continue
            }
            Terminator::Return(out, args) => {
              let h1 = self.get_epi();
              let_unchecked!(tctx as LCtx::Reg(tctx) =
                std::mem::replace(lctx, LCtx::Epilogue(self.epi)));
              let h2 = self.check_ret((tctx, l1), out, args);
              let l2 = app!(self.thm, okEpilogue[self.epi]);
              let (l3, h3) = self.ok_code1((lctx, l2), code);
              let code = code.expect("ghost return not allowed, I think");
              (l3, thm!(self.thm, (okCode[self.bctx, l1, code, l3]) =>
                okEpilogue_code(self.bctx, code, self.epi, self.ret, l1, l3, h1, h2, h3)))
            }
            Terminator::Unreachable(_) => todo!(),
            Terminator::If(_, _, _) => todo!(),
            Terminator::Assert(_, _, _, _) => todo!(),
            &Terminator::Call { ctx: _, f, se, ref tys, ref args, reach, tgt: block, ref rets } => {
              let f = self.elf_proof.get_func(f).expect("missing function");
              let abi = self.elf_proof.proc_abi(f);
              let proc_thm = *self.proc_proof.get(&Some(f))
                .unwrap_or_else(|| unimplemented!("recursive function"));
              let (x, h1) = self.thm.thm0(self.elab, proc_thm);
              let (tgt, args, ret, clob) = app_match!(self.thm, x => {
                (okProc _ tgt args ret clob _) => (tgt, args, ret, clob),
                !
              });
              let (l2, h2) = self.apply_call((tctx, l1), abi, args, ret, clob, code.is_some());
              if reach {
                tctx.viter.kind = StatementIterKind::PostCall(block, rets);
              } else {
                *lctx = LCtx::Dead
              }
              match (code, se) {
                (Some(code), true) => (l2, thm!(self.thm, (okCode[self.bctx, l1, code, l2]) =>
                  ok_call_proc(args, clob, self.epi, self.gctx, self.labs, ret, self.ret,
                    l1, l2, tgt, h1, h2))),
                (Some(code), false) => (l2, thm!(self.thm, (okCode[self.bctx, l1, code, l2]) =>
                  ok_call_func(args, clob, self.gctx, self.labs, self.pctx1, ret,
                    l1, l2, tgt, h1, h2))),
                (None, false) => (l2, thm!(self.thm, (okWeak[self.bctx, l1, l2]) =>
                  okWeak_call_func(args, clob, self.gctx, self.labs, self.pctx1, ret,
                    l1, l2, tgt, h1, h2))),
                (None, true) => unreachable!("side effecting function must have control flow"),
              }
            }
            Terminator::Exit(op) => {
              tctx.viter.kind = StatementIterKind::Defer(2, l1, DeferredKind::Exit(op));
              continue
            }
            Terminator::Dead => unreachable!(),
          }
        } else {
          todo!()
        }
        StatementIterKind::PostCall(tgt, rets) => {
          assert!(rets.is_empty()); // TODO
          tctx.viter.kind = StatementIterKind::Jump1(tgt);
          continue
        }
        StatementIterKind::Jump1(tgt) => {
          tctx.retarget(self.proc.block(tgt));
          let lctx = std::mem::take(lctx);
          if let Some(vid) = self.proc.vblock_id(tgt) {
            let code = code.expect("jumping to a real block requires code");
            let (a, h1) = self.vblock_asm[&vid];
            let (ip, code1) = app_match!(self.thm, a => { (asmAt ip code) => (ip, code), ! });
            let h2 = self.ok_code0((lctx, l1), Some(code1));
            let th = thm!(self.thm, (okBlock[self.bctx, ip, l1]) =>
              okBlockI(self.labs, code1, ip, l1, self.pctx, h1, h2));
            (self.ok0, thm!(self.thm, (okCode[self.bctx, l1, code, self.ok0]) =>
              ok_jump(self.bctx, l1, ip, th)))
          } else {
            (self.ok0, self.ok_code0((lctx, l1), None))
          }
        }
        StatementIterKind::Defer(0, l0, DeferredKind::Exit(op)) => {
          let code = code.expect("defer requires code");
          let u_gctx = self.thm.get_def0(self.elab, self.t_gctx);
          let (c, ty) = app_match!(self.thm, u_gctx => { (mkGCtx c t) => (c, t), ! });
          let th = thm!(self.thm, okResultGI(ty, c): okResult[u_gctx, ty]);
          let h1 = thm!(self.thm, (okResult[self.gctx, ty]) =>
            CONV({th} => (okResult (UNFOLD({self.t_gctx}); u_gctx) ty)));
          let (ty2, h2) = self.read_hyp_operand((tctx, l0), op);
          let h2 = self.read_hyp_coerce(ty2, h2, ty);
          *lctx = LCtx::Dead;
          (self.ok0, thm!(self.thm, (okCode[self.bctx, l1, code, self.ok0]) =>
            ok_exit(ty, self.gctx, self.labs, self.pctx1, l0, h1, h2)))
        }
        StatementIterKind::Defer(ref mut n, _, _) => {
          let code = code.expect("defer requires code");
          tctx.piter.as_mut().and_then(Iterator::next).expect("defer requires code");
          *n -= 1;
          let l2 = app!(self.thm, (okDefer l1 code));
          (l2, thm!(self.thm, okDeferI(self.bctx, code, l1): okCode[self.bctx, l1, code, l2]))
        }
      }
    }
  }

  /// Returns `(lctx', |- okCode bctx lctx code lctx')` or `(lctx', |- okWeak bctx lctx lctx')`,
  /// where `code` is atomic.
  fn ok_code1(&mut self,
    (lctx, l1): P<&mut LCtx<'a>>, code: Option<ProofId>
  ) -> (ProofId, ProofId) {
    match (&mut *lctx, code) {
      (LCtx::Dead, None) =>
        (l1, thm!(self.thm, okWeak_id(self.bctx, l1): okWeak[self.bctx, l1, l1])),
      (LCtx::Dead, Some(code)) =>
        (l1, thm!(self.thm, okCode_0(self.bctx, code): okCode[self.bctx, l1, code, l1])),
      (LCtx::Prologue(_), None) => unreachable!("entry block must have code"),
      (LCtx::Prologue(p), Some(code)) => if let Some(&reg) = p.iter.next() {
        let Prologue { epi, sp, ref mut mctx, prol, ref mut piter, .. } = **p;
        let r = reg.index(); let er = self.hex[r];
        let n = self.hex.h2n(&mut self.thm, 8);
        let (sp2, h1) = self.hex.add(&mut self.thm, sp, n);
        let mctx1 = mctx.1;
        let t = ((r, MCtxRegValue::Free), app!(self.thm, (FREE er)));
        let h2 = MCtx::push_reg::<PushMCtx>(mctx, &mut self.thm, t);
        p.epi = app!(self.thm, epiPop[er, epi]);
        p.sp = sp2;
        piter.next();
        let l2 = app!(self.thm, okPrologue[p.epi, *sp2, mctx.1, prol]);
        (l2, thm!(self.thm, (okCode[self.bctx, l1, code, l2]) =>
          okPrologue_push(self.bctx, epi, mctx1, mctx.1, prol, er, *sp, *sp2, h1, h2)))
      } else {
        let Prologue { epi, sp, mut mctx, viter, mut piter, vctx, .. } =
          *let_unchecked!(LCtx::Prologue(p) = std::mem::take(lctx), p);
        let h1 = mctx.0.ok(&mut self.thm);
        let mctx1 = mctx.1;
        if self.sp_max.val != 0 {
          piter.next();
          MCtx::add_stack(&mut mctx, &mut self.thm, self.ctx.sp_max);
        }
        let (vctx1, sz1) = (vctx.e, *vctx.nvars);
        let tctx = Box::new(TCtx { viter, piter: Some(piter.peekable()), vctx, mctx });
        let l2 = tctx.mk(&mut self.thm);
        *lctx = LCtx::Reg(tctx);
        if self.sp_max.val == 0 {
          let (l3, h2) = self.ok_code1((lctx, l2), Some(code));
          (l3, thm!(self.thm, (okCode[self.bctx, l1, code, l3]) =>
            okPrologue_alloc0(self.bctx, code, epi, l3, mctx1, *sp, sz1, vctx1, h1, h2)))
        } else {
          let (m, h2) = self.hex.add(&mut self.thm, sp, self.ctx.sp_max);
          let max = self.hex.from_u32(&mut self.thm, 1 << 12);
          let h3 = self.hex.lt(&mut self.thm, m, max);
          (l2, thm!(self.thm, (okCode[self.bctx, l1, code, l2]) =>
            okPrologue_alloc(self.bctx, epi, *m, mctx1, *self.sp_max, *sp,
              sz1, vctx1, h1, h2, h3)))
        }
      }
      (LCtx::Reg(tctx), code) => {
        if_chain! {
          if let Some(iter) = &mut tctx.piter;
          if let Some(code) = code;
          if let Some(inst) = iter.peek();
          if matches!(inst.inst, PInst::MovRR { .. } |
            PInst::Load64 { spill: true, .. } | PInst::Store { spill: true, .. });
          then {
            let inst = iter.next().expect("impossible");
            return self.ok_spill_op((tctx, l1), inst.inst, code)
          }
        }
        self.ok_code_reg((lctx, l1), code)
      }
      (LCtx::Epilogue(_), None) => unreachable!("epilogue must have code"),
      (LCtx::Epilogue(epi), Some(code)) => app_match!(self.thm, *epi => {
        (epiFree n epi2) => {
          let l2 = app!(self.thm, (okEpilogue epi2));
          *epi = epi2;
          (l2, thm!(self.thm,
            okEpilogue_free(epi2, self.bctx, n): (okCode {self.bctx} l1 code l2)))
        }
        (epiPop r epi2) => {
          let l2 = app!(self.thm, (okEpilogue epi2));
          *epi = epi2;
          (l2, thm!(self.thm, okEpilogue_pop(epi2, self.bctx, r): (okCode {self.bctx} l1 code l2)))
        }
        (epiRet) => {
          let l2 = app!(self.thm, (ok0));
          *lctx = LCtx::Dead;
          (l2, thm!(self.thm, okEpilogue_ret(self.bctx): (okCode {self.bctx} l1 code l2)))
        }
        !
      })
    }
  }

  /// Returns `(lctx', |- okCode bctx lctx code lctx')` or `(lctx', |- okWeak bctx lctx lctx')`
  fn ok_code(&mut self,
    (lctx, l1): P<&mut LCtx<'a>>, mut code: Option<ProofId>
  ) -> (ProofId, ProofId) {
    if !matches!(lctx, LCtx::Dead) {
      if let Some(code) = code {
        app_match!(self.thm, code => {
          (localAssembleA c1 c2) => {
            let (l2, h1) = self.ok_code((lctx, l1), Some(c1));
            let (l3, h2) = self.ok_code((lctx, l2), Some(c2));
            return (l3, thm!(self.thm, (okCode[self.bctx, l1, code, l3]) =>
              okCode_A(self.bctx, c1, c2, l1, l2, l3, h1, h2)))
          }
          _ => {}
        })
      }
    }
    self.ok_code1((lctx, l1), code)
  }

  /// Returns `|- okCode bctx lctx code ok0` or `|- okWeak bctx lctx ok0`
  fn ok_code0(&mut self, (mut lctx, l1): P<LCtx<'a>>, code: Option<ProofId>) -> ProofId {
    let (_, th) = self.ok_code((&mut lctx, l1), code);
    if let LCtx::Dead = lctx { th } else { panic!("incomplete block") }
  }

  /// Proves `|- okProc gctx start args ret clob se`,
  /// or `|- okStart gctx start` for the start procedure
  fn prove_proc(&mut self, root: VCtx) -> ProofId {
    let name = self.proc.name();
    let (asm, asmd_thm) = self.proc_asm[&self.proc.id];
    let (x, th) = self.thm.thm0(self.elab, asmd_thm);
    app_match!(self.thm, x => {
      (assembled g (asmProc p a)) => {
        let th = thm!(self.thm, okAssembledI(a, g, self.pctx1, p, th): okAssembled[self.pctx, a]);
        let a2 = self.thm.get_def0(self.elab, asm);
        let th = thm!(self.thm, (okAssembled[self.pctx, a2]) =>
          CONV({th} => SYM (okAssembled (REFL {self.pctx}) (UNFOLD({asm}); a2))));
        self.prove_vblock_asm(&mut self.proc.assembly_blocks(), a2, th)
      }
      !
    });
    let (a, h1) = self.vblock_asm[&self.proc.vblock_id(BlockId::ENTRY).expect("ghost function")];
    let (start, code) = app_match!(self.thm, a => { (asmEntry start code) => (start, code), ! });
    if name.is_some() {
      let bl = self.proc.block(BlockId::ENTRY);
      let abi = self.elf_proof.proc_abi(self.proc.id.expect("not start"));
      let mut vctx = root;
      let (args, mut mctx, h2) = self.accum_args(&mut vctx, bl.block().ctx, &abi.args);
      let mctx1 = mctx.1;
      let args2 = app!(self.thm, (mkArgs args mctx1));
      let (clob, h3) = self.accum_clob(&mut mctx, abi.clobbers.iter().map(|r| r.index()));
      let mctx2 = mctx.1;
      let viter = StatementIter {
        stmts: bl.block().stmts.iter(),
        term: Some(bl.block().terminator()),
        kind: StatementIterKind::Start,
      };
      let piter = bl.vblock().expect("entry block must have code").insts();
      let mut sp = self.hex.h2n(&mut self.thm, 0);
      let epi0 = app!(self.thm, (epiRet));
      let iter = self.proc.saved_regs().iter();
      let (vctx1, sz1) = (vctx.e, *vctx.nvars);
      let prol = app!(self.thm, mkPrologue[vctx1, sz1, self.epi]);
      let lctx = app!(self.thm, okPrologue[epi0, *sp, mctx2, prol]);
      let prol = Box::new(Prologue { epi: epi0, sp, mctx, iter, prol, viter, piter, vctx });
      let h4 = self.ok_code0((LCtx::Prologue(prol), lctx), Some(code));
      thm!(self.thm, (okProc[self.gctx, start, args2, self.ret, clob, self.se]) =>
        okProcI(args, clob, code, self.epi, self.gctx, mctx1, mctx2, self.ret, self.se,
          start, sz1, vctx1, h1, h2, h3, h4))
    } else {
      let ((tctx, l1), h2) = self.build_start(root);
      let mut sp = self.hex.h2n(&mut self.thm, 0);
      let h3 = self.ok_code0((LCtx::Reg(tctx), l1), Some(code));
      thm!(self.thm, (okStart[self.gctx, start]) =>
        okStartI(code, self.gctx, self.pctx1, start, l1, h1, h2, h3))
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
) -> Result<()> {
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
    let ctx = &build.ctx;
    let (ok_thm, doc) = mangler.get_data(build.elab,
      proc.name().map_or(Name::StartOkThm, Name::ProcOkThm));
    let ok_thm = build.elab.env
      .add_thm(build.thm.build_thm0(ok_thm, Modifiers::empty(), span.clone(), full, Some(doc), th))
      .map_err(|e| e.into_elab_error(full))?;
    proc_proof.insert(proc.id, ok_thm);
  }
  Ok(())
}
