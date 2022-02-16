#![allow(clippy::cast_possible_truncation)]

use std::cell::RefCell;
use std::collections::HashMap;

use mmcc::Idx;
use mmcc::types::IdxVec;
use mmcc::types::mir::{Cfg, Contexts, CtxBufId, CtxId, ExprKind, Statement, Terminator, VarId};
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
  app!(de, (ok0)) // TODO
}

type P<A> = (A, ProofId);

struct Ctx {
  gctx: ProofId,
  start: Num,
  args: ProofId,
  ret: ProofId,
  epi: ProofId,
  sp_max: Num,
  pctx1: ProofId,
  pctx: ProofId,
  labs: ProofId,
  bctx: ProofId,
}

impl Ctx {
  fn new(de: &mut ProofDedup<'_>, hex: &HexCache, proc: &Proc<'_>, gctx: TermId) -> Ctx {
    let gctx = app!(de, ({gctx}));
    let start = hex.from_u32(de, proc.start);
    let args = app!(de, (ok0)); // todo!();
    let ret = app!(de, (ok0)); // todo!();
    let mut epi = app!(de, (epiRet));
    #[allow(clippy::cast_possible_truncation)]
    for &reg in proc.saved_regs() {
      epi = app!(de, epiPop[hex[reg.index()], epi]);
    }
    let sp_max = hex.from_u32(de, proc.stack_size());
    if sp_max.val != 0 { epi = app!(de, epiFree[*sp_max, epi]) }
    let pctx1 = app!(de, mkPCtx1[*start, ret, epi]);
    let pctx = app!(de, mkPCtx[gctx, pctx1]);
    let labs = app!(de, (labelGroup0));
    let bctx = app!(de, mkBCtx[pctx, labs]);
    Ctx { gctx, start, args, ret, epi, sp_max, pctx1, pctx, labs, bctx }
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

enum StatementIterKind {
  Start,
}

struct StatementIter<'a> {
  stmts: std::slice::Iter<'a, Statement>,
  term: Option<&'a Terminator>,
  kind: StatementIterKind,
}

struct TCtx<'a> {
  viter: StatementIter<'a>,
  piter: Option<std::iter::Peekable<InstIter<'a>>>,
  vctx: VCtx,
  mctx: ProofId,
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
      okPushVarI(self.mctx, self.mctx, *n, *n2, ty, old, self.vctx.e))))
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
      okPushVarI(self.mctx, *self.vctx.nvars, ty, old, self.vctx.e)))
  }

  fn mk(&self, de: &mut ProofDedup<'_>) -> ProofId {
    app!(de, mkTCtx[self.vctx.e, *self.vctx.nvars, self.mctx])
  }
}

struct Prologue<'a> {
  epi: ProofId,
  sp: Num,
  iter: std::slice::Iter<'a, PReg>,
  ok_epi: ProofId,
  tctx: PTCtx<'a>,
}

enum LCtx<'a> {
  Dead,
  Prologue(Box<Prologue<'a>>),
  Reg(Box<TCtx<'a>>),
}

impl Default for LCtx<'_> {
  fn default() -> Self { Self::Dead }
}

struct ProcProver<'a> {
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
      mctx: app!(self.thm, (d0)), // TODO
    });
    let mut l = tctx.mk(&mut self.thm);
    for &(v, _, (ref e, ref ty)) in self.proc.cfg.ctxs.iter_range(base..bl.block().ctx) {
      let (l2, th) = match e {
        Some(e) if match **e {
          ExprKind::Var(u) if u == v => false,
          ExprKind::Unit => false,
          _ => true,
        } => {
          let ty = app!(self.thm, (ok0)); // TODO
          tctx.push_hyp(l, &mut self.thm, &self.hex, v, VarKind::Typed, ty)
        }
        _ => {
          let ty = app!(self.thm, (ok0)); // TODO
          tctx.push_var(l, &mut self.thm, &self.hex, v, ty).1
        }
      };
      l = l2;
    }
    (tctx, l)
  }

  /// Returns `(tctx, |- okEpi bctx epi sp_max tctx, |- buildProc pctx args ret tctx)`
  fn build_proc(&mut self, root: VCtx) -> (PTCtx<'a>, ProofId, ProofId) {
    let tctx = self.block_tctx(self.proc.block(BlockId::ENTRY), root, CtxId::ROOT);
    let ok_epi = app!(self.thm, okEpi[self.bctx, self.epi, *self.sp_max, tctx.1]);
    let bproc = app!(self.thm, buildProc[self.pctx, self.args, self.ret, tctx.1]);
    (tctx, thm!(self.thm, sorry(ok_epi): ok_epi), thm!(self.thm, sorry(bproc): bproc)) // TODO
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

  /// Returns `(lctx', |- okCode bctx tctx code lctx')`
  /// or `(lctx', |- okWeak bctx lctx lctx')` in the regular case, assuming
  /// regalloc moves have already been handled and `code` is atomic.
  fn ok_code_reg(&mut self, (lctx, l1): P<&mut LCtx<'a>>, code: Option<ProofId>) -> (ProofId, ProofId) {
    let tctx = if let LCtx::Reg(tctx) = lctx { &mut **tctx } else { unreachable!() };
    // println!("ok_code_reg");
    // dbg!(self.pp(l1), code.map(|code| self.pp(code)));
    #[allow(clippy::never_loop)] loop {
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
            Terminator::Jump1(_) => todo!(),
            Terminator::Return(_, _) => todo!(),
            Terminator::Unreachable(_) => todo!(),
            Terminator::If(_, _) => todo!(),
            Terminator::Assert(_, _, _, _) => todo!(),
            Terminator::Call { f, se, tys, args, reach, tgt, rets } => todo!(),
            Terminator::Exit(_) => todo!(),
            Terminator::Dead => unreachable!(),
          }
        } else {
          todo!()
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
        let Prologue { epi, sp, ref mut tctx, .. } = **p;
        let r = self.hex[reg.index()];
        let n = self.hex.h2n(&mut self.thm, 8);
        let (sp2, h1) = self.hex.add(&mut self.thm, sp, n);
        p.epi = app!(self.thm, epiPop[r, epi]);
        p.sp = sp2;
        tctx.0.piter.as_mut().expect("impossible").next();
        let l2 = app!(self.thm, okPrologue[p.epi, *sp2, tctx.1]);
        (l2, thm!(self.thm, (okCode[self.bctx, l1, code, l2]) =>
          okPrologue_push(self.bctx, epi, r, *sp, *sp2, tctx.1, h1)))
      } else {
        let Prologue { epi, sp, tctx: (mut tctx, l2), ok_epi, .. } =
          *let_unchecked!(LCtx::Prologue(p) = std::mem::take(lctx), p);
        if self.sp_max.val == 0 {
          *lctx = LCtx::Reg(tctx);
          let (l3, th) = self.ok_code1((lctx, l2), Some(code));
          (l3, thm!(self.thm, (okCode[self.bctx, l1, code]) =>
            okPrologue_alloc0(self.bctx, code, epi, l3, *sp, l2, ok_epi, th)))
        } else {
          tctx.piter.as_mut().expect("impossible").next();
          *lctx = LCtx::Reg(tctx);
          let (m, h2) = self.hex.add(&mut self.thm, sp, self.ctx.sp_max);
          let max = self.hex.from_u32(&mut self.thm, 1 << 12);
          let h3 = self.hex.lt(&mut self.thm, m, max);
          (l2, thm!(self.thm, (okCode[self.bctx, l1, code]) =>
            okPrologue_alloc(self.bctx, epi, *m, *self.sp_max, *sp, l2, ok_epi, h2, h3)))
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

  /// Proves `|- buildProc gctx start args ret`
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
    let code = app_match!(self.thm, a => { (asmEntry _ code) => code, ! });
    let (tctx@(_, l1), ok_epi, h2) = self.build_proc(root);
    let mut sp = self.hex.h2n(&mut self.thm, 0);
    let mut epi = app!(self.thm, (epiRet));
    let lctx = app!(self.thm, okPrologue[epi, *sp, l1]);
    let iter = self.proc.saved_regs().iter();
    let prol = Box::new(Prologue { epi, sp, iter, ok_epi, tctx });
    let h3 = self.ok_code0((LCtx::Prologue(prol), lctx), Some(code));
    thm!(self.thm, (okProc[self.gctx, *self.start, self.args, self.ret]) =>
      okProcI(self.args, code, self.gctx, self.pctx1, self.ret, *self.start, l1, h1, h2, h3))
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
    let ok_thm = mangler.mangle(build.elab, proc.name().map_or(Name::StartOkThm, Name::ProcOkThm));
    let ok_thm = build.elab.env
      .add_thm(build.thm.build_thm0(ok_thm, Modifiers::empty(), span.clone(), full, th))
      .map_err(|e| e.into_elab_error(full))?;
    proc_proof.insert(proc.id, ok_thm);
  }
  Ok(())
}
