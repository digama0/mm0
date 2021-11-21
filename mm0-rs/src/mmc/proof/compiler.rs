#![allow(clippy::cast_possible_truncation)]

use std::collections::HashMap;

use mmcc::Idx;
use mmcc::types::IdxVec;
use mmcc::types::mir::{Cfg, Contexts, CtxBufId, CtxId, ExprKind, Statement, Terminator, VarId};
use mmcc::{Symbol, TEXT_START, types::Size};
use mmcc::arch::{ExtMode, OpcodeLayout, PInst, PRegMemImm, Unop};
use mmcc::proof::{AssemblyBlocks, AssemblyItem, AssemblyItemIter, BlockId, BlockProof,
  BlockProofTree, BlockTreeIter, ElfProof, Inst, InstIter, PReg, Proc, VBlockId};
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
  fn new(
    de: &mut ProofDedup<'_>,
    hex: &HexCache,
    proc: &Proc<'_>,
    gctx: TermId,
  ) -> Ctx {
    let gctx = app!(de, ({gctx}));
    let start = hex.from_u32(de, proc.start);
    let args = app!(de, (ok0)); // todo!();
    let ret = app!(de, (ok0)); // todo!();
    let mut epi = app!(de, (epiRet));
    #[allow(clippy::cast_possible_truncation)]
    for &reg in proc.saved_regs() {
      epi = app!(de, epiPop[hex[reg.index() as u8], epi]);
    }
    let sp_max = hex.from_u32(de, proc.stack_size());
    if sp_max.val != 0 { epi = app!(de, epiFree[*sp_max, epi]) }
    let pctx1 = app!(de, mkPCtx1[*start, ret, epi, *sp_max]);
    let pctx = app!(de, mkPCtx[gctx, pctx1]);
    let labs = app!(de, (labelGroup0));
    let bctx = app!(de, mkBCtx[pctx, labs]);
    Ctx { gctx, start, args, ret, epi, sp_max, pctx1, pctx, labs, bctx }
  }
}

struct VContexts {
  root: VarMap,
  bufs: IdxVec<CtxBufId, VCtxBuf>
}

struct VCtxBuf {
  vctxs: Vec<VCtxNext>,
}

struct VCtxNext {
  map: VarMap,
}

#[derive(Clone)]
struct VarMap {
  e: ProofId,
  map: im::HashMap<VarId, ProofId>,
}

impl VContexts {
  fn get_map(&self, ctxs: &Contexts, mut id: CtxId) -> &VarMap {
    while id.1 == 0 {
      if id.0 == CtxBufId::ROOT { return &self.root }
      id = ctxs[id.0].parent
    }
    &self.bufs[id.0].vctxs[(id.1 - 1) as usize].map
  }

  fn expr(
    &self,
    de: &mut ProofDedup<'_>,
    cfg: &Cfg,
    e: &ExprKind,
  ) -> ProofId {
    todo!()
  }

  fn new(
    de: &mut ProofDedup<'_>,
    cfg: &Cfg,
  ) -> Self {
    let mut max = vec![0; cfg.ctxs.len()];
    for (id, bl) in cfg.blocks() {
      let CtxId(buf, n) = bl.ctx;
      if max[buf.0 as usize] < n { max[buf.0 as usize] = n }
    }
    let mut ctxs = Self {
      root: VarMap {
        e: app!(de, (vctx0)),
        map: Default::default(),
      },
      bufs: IdxVec::with_capacity(max.len())
    };
    for (id, i) in max.into_iter().enumerate() {
      let id = CtxBufId::from_usize(id);
      let mut map = ctxs.get_map(&cfg.ctxs, CtxId(id, 0)).clone();
      let buf = &cfg.ctxs[id];
      ctxs.bufs.push(VCtxBuf {
        vctxs: buf.vars[..i as usize].iter().enumerate().map(|(i, &(v, _, (ref e, ref ty)))| {
          match e {
            Some(e) => {
              let e = ctxs.expr(de, cfg, e);
              map.map.insert(v, e);
            }
            None => {
              todo!()
            }
          }
          VCtxNext { map: map.clone() }
        }).collect(),
      });
    }
    ctxs
  }
}

struct TCtx<'a> {
  stmts: std::slice::Iter<'a, Statement>,
  term: Option<&'a Terminator>,
  iter: Option<std::iter::Peekable<InstIter<'a>>>,
}

type PTCtx<'a> = P<Box<TCtx<'a>>>;

struct Prologue<'a> {
  epi: ProofId,
  sp: Num,
  iter: std::slice::Iter<'a, PReg>,
  ok_epi: ProofId,
  tctx: PTCtx<'a>
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
  proc_asm: &'a HashMap<Option<Symbol>, (TermId, ThmId)>,
  proc_proof: &'a mut HashMap<Option<Symbol>, ThmId>,
  vblock_asm: HashMap<VBlockId, (ProofId, ProofId)>,
  /// Contains a map from a block id to
  /// `[labs, ip, lctx, |- okBlock (mkBCtx pctx labs) ip lctx]`
  block_proof: HashMap<BlockId, [ProofId; 4]>,
  vctxs: VContexts,
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

  // fn get_ctx(&mut self, id: CtxId) -> ProofId {
  //   if let Some(&e) = self.ctxs.get(&id) { return e }
  //   let buf = &self.proc.cfg.ctxs[id.0];
  //   let (i, e) = (0..id.1)
  //     .filter_map(|i| Some((i, *self.ctxs.get(&CtxId(id.0, i))?)))
  //     .next_back()
  //     .unwrap_or_else(|| (0, if id.0 == CtxBufId::ROOT {

  //     } else {
  //       self.get_ctx(buf.parent)
  //     }))
  //      {
  //       Some((i, e)) => {

  //       }
  //       None => todo!(),
  //   }
  // }

  /// Returns the `tctx` type state for the entry of a block.
  fn block_tctx(&mut self, bl: BlockProof<'a>) -> PTCtx<'a> {
    let tctx = Box::new(TCtx {
      stmts: bl.block().stmts.iter(),
      term: Some(bl.block().terminator()),
      iter: bl.vblock().map(|vbl| vbl.insts().peekable()),
    });

    let l = app!(self.thm, (ok0)); // TODO
    (tctx, l)
  }

  /// Returns `(id, [ip, lctx, |- okBlock bctx ip lctx])`
  fn ok_code_block(&mut self,
    mut tree: BlockProofTree<'a>
  ) -> (BlockId, [ProofId; 3]) {
    loop {
      match tree {
        BlockProofTree::Induction(labs, seq) => {
          let var = todo!();
          let ls = todo!();
          let old@[labs, bctx] = self.push_label_group(var, ls);
          for tree in seq.deps() { self.add_block(tree) }
          let (id, [ip, lctx, th]) = self.ok_code_block(seq.main());
          let th = thm!(self.thm, ((okBlock bctx ip lctx)) =>
            okBlock_loop(labs, ip, lctx, ls, self.pctx, var, th));
          self.pop_label_group(old);
          return (id, [ip, lctx, th])
        }
        BlockProofTree::Seq(seq) => {
          for tree in seq.deps() { self.add_block(tree) }
          tree = seq.main()
        }
        BlockProofTree::One(bl) => {
          let (tctx, l1) = self.block_tctx(bl);
          return (bl.id, match bl.vblock() {
            None => {
              let th = self.ok_code0((LCtx::Reg(tctx), l1), None);
              let ip = app!(self.thm, (d0));
              let th = thm!(self.thm, okBlock0(self.labs, l1, self.pctx, th):
                okBlock[self.bctx, ip, l1]);
              [ip, l1, th]
            }
            Some(vbl) => {
              let (a, h1) = self.vblock_asm[&vbl.id];
              let (ip, code) = app_match!(self.thm, a => { (asmAt ip code) => (ip, code), ! });
              let h2 = self.ok_code0((LCtx::Reg(tctx), l1), Some(code));
              let th = thm!(self.thm, okBlockI(self.labs, code, ip, l1, self.pctx, h1, h2):
                okBlock[self.bctx, ip, l1]);
              [ip, l1, th]
            }
          })
        }
      }
    }
  }

  fn add_block(&mut self, tree: BlockProofTree<'a>) {
    let (id, [ip, lctx, th]) = self.ok_code_block(tree);
    assert!(self.block_proof.insert(id, [self.labs, ip, lctx, th]).is_none())
  }

  /// Returns `(tctx, |- okEpi bctx epi sp_max tctx, |- buildProc pctx args ret tctx)`
  fn build_proc(&mut self) -> (PTCtx<'a>, ProofId, ProofId) {
    let mut tree = self.proc.proof_tree();
    let tctx = loop {
      match tree {
        BlockProofTree::Induction(_, _) => unreachable!("entry block cannot be an induction"),
        BlockProofTree::Seq(seq) => {
          for tree in seq.deps() { self.add_block(tree) }
          tree = seq.main()
        }
        BlockProofTree::One(pf) => break self.block_tctx(pf),
      }
    };
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
        let lsrc = Loc::Reg((src.index() as u8, esrc)).as_expr(&mut self.thm);
        let ldst = Loc::Reg((dst.index() as u8, edst)).as_expr(&mut self.thm);
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
        let ldst = Loc::Reg((dst.index() as u8, edst)).as_expr(&mut self.thm);
        let (v, h1) = match self.read((tctx, l1), &lsrc) {
          ((Value::SpillSlot(v), _), h1) => (v, h1),
          _ => unreachable!(),
        };
        let (l2, h2) = self.write((tctx, l1), &ldst, &(Value::Reg, v));
        (l2, thm!(self.thm, (okCode[self.bctx, l1, code, l2]) =>
          ok_unspill(self.bctx, edst, esrc, l1, l2, v, h1, h2)))
      }
      (Err(edst), Ok(esrc), &PInst::Store { src, .. }) => {
        let lsrc = Loc::Reg((src.index() as u8, esrc)).as_expr(&mut self.thm);
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
    println!("ok_code_reg");
    dbg!(self.pp(l1), code.map(|code| self.pp(code)));
    if let Some(stmt) = tctx.stmts.next() {
      match stmt {
        Statement::Let(lk, ty, rv) => todo!(),
        Statement::Assign(_, _, _, _) => todo!(),
        Statement::LabelGroup(..) => todo!(),
        Statement::PopLabelGroup => todo!(),
        Statement::DominatedBlock(_, _) => todo!(),
    }
      dbg!(stmt);
    } else {
      todo!()
    }
  }

  /// Returns `(lctx', |- okCode bctx lctx code lctx')` or `(lctx', |- okWeak bctx lctx lctx')`,
  /// where `code` is atomic.
  fn ok_code1(&mut self, (lctx, l1): P<&mut LCtx<'a>>, code: Option<ProofId>) -> (ProofId, ProofId) {
    match (&mut *lctx, code) {
      (LCtx::Dead, None) =>
        (l1, thm!(self.thm, okWeak_id(self.bctx, l1): okWeak[self.bctx, l1, l1])),
      (LCtx::Dead, Some(code)) =>
        (l1, thm!(self.thm, okCode_0(self.bctx, code): okCode[self.bctx, l1, code, l1])),
      (LCtx::Prologue(p), None) => unreachable!("entry block must have code"),
      (LCtx::Prologue(p), Some(code)) => if let Some(&reg) = p.iter.next() {
        let Prologue {epi, sp, ref tctx, ..} = **p;
        let r = self.hex[reg.index() as u8];
        let n = self.hex.h2n(&mut self.thm, 8);
        let (sp2, h1) = self.hex.add(&mut self.thm, sp, n);
        p.epi = app!(self.thm, epiPop[r, epi]);
        p.sp = sp2;
        let l2 = app!(self.thm, okPrologue[p.epi, *sp2, tctx.1]);
        (l2, thm!(self.thm, (okCode[self.bctx, l1, code, l2]) =>
          okPrologue_push(self.bctx, epi, r, *sp, *sp2, tctx.1, h1)))
      } else {
        let Prologue {epi, sp, tctx: (mut tctx, l2), ok_epi, ..} =
          *let_unchecked!(LCtx::Prologue(p) = std::mem::take(lctx), p);
        *lctx = LCtx::Reg(tctx);
        if self.sp_max.val == 0 {
          let (l3, th) = self.ok_code1((lctx, l2), Some(code));
          (l3, thm!(self.thm, (okCode[self.bctx, l1, code]) =>
            okPrologue_alloc0(self.bctx, code, epi, l2, *sp, l3, ok_epi)))
        } else {
          let (m, h2) = self.hex.add(&mut self.thm, sp, self.ctx.sp_max);
          let max = self.hex.from_u32(&mut self.thm, 1 << 12);
          let h3 = self.hex.lt(&mut self.thm, m, max);
          (l2, thm!(self.thm, (okCode[self.bctx, l1, code]) =>
            okPrologue_alloc(self.bctx, epi, *m, *self.sp_max, *sp, l2, ok_epi, h2, h3)))
        }
      }
      (LCtx::Reg(tctx), code) => {
        if_chain! {
          if let Some(iter) = &mut tctx.iter;
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
  fn ok_code(&mut self, (lctx, l1): P<&mut LCtx<'a>>, mut code: Option<ProofId>) -> (ProofId, ProofId) {
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
  fn prove_proc(&mut self) -> ProofId {
    let (asm, asmd_thm) = self.proc_asm[&self.proc.name()];
    let (x, th) = self.thm.thm0(self.elab, asmd_thm);
    app_match!(self.thm, x => {
      (assembled g (asmProc p a)) => {
        let th = thm!(self.thm, okAssembledI(a, g, self.pctx1, p, th): okAssembled[self.pctx, a]);
        let a2 = self.thm.get_def0(self.elab, asm);
        let th = thm!(self.thm, (okAssembled[self.pctx, a2]) =>
          CONV({th} => (okAssembled {self.pctx} (UNFOLD({asm}); a2))));
        self.prove_vblock_asm(&mut self.proc.assembly_blocks(), a2, th)
      }
      !
    });
    let (a, h1) = self.vblock_asm[&self.proc.vblock_id(BlockId::ENTRY).expect("ghost function")];
    let code = app_match!(self.thm, a => { (asmEntry _ code) => code, ! });
    let (tctx@(_, l1), ok_epi, h2) = self.build_proc();
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
  proc_asm: &HashMap<Option<Symbol>, (TermId, ThmId)>,
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
    let mut build = ProcProver {
      proc: &proc,
      proc_asm,
      proc_proof: &mut proc_proof,
      vblock_asm: Default::default(),
      block_proof: Default::default(),
      elab,
      ctx: Ctx::new(&mut thm, &hex, &proc, gctx),
      vctxs: VContexts::new(&mut thm, proc.cfg),
      hex,
      thm,
    };
    let th = build.prove_proc();
    let ctx = &build.ctx;
    let ok_thm = mangler.mangle(build.elab, Name::AsmdThm);
    let ok_thm = build.elab.env
      .add_thm(build.thm.build_thm0(ok_thm, Modifiers::empty(), span.clone(), full, th))
      .map_err(|e| e.into_elab_error(full))?;
    proc_proof.insert(proc.name(), ok_thm);
  }
  Ok(())
}
