#![allow(clippy::cast_possible_truncation)]

use std::collections::HashMap;

use mmcc::{Symbol, TEXT_START, types::Size};
use mmcc::arch::{ExtMode, OpcodeLayout, PInst, PRegMemImm, Unop};
use mmcc::proof::{AssemblyBlocks, AssemblyItem, AssemblyItemIter, BlockId, ElfProof, Inst, InstIter, PReg, Proc, VBlockId};
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
    let args = todo!();
    let ret = todo!();
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

struct TCtx<'a> {
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

struct ProcProver<'a> {
  proc: &'a Proc<'a>,
  proc_asm: &'a HashMap<Option<Symbol>, (TermId, ThmId)>,
  proc_proof: &'a mut HashMap<Option<Symbol>, ThmId>,
  vblock_asm: HashMap<VBlockId, (ProofId, ProofId)>,
  block_proof: HashMap<BlockId, ThmId>,
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

  /// Returns `(tctx, |- okEpi bctx epi sp_max tctx, |- buildProc pctx args ret tctx)`
  fn build_proc(&mut self) -> (PTCtx<'a>, ProofId, ProofId) {
    todo!()
  }

  /// Returns `(v, |- okRead tctx loc v)`
  fn read(&mut self, tctx: &PTCtx<'a>, loc: &P<Loc>) -> (P<Value>, ProofId) {
    todo!()
  }

  /// Returns `(tctx2, |- okWrite tctx loc v tctx2)`
  fn write(&mut self, tctx: PTCtx<'a>, loc: &P<Loc>, v: &P<Value>) -> (PTCtx<'a>, ProofId) {
    (tctx, todo!())
  }

  /// Returns `(tctx', |- okCode bctx tctx code tctx')` for a regalloc operation.
  fn ok_spill_op(&mut self, tctx@(_, l1): PTCtx<'a>, inst: &PInst, code: ProofId) -> (PTCtx<'a>, ProofId) {
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
        let (v, h1) = match self.read(&tctx, &lsrc) {
          ((Value::Reg, v), h1) => (v, h1),
          _ => unreachable!(),
        };
        let (tctx2@(_, l2), h2) = self.write(tctx, &ldst, &(Value::Reg, v));
        let th = thm!(self.thm, (okCode[self.bctx, l1, code, l2]) =>
          ok_movRR(self.bctx, edst, esrc, l1, l2, v, h1, h2));
        (tctx2, th)
      }
      (Ok(edst), Err(esrc), &PInst::Load64 { dst, .. }) => {
        let lsrc = Loc::Local(esrc).as_expr(&mut self.thm);
        let ldst = Loc::Reg((dst.index() as u8, edst)).as_expr(&mut self.thm);
        let (v, h1) = match self.read(&tctx, &lsrc) {
          ((Value::SpillSlot(v), _), h1) => (v, h1),
          _ => unreachable!(),
        };
        let (tctx2@(_, l2), h2) = self.write(tctx, &ldst, &(Value::Reg, v));
        let th = thm!(self.thm, (okCode[self.bctx, l1, code, l2]) =>
          ok_unspill(self.bctx, edst, esrc, l1, l2, v, h1, h2));
        (tctx2, th)
      }
      (Err(edst), Ok(esrc), &PInst::Store { src, .. }) => {
        let lsrc = Loc::Reg((src.index() as u8, esrc)).as_expr(&mut self.thm);
        let ldst = Loc::Local(edst).as_expr(&mut self.thm);
        let (v, h1) = match self.read(&tctx, &lsrc) {
          ((Value::Reg, v), h1) => (v, h1),
          _ => unreachable!(),
        };
        let ss = app!(self.thm, (spillslot v));
        let (tctx2@(_, l2), h2) = self.write(tctx, &ldst, &(Value::SpillSlot(v), ss));
        let th = thm!(self.thm, (okCode[self.bctx, l1, code, l2]) =>
          ok_spill(self.bctx, edst, esrc, l1, l2, v, h1, h2));
        (tctx2, th)
      }
      _ => unreachable!()
    }
  }

  /// Returns `(lctx', |- okCode bctx lctx code lctx')`
  fn ok_code1(&mut self, lctx: P<LCtx<'a>>, code: ProofId) -> (P<LCtx<'a>>, ProofId) {
    match lctx.0 {
      LCtx::Dead => {
        let th = thm!(self.thm, (okCode[self.bctx, lctx.1, code, lctx.1]) =>
          okCode_0(self.bctx, code));
        (lctx, th)
      }
      LCtx::Prologue(mut p) => if let Some(&reg) = p.iter.next() {
        let Prologue {epi, sp, ref tctx, ..} = *p;
        let r = self.hex[reg.index() as u8];
        let n = self.hex.h2n(&mut self.thm, 8);
        let (sp2, h1) = self.hex.add(&mut self.thm, sp, n);
        p.epi = app!(self.thm, epiPop[r, epi]);
        p.sp = sp2;
        let l2 = app!(self.thm, okPrologue[p.epi, *sp2, tctx.1]);
        let th = thm!(self.thm, (okCode[self.bctx, lctx.1, code, l2]) =>
          okPrologue_push(self.bctx, epi, r, *sp, *sp2, tctx.1, h1));
        ((LCtx::Prologue(p), l2), th)
      } else {
        let Prologue {epi, sp, tctx, ok_epi, ..} = *p;
        if self.sp_max.val == 0 {
          let (lctx2, th) = self.ok_code1((LCtx::Reg(tctx.0), tctx.1), code);
          let th = thm!(self.thm, (okCode[self.bctx, lctx.1, code]) =>
            okPrologue_alloc0(self.bctx, code, epi, lctx2.1, *sp, tctx.1, ok_epi));
          (lctx2, th)
        } else {
          let (m, h2) = self.hex.add(&mut self.thm, sp, self.ctx.sp_max);
          let max = self.hex.from_u32(&mut self.thm, 1 << 12);
          let h3 = self.hex.lt(&mut self.thm, m, max);
          let th = thm!(self.thm, (okCode[self.bctx, lctx.1, code]) =>
            okPrologue_alloc(self.bctx, epi, *m, *self.sp_max, *sp, tctx.1, ok_epi, h2, h3));
          ((LCtx::Reg(tctx.0), tctx.1), th)
        }
      }
      LCtx::Reg(mut tctx) => {
        if let Some(iter) = &mut tctx.iter {
          if let Some(inst) = iter.peek() {
            if matches!(inst.inst, PInst::MovRR { .. } |
              PInst::Load64 { spill: true, .. } | PInst::Store { spill: true, .. })
            {
              let inst = iter.next().expect("impossible");
              let (tctx, th) = self.ok_spill_op((tctx, lctx.1), inst.inst, code);
              return ((LCtx::Reg(tctx.0), tctx.1), th)
            }
          }
        }
        todo!()
      }
    }
  }

  /// Returns `(lctx', |- okCode bctx lctx code lctx')`
  fn ok_code(&mut self, lctx@(_, l1): P<LCtx<'a>>, code: ProofId) -> (P<LCtx<'a>>, ProofId) {
    if let LCtx::Dead = lctx.0 { return self.ok_code1(lctx, code) }
    app_match!(self.thm, code => {
      (localAssembleA c1 c2) => {
        let (lctx2@(_, l2), h1) = self.ok_code(lctx, c1);
        let (lctx3@(_, l3), h2) = self.ok_code(lctx2, c2);
        let th = thm!(self.thm, (okCode[self.bctx, l1, code, l3]) =>
          okCode_A(self.bctx, c1, c2, l1, l2, l3, h1, h2));
        (lctx3, th)
      }
      _ => self.ok_code1(lctx, code)
    })
  }

  /// Returns `|- okCode bctx lctx code ok0`
  fn ok_code0(&mut self, lctx: P<LCtx<'a>>, code: ProofId) -> ProofId {
    if let ((LCtx::Dead, _), th) = self.ok_code(lctx, code) { th }
    else { panic!("incomplete block") }
  }

  /// Proves `|- buildProc gctx start args ret`
  fn prove_proc(&mut self) -> ProofId {
    let (asm, asmd_thm) = self.proc_asm[&self.proc.name()];
    let (x, th) = self.thm.thm0(self.elab, asmd_thm);
    app_match!(self.thm, x => {
      (assembled g (asmProc p a)) => {
        let th = thm!(self.thm, okAssembledI(a, g, self.pctx1, p, th): okAssembled[self.pctx, a]);
        self.prove_vblock_asm(&mut self.proc.assembly_blocks(), a, th)
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
    let h3 = self.ok_code0((LCtx::Prologue(prol), lctx), code);
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
