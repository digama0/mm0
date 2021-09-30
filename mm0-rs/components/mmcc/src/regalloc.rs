use std::collections::HashMap;

use mm0_util::u32_as_usize;
use regalloc2::{Allocation, Edit, PReg, ProgPoint, SpillSlot, VReg};

use crate::arch::{AMode, Imm, Inst, PAMode, PInst, PRegMem, PRegMemImm, PShiftIndex, RegMem, RegMemImm};
use crate::mir_opt::storage::Allocations;
use crate::types::{IdxVec, Size};
use crate::types::mir::*;
use crate::{Entity, Idx, Symbol};
use crate::build_vcode::build_vcode;
use crate::types::vcode::{self, InstId, ProcAbi, ProcId, SpillId};

impl<I: vcode::Inst> vcode::VCode<I> {
  fn regalloc(&self) -> regalloc2::Output {
    let opts = regalloc2::RegallocOptions { verbose_log: true };
    regalloc2::run(self, &crate::arch::MACHINE_ENV, &opts).expect("fatal regalloc error")
  }
}

pub(crate) struct ApplyRegalloc {
  num_allocs: usize,
  alloc_iter: std::vec::IntoIter<Allocation>,
  offset_iter: std::vec::IntoIter<u32>,
  regspills: usize,
}

impl ApplyRegalloc {
  fn new(allocs: Vec<Allocation>, offsets: Vec<u32>, regspills: usize) -> Self {
    Self {
      num_allocs: allocs.len(),
      alloc_iter: allocs.into_iter(),
      offset_iter: offsets.into_iter(),
      regspills,
    }
  }

  fn spill(&self, n: SpillSlot) -> SpillId {
    SpillId::from_usize(self.regspills + n.index())
  }

  fn next_inst(&mut self, i: InstId) {
    assert_eq!(u32_as_usize(self.offset_iter.next().expect("inst align")),
      self.num_allocs - self.alloc_iter.len());
  }

  fn next(&mut self) -> Allocation {
    self.alloc_iter.next().expect("allocation align")
  }

  fn reg(&mut self) -> PReg {
    self.next().as_reg().expect("expected a register")
  }
  fn mem(&mut self, a: &AMode) -> PAMode {
    PAMode {
      off: a.off,
      base: if a.base == VReg::invalid() { PReg::invalid() } else { self.reg() },
      si: a.si.map(|si| PShiftIndex { index: self.reg(), shift: si.shift }),
    }
  }

  fn rm(&mut self, rm: &RegMem) -> PRegMem {
    match rm {
      RegMem::Reg(_) => PRegMem::Reg(self.reg()),
      RegMem::Mem(a) => PRegMem::Mem(self.mem(a)),
    }
  }

  fn rmi(&mut self, rmi: &RegMemImm) -> Option<PRegMemImm> {
    match rmi {
      RegMemImm::Reg(_) => Some(PRegMemImm::Reg(self.reg())),
      RegMemImm::Mem(a) => Some(PRegMemImm::Mem(self.mem(a))),
      RegMemImm::Imm(i) => Some(PRegMemImm::Imm(*i)),
      RegMemImm::Uninit => None,
    }
  }

  fn rmi0(&mut self, rmi: &RegMemImm) -> PRegMemImm {
    self.rmi(rmi).unwrap_or(PRegMemImm::Imm(Imm::ZERO))
  }
}

fn apply_edits(
  insts: &mut Vec<PInst>,
  edits: &mut std::iter::Peekable<impl Iterator<Item=(ProgPoint, Edit)>>,
  ar: &mut ApplyRegalloc,
  pt: ProgPoint
) {
  while edits.peek().map_or(false, |p| p.0 == pt) {
    if let Some((_, Edit::Move { from, to, to_vreg })) = edits.next() {
      match (from.as_reg(), to.as_reg()) {
        (Some(src), Some(dst)) => insts.push(PInst::MovRR { sz: Size::S64, dst, src }),
        (Some(src), _) => {
          let dst = AMode::spill(ar.spill(to.as_stack().expect("bad regalloc")));
          insts.push(PInst::Store { sz: Size::S64, dst, src })
        }
        (_, Some(dst)) => {
          let src = AMode::spill(ar.spill(from.as_stack().expect("bad regalloc")));
          insts.push(PInst::Load64 { dst, src })
        }
        _ => panic!("bad regalloc")
      }
    }
  }
}

#[derive(Debug)]
pub(crate) struct PCode {
  abi: ProcAbi,
  insts: Vec<PInst>,
  blocks: IdxVec<BlockId, (InstId, InstId)>,
  spill_offs: IdxVec<SpillId, u32>,
}

impl PCode {
  fn push(&mut self, i: PInst) { self.insts.push(i) }
}

struct BlockBuilder<'a> {
  blocks: &'a [(InstId, InstId)],
  start: InstId,
  cur: usize,
  next: InstId,
}

impl<'a> BlockBuilder<'a> {
  fn next(&mut self) {
    self.next = self.blocks.get(self.cur).map(|p| p.1).unwrap_or_else(InstId::invalid);
  }

  fn new(blocks: &'a [(InstId, InstId)]) -> Self {
    let mut this = Self { blocks, start: InstId(0), cur: 0, next: InstId(0) };
    this.next();
    this
  }

  fn push(&mut self, code: &mut PCode) {
    let end = InstId::from_usize(code.insts.len());
    self.cur += 1;
    self.next();
    code.blocks.push((std::mem::replace(&mut self.start, end), end));
  }
}

pub(crate) fn regalloc_vcode(
  names: &HashMap<Symbol, Entity>,
  func_mono: &HashMap<Symbol, ProcId>,
  funcs: &IdxVec<ProcId, ProcAbi>,
  cfg: &Cfg,
  allocs: &Allocations,
  rets: &[Arg],
) -> PCode {
  // simplelog::SimpleLogger::init(simplelog::LevelFilter::Debug, simplelog::Config::default());
  let mut vcode = build_vcode(names, func_mono, funcs, cfg, allocs, rets);
  // println!("{:#?}", vcode);
  let out = vcode.regalloc();
  // println!("{:#?}", out);
  let mut edits = out.edits.into_iter().peekable();
  let mut ar = ApplyRegalloc::new(out.allocs, out.inst_alloc_offsets, vcode.spills.len());
  for _ in 0..out.num_spillslots { vcode.fresh_spill(8); }
  let spill_offs = if let [incoming, outgoing, ref spills @ ..] = *vcode.spills.0 {
    vcode.abi.args_space = incoming;
    let mut offs = vec![0, 0];
    let mut rsp_off = 8;
    for n in spills {
      rsp_off += n;
      offs.push(rsp_off);
    }
    offs.into()
  } else { unreachable!() };
  let mut code = PCode {
    abi: vcode.abi,
    insts: vec![],
    blocks: IdxVec::from(vec![]),
    spill_offs
  };
  let mut bb = BlockBuilder::new(&vcode.blocks.0);
  for (i, inst) in vcode.insts.enum_iter() {
    ar.next_inst(i);
    if bb.next == i { bb.push(&mut code) };
    apply_edits(&mut code.insts, &mut edits, &mut ar, ProgPoint::before(i));
    match *inst {
      Inst::Fallthrough { dst } =>
        assert!(vcode.blocks[dst].0 == i.next()),
      Inst::Binop { op, sz, ref src2, .. } => {
        let (_, src, dst) = (ar.reg(), ar.rmi0(src2), ar.reg());
        code.push(PInst::Binop { op, sz, dst, src });
      }
      Inst::Unop { op, sz, .. } => {
        let (_, dst) = (ar.reg(), ar.reg());
        code.push(PInst::Unop { op, sz, dst });
      }
      Inst::DivRem { sz, ref src2, .. } => {
        let (_, src, _, _) = (ar.reg(), ar.rm(src2), ar.reg(), ar.reg());
        code.push(PInst::DivRem { sz, src });
      }
      Inst::Mul { sz, ref src2, .. } => {
        let (_, src, _, _) = (ar.reg(), ar.rm(src2), ar.reg(), ar.reg());
        code.push(PInst::Mul { sz, src });
      }
      Inst::Imm { sz, src, .. } => code.push(PInst::Imm { sz, dst: ar.reg(), src }),
      Inst::MovRR { .. } | Inst::MovRP { .. } | Inst::MovPR { .. } => {}
      Inst::MovzxRmR { ext_mode, ref src, .. } =>
        code.push(PInst::MovzxRmR { ext_mode, src: ar.rm(src), dst: ar.reg() }),
      Inst::Load64 { ref src, .. } =>
        code.push(PInst::Load64 { src: ar.mem(src), dst: ar.reg() }),
      Inst::Lea { ref addr, .. } =>
        code.push(PInst::Lea { addr: ar.mem(addr), dst: ar.reg() }),
      Inst::MovsxRmR { ext_mode, ref src, .. } =>
        code.push(PInst::MovsxRmR { ext_mode, src: ar.rm(src), dst: ar.reg() }),
      Inst::Store { sz, ref dst, .. } =>
        code.push(PInst::Store { sz, src: ar.reg(), dst: ar.mem(dst) }),
      Inst::ShiftImm { sz, kind, num_bits, .. } => {
        let (_, dst) = (ar.reg(), ar.reg());
        code.push(PInst::Shift { sz, kind, num_bits: Some(num_bits), dst })
      }
      Inst::ShiftRR { sz, kind, .. } => {
        let (_, _, dst) = (ar.reg(), ar.reg(), ar.reg());
        code.push(PInst::Shift { sz, kind, num_bits: None, dst })
      }
      Inst::Cmp { sz, op, ref src2, .. } => {
        code.push(PInst::Cmp { sz, op, src1: ar.reg(), src2: ar.rmi0(src2) })
      }
      Inst::SetCC { cc, .. } => code.push(PInst::SetCC { cc, dst: ar.reg() }),
      Inst::Cmov { sz, cc, dst, src1, ref src2 } => {
        let (_, src, dst) = (ar.reg(), ar.rm(src2), ar.reg());
        code.push(PInst::Cmov { sz, cc, dst, src });
      }
      Inst::Push64 { ref src } => code.push(PInst::Push64 { src: ar.rmi0(src) }),
      Inst::Pop64 { .. } => code.push(PInst::Pop64 { dst: ar.reg() }),
      Inst::CallKnown { f, ref operands, ref clobbers } => {
        for _ in &**operands { ar.reg(); }
        code.push(PInst::CallKnown { f })
      }
      Inst::Ret { ref params } => {
        for _ in &**params { ar.reg(); }
        code.push(PInst::Ret)
      }
      Inst::JmpKnown { dst, ref params } => {
        for _ in &**params { ar.reg(); }
        if vcode.blocks[dst].0 != i.next() {
          code.push(PInst::JmpKnown { dst, short: false });
        }
      }
      Inst::JmpCond { cc, taken, not_taken } =>
        if vcode.blocks[not_taken].0 == i.next() {
          code.push(PInst::JmpCond { cc, dst: taken, short: false })
        } else if vcode.blocks[taken].0 == i.next() {
          code.push(PInst::JmpCond { cc: cc.invert(), dst: not_taken, short: false })
        } else {
          code.push(PInst::JmpCond { cc, dst: taken, short: false });
          code.push(PInst::JmpKnown { dst: not_taken, short: false });
        },
      Inst::TrapIf { cc } => code.push(PInst::TrapIf { cc }),
      Inst::Ud2 => code.push(PInst::Ud2),
    }
    apply_edits(&mut code.insts, &mut edits, &mut ar, ProgPoint::after(i));
  }
  bb.push(&mut code);
  code
}

#[cfg(test)]
mod test {
  use std::rc::Rc;
  use crate::types::{IntTy, Spanned, hir::ProcKind};
  use super::*;

  #[test] fn two_plus_two() {
    let names = HashMap::new();
    let func_mono = HashMap::new();
    let funcs = IdxVec::new();
    let mut fresh_var = VarId::default();
    let u8 = IntTy::UInt(Size::S8);
    let u8ty = Rc::new(TyKind::Int(u8));
    let mut proc = Proc {
      kind: ProcKind::Proc,
      name: Spanned::dummy(crate::intern("foo")),
      tyargs: 0,
      args: vec![],
      rets: vec![Arg {
        attr: ArgAttr::NONDEP,
        var: fresh_var.fresh(),
        ty: u8ty.clone(),
      }],
      body: Cfg::default(),
    };
    let cfg = &mut proc.body;
    let bl1 = cfg.new_block(CtxId::ROOT);
    let xs: Vec<_> = (0..2).map(|_| {
      let x = fresh_var.fresh();
      cfg[bl1].stmts.push(Statement::Let(
        LetKind::Let(x, true, None),
        Rc::new(TyKind::Int(u8)),
        RValue::Use(Operand::Const(Box::new(Constant::int(u8, 2.into()))))));
      x
    }).collect();
    let mut it = xs.iter().rev().copied();
    let mut x = it.next().unwrap();
    for y in it {
      let new = fresh_var.fresh();
      cfg[bl1].stmts.push(Statement::Let(
        LetKind::Let(new, true, None),
        Rc::new(TyKind::Int(u8)),
        RValue::Binop(Binop::Add(u8),
          Operand::Copy(Place::local(x)),
          Operand::Copy(Place::local(y)))));
      x = new;
    }
    let y = fresh_var.fresh();
    let bl2ctx = cfg.ctxs.extend(CtxId::ROOT, y, true, (None, u8ty.clone()));
    let bl2 = cfg.new_block(bl2ctx);
    cfg[bl1].terminate(Terminator::Jump(bl2, vec![
      (y, true, Operand::Copy(Place::local(x)))
    ]));
    cfg[bl2].terminate(Terminator::Return(vec![
      (proc.rets[0].var, true, Operand::Copy(Place::local(y)))
    ]));
    println!("before opt:\n{:#?}", proc);
    crate::mir_opt::optimize(&mut proc, &names);
    println!("after opt:\n{:#?}", proc);
    let cfg = &mut proc.body;
    let allocs = cfg.storage(&names);
    println!("after storage:\n{:#?}", cfg);
    println!("allocs = {:#?}", allocs);
    let res = regalloc_vcode(&names, &func_mono, &funcs, &cfg, &allocs, &proc.rets);
    println!("{:#?}", res);
  }
}
