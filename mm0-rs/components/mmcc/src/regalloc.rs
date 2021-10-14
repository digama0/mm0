//! The interface to the [`regalloc2`] register allocator, generating [`PCode`] from [`VCode`].
//!
//! The actual register allocator work is offloaded to the [`regalloc2`] crate,
//! but once we receive the result of register allocation we have to apply the
//! results to construct a [`PCode`], physical register code. This pass also
//! handles concrete code size measurement, so jumps can be replaced by literal
//! relative integers at this point. Globals and constants are not yet located,
//! so they remain symbolic at this stage.

use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};

use mm0_util::u32_as_usize;
use regalloc2::{Allocation, Edit, Function, PReg, ProgPoint, SpillSlot, VReg};

use crate::arch::{AMode, Inst, callee_saved, non_callee_saved, MACHINE_ENV, Offset, PAMode, PInst,
  PRegMem, PRegMemImm, PRegSet, PShiftIndex, RSP, RegMem, RegMemImm};
use crate::mir_opt::storage::Allocations;
use crate::types::{IdxVec, Size};
use crate::types::mir::{Arg, Cfg};
use crate::{Entity, Idx, Symbol};
use crate::build_vcode::{VCode, build_vcode};
use crate::types::vcode::{self, InstId, ProcAbi, ProcId, SpillId, BlockId};

impl<I: vcode::Inst> vcode::VCode<I> {
  fn regalloc(&self) -> regalloc2::Output {
    let opts = regalloc2::RegallocOptions { verbose_log: true };
    regalloc2::run(self, &MACHINE_ENV, &opts).expect("fatal regalloc error")
  }
}

pub(crate) struct ApplyRegalloc {
  num_allocs: usize,
  alloc_iter: std::vec::IntoIter<Allocation>,
  offset_iter: std::vec::IntoIter<u32>,
  regspill_off: u32,
  spill_map: IdxVec<SpillId, u32>,
}

impl ApplyRegalloc {
  fn new(allocs: Vec<Allocation>, offsets: Vec<u32>,
    regspill_off: u32,
    spill_map: IdxVec<SpillId, u32>,
  ) -> Self {
    Self {
      num_allocs: allocs.len(),
      alloc_iter: allocs.into_iter(),
      offset_iter: offsets.into_iter(),
      regspill_off,
      spill_map,
    }
  }

  fn spill(&self, n: SpillSlot) -> PAMode {
    let off = (self.regspill_off + u32::try_from(n.index()).expect("impossible") * 8).into();
    PAMode { base: RSP, si: None, off }
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
    let (off, base) = match (a.off, a.base == VReg::invalid()) {
      (Offset::Spill(sp, n), true) => ((self.spill_map[sp] + n).into(), RSP),
      (off, false) => (off, self.reg()),
      (off, true) => (off, PReg::invalid()),
    };
    let si = a.si.map(|si| PShiftIndex { index: self.reg(), shift: si.shift });
    PAMode { off, base, si }
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
    self.rmi(rmi).unwrap_or(PRegMemImm::Imm(0))
  }
}

mk_id! {
  /// A [`PInst`] ID, which indexes into [`PCode::insts`].
  PInstId(Debug("pi"))
}

#[derive(Debug)]
pub(crate) struct PCode {
  abi: ProcAbi,
  insts: IdxVec<PInstId, PInst>,
  blocks: IdxVec<BlockId, (PInstId, PInstId)>,
  block_addr: IdxVec<BlockId, u32>,
  len: u32,
}

#[derive(Debug)]
struct PCodeBuilder {
  code: PCode,
  fwd_jumps: Vec<(u32, PInstId)>,
}

impl std::ops::Deref for PCodeBuilder {
  type Target = PCode;
  fn deref(&self) -> &Self::Target { &self.code }
}
impl std::ops::DerefMut for PCodeBuilder {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.code }
}

impl PCodeBuilder {
  fn push(&mut self, mut inst: PInst) {
    self.len += u32::from(inst.len());
    if let Some(dst) = inst.is_jump() {
      let addr = self.block_addr.get(dst);
      if let Some(&ub) = self.block_addr.get(dst) {
        if i8::try_from(self.len - ub).is_ok() { inst.shorten() }
        self.insts.push(inst);
      } else {
        self.fwd_jumps.push((self.len, self.code.insts.push(inst)));
      }
    } else {
      self.insts.push(inst);
    }
  }

  fn push_prologue(&mut self, stack_size: u32, saved_regs: impl Iterator<Item=PReg>) {
    self.push(PInst::Binop {
      op: crate::arch::Binop::Sub,
      sz: Size::S64,
      dst: RSP,
      src: PRegMemImm::Imm(stack_size)
    });
    for reg in saved_regs {
      self.push(PInst::Push64 { src: PRegMemImm::Reg(reg) });
    }
  }

  fn push_epilogue(&mut self, stack_size: u32, saved_regs: impl DoubleEndedIterator<Item=PReg>) {
    for dst in saved_regs.rev() {
      self.push(PInst::Pop64 { dst });
    }
    self.push(PInst::Binop {
      op: crate::arch::Binop::Add,
      sz: Size::S64,
      dst: RSP,
      src: PRegMemImm::Imm(stack_size)
    });
    self.push(PInst::Ret)
  }

  fn apply_edits(&mut self,
    edits: &mut std::iter::Peekable<impl Iterator<Item=(ProgPoint, Edit)>>,
    ar: &mut ApplyRegalloc,
    pt: ProgPoint
  ) {
    while edits.peek().map_or(false, |p| p.0 == pt) {
      if let Some((_, Edit::Move { from, to, to_vreg })) = edits.next() {
        match (from.as_reg(), to.as_reg()) {
          (Some(src), Some(dst)) => self.push(PInst::MovRR { sz: Size::S64, dst, src }),
          (Some(src), _) => {
            let dst = ar.spill(to.as_stack().expect("bad regalloc"));
            self.push(PInst::Store { sz: Size::S64, dst, src });
          }
          (_, Some(dst)) => {
            let src = ar.spill(from.as_stack().expect("bad regalloc"));
            self.push(PInst::Load64 { dst, src });
          }
          _ => panic!("bad regalloc")
        }
      }
    }
  }

  fn finish(self) -> PCode {
    let Self {mut code, fwd_jumps, ..} = self;
    for (pos, i) in fwd_jumps {
      let inst = &mut code.insts[i];
      let dst = inst.is_jump().expect("list contains jumps");
      let pos = i32::try_from(pos).expect("overflow");
      let ub = i32::try_from(code.block_addr[dst]).expect("overflow");
      if i8::try_from(pos - ub).is_ok() { inst.shorten() }
    }
    code.block_addr.0.clear();
    code.len = 0;
    let mut iter = code.blocks.0.iter();
    let mut cur = iter.next().expect("nonempty").0;
    for (id, inst) in code.insts.enum_iter() {
      if id == cur {
        code.block_addr.push(code.len);
        if let Some(n) = iter.next() { cur = n.0 }
      }
      code.len += u32::from(inst.len());
    }
    code
  }
}

struct BlockBuilder<'a> {
  blocks: &'a [(InstId, InstId)],
  start: PInstId,
  cur: usize,
  next: InstId,
}

impl<'a> BlockBuilder<'a> {
  fn next(&mut self) {
    self.next = self.blocks.get(self.cur).map_or_else(InstId::invalid, |p| p.1);
  }

  fn new(blocks: &'a [(InstId, InstId)]) -> Self {
    let mut this = Self { blocks, start: PInstId(0), cur: 0, next: InstId(0) };
    this.next();
    this
  }

  fn finish_block(&mut self, code: &mut PCode) {
    let end = PInstId::from_usize(code.insts.len());
    self.cur += 1;
    self.next();
    code.blocks.push((std::mem::replace(&mut self.start, end), end));
  }
}

fn get_clobbers(vcode: &VCode, out: &regalloc2::Output) -> PRegSet {
  let mut result = PRegSet::default();
  for (_, edit) in &out.edits {
    if let Edit::Move { to, .. } = *edit {
      if let Some(r) = to.as_reg() { result.insert(r) }
    }
  }
  for (i, _) in vcode.insts.enum_iter() {
    for &r in vcode.inst_clobbers(i) { result.insert(r) }
    for (op, alloc) in vcode.inst_operands(i).iter().zip(out.inst_allocs(i)) {
      if op.kind() != regalloc2::OperandKind::Use {
        if let Some(r) = alloc.as_reg() { result.insert(r) }
      }
    }
  }
  result
}

#[allow(clippy::similar_names)]
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
  let clobbers = get_clobbers(&vcode, &out);
  let saved_regs = callee_saved().filter(move |&r| clobbers.get(r));
  vcode.abi.clobbers = non_callee_saved().filter(|&r| clobbers.get(r)).collect();
  let mut edits = out.edits.into_iter().peekable();
  for _ in 0..out.num_spillslots { vcode.fresh_spill(8); }
  let stack_size_no_ret;
  let mut ar = if let [incoming, outgoing, ref spills @ ..] = *vcode.spills.0 {
    let mut spill_map = vec![0; vcode.spills.len()];
    let mut rsp_off = outgoing + u32::try_from(out.num_spillslots * 8).expect("overflow");
    for (&n, len) in spills.iter().zip(&mut spill_map[2..]).rev() {
      *len = rsp_off;
      rsp_off += n;
    }
    stack_size_no_ret = rsp_off + u32::try_from(saved_regs.clone().count() * 8).expect("overflow");
    spill_map[0] = stack_size_no_ret + 8;
    ApplyRegalloc::new(out.allocs, out.inst_alloc_offsets, outgoing, spill_map.into())
  } else { unreachable!() };
  let mut code = PCodeBuilder {
    code: PCode {
      abi: vcode.abi,
      insts: IdxVec::new(),
      blocks: IdxVec::from(vec![]),
      block_addr: IdxVec::from(vec![0]),
      len: 0,
    },
    fwd_jumps: vec![],
  };
  let mut bb = BlockBuilder::new(&vcode.blocks.0);
  code.push_prologue(stack_size_no_ret, saved_regs.clone());
  for (i, inst) in vcode.insts.enum_iter() {
    ar.next_inst(i);
    if bb.next == i {
      bb.finish_block(&mut code);
      code.code.block_addr.push(code.len);
    };
    code.apply_edits(&mut edits, &mut ar, ProgPoint::before(i));
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
      Inst::CMov { sz, cc, dst, src1, ref src2 } => {
        let (_, src, dst) = (ar.reg(), ar.rm(src2), ar.reg());
        code.push(PInst::CMov { sz, cc, dst, src });
      }
      Inst::Push64 { ref src } => code.push(PInst::Push64 { src: ar.rmi0(src) }),
      Inst::Pop64 { .. } => code.push(PInst::Pop64 { dst: ar.reg() }),
      Inst::CallKnown { f, ref operands, ref clobbers } => {
        for _ in &**operands { ar.reg(); }
        code.push(PInst::CallKnown { f })
      }
      Inst::Epilogue { ref params } => {
        for _ in &**params { ar.reg(); }
        code.push_epilogue(stack_size_no_ret, saved_regs.clone())
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
    code.apply_edits(&mut edits, &mut ar, ProgPoint::after(i));
  }
  bb.finish_block(&mut code);
  code.finish()
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::wildcard_imports)]
mod test {
  use std::rc::Rc;
  use crate::types::{IntTy, Spanned, hir::ProcKind, mir::*};
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
    let bl2ctx = cfg.ctxs.extend(CtxId::ROOT, y, true, (None, u8ty));
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
    let res = regalloc_vcode(&names, &func_mono, &funcs, cfg, &allocs, &proc.rets);
    println!("{:#?}", res);
  }
}
