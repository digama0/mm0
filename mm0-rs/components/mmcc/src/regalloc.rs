//! The interface to the [`regalloc2`] register allocator, generating [`PCode`] from [`VCode`].
//!
//! The actual register allocator work is offloaded to the [`regalloc2`] crate,
//! but once we receive the result of register allocation we have to apply the
//! results to construct a [`PCode`], physical register code. This pass also
//! handles concrete code size measurement, so jumps can be replaced by literal
//! relative integers at this point. Globals and constants are not yet located,
//! so they remain symbolic at this stage.

use std::collections::HashMap;

use mm0_util::u32_as_usize;
use regalloc2::{Allocation, Edit, Function, ProgPoint, SpillSlot};

use crate::arch::{AMode, Inst, callee_saved, caller_saved, MACHINE_ENV, Offset, PAMode, PInst,
  PRegMem, PRegMemImm, PRegSet, PShiftIndex, RSP, PReg, RegMem, RegMemImm};
use crate::types::classify::Trace;
use crate::types::{IdxVec, Size};
use crate::types::mir;
use crate::Idx;
use crate::build_vcode::VCode;
use crate::types::vcode::{self, IsReg, InstId, ProcAbi, SpillId, BlockId, ChunkVec};

impl<I: vcode::Inst> vcode::VCode<I> {
  fn do_regalloc(&self) -> regalloc2::Output {
    let opts = regalloc2::RegallocOptions {
      verbose_log: true,
      validate_ssa: true,
      algorithm: regalloc2::Algorithm::Ion
    };
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

  fn next_inst(&mut self) {
    assert_eq!(u32_as_usize(self.offset_iter.next().expect("inst align")),
      self.num_allocs - self.alloc_iter.len());
  }

  fn next(&mut self) -> Allocation {
    self.alloc_iter.next().expect("allocation align")
  }

  fn reg(&mut self) -> PReg {
    PReg(self.next().as_reg().expect("expected a register"))
  }
  fn mem(&mut self, a: &AMode) -> PAMode {
    let (off, base) = match (a.off, a.base.is_valid()) {
      (Offset::Spill(sp, n), false) => ((self.spill_map[sp] + n).into(), RSP),
      (off, true) => (off, self.reg()),
      (off, false) => (off, PReg::invalid()),
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

  fn rmi(&mut self, rmi: &RegMemImm) -> PRegMemImm {
    match rmi {
      RegMemImm::Reg(_) => PRegMemImm::Reg(self.reg()),
      RegMemImm::Mem(a) => PRegMemImm::Mem(self.mem(a)),
      RegMemImm::Imm(i) => PRegMemImm::Imm(*i),
    }
  }
}

mk_id! {
  /// A [`PInst`] ID, which indexes into [`PCode::insts`].
  PInstId(Debug("pi"))
}

#[derive(Clone)]
pub(crate) struct PCode {
  pub(crate) insts: IdxVec<PInstId, PInst>,
  pub(crate) block_map: HashMap<mir::BlockId, BlockId>,
  pub(crate) blocks: IdxVec<BlockId, (mir::BlockId, PInstId, PInstId)>,
  pub(crate) block_addr: IdxVec<BlockId, u32>,
  pub(crate) block_params: ChunkVec<BlockId, (mir::VarId, PRegMem)>,
  pub(crate) trace: Trace,
  pub(crate) stack_size: u32,
  pub(crate) saved_regs: Vec<PReg>,
  pub(crate) len: u32,
}

impl PCode {
  pub(crate) fn block_insts(&self, id: BlockId) -> &[PInst] {
    let (_, inst_start, inst_end) = self.blocks[id];
    &self.insts[inst_start..inst_end]
  }
}

impl std::fmt::Debug for PCode {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for (bl, &(_, start, end)) in self.blocks.enum_iter() {
      write!(f, "vb{}(", bl.index())?;
      let mut first = true;
      for (v, m) in &self.block_params[bl] {
        if !std::mem::take(&mut first) { write!(f, ", ")? }
        write!(f, "{v:?} @ {m:?}")?;
      }
      writeln!(f, "):")?;
      for inst in &self.insts[start..end] { writeln!(f, "    {inst:?};")? }
    }
    Ok(())
  }
}

#[derive(Debug)]
struct PCodeBuilder {
  code: Box<PCode>,
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
  fn push(&mut self, mut inst: PInst) -> PInstId {
    self.len += u32::from(inst.len());
    if let Some(dst) = inst.is_jump() {
      if let Some(&ub) = self.block_addr.get(dst) {
        if i8::try_from(self.len - ub).is_ok() { inst.shorten() }
        self.insts.push(inst)
      } else {
        let id = self.code.insts.push(inst);
        self.fwd_jumps.push((self.len, id));
        id
      }
    } else {
      self.insts.push(inst)
    }
  }

  fn push_prologue(&mut self, stack_size: u32, saved_regs: impl Iterator<Item=PReg>) {
    for reg in saved_regs {
      self.push(PInst::Push64 { src: PRegMemImm::Reg(reg) });
    }
    if stack_size != 0 {
      self.push(PInst::Binop {
        op: crate::arch::Binop::Sub,
        sz: Size::S64,
        dst: RSP,
        src: PRegMemImm::Imm(stack_size)
      });
    }
  }

  fn push_epilogue(&mut self, stack_size: u32, saved_regs: impl DoubleEndedIterator<Item=PReg>) {
    if stack_size != 0 {
      self.push(PInst::Binop {
        op: crate::arch::Binop::Add,
        sz: Size::S64,
        dst: RSP,
        src: PRegMemImm::Imm(stack_size)
      });
    }
    for dst in saved_regs.rev() {
      self.push(PInst::Pop64 { dst });
    }
    self.push(PInst::Ret);
  }

  fn apply_edits(&mut self,
    edits: &mut std::iter::Peekable<impl Iterator<Item=(ProgPoint, Edit)>>,
    ar: &ApplyRegalloc,
    pt: ProgPoint
  ) {
    while edits.peek().is_some_and(|p| p.0 == pt) {
      if let Some((_, Edit::Move { from, to, .. })) = edits.next() {
        match (from.as_reg().map(PReg), to.as_reg().map(PReg)) {
          (Some(src), Some(dst)) => { self.push(PInst::MovRR { sz: Size::S64, dst, src }); }
          (Some(src), _) => {
            let dst = ar.spill(to.as_stack().expect("bad regalloc"));
            self.push(PInst::Store { spill: true, sz: Size::S64, dst, src });
          }
          (_, Some(dst)) => {
            let src = ar.spill(from.as_stack().expect("bad regalloc"));
            self.push(PInst::Load64 { spill: true, dst, src });
          }
          _ => panic!("bad regalloc")
        }
      }
    }
  }

  #[allow(clippy::unnecessary_box_returns)]
  fn finish(self, saved_regs: Vec<PReg>) -> Box<PCode> {
    let Self {mut code, fwd_jumps, ..} = self;
    code.saved_regs = saved_regs;
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
    let mut cur = iter.next().expect("nonempty").1;
    for (id, inst) in code.insts.enum_iter() {
      while id == cur {
        code.block_addr.push(code.len);
        if let Some(n) = iter.next() { cur = n.1 } else { break }
      }
      code.len += u32::from(inst.len());
    }
    code
  }
}

struct BlockBuilder<'a> {
  blocks: &'a [(mir::BlockId, InstId, InstId)],
  start: PInstId,
  cur: usize,
  next_id: mir::BlockId,
  next: InstId,
}

impl<'a> BlockBuilder<'a> {
  fn next(&mut self) {
    match self.blocks.get(self.cur) {
      Some(&(id, _, next)) => { self.next_id = id; self.next = next }
      None => self.next = InstId::invalid()
    }
  }

  fn new(blocks: &'a [(mir::BlockId, InstId, InstId)]) -> Self {
    let mut this = Self {
      blocks, start: PInstId(0), cur: 0, next_id: mir::BlockId(0), next: InstId(0)
    };
    this.next();
    this
  }

  fn finish_block(&mut self, code: &mut PCode) {
    let end = PInstId::from_usize(code.insts.len());
    self.cur += 1;
    let id = self.next_id;
    self.next();
    code.blocks.push((id, std::mem::replace(&mut self.start, end), end));
  }
}

fn get_clobbers(vcode: &VCode, out: &regalloc2::Output) -> PRegSet {
  let mut result = PRegSet::default();
  for (_, edit) in &out.edits {
    let Edit::Move { to, .. } = *edit;
    if let Some(r) = to.as_reg() { result.insert(PReg(r)) }
  }
  for (i, _) in vcode.insts.enum_iter() {
    use crate::types::vcode::Inst;
    result |= vcode.insts[i].clobbers();
    for (op, alloc) in vcode.inst_operands(i).iter().zip(out.inst_allocs(i)) {
      if op.kind() != regalloc2::OperandKind::Use {
        if let Some(r) = alloc.as_reg() { result.insert(PReg(r)) }
      }
    }
  }
  for abi in &*vcode.abi.args {
    if let vcode::ArgAbi::Reg(reg, _) | vcode::ArgAbi::Boxed {reg, ..} = *abi {
      result.remove(reg)
    }
  }
  for abi in &*vcode.abi.rets {
    if let vcode::ArgAbi::Reg(r, _) = *abi { result.remove(r) }
  }
  result
}

impl VCode {
  #[allow(clippy::similar_names)]
  pub(crate) fn regalloc(mut self) -> (ProcAbi, Box<PCode>) {
    // drop(simplelog::SimpleLogger::init(simplelog::LevelFilter::Trace, simplelog::Config::default()));
    // eprintln!("{:#?}", self);
    let out = self.do_regalloc();
    // eprintln!("{:#?}", out);
    let clobbers = get_clobbers(&self, &out);
    let saved_regs = callee_saved().filter(move |&r| clobbers.get(r)).collect::<Vec<_>>();
    self.abi.clobbers = caller_saved().filter(|&r| clobbers.get(r)).collect();
    let mut edits = out.edits.into_iter().peekable();
    for _ in 0..out.num_spillslots { self.fresh_spill(8); }
    let stack_size_no_ret;
    let mut ar = if let [_incoming, outgoing, ref spills @ ..] = *self.spills.0 {
      let mut spill_map = vec![0; self.spills.len()];
      let mut rsp_off = outgoing + u32::try_from(out.num_spillslots * 8).expect("overflow");
      for (&n, len) in spills.iter().zip(&mut spill_map[2..]).rev() {
        *len = rsp_off;
        rsp_off += n;
      }
      stack_size_no_ret = rsp_off + u32::try_from(saved_regs.len() * 8).expect("overflow");
      spill_map[0] = stack_size_no_ret + 8;
      ApplyRegalloc::new(out.allocs, out.inst_alloc_offsets, outgoing, spill_map.into())
    } else { unreachable!() };
    let mut code = PCodeBuilder {
      code: Box::new(PCode {
        insts: IdxVec::new(),
        block_map: self.block_map,
        blocks: IdxVec::from(vec![]),
        block_addr: IdxVec::from(vec![0]),
        block_params: std::iter::once([]).collect(),
        trace: self.trace,
        stack_size: stack_size_no_ret,
        saved_regs: vec![],
        len: 0,
      }),
      fwd_jumps: vec![],
    };
    let mut bb = BlockBuilder::new(&self.blocks.0);
    code.push_prologue(stack_size_no_ret, saved_regs.iter().copied());
    // let mut last_let_start = Default::default();
    for (i, inst) in self.insts.enum_iter() {
      ar.next_inst();
      if bb.next == i {
        bb.finish_block(&mut code);
        code.block_params.push_new();
        code.code.block_addr.push(code.len);
      }
      code.apply_edits(&mut edits, &ar, ProgPoint::before(i));
      match *inst {
        Inst::Fallthrough { dst } => {
          assert!(self.blocks[dst].1 == i.next());
          code.push(PInst::Fallthrough { dst });
        }
        // Inst::LetStart { size } =>
        //   last_let_start = code.push(PInst::LetStart { size, dst: Default::default() }),
        // Inst::LetEnd { dst: ref vdst } => {
        //   if let PInst::LetStart { dst, .. } = &mut code.insts[last_let_start] {
        //     *dst = ar.rm(vdst)
        //   } else { unreachable!() }
        // }
        Inst::BlockParam { var, ref val } => {
          code.block_params.extend_last((var, ar.rm(val)))
        }
        Inst::Binop { op, sz, ref src2, .. } => {
          let (_, src, dst) = (ar.reg(), ar.rmi(src2), ar.reg());
          code.push(PInst::Binop { op, sz, dst, src });
        }
        Inst::Unop { op, sz, .. } => {
          let (_, dst) = (ar.reg(), ar.reg());
          code.push(PInst::Unop { op, sz, dst });
        }
        // Inst::DivRem { sz, ref src2, .. } => {
        //   let (_, src, _, _) = (ar.next(), ar.rm(src2), ar.next(), ar.next());
        //   code.push(PInst::Cdx { sz });
        //   code.push(PInst::DivRem { sz, src });
        // }
        Inst::Mul { sz, ref src2, .. } => {
          let (_, src, _, _) = (ar.next(), ar.rm(src2), ar.next(), ar.next());
          code.push(PInst::Mul { sz, src });
        }
        Inst::Imm { sz, src, .. } => { code.push(PInst::Imm { sz, dst: ar.reg(), src }); }
        Inst::MovId => { code.push(PInst::MovId); }
        // Inst::MovRR { .. } => { code.push(PInst::MovId); }
        // Inst::MovRP { .. } |
        Inst::MovPR { .. } => { ar.next(); code.push(PInst::MovId); }
        Inst::MovzxRmR { ext_mode, ref src, .. } => {
          code.push(PInst::MovzxRmR { ext_mode, src: ar.rm(src), dst: ar.reg() });
        }
        Inst::Load64 { ref src, .. } => {
          code.push(PInst::Load64 { spill: false, src: ar.mem(src), dst: ar.reg() });
        }
        Inst::Lea { sz, ref addr, .. } => {
          code.push(PInst::Lea { sz, addr: ar.mem(addr), dst: ar.reg() });
        }
        Inst::MovsxRmR { ext_mode, ref src, .. } => {
          code.push(PInst::MovsxRmR { ext_mode, src: ar.rm(src), dst: ar.reg() });
        }
        Inst::Store { sz, ref dst, .. } => {
          code.push(PInst::Store { spill: false, sz, src: ar.reg(), dst: ar.mem(dst) });
        }
        Inst::ShiftImm { sz, kind, num_bits, .. } => {
          let (_, dst) = (ar.next(), ar.reg());
          code.push(PInst::Shift { sz, kind, num_bits: Some(num_bits), dst });
        }
        Inst::ShiftRR { sz, kind, .. } => {
          let (_, _, dst) = (ar.next(), ar.next(), ar.reg());
          code.push(PInst::Shift { sz, kind, num_bits: None, dst });
        }
        Inst::Cmp { sz, op, ref src2, .. } => {
          code.push(PInst::Cmp { sz, op, src1: ar.reg(), src2: ar.rmi(src2) });
        }
        Inst::SetCC { cc, .. } => { code.push(PInst::SetCC { cc, dst: ar.reg() }); }
        Inst::CMov { sz, cc, ref src2, .. } => {
          let (_, src, dst) = (ar.reg(), ar.rm(src2), ar.reg());
          code.push(PInst::CMov { sz, cc, dst, src });
        }
        Inst::CallKnown { f, ref operands, .. } => {
          for _ in &**operands { ar.next(); }
          code.push(PInst::CallKnown { f });
        }
        Inst::SysCall { ref operands, .. } => {
          for _ in &**operands { ar.next(); }
          code.push(PInst::SysCall);
        }
        Inst::Epilogue { ref params } => {
          for _ in &**params { ar.next(); }
          code.push_epilogue(stack_size_no_ret, saved_regs.iter().copied())
        }
        Inst::JmpKnown { dst, .. } =>
          if self.blocks[dst].1 == i.next() {
            code.push(PInst::Fallthrough { dst });
          } else {
            code.push(PInst::JmpKnown { dst, short: false });
          },
        Inst::JmpCond { cc, taken, not_taken } =>
          if self.blocks[not_taken].1 == i.next() {
            code.push(PInst::JmpCond { cc, dst: taken, short: false });
            code.push(PInst::Fallthrough { dst: not_taken });
          } else if self.blocks[taken].1 == i.next() {
            code.push(PInst::JmpCond { cc: cc.invert(), dst: not_taken, short: false });
            code.push(PInst::Fallthrough { dst: taken });
          } else {
            code.push(PInst::JmpCond { cc, dst: taken, short: false });
            code.push(PInst::JmpKnown { dst: not_taken, short: false });
          },
        Inst::Assert { cc, dst } => {
          assert!(self.blocks[dst].1 == i.next());
          code.push(PInst::Assert { cc, dst });
        }
        Inst::Ud2 => { code.push(PInst::Ud2); }
      }
      code.apply_edits(&mut edits, &ar, ProgPoint::after(i));
    }
    bb.finish_block(&mut code);
    (self.abi, code.finish(saved_regs))
  }
}
