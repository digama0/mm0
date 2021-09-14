use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::ops::Mul;

use num::BigInt;
use regalloc2::Operand as ROperand;

use crate::types::entity::ConstTc;
use crate::{Symbol, Entity};
use crate::arch::{AMode, Binop as VBinop, CC, Cmp, ExtMode,
  GhostInst, Imm, Inst, RegMem, RegMemImm, ShiftKind, Unop as VUnop};
use crate::mir_opt::BitSet;
use crate::mir_opt::storage::{Allocations, AllocId};
use crate::types::{IdxVec, IntTy, Size, Spanned};
use crate::types::vcode::{self, ArgAbi, BlockId as VBlockId,
  ChunkVec, InstId, ProcId, ProcAbi, RegClass, SpillId, VReg};

#[allow(clippy::wildcard_imports)]
use crate::types::mir::*;

type VCode = vcode::VCode<Inst>;

/// A very simple jump threading visitor. Start at an unvisited basic block, then follow forward
/// edges to unvisited basic blocks as long as possible. Then start over somewhere else.
/// This ordering is good for code placement since a jump or branch to the immediately following
/// block can be elided.
fn visit_blocks(cfg: &Cfg, mut f: impl FnMut(BlockId, &BasicBlock)) {
  let mut visited: BitSet<BlockId> = BitSet::default();
  for (mut i, mut bl) in cfg.blocks() {
    if visited.insert(i) && !bl.is_dead() {
      while let Some((_, j)) = {
        f(i, bl);
        bl.successors().find(|&(_, j)| visited.insert(j))
      } {
        i = j;
        bl = &cfg[i];
      }
    }
  }
}

struct TyCtx<'a> {
  cfg: &'a Cfg,
  ctx: HashMap<VarId, Ty>,
}

impl<'a> TyCtx<'a> {
  fn new(cfg: &'a Cfg) -> Self { Self { cfg, ctx: Default::default() } }

  fn insert(&mut self, v: VarId, ty: Ty) { self.ctx.insert(v, ty); }

  fn start_block(&mut self, bl: &BasicBlock) {
    self.ctx.clear();
    for (v, _, (_, ty)) in bl.ctx_rev_iter(&self.cfg.ctxs) {
      self.insert(v, ty.clone());
    }
  }
}

struct LowerCtx<'a> {
  cfg: &'a Cfg,
  allocs: &'a Allocations,
  names: &'a HashMap<Symbol, Entity>,
  func_mono: &'a HashMap<Symbol, ProcId>,
  funcs: &'a IdxVec<ProcId, ProcAbi>,
  code: VCode,
  var_map: HashMap<AllocId, (RegMem, Size)>,
  block_map: HashMap<BlockId, VBlockId>,
  rets: &'a [VReg],
  ctx: TyCtx<'a>,
  unpatched: Vec<(VBlockId, InstId)>,
}

impl<'a> LowerCtx<'a> {
  /// Create a new lowering context.
  fn new(
    names: &'a HashMap<Symbol, Entity>,
    func_mono: &'a HashMap<Symbol, ProcId>,
    funcs: &'a IdxVec<ProcId, ProcAbi>,
    cfg: &'a Cfg,
    allocs: &'a Allocations,
  ) -> Self {
    LowerCtx {
      cfg,
      allocs,
      names,
      func_mono,
      funcs,
      code: VCode::default(),
      block_map: HashMap::new(),
      rets: &[],
      var_map: HashMap::new(),
      ctx: TyCtx::new(cfg),
      unpatched: vec![],
    }
  }

  fn emit(&mut self, inst: Inst) -> InstId { self.code.emit(inst) }

  fn get_alloc(&mut self, a: AllocId) -> (&(RegMem, Size), u64) {
    assert_ne!(a, AllocId::ZERO);
    let code = &mut self.code;
    let m = self.allocs[a].m;
    (self.var_map.entry(a).or_insert_with(|| {
      let rm = if m.on_stack {
        RegMem::Mem(AMode::spill(code.fresh_spill()))
      } else {
        RegMem::Reg(code.fresh_vreg())
      };
      (rm, Size::from_u64(m.size))
    }), m.size)
  }

  fn get_var(&self, v: VarId) -> &(RegMem, Size) {
    let a = self.allocs.get(v);
    assert!(a != AllocId::ZERO);
    &self.var_map[&a]
  }

  fn get_place(&mut self, p: &Place) -> RegMem {
    let mut rm = self.get_var(p.local).0;
    for proj in &p.proj {
      match proj.1 {
        Projection::Deref =>
          rm = RegMem::Mem(rm.emit_deref(&mut self.code, Size::S64)),
        Projection::Proj(ListKind::And | ListKind::Sn, _) => {}
        Projection::Proj(ListKind::Array, i) => {
          let ty = if let TyKind::Array(ty, _) = &*proj.0 { ty } else { unreachable!() };
          let sz = ty.sizeof(self.names)
            .expect("array element size not known at compile time");
          let off = u32::try_from(sz).expect("overflow") * i;
          if off != 0 {
            match &mut rm {
              RegMem::Reg(_) => panic!("register should be address-taken"),
              RegMem::Mem(a) => *a = &*a + off,
            }
          }
        }
        Projection::Proj(ListKind::Struct, i) => {
          let args = if let TyKind::Struct(args) = &*proj.0 { args } else { unreachable!() };
          let off = args[..i as usize].iter().map(|arg| {
            if arg.attr.contains(ArgAttr::GHOST) { return 0 }
            let sz = arg.ty.sizeof(self.names)
              .expect("struct element size not known at compile time");
            u32::try_from(sz).expect("overflow")
          }).sum();
          if off != 0 {
            match &mut rm {
              RegMem::Reg(_) => panic!("register should be address-taken"),
              RegMem::Mem(a) => *a = &*a + off,
            }
          }
        }
        Projection::Index(i, _) |
        Projection::Slice(i, _, _) => {
          let ty = if let TyKind::Array(ty, _) = &*proj.0 { ty } else { unreachable!() };
          let stride = if let Some(sz) = ty.sizeof(self.names) { sz } else {
            panic!("array stride not known at compile time")
          };
          if stride != 0 {
            let (v, sz) = *self.get_var(i);
            let v = v.into_reg(&mut self.code, sz);
            match &mut rm {
              RegMem::Reg(_) => panic!("register should be address-taken"),
              RegMem::Mem(a) => *a = a.add_scaled(&mut self.code, stride, v),
            }
          }
        }
      }
    }
    rm
  }

  fn get_const_64(&mut self, c: &Constant) -> u64 {
    match c.k {
      ConstKind::Bool => {
        let_unchecked!(e as Some(e) = &c.ety.0);
        let_unchecked!(ExprKind::Bool(b) = **e, b.into())
      }
      ConstKind::Int => {
        let_unchecked!(e as Some(e) = &c.ety.0);
        let_unchecked!(n as ExprKind::Int(n) = &**e);
        if let Ok(n) = u64::try_from(n) { n }
        else { (n & BigInt::from(u64::MAX)).try_into().expect("impossible") }
      }
      ConstKind::Uninit => 0,
      ConstKind::Const(c) => if_chain! {
        if let Some(Entity::Const(tc)) = self.names.get(&c);
        if let ConstTc::Checked { imm64: Some(imm), .. } = tc.k;
        then { imm }
        else { panic!("cannot resolve constant to an integer value") }
      },
      ConstKind::Sizeof => {
        let_unchecked!(e as Some(e) = &c.ety.0);
        let_unchecked!(ty as ExprKind::Sizeof(ref ty) = **e);
        ty.sizeof(self.names).expect("size must be known at compile time")
      }
      ConstKind::Unit |
      ConstKind::ITrue |
      ConstKind::Mm0Proof(_) |
      ConstKind::Contra(_, _) => unreachable!("unexpected ZST"),
      ConstKind::As(ref c) => {
        let n = self.get_const_64(&c.0);
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss, clippy::cast_lossless)]
        match c.1 {
          IntTy::Int(Size::S8) => n as i8 as u64,
          IntTy::Int(Size::S16) => n as i16 as u64,
          IntTy::Int(Size::S32) => n as i32 as u64,
          IntTy::UInt(Size::S8) => n as u8 as u64,
          IntTy::UInt(Size::S16) => n as u16 as u64,
          IntTy::UInt(Size::S32) => n as u32 as u64,
          _ => n,
        }
      }
    }
  }

  fn get_operand(&mut self, o: &Operand) -> RegMemImm<u64> {
    match o.place() {
      Ok(p) => self.get_place(p).into(),
      Err(c) => Imm::Real(self.get_const_64(c)).into(),
    }
  }

  fn get_operand_reg(&mut self, o: &Operand, sz: Size) -> VReg {
    self.get_operand(o).into_reg(&mut self.code, sz)
  }

  fn get_operand_rm(&mut self, o: &Operand, sz: Size) -> RegMem {
    self.get_operand(o).into_rm(&mut self.code, sz)
  }

  fn get_operand_32(&mut self, o: &Operand) -> RegMemImm {
    self.get_operand(o).into_rmi_32(&mut self.code)
  }

  fn build_shift_or_zero(&mut self,
    sz: Size, dst: RegMem, kind: ShiftKind, o1: &Operand, o2: &Operand
  ) {
    let bits = sz.bits().expect("unbounded");
    let src1 = self.get_operand_reg(o1, sz);
    let temp = match self.get_operand(o2) {
      RegMemImm::Imm(Imm::Real(n)) => {
        if n >= bits.into() { self.code.emit_copy(sz, dst, 0_u64); return }
        #[allow(clippy::cast_possible_truncation)]
        self.code.emit_shift(sz, kind, src1, Ok(n as u8))
      }
      src2 => {
        let src2 = src2.into_reg(&mut self.code, sz);
        let temp = self.code.emit_shift(sz, kind, src1, Err(src2));
        let zero = self.code.emit_imm(sz, 0);
        let cond = self.code.emit_cmp(sz, Cmp::Cmp, CC::NB, src1, u32::from(bits));
        cond.select(sz, zero, temp)
      }
    };
    self.code.emit_copy(sz, dst, temp);
  }

  fn build_binop(&mut self, sz: Size, dst: RegMem, op: VBinop, o1: &Operand, o2: &Operand) {
    assert_ne!(sz, Size::Inf);
    let src1 = self.get_operand_reg(o1, sz);
    let src2 = self.get_operand_32(o2);
    let temp = self.code.emit_binop(sz, op, src1, src2);
    self.code.emit_copy(sz, dst, temp);
}

  fn build_cmp(&mut self, sz: Size, dst: RegMem, cc: CC, o1: &Operand, o2: &Operand) {
    assert_ne!(sz, Size::Inf);
    let src1 = self.get_operand_reg(o1, sz);
    let src2 = self.get_operand_32(o2);
    let temp = self.code.emit_cmp(sz, Cmp::Cmp, cc, src1, src2).into_reg();
    self.code.emit_copy(Size::S8, dst, temp);
  }

  fn build_as(&mut self, dst: RegMem, from: IntTy, to: IntTy, o: &Operand) {
    let sz = from.size().min(to.size()); assert_ne!(sz, Size::Inf);
    let src = self.get_operand(o).into_rm(&mut self.code, sz);
    match ExtMode::new(sz, Size::S64) {
      None => self.code.emit_copy(sz, dst, src),
      Some(ext_mode) => {
        let temp = self.code.fresh_vreg();
        self.code.emit(match to.signed() {
          true => Inst::MovsxRmR { ext_mode, dst: temp, src },
          false => Inst::MovzxRmR { ext_mode, dst: temp, src },
        });
        self.code.emit_copy(to.size(), dst, temp);
      }
    }
  }

  fn build_memcpy(&mut self, tysize: u64, sz: Size, dst: RegMem, src: AMode) {
    if sz == Size::Inf {
      unimplemented!("large copy");
    } else {
      self.code.emit_copy(sz, dst, src);
    }
  }

  fn build_move(&mut self, tysize: u64, sz: Size, dst: RegMem, o: &Operand) {
    if sz == Size::Inf {
      unimplemented!("large copy");
    } else {
      let src = self.get_operand(o);
      self.code.emit_copy(sz, dst, src);
    }
  }

  fn build_rvalue(&mut self, ty: &TyKind, tysize: u64, sz: Size, dst: RegMem, rv: &RValue) {
    match rv {
      RValue::Use(o) => self.build_move(tysize, sz, dst, o),
      RValue::Unop(Unop::Not, o) => {
        assert_ne!(sz, Size::Inf);
        let src = self.get_operand_reg(o, sz);
        let temp = self.code.emit_binop(sz, VBinop::Xor, src, 1);
        self.code.emit_copy(sz, dst, temp);
      }
      RValue::Unop(Unop::Neg(_), o) => {
        assert_ne!(sz, Size::Inf);
        let src = self.get_operand_reg(o, sz);
        let temp = self.code.emit_unop(sz, VUnop::Neg, src);
        self.code.emit_copy(sz, dst, temp);
      }
      RValue::Unop(Unop::BitNot(_), o) => {
        assert_ne!(sz, Size::Inf);
        let src = self.get_operand_reg(o, sz);
        let temp = self.code.emit_unop(sz, VUnop::Not, src);
        self.code.emit_copy(sz, dst, temp);
      }
      &RValue::Unop(Unop::As(from, to), ref o) => self.build_as(dst, from, to, o),
      RValue::Binop(Binop::Add(ity), o1, o2) =>
        self.build_binop(ity.size(), dst, VBinop::Add, o1, o2),
      RValue::Binop(Binop::Mul(ity), o1, o2) => {
        let sz = ity.size(); assert_ne!(sz, Size::Inf);
        let src1 = self.get_operand_reg(o1, sz);
        let src2 = self.get_operand_rm(o2, sz);
        let temp = self.code.emit_mul(sz, src1, src2).0;
        self.code.emit_copy(sz, dst, temp);
      }
      RValue::Binop(Binop::Sub(ity), o1, o2) =>
        self.build_binop(ity.size(), dst, VBinop::Sub, o1, o2),
      RValue::Binop(Binop::Max(ity), o1, o2) => {
        let sz = ity.size(); assert_ne!(sz, Size::Inf);
        let src1 = self.get_operand_reg(o1, sz);
        let src2 = self.get_operand_reg(o2, sz);
        let cc = if ity.signed() { CC::LE } else { CC::BE };
        let cond = self.code.emit_cmp(sz, Cmp::Cmp, cc, src1, src2);
        let temp = cond.select(sz, src2, src1);
        self.code.emit_copy(sz, dst, temp);
      }
      RValue::Binop(Binop::Min(ity), o1, o2) => {
        let sz = ity.size(); assert_ne!(sz, Size::Inf);
        let src1 = self.get_operand_reg(o1, sz);
        let src2 = self.get_operand_reg(o2, sz);
        let cc = if ity.signed() { CC::LE } else { CC::BE };
        let cond = self.code.emit_cmp(sz, Cmp::Cmp, cc, src1, src2);
        let temp = cond.select(sz, src1, src2);
        self.code.emit_copy(sz, dst, temp);
      }
      RValue::Binop(Binop::And, o1, o2) =>
        self.build_binop(Size::S8, dst, VBinop::And, o1, o2),
      RValue::Binop(Binop::Or, o1, o2) =>
        self.build_binop(Size::S8, dst, VBinop::Or, o1, o2),
      RValue::Binop(Binop::BitAnd(ity), o1, o2) =>
        self.build_binop(ity.size(), dst, VBinop::And, o1, o2),
      RValue::Binop(Binop::BitOr(ity), o1, o2) =>
        self.build_binop(ity.size(), dst, VBinop::Or, o1, o2),
      RValue::Binop(Binop::BitXor(ity), o1, o2) =>
        self.build_binop(ity.size(), dst, VBinop::Xor, o1, o2),
      RValue::Binop(Binop::Shl(_), o1, o2) =>
        self.build_shift_or_zero(sz, dst, ShiftKind::Shl, o1, o2),
      RValue::Binop(Binop::Shr(ity), o1, o2) => {
        let kind = if ity.signed() { ShiftKind::ShrA } else { ShiftKind::ShrL };
        self.build_shift_or_zero(sz, dst, kind, o1, o2)
      }
      RValue::Binop(Binop::Lt(ity), o1, o2) =>
        self.build_cmp(ity.size(), dst, if ity.signed() { CC::L } else { CC::B }, o1, o2),
      RValue::Binop(Binop::Le(ity), o1, o2) =>
        self.build_cmp(ity.size(), dst, if ity.signed() { CC::LE } else { CC::BE }, o1, o2),
      RValue::Binop(Binop::Eq(ity), o1, o2) => self.build_cmp(ity.size(), dst, CC::Z, o1, o2),
      RValue::Binop(Binop::Ne(ity), o1, o2) => self.build_cmp(ity.size(), dst, CC::NZ, o1, o2),
      &RValue::Eq(ref ty, invert, ref o1, ref o2) => {
        let meta = ty.meta(self.names).expect("size of type not a compile time constant");
        let sz = Size::from_u64(meta.size);
        if meta.on_stack {
          unimplemented!("memcmp")
        } else {
          self.build_cmp(sz, dst, if invert { CC::NZ } else { CC::Z }, o1, o2)
        }
      }
      RValue::Pun(..) => unreachable!("handled in build()"),
      RValue::Cast(_, o, tyin) =>
        if let (Some(from), Some(to)) = (tyin.as_int_ty(), ty.as_int_ty()) {
          self.build_as(dst, from, to, o);
        } else {
          unimplemented!("casting between non-integral types")
        },
      RValue::List(os) => {
        let args = if let TyKind::Struct(args) = ty { args } else { unreachable!() };
        assert_eq!(args.len(), os.len());
        let mut rm = dst;
        let mut last_off = 0;
        for (arg, o) in args.iter().zip(&**os) {
          if arg.attr.contains(ArgAttr::GHOST) { continue }
          let sz = arg.ty.sizeof(self.names)
            .expect("struct element size not known at compile time");
          if sz != 0 {
            if last_off != 0 {
              match &mut rm {
                RegMem::Reg(_) => panic!("register should be address-taken"),
                RegMem::Mem(a) => *a = &*a + u32::try_from(last_off).expect("overflow")
              }
            }
            last_off = sz;
            self.build_move(sz, Size::from_u64(sz), rm, o);
          }
        }
      }
      RValue::Array(os) => if let [ref o] = **os {
        self.build_move(tysize, sz, dst, o)
      } else {
        let ty = if let TyKind::Array(ty, _) = ty { ty } else { unreachable!() };
        let sz64 = ty.sizeof(self.names).expect("impossible");
        if sz64 != 0 {
          let sz32 = u32::try_from(sz64).expect("overflow");
          let sz = Size::from_u64(sz64);
          let mut a = match dst {
            RegMem::Reg(_) => panic!("register should be address-taken"),
            RegMem::Mem(a) => a
          };
          for o in &**os {
            self.build_move(sz64, sz, RegMem::Mem(a), o);
            a = &a + sz32;
          }
        }
      }
      RValue::Ghost(_) |
      RValue::Mm0(_) |
      RValue::Typeof(_) => {}
      RValue::Borrow(p) => {
        let temp = match self.get_place(p) {
          RegMem::Reg(_) => panic!("register should be address-taken"),
          RegMem::Mem(a) => self.code.emit_lea(a),
        };
        self.code.emit_copy(sz, dst, temp);
      }
    }
  }

  fn build_block_params(&mut self, params: &[VReg], args: &[(VarId, bool, Operand)]) {
    let mut params_it = params.iter().peekable();
    for &(v, r, ref o) in args {
      if !r { continue }
      let a = self.allocs.get(v);
      if a == AllocId::ZERO { continue }
      let (&(dst, sz), size) = self.get_alloc(a);
      self.build_move(size, sz, dst, o);
      if let RegMem::Reg(v) = dst {
        if params_it.peek() == Some(&&v) { params_it.next(); }
      }
    }
    assert!(params_it.peek().is_none());
  }

  fn build_call(&mut self,
    vbl: VBlockId,
    f: ProcId,
    args: &[(bool, Operand)],
    reach: bool,
    tgt: BlockId,
    rets: &[VarId],
  ) {
    let fabi = &self.funcs[f];
    let outgoing = AMode::spill(SpillId::OUTGOING);
    let mut operands = vec![];
    for (arg, &(r, ref o)) in fabi.args.iter().zip(args) {
      if !r { continue }
      match *arg {
        ArgAbi::Ghost => {}
        ArgAbi::Reg(reg, sz) => {
          let src = self.get_operand(o);
          let temp = self.code.fresh_vreg();
          self.code.emit_copy(sz, temp.into(), src);
          operands.push(ROperand::reg_fixed_use(temp, reg));
        }
        ArgAbi::Mem { off, sz } => {
          let sz64 = sz.into();
          self.build_move(sz64, Size::from_u64(sz64), (&outgoing + off).into(), o);
        }
        ArgAbi::Boxed { reg, sz } => {
          let sz64 = sz.into();
          let sz = Size::from_u64(sz64);
          let src = self.get_operand(o).into_mem(&mut self.code, sz);
          let temp = self.code.emit_lea(src);
          operands.push(ROperand::reg_fixed_use(temp, reg));
        }
        ArgAbi::BoxedMem { off, sz } => {
          let sz64 = sz.into();
          let sz = Size::from_u64(sz64);
          let src = self.get_operand(o).into_mem(&mut self.code, sz);
          let temp = self.code.emit_lea(src);
          self.code.emit_copy(Size::S64, (&outgoing + off).into(), temp);
        }
      }
    }
    if let Some(ref retabi) = fabi.rets {
      assert!(reach);
      let mut boxes = vec![];
      let mut ret_regs = vec![];
      for (arg, &v) in retabi.iter().zip(rets) {
        if let ArgAbi::Reg(reg, _) = *arg {
          let src = self.code.fresh_vreg();
          operands.push(ROperand::reg_fixed_def(src, reg));
          ret_regs.push(src);
        }
        if let ArgAbi::Boxed {..} | ArgAbi::BoxedMem {..} = arg {
          let a = self.allocs.get(v);
          if a == AllocId::ZERO { continue }
          let (&(dst, sz), size) = self.get_alloc(a);
          let addr = match dst {
            RegMem::Reg(r) => {
              let a = AMode::spill(self.code.fresh_spill());
              boxes.push((sz, r, a));
              a
            }
            RegMem::Mem(a) => a,
          };
          let temp = self.code.emit_lea(addr);
          match *arg {
            ArgAbi::Boxed { reg, .. } =>
              operands.push(ROperand::reg_fixed_use(temp, reg)),
            ArgAbi::BoxedMem { off, .. } =>
              self.code.emit_copy(Size::S64, (&outgoing + off).into(), temp),
            _ => unreachable!()
          }
        }
      }
      self.emit(Inst::CallKnown {
        f,
        operands: operands.into(),
        clobbers: Some(fabi.clobbers.clone()),
      });
      let mut ret_regs = ret_regs.into_iter();
      for (arg, &v) in retabi.iter().zip(rets) {
        let a = self.allocs.get(v);
        if a == AllocId::ZERO { continue }
        let (&(dst, sz), size) = self.get_alloc(a);
        match *arg {
          ArgAbi::Reg(_, sz) =>
            self.code.emit_copy(sz, dst, ret_regs.next().expect("pushed")),
          ArgAbi::Mem { off, sz } => {
            let sz64 = sz.into();
            self.build_memcpy(sz64, Size::from_u64(sz64), dst, &outgoing + off);
          }
          _ => {}
        }
      }
      for (sz, dst, a) in boxes { self.code.emit_copy(sz, dst.into(), a); }
      self.unpatched.push((vbl, self.code.emit(Inst::Ghost(GhostInst::Fallthrough {
        dst: VBlockId(tgt.0),
      }))));
    } else {
      self.emit(Inst::CallKnown { f, operands: operands.into(), clobbers: None });
    }
  }

  fn build_terminator(&mut self,
    block_args: &ChunkVec<BlockId, VReg>, vbl: VBlockId, term: &Terminator
  ) {
    match *term {
      Terminator::Jump(tgt, ref args) => {
        let params = &block_args[tgt];
        self.build_block_params(params, args);
        self.unpatched.push((vbl, self.code.emit(Inst::JmpKnown {
          dst: VBlockId(tgt.0),
          params: params.iter().map(|&v| ROperand::reg_use(v)).collect()
        })))
      }
      Terminator::Jump1(tgt) =>
        self.unpatched.push((vbl, self.code.emit(Inst::Ghost(GhostInst::Fallthrough {
          dst: VBlockId(tgt.0)
        })))),
      Terminator::Return(ref args) => {
        self.build_block_params(self.rets, args);
        self.code.emit(Inst::Ret);
      }
      Terminator::If(ref o, [(_, bl1), (_, bl2)]) => {
        let src = self.get_operand_reg(o, Size::S8);
        let cond = self.code.emit_cmp(Size::S8, Cmp::Cmp, CC::NZ, src, 0_u32);
        self.unpatched.push((vbl, cond.branch(VBlockId(bl1.0), VBlockId(bl2.0))));
      }
      Terminator::Assert(ref o, _, true, _) => {
        let src = self.get_operand_reg(o, Size::S8);
        self.code.emit_cmp(Size::S8, Cmp::Cmp, CC::NZ, src, 0_u32).trap_if();
      }
      Terminator::Assert(_, _, false, _) => { self.code.emit(Inst::Ud2); }
      Terminator::Call { f, se, ref tys, ref args, reach, tgt, ref rets } => {
        if !tys.is_empty() { unimplemented!("monomorphization") }
        let f = *self.func_mono.get(&f).expect("function ABI not found");
        self.build_call(vbl, f, args, reach, tgt, rets)
      }
      Terminator::Unreachable(_) |
      Terminator::Dead => unreachable!(),
    }
  }

  fn build_block_args(&mut self, rets_out: &'a mut Vec<VReg>, rets: &[Arg]
  ) -> ChunkVec<BlockId, VReg> {
    let preds = self.cfg.predecessors();

    let allocs = self.allocs;
    let cfg = self.cfg;
    let mut insert = |out: &mut Vec<_>, v| {
      let a = allocs.get(v);
      if a != AllocId::ZERO {
        if let RegMem::Reg(v) = self.get_alloc(a).0 .0 {
          if !out.contains(&v) { out.push(v) }
        }
      }
    };

    let block_args = cfg.blocks.enum_iter().map(|(i, bl)| {
      let mut out = vec![];
      if i == BlockId::ENTRY {
        for &(v, b, _) in cfg.ctxs.rev_iter(bl.ctx) { if b { insert(&mut out, v) } }
        out.reverse()
      } else if !bl.is_dead() {
        for &(e, j) in &preds[i] {
          if !matches!(e, Edge::Jump) { continue }
          let_unchecked!(args as Terminator::Jump(_, args) = cfg[j].terminator());
          for &(v, b, _) in args { if b { insert(&mut out, v) } }
        }
      }
      out
    }).collect();

    for &Arg { var, ref ty, .. } in rets { insert(rets_out, var) }
    self.rets = rets_out;
    block_args
  }

  fn build_blocks(&mut self, block_args: &ChunkVec<BlockId, VReg>) {
    visit_blocks(self.cfg, |i, bl| {
      let vbl = self.code.new_block(block_args[i].iter().copied());
      self.block_map.insert(i, vbl);
      self.ctx.start_block(bl);
      for (i, stmt) in bl.stmts.iter().enumerate() {
        if stmt.relevant() {
          match stmt {
            Statement::Let(lk, ty, rv) => {
              let ((&LetKind::Let(v, _, _), &ref ty) |
                (&LetKind::Own([_, (v, _, ref ty)]), _)) = (lk, ty);
              let a = self.allocs.get(v);
              if a != AllocId::ZERO {
                if let RValue::Pun(_, p) = rv {
                  let code = &mut self.code;
                  let m = self.allocs[a].m;
                  let rm = self.get_place(p);
                  self.var_map.entry(a).or_insert_with(|| (rm, Size::from_u64(m.size)));
                } else {
                  let (&(dst, sz), size) = self.get_alloc(a);
                  self.build_rvalue(ty, size, sz, dst, rv);
                }
              }
            }
            Statement::Assign(p, ty, o, _) => {
              let size = ty.sizeof(self.names).expect("size of type not a compile time constant");
              let dst = self.get_place(p);
              self.build_move(size, Size::from_u64(size), dst, o);
            }
          }
        }
        stmt.foreach_def(|v, _, _, ty| self.ctx.insert(v, ty.clone()))
      }
      self.build_terminator(block_args, vbl, bl.terminator());
      self.code.finish_block();
    });
  }

  fn finish(self) -> VCode {
    let LowerCtx { mut code, block_map, unpatched, .. } = self;
    let mut patch = |dst: &mut VBlockId| { *dst = block_map[&BlockId(dst.0)]; *dst };
    for (vbl, inst) in unpatched {
      match &mut code[inst] {
        Inst::Ghost(GhostInst::Fallthrough { dst }) |
        Inst::JmpKnown { dst, .. } => {
          let dst = patch(dst);
          code.add_edge(vbl, dst)
        }
        Inst::JmpCond { taken, not_taken, .. } => {
          let (bl1, bl2) = (patch(taken), patch(not_taken));
          code.add_edge(vbl, bl1);
          code.add_edge(vbl, bl2);
        }
        _ => unreachable!(),
      }
    }
    code
  }
}

pub(crate) fn build_vcode(
  names: &HashMap<Symbol, Entity>,
  func_mono: &HashMap<Symbol, ProcId>,
  funcs: &IdxVec<ProcId, ProcAbi>,
  cfg: &Cfg,
  allocs: &Allocations,
  rets: &[Arg],
) -> VCode {
  let mut lctx = LowerCtx::new(names, func_mono, funcs, cfg, allocs);
  let temp = &mut vec![];
  let block_args = lctx.build_block_args(temp, rets);
  lctx.build_blocks(&block_args);
  lctx.finish()
}