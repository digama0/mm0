//! A high level classification of `VCode` emit patterns, used for relating MIR to `VCode`.
use crate::arch::{PInst, SysCall};

use super::{vcode::{BlockId, ChunkVec, ProcAbi, ArgAbi, ProcId}, IdxVec, mir, IntTy, entity::IntrinsicProc};

/// A call to `get_place`, to resolve a place reference into a register or memory.
#[derive(Clone, Copy, Debug)]
pub struct Place {
  /// The number of projection entries, found in `Trace.projs`
  pub projs: u8,
}

/// A call to `get_const`, which resolves to a value or a constant in static memory.
#[derive(Clone, Copy, Debug)]
pub enum Const {
  /// A directly given value as a `u64`.
  Value,
  /// A larger or structured value stored in static memory.
  Ptr,
}

/// A call to `get_operand`.
#[derive(Clone, Copy, Debug)]
pub enum Operand {
  /// The operand is a place.
  Place(Place),
  /// The operand is a const.
  Const(Const),
}

/// A call to `into_reg`. The bool is true if a mov instruction was emitted.
#[derive(Clone, Copy, Debug)]
pub struct IntoReg(pub bool);

/// A call to `into_mem`. The bool is true if a mov instruction was emitted.
#[derive(Clone, Copy, Debug)]
pub struct IntoMem(pub bool);

/// A call to `into_rm`. The bool is true if a mov instruction was emitted.
#[derive(Clone, Copy, Debug)]
pub struct IntoRM(pub bool);

/// A call to `into_rmi_32`. The bool is true if a mov instruction was emitted.
#[derive(Clone, Copy, Debug)]
pub struct IntoRMI32(pub bool);

/// A call to `get_operand_reg`.
pub type OperandReg = (Operand, IntoReg);
/// A call to `get_operand_rm`.
pub type OperandRM = (Operand, IntoRM);
/// A call to `get_operand_32`.
pub type Operand32 = (Operand, IntoRMI32);

/// A call to `emit_copy`.
#[derive(Clone, Copy, Debug)]
pub enum Copy {
  /// One instruction was emitted (load or store or imm).
  One,
  /// Two instructions were emitted for a mem-mem move.
  Two,
}

/// A call to `build_move`.
#[derive(Clone, Copy, Debug)]
pub enum Move {
  /// A small (<= 8 byte) move, implemented via a copy.
  Small(Operand, Copy),
}

/// A `build_as` call.
#[derive(Clone, Copy, Debug)]
pub enum As {
  /// This is a truncating `as`, no sign extension is needed.
  Truncate(Copy),
  /// This is an extending `as`, with a zero/sign extension.
  Extend(Copy),
}

/// A `build_shift_or_zero` call.
#[derive(Clone, Copy, Debug)]
#[allow(variant_size_differences)]
pub enum Shift {
  /// The right operand is zero, so we read the left operand and write 0.
  Zero,
  /// The right operand is an immediate, so we read the left operand, shift, and write the result.
  Imm(Copy),
  /// The right operand is a variable, so we read the operands, shift, and write the result.
  Var(OperandReg, Copy),
}

/// A `build_rvalue` call.
#[derive(Clone, Copy, Debug)]
pub enum RValue {
  /// A `Use` statement
  Use(Move),
  /// A `Unop` statement, except `As`
  Unop(OperandReg, Copy),
  /// A `Unop(As)` statement
  As(OperandRM, As),
  /// A generic `Binop` statement
  Binop(OperandReg, Operand32, Copy),
  /// A `Binop(Mul)` statement
  Mul(OperandReg, OperandRM, Copy),
  /// A `Binop(Max)` statement
  Max(OperandReg, OperandReg, Copy),
  /// A `Binop(Min)` statement
  Min(OperandReg, OperandReg, Copy),
  /// A `Binop(Shl|Shr)` statement
  Shift(OperandReg, Shift),
  /// A `Binop(Eq|Ne|Lt|Le)` or `Eq` statement
  Cmp(OperandReg, Operand32, Copy),
  /// A `Pun` statement
  Pun(Place),
  /// A `Cast` statement
  Cast(OperandRM, As),
  /// A `List` statement. The arguments are stored in `Trace.lists`
  List(u32),
  /// A `Array` statement with one argument.
  Array1(Move),
  /// A `Array` statement. The arguments are stored in `Trace.lists`
  Array(u32),
  /// A `Borrow` statement
  Borrow(Place, Copy),
  /// A statement producing no code.
  Ghost,
}

/// A call to `add_scaled`.
#[derive(Clone, Copy, Debug)]
pub enum AddScaled {
  /// The address has no base and scale 1,
  /// so the address mode was updated and no code was emitted
  NoBase1,
  /// The address has scale 1/2/4/8,
  /// so the address mode was updated and no code was emitted
  Pow2,
  /// The address has no base and scale 3/5/9,
  /// so the address mode was updated and no code was emitted
  NoBasePow2Add,
  /// A LEA was emitted to reduce to the `Pow2` case, resulting in 1 instruction
  ComposePow2,
  /// The scale or base was not one of the easy cases, so IMM+MUL was emitted
  Large,
  /// A LEA was emitted to reduce to the `Large` case, resulting in 3 instructions
  ComposeLarge,
}

impl AddScaled {
  /// Strip `Compose` from an [`AddScaled`] element.
  #[must_use] pub fn decompose(self) -> Option<Self> {
    match self {
      AddScaled::ComposePow2 => Some(AddScaled::Pow2),
      AddScaled::ComposeLarge => Some(AddScaled::Large),
      _ => None
    }
  }
}

/// One projection in the `get_place` call.
#[derive(Clone, Copy, Debug)]
pub enum Projection {
  /// A `Deref` projection
  Deref(IntoReg),
  /// A `Proj(And|Sn)` projection
  Ghost,
  /// A `Proj(Array)` projection
  ProjArray,
  /// A `Proj(Struct)` projection
  ProjStruct,
  /// A `Index|Slice` projection
  IndexSlice(IntoReg, AddScaled),
}

  /// An operand element in `List`, `Array`, `Call` or `Return`
#[derive(Clone, Copy, Debug)]
pub enum Elem {
  /// A ghost element
  Ghost,
  /// The operand was evaluated
  Operand(Operand),
  /// The operand was evaluated and placed in a memory location
  Boxed(Operand, IntoMem),
  /// The operand was evaluated and placed in a memory location
  BoxedMem(Operand, IntoMem),
  /// The operand was moved
  Move(Move),
  /// A return slot pointer was placed in memory
  RetArg(IntoMem),
  /// A return value was placed in a register
  RetReg,
  /// A return value was placed in memory
  RetMem(Copy),
}

/// A statement.
#[derive(Clone, Copy, Debug)]
#[allow(variant_size_differences)]
pub enum Statement {
  /// A `Let` statement
  Let(RValue),
  /// An `Assign` statement
  Assign(Place, Move),
  /// A statement with no code
  Ghost,
}

/// A block terminator statement
#[derive(Clone, Copy, Debug)]
pub enum Terminator {
  /// A `Jump` statement. The arguments are stored in `Trace.lists`
  Jump(u32),
  /// A `Jump1` statement.
  Jump1,
  /// A `Return` statement. The arguments are stored in `Trace.lists`
  Return,
  /// An `Exit` statement.
  Exit,
  /// An `If` statement.
  If(OperandReg),
  /// An `Assert` statement.
  Assert(OperandReg),
  /// A `Call` statement.
  Call(ProcId),
  /// An intrinsic `Call` statement. The Option is set if the return is not ignored
  Intrinsic(IntrinsicProc, Option<Copy>),
  /// An `Assert(false)` statement.
  Fail,
}

/// A classification of emitted instructions based on the input MIR.
#[derive(Clone, Debug, Default)]
pub struct Trace {
  pub(crate) stmts: ChunkVec<BlockId, Statement>,
  pub(crate) block: IdxVec<BlockId, Block>,
  pub(crate) projs: Vec<Projection>,
  pub(crate) lists: Vec<Elem>,
}

/// The data for a block (in the context of a [`Trace`]).
#[derive(Copy, Clone, Debug)]
pub struct Block {
  pub(crate) proj_start: u32,
  pub(crate) list_start: u32,
  pub(crate) term: Terminator,
}

macro_rules! mk_fold {
  ($(
    fn $before:ident, $after:ident, $do:ident(
      $self:ident, $it:ident $(, $e:ident: $ty:ty)* $(,)?
    ) $body:expr
  )*) => {
    /// A trait for consuming an instruction stream with alignment between the MIR and the
    /// generated instructions.
    #[allow(unused_variables)]
    pub trait Visitor<'a> {
      /// Called every time an instruction is emitted.
      fn on_inst(&mut self, spill: bool, inst: &crate::proof::Inst<'a>) {}
        /// Visit a single regular instruction from the stream,
        /// preceded by zero or more spill instructions.
      fn do_inst(&mut self, it: &mut TraceIter<'a>) -> crate::proof::Inst<'a> {
        loop {
          let inst = it.insts.next().expect("missing instruction");
          let spill = inst.inst.is_spill();
          self.on_inst(spill, &inst);
          if spill { continue }
          return inst
        }
      }
      /// Visit `n` instructions from the stream.
      fn do_insts(&mut self, n: usize, it: &mut TraceIter<'a>) {
        for _ in 0..n { self.do_inst(it); }
      }

      /// Called before each classifier's instructions are visited.
      /// This is the default implementation of `before_foo()`.
      fn before(&mut self) {}
      /// Called after each classifier's instructions are visited.
      /// This is the default implementation of `after_foo()`.
      fn after(&mut self) {}

      $(
        /// Called before a certain classifier's instructions are visited. Intended for overriding.
        fn $before(&mut self, $($e: $ty),*) { self.before() }
        /// Called after a certain classifier's instructions are visited. Intended for overriding.
        fn $after(&mut self, $($e: $ty),*) { self.after() }
        /// Consumes the instructions for a classifier. Not intended for overriding.
        fn $do(&mut $self, $($e: $ty,)* $it: &mut TraceIter<'a>) {
          $self.$before($($e),*);
          { $body }
          $self.$after($($e),*);
        }
      )*
    }
  }
}

mk_fold! {
  fn before_into_reg, after_into_reg, do_into_reg(self, it, cl: IntoReg) {
    if cl.0 { self.do_inst(it); }
  }
  fn before_into_mem, after_into_mem, do_into_mem(self, it, cl: IntoMem) {
    if cl.0 { self.do_inst(it); }
  }
  fn before_into_rm, after_into_rm, do_into_rm(self, it, cl: IntoRM) {
    if cl.0 { self.do_inst(it); }
  }
  fn before_into_32, after_into_32, do_into_32(self, it, cl: IntoRMI32) {
    if cl.0 { self.do_inst(it); }
  }
  fn before_add_scaled, after_add_scaled, do_add_scaled(self, it, cl: AddScaled) {
    if let Some(cl) = cl.decompose() {
      self.do_inst(it);
      self.do_add_scaled(cl, it);
    } else if let AddScaled::Large = cl {
      self.do_insts(2, it);
    }
  }

  fn before_proj, after_proj, do_proj(self, it,
    ty: &mir::Ty, proj: &mir::Projection, cl: &Projection
  ) {
    match *cl {
      Projection::Ghost |
      Projection::ProjArray |
      Projection::ProjStruct => {}
      Projection::Deref(cl) => self.do_into_reg(cl, it),
      Projection::IndexSlice(cl, cl2) => { self.do_into_reg(cl, it); self.do_add_scaled(cl2, it) }
    }
  }

  fn before_place, after_place, do_place(self, it, p: &mir::Place, cl: Place) {
    assert!(usize::from(cl.projs) == p.proj.len());
    for (ty, proj) in &p.proj {
      let cl = it.projs.next().expect("iter mismatch");
      self.do_proj(ty, proj, cl, it);
    }
  }

  fn before_const, after_const, do_const(self, it, c: &mir::Constant, cl: Const) {}

  fn before_operand, after_operand, do_operand(self, it, o: &mir::Operand, cl: Operand) {
    match (cl, o.place()) {
      (Operand::Place(cl), Ok(p)) => self.do_place(p, cl, it),
      (Operand::Const(cl), Err(c)) => self.do_const(c, cl, it),
      _ => unreachable!(),
    }
  }

  fn before_operand_reg, after_operand_reg, do_operand_reg(self, it, o: &mir::Operand, cl: &OperandReg) {
    self.do_operand(o, cl.0, it);
    self.do_into_reg(cl.1, it);
  }

  fn before_operand_rm, after_operand_rm, do_operand_rm(self, it, o: &mir::Operand, cl: &OperandRM) {
    self.do_operand(o, cl.0, it);
    self.do_into_rm(cl.1, it);
  }

  fn before_operand_32, after_operand_32, do_operand_32(self, it, o: &mir::Operand, cl: &Operand32) {
    self.do_operand(o, cl.0, it);
    self.do_into_32(cl.1, it);
  }

  fn before_copy, after_copy, do_copy(self, it, cl: Copy) {
    match cl {
      Copy::One => { self.do_inst(it); }
      Copy::Two => self.do_insts(2, it),
    }
  }

  fn before_move, after_move, do_move(self, it, o: &mir::Operand, cl: Move) {
    let Move::Small(cl1, cl2) = cl;
    self.do_operand(o, cl1, it);
    self.do_copy(cl2, it);
  }

  fn before_as, after_as, do_as(self, it, from: IntTy, to: IntTy, cl: As) {
    match cl {
      As::Truncate(cl) => self.do_copy(cl, it),
      As::Extend(cl) => { self.do_inst(it); self.do_copy(cl, it) }
    }
  }

  fn before_shift, after_shift, do_shift(self, it, o: &mir::Operand, cl: &Shift) {
    match cl {
      Shift::Zero => self.do_copy(Copy::One, it),
      Shift::Imm(cl) => { self.do_inst(it); self.do_copy(*cl, it) }
      Shift::Var(cl1, cl2) => {
        self.do_operand_reg(o, cl1, it);
        self.do_insts(4, it);
        self.do_copy(*cl2, it)
      }
    }
  }

  fn before_list_elem, after_list_elem, do_list_elem(self, it, o: &mir::Operand, cl: &Elem) {
    match *cl {
      Elem::Ghost => {}
      Elem::Move(cl) => self.do_move(o, cl, it),
      _ => unreachable!()
    }
  }

  fn before_rvalue, after_rvalue, do_rvalue(self, it,
    ty: &mir::Ty, rv: &mir::RValue, cl: &RValue
  ) {
    match (cl, rv) {
      (RValue::Ghost, _) => {}
      (&RValue::Use(cl), mir::RValue::Use(o)) => self.do_move(o, cl, it),
      (RValue::Unop(cl1, cl2), mir::RValue::Unop(_, o)) => {
        self.do_operand_reg(o, cl1, it);
        self.do_inst(it);
        self.do_copy(*cl2, it);
      }
      (RValue::As(cl1, cl2), &mir::RValue::Unop(mir::Unop::As(from, to), ref o)) => {
        self.do_operand_rm(o, cl1, it);
        self.do_as(from, to, *cl2, it);
      }
      (RValue::Binop(cl1, cl2, cl3), mir::RValue::Binop(_, o1, o2)) => {
        self.do_operand_reg(o1, cl1, it);
        self.do_operand_32(o2, cl2, it);
        self.do_inst(it);
        self.do_copy(*cl3, it);
      }
      (RValue::Mul(cl1, cl2, cl3), mir::RValue::Binop(_, o1, o2)) => {
        self.do_operand_reg(o1, cl1, it);
        self.do_operand_rm(o2, cl2, it);
        self.do_inst(it);
        self.do_copy(*cl3, it);
      }
      (RValue::Max(cl1, cl2, cl3) | RValue::Min(cl1, cl2, cl3), mir::RValue::Binop(_, o1, o2)) => {
        self.do_operand_reg(o1, cl1, it);
        self.do_operand_reg(o2, cl2, it);
        self.do_insts(2, it);
        self.do_copy(*cl3, it);
      }
      (RValue::Shift(cl1, cl2), mir::RValue::Binop(_, o1, o2)) => {
        self.do_operand_reg(o1, cl1, it);
        self.do_shift(o2, cl2, it);
      }
      (RValue::Cmp(cl1, cl2, cl3), mir::RValue::Binop(_, o1, o2) | mir::RValue::Eq(_, _, o1, o2)) => {
        self.do_operand_reg(o1, cl1, it);
        self.do_operand_32(o2, cl2, it);
        self.do_insts(2, it);
        self.do_copy(*cl3, it);
      }
      (&RValue::Pun(cl), mir::RValue::Pun(_, p)) => self.do_place(p, cl, it),
      (RValue::Cast(cl1, cl2), mir::RValue::Cast(_, o, tyin)) => {
        self.do_operand_rm(o, cl1, it);
        let from = tyin.as_int_ty().expect("unreachable");
        let to = ty.as_int_ty().expect("unreachable");
        self.do_as(from, to, *cl2, it);
      }
      (RValue::Array1(cl), mir::RValue::Array(os)) => self.do_move(&os[0], *cl, it),
      (RValue::List(_), mir::RValue::List(os)) | (RValue::Array(_), mir::RValue::Array(os)) => {
        for o in &**os {
          let cl = it.lists.next().expect("iter mismatch");
          self.do_list_elem(o, cl, it)
        }
      }
      (&RValue::Borrow(cl1, cl2), mir::RValue::Borrow(p)) => {
        self.do_place(p, cl1, it);
        self.do_inst(it);
        self.do_copy(cl2, it);
      }
      _ => unreachable!()
    }
  }

  fn before_stmt, after_stmt, do_stmt(self, it, stmt: &mir::Statement, cl: &Statement) {
    match (cl, stmt) {
      (Statement::Ghost, _) => {}
      (Statement::Let(cl), mir::Statement::Let(_, _, ty, rv)) => self.do_rvalue(ty, rv, cl, it),
      (&Statement::Assign(cl1, cl2), mir::Statement::Assign(p, ty, o, _)) => {
        self.do_place(p, cl1, it);
        self.do_move(o, cl2, it);
      }
      _ => unreachable!()
    }
  }

  fn before_jump_elem, after_jump_elem, do_jump_elem(self, it,
    v: mir::VarId, r: bool, o: &mir::Operand, cl: &Elem
  ) {
    match *cl {
      Elem::Ghost => {}
      Elem::Move(cl) => self.do_move(o, cl, it),
      _ => unreachable!()
    }
  }

  fn before_ret_elem, after_ret_elem, do_ret_elem(self, it,
    v: mir::VarId, r: bool, o: &mir::Operand, ret: &ArgAbi, cl: &Elem
  ) {
    match *cl {
      Elem::Ghost => {}
      Elem::Move(cl) => {
        if let ArgAbi::BoxedMem {..} = ret { self.do_inst(it); }
        self.do_move(o, cl, it);
      }
      Elem::Operand(cl) => { self.do_operand(o, cl, it); self.do_copy(Copy::One, it) }
      _ => unreachable!()
    }
  }

  fn before_epilogue, after_epilogue, do_epilogue(self, it) {
    while !matches!(self.do_inst(it).inst, PInst::Ret) {}
  }

  fn before_call_arg, after_call_arg, do_call_arg(self, it,
    r: bool, o: &mir::Operand, arg: &ArgAbi, cl: &Elem
  ) {
    match *cl {
      Elem::Ghost => {}
      Elem::Move(cl) => self.do_move(o, cl, it),
      Elem::Operand(cl) => { self.do_operand(o, cl, it); self.do_copy(Copy::One, it) }
      Elem::Boxed(cl1, cl2) => {
        self.do_operand(o, cl1, it);
        self.do_into_mem(cl2, it);
        self.do_inst(it);
      }
      Elem::BoxedMem(cl1, cl2) => {
        self.do_operand(o, cl1, it);
        self.do_into_mem(cl2, it);
        self.do_inst(it);
        self.do_copy(Copy::One, it)
      }
      _ => unreachable!()
    }
  }

  fn before_call_retarg, after_call_retarg, do_call_retarg(self, it, cl: IntoMem, arg: &ArgAbi) {
    self.do_inst(it);
    if let ArgAbi::BoxedMem {..} = arg { self.do_copy(Copy::One, it) }
  }

  fn before_call_ret, after_call_ret, do_call_ret(self, it, arg: &ArgAbi, cl: &Elem) {
    match (cl, arg) {
      (Elem::Ghost, _) => {}
      (Elem::RetReg, ArgAbi::Reg(_, _)) => { self.do_copy(Copy::One, it) }
      (Elem::RetMem(cl), ArgAbi::Mem { .. }) => { self.do_copy(Copy::One, it) }
      _ => unreachable!()
    }
  }

  fn before_call_rets, after_call_rets, do_call_rets(self, it,
    boxes: u8, retabi: &[ArgAbi], rets: &[(bool, mir::VarId)],
  ) {
    for (arg, &(vr, _)) in retabi.iter().zip(rets) {
      if !vr { continue }
      let cl = it.lists.next().expect("iter mismatch");
      self.do_call_ret(arg, cl, it)
    }
    for _ in 0..boxes { self.do_copy(Copy::One, it) }
    self.do_inst(it);
  }

  fn before_call_args, after_call_args, do_call_args(self, it,
    f: ProcId, fabi: &ProcAbi, args: &[(bool, mir::Operand)],
  ) {
    for (arg, &(r, ref o)) in fabi.args.iter().zip(args) {
      let cl = it.lists.next().expect("iter mismatch");
      self.do_call_arg(r, o, arg, cl, it);
    }
  }

  // do_call_retargs is unused, before and after are called directly
  fn before_call_retargs, after_call_retargs, do_call_retargs(self, it,
    f: ProcId, fabi: &ProcAbi, retabi: &[ArgAbi], rets: &[(bool, mir::VarId)],
  ) {}

  fn before_call, after_call, do_call(self, it,
    f: ProcId, fabi: &ProcAbi, args: &[(bool, mir::Operand)],
    reach: bool, rets: &[(bool, mir::VarId)],
  ) {
    self.do_call_args(f, fabi, args, it);
    if let Some(retabi) = &fabi.rets {
      let mut boxes = 0;
      self.before_call_retargs(f, fabi, retabi, rets);
      for (arg, &(vr, _)) in retabi.iter().zip(rets) {
        if vr && matches!(arg, ArgAbi::Boxed {..} | ArgAbi::BoxedMem {..}) {
          let cl = match it.lists.next() {
            Some(&Elem::RetArg(cl)) => cl,
            _ => unreachable!(),
          };
          if cl.0 { boxes += 1 }
          self.do_call_retarg(cl, arg, it)
        }
      }
      self.after_call_retargs(f, fabi, retabi, rets);
      self.do_inst(it);
      self.do_call_rets(boxes, retabi, rets, it);
    } else {
      self.do_inst(it);
    }
  }

  fn before_syscall, after_syscall, do_syscall(self, it,
    f: SysCall, args: &[Option<&(bool, mir::Operand)>], cl: Option<Copy>
  ) {
    for arg in args {
      let cl = it.lists.next().expect("iter mismatch");
      match (cl, arg) {
        (Elem::Operand(Operand::Const(Const::Value)), None) => {}
        (&Elem::Operand(cl), Some((_, o))) => self.do_operand(o, cl, it),
        _ => unreachable!(),
      }
    }
    self.do_insts(args.len() + 2, it);
    if f != SysCall::Exit {
      if let Some(cl) = cl { self.do_copy(cl, it) }
      self.do_inst(it);
    }
  }

  fn before_terminator, after_terminator, do_terminator(self, it,
    funcs: &IdxVec<ProcId, ProcAbi>, abi_rets: Option<&[ArgAbi]>,
    term: &mir::Terminator, cl: &Terminator
  ) {
    match (cl, term) {
      (Terminator::Jump(_), mir::Terminator::Jump(_, args, _)) => {
        for &(v, r, ref o) in &**args {
          let cl = it.lists.next().expect("iter mismatch");
          self.do_jump_elem(v, r, o, cl, it)
        }
        self.do_inst(it);
      }
      (Terminator::Jump1 | Terminator::Fail, _) => { self.do_inst(it); }
      (Terminator::Return, mir::Terminator::Return(_, args)) => {
        for (&(v, r, ref o), ret) in args.iter().zip(abi_rets.expect("expected return ABI")) {
          let cl = it.lists.next().expect("iter mismatch");
          self.do_ret_elem(v, r, o, ret, cl, it)
        }
        self.do_epilogue(it);
      }
      (Terminator::Exit, _) => self.do_syscall(SysCall::Exit, &[None], None, it),
      (Terminator::If(cl), mir::Terminator::If(o, _)) => {
        self.do_operand_reg(o, cl, it);
        self.do_insts(3, it);
      }
      (Terminator::Assert(cl), mir::Terminator::Assert(o, _, true, _)) => {
        self.do_operand_reg(o, cl, it);
        self.do_insts(2, it);
      }
      (&Terminator::Call(f), mir::Terminator::Call { args, reach, rets, .. }) => {
        self.do_call(f, &funcs[f], args, *reach, rets, it)
      }
      (&Terminator::Intrinsic(f, cl), mir::Terminator::Call { args, rets, .. }) => {
        use SysCall::*;
        match (f, &**args) {
          (IntrinsicProc::Open | IntrinsicProc::Create, [fname]) =>
            self.do_syscall(Open, &[Some(fname), None, None], cl, it),
          (IntrinsicProc::Read, [fd, count, _, p]) =>
            self.do_syscall(Read, &[Some(fd), Some(p), Some(count)], cl, it),
          (IntrinsicProc::Write, [fd, count, _, p]) =>
            self.do_syscall(Write, &[Some(fd), Some(p), Some(count)], cl, it),
          (IntrinsicProc::FStat, [fd, _, p]) =>
            self.do_syscall(FStat, &[Some(fd), Some(p)], cl, it),
          (IntrinsicProc::MMap, [len, prot, fd]) =>
            self.do_syscall(MMap, &[None, Some(len), Some(prot), None, Some(fd), None], cl, it),
          (IntrinsicProc::MMapAnon, [len, prot]) =>
            self.do_syscall(MMap, &[None, Some(len), Some(prot), None, None, None], cl, it),
          _ => unreachable!(),
        }
      }
      _ => unreachable!()
    }
  }
}

/// Internal state for [`Visitor`].
#[derive(Clone, Debug)]
pub struct TraceIter<'a> {
  insts: crate::proof::InstIter<'a>,
  projs: std::slice::Iter<'a, Projection>,
  lists: std::slice::Iter<'a, Elem>,
}

impl Trace {
  #[allow(clippy::iter_not_returning_iterator)]
  pub(crate) fn iter<'a>(&'a self,
    id: BlockId, insts: crate::proof::InstIter<'a>,
  ) -> (TraceIter<'a>, &'a Terminator) {
    let Block { proj_start, list_start, ref term } = self.block[id];
    (TraceIter {
      insts,
      projs: self.projs[proj_start as usize..].iter(),
      lists: self.lists[list_start as usize..].iter(),
    }, term)
  }
}
