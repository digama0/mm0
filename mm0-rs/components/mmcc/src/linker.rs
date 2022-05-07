//! Handles layout of functions, globals, constants in the overall program.

use std::collections::{HashMap, HashSet};

use crate::build_vcode::{VCodeCtx, build_vcode};
use crate::codegen::FUNCTION_ALIGN;
use crate::mir_opt::storage::{Allocations, AllocId};
use crate::regalloc::PCode;
use crate::types::global::{TyKind, ExprKind};
use crate::types::entity::{ConstTc, Entity, ProcTc};
use crate::types::mir::{
  Cfg, ConstKind, Constant, Place, Proc, Terminator, Ty, VarId, Visitor};
use crate::types::vcode::{GlobalId, ProcId, ConstRef, ProcAbi};
use crate::types::{IdxVec, Size};
use crate::{Symbol, LowerErr};

type GenericCall = (Symbol, Box<[Ty]>);

type ConstVal = (u32, ConstRef);

#[derive(Debug, Default)]
pub(crate) struct ConstData {
  pub(crate) map: HashMap<Symbol, ConstVal>,
  pub(crate) ordered: Vec<Symbol>,
  pub(crate) rodata: Vec<u8>,
}

impl std::ops::Index<Symbol> for ConstData {
  type Output = ConstVal;
  fn index(&self, s: Symbol) -> &Self::Output { &self.map[&s] }
}

impl ConstData {
  pub(crate) fn load_mem(&self, sz: Size, addr: u32) -> u64 {
    let len = sz.bytes().expect("size Inf not allowed").into();
    let mut buf = [0; 8];
    buf[..len].copy_from_slice(&self.rodata[addr.try_into().expect("overflow")..][..len]);
    u64::from_le_bytes(buf)
  }

  pub(crate) fn value(&self, (sz, c): ConstVal) -> u64 {
    match c {
      ConstRef::Value(val) => val,
      ConstRef::Ptr(addr) => self.load_mem(Size::from_u64(sz.into()), addr)
    }
  }

  fn here(&self) -> u32 {
    self.rodata.len().try_into().expect("overflow")
  }

  fn alloc(&mut self, buf: &[u8]) -> u32 {
    let addr = self.here();
    self.rodata.extend_from_slice(buf);
    addr
  }
}

struct Collector<'a> {
  names: &'a HashMap<Symbol, Entity>,
  mir: &'a HashMap<Symbol, Proc>,
  implications: HashMap<Symbol, Option<HashSet<GenericCall>>>,
  funcs: (HashMap<Symbol, ProcId>, IdxVec<ProcId, Symbol>),
  postorder: Vec<ProcId>,
  consts: ConstData,
}

impl<'a> Collector<'a> {
  fn new(names: &'a HashMap<Symbol, Entity>, mir: &'a HashMap<Symbol, Proc>) -> Self {
    Self {
      names,
      mir,
      implications: Default::default(),
      funcs: Default::default(),
      consts: Default::default(),
      postorder: Default::default(),
    }
  }

  fn collect_generics(&mut self, args: &[Ty], calls: &HashSet<GenericCall>) {
    for &(g, ref tys) in calls {
      let args: Box<[_]> = tys.iter().map(|ty| ty.subst(args)).collect();
      self.collect_func(g, &args);
    }
  }

  fn collect_cfg(&mut self, body: &Cfg, args: &[Ty]) -> HashSet<GenericCall> {
    if !args.is_empty() {
      unimplemented!("functions with type args")
    }
    let mut calls = HashSet::new();
    for (_, bl) in body.blocks() {
      struct ConstVisitor<'a, 'b>(&'b mut Collector<'a>);
      impl Visitor for ConstVisitor<'_, '_> {
        fn visit_place(&mut self, _: &Place) {}
        fn visit_constant(&mut self, c: &Constant) {
          if let ConstKind::Const(s) = c.k { self.0.collect_const(s); }
        }
      }
      ConstVisitor(self).visit_basic_block(bl);
      if let Terminator::Call { f, tys, .. } = bl.terminator() {
        if tys.iter().any(|ty| ty.has_tyvar()) {
          calls.insert((*f, tys.clone()));
        } else {
          self.collect_func(*f, tys);
        }
      }
    }
    calls
  }

  fn collect_func(&mut self, f: Symbol, args: &[Ty]) -> Option<ProcId> {
    if !args.is_empty() {
      unimplemented!("functions with type args")
    }
    if let Some(&id) = self.funcs.0.get(&f) { return Some(id) }
    if_chain! {
      if let Some(Entity::Proc(tc)) = self.names.get(&f);
      if let ProcTc::Typed(ty) = &tc.k;
      if ty.intrinsic.is_some();
      then { return None }
    }
    let id = self.funcs.1.push(f);
    self.funcs.0.insert(f, id);
    if let Some(imps) = self.implications.get_mut(&f) {
      let calls = imps.take().expect("cycle in collector?");
      self.collect_generics(args, &calls);
      self.implications.insert(f, Some(calls));
    } else if let Some(proc) = self.mir.get(&f) {
      let calls = self.collect_cfg(&proc.body, args);
      if !calls.is_empty() {
        self.implications.insert(f, None);
        self.collect_generics(args, &calls);
      }
      self.implications.insert(f, Some(calls));
    }
    self.postorder.push(id);
    Some(id)
  }

  fn alloc_const(&mut self, ty: &TyKind, e: &ExprKind) -> Option<(u32, u32)> {
    Some(match self.eval_const(ty, e)? {
      (sz, ConstRef::Ptr(addr)) => (sz, addr),
      (sz, ConstRef::Value(val)) =>
        (sz, self.consts.alloc(&val.to_le_bytes()[..sz.try_into().expect("overflow")]))
    })
  }

  fn eval_const(&mut self, ty: &TyKind, e: &ExprKind) -> Option<ConstVal> {
    match e {
      ExprKind::Unit => Some((0, ConstRef::Value(0))),
      &ExprKind::Const(s) => Some(self.collect_const(s)),
      &ExprKind::Bool(b) => Some((1, ConstRef::Value(b.into()))),
      ExprKind::Int(n) => if let TyKind::Int(ity) = *ty {
        Some((ity.size().bytes()?.into(), ConstRef::Value(ity.zero_extend_as_u64(n)?)))
      } else {
        None
      }
      ExprKind::List(es) => match ty {
        TyKind::Sn(_, ty) => self.eval_const(ty, &es[0]),
        TyKind::List(tys) => {
          let addr = self.consts.here();
          for (ty, e) in tys.iter().zip(&**es) { self.alloc_const(ty, e)?; }
          Some((self.consts.here() - addr, ConstRef::Ptr(addr)))
        }
        TyKind::Struct(tys) => {
          let addr = self.consts.here();
          for (arg, e) in tys.iter().zip(&**es) { self.alloc_const(arg.1.ty(), e)?; }
          Some((self.consts.here() - addr, ConstRef::Ptr(addr)))
        }
        _ => None
      },
      ExprKind::Array(es) => if let TyKind::Array(ty, _) = ty {
        let addr = self.consts.here();
        for e in &**es { self.alloc_const(ty, e)?; }
        Some((self.consts.here() - addr, ConstRef::Ptr(addr)))
      } else {
        None
      }
      ExprKind::Var(_) |
      ExprKind::Unop(_, _) |
      ExprKind::Binop(_, _, _) |
      ExprKind::Index(_, _) |
      ExprKind::Slice(_) |
      ExprKind::Proj(_, _) |
      ExprKind::UpdateIndex(_) |
      ExprKind::UpdateSlice(_) |
      ExprKind::UpdateProj(_, _, _) |
      ExprKind::Sizeof(_) |
      ExprKind::Ref(_) |
      ExprKind::Mm0(_) |
      ExprKind::Call { .. } |
      ExprKind::If { .. } |
      ExprKind::Error => None, // TODO: const eval
    }
  }

  fn collect_const(&mut self, c: Symbol) -> ConstVal {
    if let Some(&id) = self.consts.map.get(&c) { return id }
    let value = if_chain! {
      if let Some(Entity::Const(tc)) = self.names.get(&c);
      if let ConstTc::Checked { ref ty, ref whnf, .. } = tc.k;
      then { self.eval_const(ty, whnf) }
      else { None }
    }.expect("cannot resolve constant to an integer value");
    if matches!(value.1, ConstRef::Ptr(_)) {
      self.consts.ordered.push(c);
    }
    self.consts.map.insert(c, value);
    value
  }
}

/// The start of the `.text` section, also the entry point for the program.
pub const TEXT_START: u32 = 0x40_0078;

//// A completed code object. This includes the list of instructions,
/// and can be serialized to a list of bytes using the [`LinkedCode::write_elf`] method.
#[derive(Debug)]
pub struct LinkedCode {
  pub(crate) mir: HashMap<Symbol, Proc>,
  pub(crate) consts: ConstData,
  pub(crate) globals: IdxVec<GlobalId, (Symbol, u32, u32)>,
  pub(crate) global_size: u32,
  pub(crate) init: (Cfg, Box<PCode>),
  pub(crate) func_names: (HashMap<Symbol, ProcId>, IdxVec<ProcId, Symbol>),
  pub(crate) func_abi: IdxVec<ProcId, ProcAbi>,
  pub(crate) funcs: IdxVec<ProcId, (u32, Box<PCode>)>,
  pub(crate) postorder: Vec<ProcId>,
  pub(crate) text_size: u32,
}

/// Errors that occur during linking.
#[derive(Debug)]
pub enum LinkerErr {
  /// An error that occurred during `VCode` lowering
  LowerErr(LowerErr),
}

impl From<LowerErr> for LinkerErr {
  fn from(v: LowerErr) -> Self { Self::LowerErr(v) }
}

impl LinkedCode {
  pub(crate) fn link(
    names: &HashMap<Symbol, Entity>,
    mir: HashMap<Symbol, Proc>,
    init: Cfg,
    allocs: &Allocations,
    globals: &[(Symbol, bool, VarId, Ty)]
  ) -> Result<Box<Self>, LinkerErr> {
    let mut coll = Collector::new(names, &mir);
    coll.collect_cfg(&init, &[]);
    let mut func_abi = IdxVec::from_default(coll.funcs.1.len());
    let mut func_code = IdxVec::from_default(coll.funcs.1.len());
    for &f in &coll.postorder {
      let sym = coll.funcs.1[f];
      if let Some(proc) = mir.get(&sym) {
        let (abi, code) = build_vcode(
          names, &coll.funcs.0, &func_abi, &coll.consts, &proc.body,
          proc.allocs.as_deref().expect("optimized already"),
          VCodeCtx::Proc(&proc.rets)
        )?.regalloc();
        // println!("mir {} = {:#?}", sym, proc);
        // println!("abi {} = {:#?}", sym, abi);
        // println!("code {} = {:#?}", sym, code);
        func_abi[f] = abi;
        func_code[f] = Some(code);
      }
    }

    let mut global_size = 0;
    let globals_out = globals.iter().filter_map(|&(g, r, v, _)| {
      if !r { return None }
      let off = global_size;
      let a = allocs.get(v);
      assert_ne!(a, AllocId::ZERO);
      let size = allocs[a].m.size.try_into().expect("overflow");
      global_size += size;
      Some((g, off, size))
    }).collect();
    let init_code = build_vcode(
      names, &coll.funcs.0, &func_abi, &coll.consts, &init, allocs, VCodeCtx::Start(globals)
    )?.regalloc().1;

    let mut pos = (TEXT_START + init_code.len + FUNCTION_ALIGN - 1) & !(FUNCTION_ALIGN - 1);
    let funcs = func_code.0.into_iter().map(|code| {
      let code = code.expect("impossible");
      let cur = pos;
      pos = (pos + code.len + FUNCTION_ALIGN - 1) & !(FUNCTION_ALIGN - 1);
      (cur, code)
    }).collect();

    Ok(Box::new(Self {
      consts: coll.consts,
      globals: globals_out,
      global_size,
      init: (init, init_code),
      func_names: coll.funcs,
      func_abi,
      funcs,
      postorder: coll.postorder,
      text_size: pos - TEXT_START,
      mir,
    }))
  }
}
