//! The legalization pass, which transforms certain patterns on unbounded integers into
//! compilable expressions.

use std::collections::HashMap;

use super::super::types::{self, Size, IntTy};
#[allow(clippy::wildcard_imports)] use super::*;

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
enum Predicate {
  As(IntTy),
}

#[derive(Clone, Debug)]
enum PackedOp {
  Copy(VarId),
  Const(Box<Constant>),
}
impl PackedOp {
  fn unpack(self) -> Operand {
    match self {
      Self::Copy(v) => Operand::Copy(v.into()),
      Self::Const(c) => Operand::Const(c)
    }
  }
}

impl Replace<Statement> for RValue {
  fn replace(self, t: &mut Statement) {
    if let Statement::Let(_, _, _, rv) = t { *rv = self }
  }
}
struct Legalizer<'a> {
  max_var: &'a mut VarId,
  stmts: &'a [Statement],
  infinite_vars: HashMap<VarId, usize>,
  buffer: VecPatch<Statement, RValue>,
  generated: HashMap<(VarId, Predicate), PackedOp>,
}

impl<'a> Legalizer<'a> {
  fn new(max_var: &'a mut VarId, stmts: &'a [Statement]) -> Self {
    let mut infinite_vars = HashMap::default();
    for (i, s) in stmts.iter().enumerate() {
      s.foreach_def(|v, r, _, ty| if r {
        if let Some(ity) = ty.as_int_ty() {
          if ity.size() == Size::Inf { infinite_vars.insert(v, i); }
        }
      })
    }
    Self {
      max_var,
      stmts,
      infinite_vars,
      buffer: Default::default(),
      generated: Default::default()
    }
  }

  fn try_legalize(&mut self, v: VarId, pred: Predicate) -> Option<PackedOp> {
    let i = if let Some(&i) = self.infinite_vars.get(&v) { i } else {
      return Some(PackedOp::Copy(v))
    };
    if let Some(res) = self.generated.get(&(v, pred)) { return Some(res.clone()) }
    let res = (|| match &self.stmts[i] {
      Statement::Let(LetKind::Let(_, e), _, _, rv) => {
        if let RValue::Use(o) | RValue::Cast(_, o, _) = rv {
          return self.try_legalize_operand(o, pred)
        }
        match pred {
          Predicate::As(ity) => match rv {
            RValue::Unop(op, o) => {
              let op = op.as_(ity)?;
              let o = self.try_legalize_operand(o, Predicate::As(ity))?.unpack();
              let v = self.max_var.fresh();
              self.buffer.insert(i+1, Statement::Let(
                LetKind::Let(v, e.as_ref().map(|e|
                  Expr::new(ExprKind::Unop(types::Unop::As(ity), e.clone())))),
                true, Ty::new(TyKind::Int(ity)),
                RValue::Unop(op, o)));
              Some(PackedOp::Copy(v))
            }
            RValue::Binop(op, o1, o2) => {
              let op = op.as_(ity)?;
              let o1 = self.try_legalize_operand(o1, Predicate::As(ity))?.unpack();
              let o2 = self.try_legalize_operand(o2, Predicate::As(ity))?.unpack();
              let v = self.max_var.fresh();
              self.buffer.insert(i+1, Statement::Let(
                LetKind::Let(v, e.as_ref().map(|e|
                  Expr::new(ExprKind::Unop(types::Unop::As(ity), e.clone())))),
                true, Ty::new(TyKind::Int(ity)),
                RValue::Binop(op, o1, o2)));
              Some(PackedOp::Copy(v))
            }
            _ => None,
          }
        }
      }
      Statement::Assign(p, _, _, vars) if vars.len() == 1 => self.try_legalize_place(p, pred),
      _ => None
    })()?;
    self.generated.insert((v, pred), res.clone());
    Some(res)
  }

  fn try_legalize_place(&mut self, p: &Place, pred: Predicate) -> Option<PackedOp> {
    if p.proj.is_empty() { self.try_legalize(p.local, pred) } else { None }
  }

  fn try_legalize_operand(&mut self, o: &Operand, pred: Predicate) -> Option<PackedOp> {
    match o.place() {
      Ok(p) => self.try_legalize_place(p, pred),
      Err(c) => match pred {
        Predicate::As(ity) => Some(PackedOp::Const(Box::new(c.as_(ity))))
      }
    }
  }

  fn is_infinite_var(&self, o: &Operand) -> bool {
    if let Ok(p) = o.place() {
      if p.proj.is_empty() { return self.infinite_vars.contains_key(&p.local) }
    }
    false
  }

  fn legalize_all(mut self) -> VecPatch<Statement, RValue> {
    for (i, s) in self.stmts.iter().enumerate().rev() {
      if let Statement::Let(LetKind::Let(..), true, ty, rv) = s {
        match rv {
          &RValue::Unop(Unop::As(from, to), ref o) if from.size() == Size::Inf => {
            if self.is_infinite_var(o) {
              if let Some(o) = self.try_legalize_operand(o, Predicate::As(to)) {
                self.buffer.replace(i, RValue::Unop(Unop::As(from, to), o.unpack()))
              }
            }
          }
          RValue::Cast(ck, o, tyin) => if_chain! {
            if self.is_infinite_var(o);
            if let (Some(ity), Some(ityin)) = (ty.as_int_ty(), tyin.as_int_ty());
            if ity.size() != Size::Inf && ityin.size() == Size::Inf;
            if let Some(o) = self.try_legalize_operand(o, Predicate::As(ity));
            then {
              self.buffer.replace(i, match o {
                PackedOp::Copy(v) =>
                  RValue::Pun(PunKind::DropAs(Box::new((ityin, ck.clone()))), v.into()),
                PackedOp::Const(c) => (*c).into()
              })
            }
          },
          // TODO: Compile equations like x + y < 17
          // RValue::Binop(op, _, _) if match op {
          //   Binop::Lt(ity) | Binop::Le(ity) |
          //   Binop::Eq(ity) | Binop::Ne(ity) => ity.size() == Size::Inf,
          //   _ => false,
          // } => {}
          _ => {}
        }
      }
    }
    self.buffer
  }
}

impl Cfg {
  /// Run the legalization pass over the CFG, which is primarily responsible for normalizing
  /// expressions like `(x + y + z) as u64` into `x +64 y +64 z` where `+64` is wrapping addition.
  /// (In the future, more expressions with unbounded intermediates may be turned into compilable
  /// operations here.)
  pub fn legalize(&mut self) {
    for (_, bl) in self.blocks.enum_iter_mut() {
      Legalizer::new(&mut self.max_var, &bl.stmts).legalize_all().apply(&mut bl.stmts);
    }
  }
}
