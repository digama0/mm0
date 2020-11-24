//! MMC type checking pass.
#![allow(unused)]

use std::rc::Rc;
use std::collections::{HashMap, HashSet};
use crate::elab::{Result as EResult, Elaborator, Environment, ElabError,
  environment::{AtomID, AtomData},
  lisp::{Uncons, LispVal, LispKind}, local_context::{try_get_span_from, try_get_span}};
use crate::util::{Span, FileSpan};
use super::{Compiler,
  types::{AST, Binop, Expr, Keyword, ProcKind, ProofExpr,
    Prop, PureExpr, Size, TuplePattern, Type, Unop},
  parser::head_keyword,
  nameck::{Type as NType, Prim, PrimType, PrimOp, PrimProp,
    Intrinsic, Entity, GlobalTC, Operator, ProcTC}};

enum InferType<'a> {
  Int,
  Unit,
  Bool,
  Star,
  Own(&'a Type),
  Ref(&'a Type),
  RefMut(&'a Type),
  Ty(&'a Type),
  Prop(&'a Prop),
  List(Box<[InferType<'a>]>),
}

impl<'a> InferType<'a> {
  fn ty(ty: &'a Type) -> Self {
    match ty {
      Type::Own(ty) => Self::Own(ty),
      Type::Ref(ty) => Self::Ref(ty),
      Type::RefMut(ty) => Self::RefMut(ty),
      ty => Self::Ty(ty),
    }
  }
}

/// Like rust, types can either be [`Copy`] or non-[`Copy`].
/// Unlike rust, non-copy types can still be used after they are moved
/// away, but their type changes to the [`Moved`] version of the type,
/// which represents the "copy core" of the type, essentially an integral
/// type of the same size as `sizeof(T)`.
///
/// [`Copy`]: CopyType::Copy
/// [`Moved`]: CopyType::Moved
#[derive(Debug)]
enum CopyType {
  /// This type is [`Copy`], so the moved version of the type is the
  /// same as the regular version.
  Copy,
  /// This type is not [`Copy`], and the moved version of the type is
  /// given here.
  Moved(Type),
}

/// The (permanent) type of a variable in the context, mixing together type variables,
/// regular variables and
#[derive(Debug)]
#[allow(variant_size_differences)]
enum GType {
  /// A type variable, of kind `*`
  Star,
  /// A regular variable, of the given type; the bool is true if this is ghost.
  /// The [`CopyType`] keeps track of the "moved away" version of the type; it
  /// is calculated lazily the first time the variable is re-used.
  Ty(bool, Type, Option<Box<CopyType>>),
  /// A hypothesis, which proves the given separating proposition
  Prop(Prop),
}

#[derive(Debug)]
struct Variable {
  /// The user-facing name of this variable, or `_` for auto names.
  user: AtomID,
  /// The target name of this variable.
  decl: AtomID,
  /// The type of this variable.
  ty: GType,
}

#[derive(Debug)]
enum VariableState {
  Owned,
  Copy,
  Moved,
}
#[derive(Debug)]
struct TypeState(Vec<VariableState>);

/// The type checker temporary.
#[derive(Debug)]
pub struct TypeChecker<'a> {
  /// A reference to the parent MMC compiler.
  mmc: &'a mut Compiler,
  /// A reference to the parent elaborator
  elab: &'a mut Elaborator,
  /// The base file span, for error reporting.
  fsp: FileSpan,
  /// The set of names that have been allocated in the declaration we are constructing.
  used_names: HashSet<AtomID>,
  /// Maps names from the MMC source in scope to their internal names.
  user_locals: HashMap<AtomID, AtomID>,
  /// The set of globals that are mutable in the current context (and their mapping to internal names).
  mut_globals: HashMap<AtomID, AtomID>,
  /// Maps internal indexes for variables in scope to their variable record.
  context: Vec<Variable>,
}

fn get_fresh_name(env: &mut Environment, mut base: Vec<u8>, mut bad: impl FnMut(AtomID, &AtomData) -> bool) -> AtomID {
  if !base.is_empty() {
    let a = env.get_atom(&base);
    if !bad(a, &env.data[a]) {return a}
  }
  base.push(b'_');
  let n = base.len();
  for i in 1.. {
    use std::io::Write;
    write!(&mut base, "{}", i).unwrap();
    let a = env.get_atom(&base);
    if !bad(a, &env.data[a]) {return a}
    base.truncate(n);
  }
  unreachable!()
}

impl Compiler {
  fn head_keyword(&self, e: &LispVal) -> Option<(Keyword, Uncons)> {
    head_keyword(&self.keywords, e)
  }
}

impl<'a> TypeChecker<'a> {
  /// Constructs a new [`TypeChecker`], which can be used to typecheck many `AST` items
  /// via [`typeck`](Self::typeck) and will reuse its internal buffers.
  pub fn new(mmc: &'a mut Compiler, elab: &'a mut Elaborator, fsp: FileSpan) -> Self {
    Self {mmc, elab, fsp,
      used_names: HashSet::new(),
      user_locals: HashMap::new(),
      mut_globals: HashMap::new(),
      context: Vec::new(),
    }
  }

  fn new_type_state(&self) -> TypeState {
    TypeState(self.context.iter().map(|v| match &v.ty {
      GType::Star => VariableState::Copy,
      GType::Ty(_, _, Some(b)) if matches!(**b, CopyType::Copy) => VariableState::Copy,
      _ => VariableState::Owned,
    }).collect())
  }

  fn todo<T, U>(&self, _: U) -> EResult<T> { Err(ElabError::new_e(self.fsp.span, "unimplemented")) }

  fn try_get_span(&self, e: &LispVal) -> Span {
    try_get_span(&self.fsp, e)
  }

  fn get_fresh_decl(&mut self, base: AtomID) -> AtomID {
    let mut s = self.mmc.prefix.clone();
    s.extend_from_slice(&self.elab.data[base].name);
    get_fresh_name(&mut self.elab, s, |_, ad| ad.decl.is_some())
  }

  fn get_fresh_local(&mut self, base: AtomID) -> AtomID {
    let s = if base == AtomID::UNDER {Vec::new()} else {(*self.elab.data[base].name).into()};
    let used_names = &self.used_names;
    get_fresh_name(&mut self.elab, s, |a, ad| used_names.contains(&a) || ad.decl.is_some())
  }

  fn find(&self, a: AtomID) -> Option<&Variable> {
    self.context.iter().find(|&v| v.decl == a)
  }

  fn infer_type(&'a self, e: &'a PureExpr) -> InferType<'a> {
    match e {
      &PureExpr::Var(i) => match &self.find(i).expect("variable not found").ty {
        GType::Ty(_, ty, _) => InferType::ty(ty),
        GType::Star => InferType::Star,
        GType::Prop(p) => InferType::Prop(p),
      },
      PureExpr::Unit => InferType::Unit,
      PureExpr::Bool(_) |
      PureExpr::Unop(Unop::Not, _) |
      PureExpr::Binop(Binop::And, _, _) |
      PureExpr::Binop(Binop::Or, _, _) |
      PureExpr::Binop(Binop::Lt, _, _) |
      PureExpr::Binop(Binop::Le, _, _) |
      PureExpr::Binop(Binop::Eq, _, _) |
      PureExpr::Binop(Binop::Ne, _, _) => InferType::Bool,
      PureExpr::Int(_) |
      PureExpr::Unop(Unop::BitNot(_), _) |
      PureExpr::Binop(Binop::Add, _, _) |
      PureExpr::Binop(Binop::Mul, _, _) |
      PureExpr::Binop(Binop::BitAnd, _, _) |
      PureExpr::Binop(Binop::BitOr, _, _) |
      PureExpr::Binop(Binop::BitXor, _, _) => InferType::Int,
      PureExpr::Index(a, _, _) => match self.infer_type(a) {
        InferType::Ty(Type::Array(ty, _)) => InferType::Ty(ty),
        _ => unreachable!(),
      },
      PureExpr::Tuple(es) => InferType::List(
        es.iter().map(|e| self.infer_type(e)).collect::<Vec<_>>().into()),
      PureExpr::DerefOwn(e) => match self.infer_type(e) {
        InferType::Ty(Type::Own(ty)) => InferType::Ty(ty),
        InferType::Own(ty) => InferType::Ty(ty),
        _ => unreachable!(),
      },
      PureExpr::Deref(e) => match self.infer_type(e) {
        InferType::Ty(Type::Ref(ty)) => InferType::Ty(ty),
        InferType::Ref(ty) => InferType::Ty(ty),
        _ => unreachable!(),
      },
      PureExpr::DerefMut(e) => match self.infer_type(e) {
        InferType::Ty(Type::RefMut(ty)) => InferType::Ty(ty),
        InferType::RefMut(ty) => InferType::Ty(ty),
        _ => unreachable!(),
      },
      PureExpr::Ghost(e) => self.infer_type(e)
    }
  }

  fn probably_a_type(&self, e: &LispVal) -> bool {
    let mut u = Uncons::New(e.clone());
    let (head, u) = match u.next() {
      None if u.is_empty() => return true,
      None => (u.into(), None),
      Some(head) => (head, Some(u)),
    };
    let name = if let Some(name) = head.as_atom() {name} else {return false};
    if name == AtomID::UNDER { return false }
    match self.mmc.names.get(&name) {
      Some(Entity::Type(_)) => true,
      Some(Entity::Prim(Prim {ty: Some(prim), ..})) => match prim {
        PrimType::And |
        PrimType::Or => u.and_then(|mut u| u.next()).map_or(true, |e| self.probably_a_type(&e)),
        _ => true,
      },
      _ => false
    }
  }

  fn check_ty(&self, e: &LispVal) -> Result<Type, ElabError> {
    let mut u = Uncons::New(e.clone());
    let (head, args) = match u.next() {
      None if u.is_empty() => return Ok(Type::Unit),
      None => (u.into(), vec![]),
      Some(head) => (head, u.collect()),
    };
    macro_rules! check_tys {($args:expr) => {{
      let mut tys = Vec::with_capacity($args.len());
      for e in $args { tys.push(self.check_ty(e)?) }
      tys.into()
    }}}
    let name = head.as_atom().ok_or_else(||
      ElabError::new_e(self.try_get_span(&head), "expected an atom"))?;
    if name == AtomID::UNDER {
      return Err(ElabError::new_e(self.try_get_span(&head), "expecting a type"));
    }
    match self.mmc.names.get(&name) {
      Some(&Entity::Prim(Prim {ty: Some(prim), ..})) => match (prim, &*args) {
        (PrimType::Array, [ty, n]) => Ok(Type::Array(
          Box::new(self.check_ty(ty)?),
          Rc::new(self.check_pure_expr(n, Some(&Type::UInt(Size::Inf)))?))),
        (PrimType::Bool, []) => Ok(Type::Bool),
        (PrimType::I8, []) => Ok(Type::Int(Size::S8)),
        (PrimType::I16, []) => Ok(Type::Int(Size::S16)),
        (PrimType::I32, []) => Ok(Type::Int(Size::S32)),
        (PrimType::I64, []) => Ok(Type::Int(Size::S64)),
        (PrimType::Int, []) => Ok(Type::Int(Size::Inf)),
        (PrimType::U8, []) => Ok(Type::UInt(Size::S8)),
        (PrimType::U16, []) => Ok(Type::UInt(Size::S16)),
        (PrimType::U32, []) => Ok(Type::UInt(Size::S32)),
        (PrimType::U64, []) => Ok(Type::UInt(Size::S64)),
        (PrimType::Nat, []) => Ok(Type::UInt(Size::Inf)),
        (PrimType::Own, [ty]) => Ok(Type::Own(Box::new(self.check_ty(ty)?))),
        (PrimType::Ref, [ty]) => Ok(Type::Ref(Box::new(self.check_ty(ty)?))),
        (PrimType::RefMut, [ty]) => Ok(Type::RefMut(Box::new(self.check_ty(ty)?))),
        (PrimType::List, args) => Ok(Type::List(check_tys!(args))),
        (PrimType::And, args) => Ok(Type::And(check_tys!(args))),
        (PrimType::Or, args) => Ok(Type::Or(check_tys!(args))),
        (PrimType::Ghost, [ty]) => Ok(Type::Ghost(Box::new(self.check_ty(ty)?))),
        _ => Err(ElabError::new_e(self.try_get_span(e), "unexpected number of arguments"))
      }
      Some(Entity::Type(NType::Unchecked)) => Err(
        ElabError::new_e(self.try_get_span(&head), "forward type references are not allowed")),
      Some(_) => Err(ElabError::new_e(self.try_get_span(&head), "expected a type")),
      None => match self.user_locals.get(&name) {
        Some(&i) if matches!(self.find(i), Some(Variable {ty: GType::Star, ..})) => Ok(Type::Var(i)),
        _ => Err(ElabError::new_e(self.try_get_span(e),
          format!("undeclared type {}", self.elab.print(&head))))
      }
    }
  }

  fn check_lassoc1_expr(&self,
    arg_1: &LispVal,
    args: &[LispVal],
    binop: Binop,
    tgt: Option<&Type>,
  ) -> Result<PureExpr, ElabError> {
    let mut e = self.check_pure_expr(arg_1, tgt)?;
    for arg in args {
      e = PureExpr::Binop(binop, Rc::new(e), Rc::new(self.check_pure_expr(arg, tgt)?))
    }
    Ok(e)
  }

  fn check_lassoc_expr(&self,
    args: &[LispVal],
    f0: impl FnOnce() -> Result<PureExpr, ElabError>,
    f1: impl FnOnce(PureExpr) -> Result<PureExpr, ElabError>,
    binop: Binop,
    tgt: Option<&Type>,
  ) -> Result<PureExpr, ElabError> {
    if let Some((arg_1, rest)) = args.split_first() {
      f1(self.check_lassoc1_expr(arg_1, rest, binop, tgt)?)
    } else {f0()}
  }

  fn check_ineq(&self, args: &[LispVal], binop: Binop) -> Result<PureExpr, ElabError> {
    if let Some((arg_1, rest)) = args.split_first() {
      let arg_1 = self.check_pure_expr(arg_1, Some(&Type::Int(Size::Inf)))?;
      if let Some((arg_2, rest)) = rest.split_first() {
        let mut arg_2 = Rc::new(self.check_pure_expr(arg_2, Some(&Type::Int(Size::Inf)))?);
        let mut e = PureExpr::Binop(binop, Rc::new(arg_1), arg_2.clone());
        for arg_3 in rest {
          let arg_3 = Rc::new(self.check_pure_expr(arg_3, Some(&Type::Int(Size::Inf)))?);
          e = PureExpr::Binop(Binop::And, Rc::new(e), Rc::new(PureExpr::Binop(binop, arg_2, arg_3.clone())));
          arg_2 = arg_3;
        }
        Ok(e)
      } else { Ok(arg_1) }
    } else { Ok(PureExpr::Bool(true)) }
  }

  fn check_pure_expr_list(&self, args: &[LispVal], tgt: Option<&Type>,
      err: impl FnOnce(String) -> ElabError) -> Result<PureExpr, ElabError> {
    let mut vec = Vec::with_capacity(args.len());
    match tgt {
      None => for e in args { vec.push(self.check_pure_expr(e, None)?) }
      Some(Type::List(ts)) if ts.len() == args.len() =>
        for (e, ty) in (&*args).iter().zip(&**ts) {
          vec.push(self.check_pure_expr(e, Some(ty))?)
        },
      Some(ty) => return Err(err(format!("type error, expected {:?}", ty))),
    }
    Ok(PureExpr::Tuple(vec.into()))
  }

  fn check_pure_expr(&self, e: &LispVal, tgt: Option<&Type>) -> Result<PureExpr, ElabError> {
    let mut u = Uncons::New(e.clone());
    let (head, args) = match u.next() {
      None if u.is_empty() => return Ok(PureExpr::Unit),
      None => (u.into(), vec![]),
      Some(head) => (head, u.collect()),
    };
    macro_rules! err {($($e:expr),*) => {
      Err(ElabError::new_e(self.try_get_span(&head), format!($($e),*)))
    }}
    macro_rules! check_tgt {($ty:pat, $s:expr) => {
      if !tgt.map_or(true, |tgt| matches!(tgt, $ty)) {
        return err!(concat!("type error, expected ", $s))
      }
    }}
    macro_rules! get_int_tgt {() => {
      match tgt {
        None => &Type::Int(Size::Inf),
        Some(ty@Type::Int(_)) => ty,
        Some(ty@Type::UInt(_)) => ty,
        Some(_) => return err!("type error, expected an integer"),
      }
    }}
    if let Some(name) = head.as_atom() {
      if name == AtomID::UNDER { return err!("holes not implemented") }
      match self.mmc.names.get(&name) {
        Some(Entity::Const(GlobalTC::Unchecked)) => err!("forward referencing constants is not allowed"),
        Some(Entity::Prim(Prim {op: Some(prim), ..})) => match (prim, &*args) {
          (PrimOp::Add, args) =>
            self.check_lassoc_expr(args, || Ok(PureExpr::Int(0.into())), Ok, Binop::Add, Some(get_int_tgt!())),
          (PrimOp::And, args) => {
            check_tgt!(Type::Bool, "a bool");
            self.check_lassoc_expr(args, || Ok(PureExpr::Bool(true)), Ok, Binop::And, Some(&Type::Bool))
          }
          (PrimOp::Or, args) => {
            check_tgt!(Type::Bool, "a bool");
            self.check_lassoc_expr(args, || Ok(PureExpr::Bool(false)), Ok, Binop::Or, Some(&Type::Bool))
          }
          (PrimOp::Assert, _) => err!("type error, expected a pure expr"),
          (PrimOp::BitAnd, args) =>
            self.check_lassoc_expr(args, || Ok(PureExpr::Int((-1).into())), Ok, Binop::BitAnd, Some(get_int_tgt!())),
          (PrimOp::BitNot, args) => {
            let (sz, ty) = match tgt {
              None => (Size::Inf, &Type::Int(Size::Inf)),
              Some(ty) => match ty {
                Type::Int(_) => (Size::Inf, ty),
                &Type::UInt(sz) => (sz, ty),
                _ => return err!("type error, expected an integer"),
              }
            };
            self.check_lassoc_expr(args, || Ok(PureExpr::Int((-1).into())),
              |e| Ok(PureExpr::Unop(Unop::BitNot(sz), Rc::new(e))), Binop::BitOr, Some(ty))
          }
          (PrimOp::BitOr, args) =>
            self.check_lassoc_expr(args, || Ok(PureExpr::Int(0.into())), Ok, Binop::BitOr, Some(get_int_tgt!())),
          (PrimOp::BitXor, args) =>
            self.check_lassoc_expr(args, || Ok(PureExpr::Int(0.into())), Ok, Binop::BitXor, Some(get_int_tgt!())),
          (PrimOp::Index, args) => {
            enum AutoDeref { Own, Ref, Mut }
            let (arr, idx, pf) = match args {
              [arr, idx] => (arr, idx, None),
              [arr, idx, pf] => (arr, idx, Some(pf)),
              _ => return err!("expected 2 or 3 arguments"),
            };
            let mut arr = self.check_pure_expr(arr, None)?;
            let idx = Rc::new(self.check_pure_expr(idx, Some(&Type::UInt(Size::Inf)))?);
            let mut aty = self.infer_type(&arr);
            let mut derefs = vec![];
            let len = loop {
              match aty {
                InferType::Own(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Own); }
                InferType::Ref(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Ref); }
                InferType::RefMut(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Mut); }
                InferType::Ty(Type::Array(_, len)) => break len.clone(),
                _ => return err!("type error, expcted an array"),
              }
            };
            for s in derefs {
              arr = match s {
                AutoDeref::Own => PureExpr::DerefOwn(Box::new(arr)),
                AutoDeref::Ref => PureExpr::Deref(Box::new(arr)),
                AutoDeref::Mut => PureExpr::DerefMut(Box::new(arr)),
              }
            }
            let prop = PureExpr::Binop(Binop::Lt, idx.clone(), len);
            let pf = match pf {
              Some(pf) => self.check_proof(pf, Some(Prop::Pure(Rc::new(prop))))?,
              None => ProofExpr::Assert(Box::new(prop)),
            };
            Ok(PureExpr::Index(Box::new(arr), idx, Box::new(pf)))
          }
          (PrimOp::List, args) => self.check_pure_expr_list(args, tgt, |err| ElabError::new_e(self.try_get_span(&head), err)),
          (PrimOp::Mul, args) =>
            self.check_lassoc_expr(args, || Ok(PureExpr::Int(1.into())), Ok, Binop::Mul, Some(get_int_tgt!())),
          (PrimOp::Not, args) => {
            check_tgt!(Type::Bool, "a bool");
            self.check_lassoc_expr(args, || Ok(PureExpr::Bool(true)),
              |e| Ok(PureExpr::Unop(Unop::Not, Rc::new(e))), Binop::Or, Some(&Type::Bool))
          }
          (PrimOp::Le, args) => { check_tgt!(Type::Bool, "a bool"); self.check_ineq(args, Binop::Le) }
          (PrimOp::Lt, args) => { check_tgt!(Type::Bool, "a bool"); self.check_ineq(args, Binop::Lt) }
          (PrimOp::Eq, args) => { check_tgt!(Type::Bool, "a bool"); self.check_ineq(args, Binop::Eq) }
          (PrimOp::Ne, args) => { check_tgt!(Type::Bool, "a bool"); self.check_ineq(args, Binop::Ne) }
          (PrimOp::Ghost, args) => Ok(PureExpr::Ghost(Rc::new({
            if let [e] = args {
              self.check_pure_expr(e, tgt)?
            } else {
              self.check_pure_expr_list(args, tgt, |err| ElabError::new_e(self.try_get_span(&head), err))?
            }
          }))),
          (PrimOp::Pun, _) |
          (PrimOp::Slice, _) |
          (PrimOp::TypeofBang, _) |
          (PrimOp::Typeof, _) =>
            Err(ElabError::new_e(self.try_get_span(&head), "not a pure operation")),
        }
        Some(Entity::Op(Operator::Proc(_, ProcTC::Unchecked))) => Err(ElabError::new_e(
          self.try_get_span(&head), "forward referencing a procedure")),
        Some(_) => Err(ElabError::new_e(self.try_get_span(&head), "expected a function/operation")),
        None => match self.user_locals.get(&name) {
          Some(&i) => match &self.find(i) {
            Some(Variable {ty: GType::Ty(_, ty, _), ..}) => match tgt {
              None |
              Some(_) /* TODO: if *tgt == ty */ => Ok(PureExpr::Var(i)),
            },
            _ => Err(ElabError::new_e(self.try_get_span(&head), "expected a regular variable")),
          },
          _ => Err(ElabError::new_e(self.try_get_span(&head),
            format!("undeclared type or expression {}", self.elab.print(&head))))
        }
      }
    } else {
      if !args.is_empty() {
        return Err(ElabError::new_e(self.try_get_span(e), "unexpected arguments"))
      }
      head.unwrapped(|e| match *e {
        LispKind::Number(ref n) => Ok(PureExpr::Int(n.clone())),
        LispKind::Bool(b) => Ok(PureExpr::Bool(b)),
        _ => Err(ElabError::new_e(self.try_get_span(&head), "unexpected expression")),
      })
    }
  }

  fn check_prop(&self, e: &LispVal) -> Result<Prop, ElabError> {
    let mut u = Uncons::New(e.clone());
    let (head, args) = match u.next() {
      None if u.is_empty() =>
        return Err(ElabError::new_e(self.try_get_span(e), "expecting a proposition, got ()")),
      None => (u.into(), vec![]),
      Some(head) => (head, u.collect()),
    };
    match head.as_atom().and_then(|name| self.mmc.names.get(&name)) {
      Some(Entity::Prim(Prim {prop: Some(prim), ..})) => match (prim, &*args) {
        (PrimProp::All, args) if !args.is_empty() => self.todo(args),
        (PrimProp::Ex, args) if !args.is_empty() => self.todo(args),
        (PrimProp::And, args) |
        (PrimProp::Or, args) |
        (PrimProp::Imp, args) |
        (PrimProp::Star, args) |
        (PrimProp::Wand, args) => self.todo(args),
        _ => Err(ElabError::new_e(self.try_get_span(&head), "incorrect number of arguments")),
      }
      _ => self.check_pure_expr(e, Some(&Type::Bool)).map(|e| Prop::Pure(Rc::new(e)))
    }
  }

  fn check_proof(&self, e: &LispVal, tgt: Option<Prop>) -> EResult<ProofExpr> {
    self.todo((e, tgt))
  }

  /// Add a list of arguments to the context.
  fn add_args_to_context(&mut self, args: &[TuplePattern], tyvar_allowed: bool, hyp_allowed: bool) -> EResult<()> {
    self.context.reserve(args.len());
    for arg in args {
      match arg {
        TuplePattern::Name(_, _, _) => {}
        TuplePattern::Typed(b, _) if matches!(**b, TuplePattern::Name(_, _, _)) => {}
        _ => return Err(ElabError::new_e(self.fsp.span,
          "tuple patterns in argument position are not implemented")),
      }
      let user = arg.name();
      let decl = self.get_fresh_local(user);
      if user != AtomID::UNDER && self.user_locals.insert(user, decl).is_some() {
        return Err(ElabError::new_e(try_get_span_from(&self.fsp, arg.fspan()), "variable declared twice"))
      }
      self.used_names.insert(decl);
      let is_ty = tyvar_allowed && arg.ty().as_atom().map_or(false, |a| a == AtomID::UNDER ||
        matches!(self.mmc.keywords.get(&a), Some(Keyword::Star)));
      let ty = if is_ty {GType::Star} else {
        let ty = arg.ty();
        if !hyp_allowed || self.probably_a_type(&ty) {
          GType::Ty(arg.ghost(), self.check_ty(&ty)?, None)
        } else {
          GType::Prop(self.check_prop(&ty)?)
        }
      };
      self.context.push(Variable {user, decl, ty});
    }
    Ok(())
  }

  fn check_expr(&mut self, ts: &mut TypeState, e: LispVal, tgt: Option<&Type>) -> EResult<Expr> {
    self.todo((ts, e, tgt))
  }

  fn check_stmts(&mut self, ts: &mut TypeState, u: Uncons, tgt: Option<&Type>) -> EResult<Box<[Expr]>> {
    Ok(match u.len().checked_sub(1) {
      None if tgt.map_or(true, |tgt| matches!(tgt, Type::Unit)) => Box::new([]),
      None => return Err(ElabError::new_e(self.try_get_span(&u.as_lisp()), "expected a value, got empty block")),
      Some(n) => u.enumerate()
        .map(|(i, e)| self.check_expr(ts, e, if i == n {tgt} else {None}))
        .collect::<EResult<Vec<_>>>()?.into()
    })
  }

  /// Performs type checking of the input AST.
  pub fn typeck(&mut self, item: &AST) -> EResult<()> {
    self.used_names.clear();
    self.user_locals.clear();
    self.context.clear();
    self.mut_globals.clear();
    match item {
      AST::Proc(proc) => match proc.kind {
        ProcKind::Func =>
          return Err(ElabError::new_e(
            try_get_span_from(&self.fsp, proc.span.as_ref()), "func is not implemented, use proc")),
        ProcKind::ProcDecl => {}
        ProcKind::Intrinsic => {
          let intrinsic = Intrinsic::from_bytes(&self.elab.data[proc.name].name)
            .ok_or_else(|| ElabError::new_e(
              try_get_span_from(&self.fsp, proc.span.as_ref()), "unknown intrinsic"))?;
          // TODO: check intrinsic signature is correct?
          match self.mmc.names.get_mut(&proc.name) {
            Some(Entity::Op(Operator::Proc(_, tc @ ProcTC::Unchecked))) =>
              *tc = ProcTC::Intrinsic(intrinsic),
            _ => unreachable!()
          }
        }
        ProcKind::Proc => {
          // let Proc {kind, name,
          //   ref span, ref args, ref rets, ref variant,
          //   body: Body {ref muts, ref stmts}} = **proc;
          self.add_args_to_context(&proc.args, false, true)?;
          self.add_args_to_context(&proc.rets, false, true)?;
          let rets = self.context.drain(proc.args.len()..).collect::<Vec<_>>();
          if let Some((e, _)) = &proc.variant {
            return Err(ElabError::new_e(self.try_get_span(e), "proc variants are not implemented"))
          }
          for &(a, ref fsp) in &*proc.body.muts {
            match self.mmc.names.get(&a) {
              Some(Entity::Global(GlobalTC::Unchecked)) =>
                return Err(ElabError::new_e(try_get_span_from(&self.fsp, fsp.as_ref()),
                  "forward referencing globals is supported")),
              Some(&Entity::Global(GlobalTC::Checked(_, decl, _))) => {self.mut_globals.insert(a, decl);}
              _ => return Err(ElabError::new_e(try_get_span_from(&self.fsp, fsp.as_ref()),
                "unknown global")),
            }
          }
          let mut ts = self.new_type_state();
          let body = self.check_stmts(&mut ts, proc.body.stmts.clone(), None);
          // println!("{:?}", proc);
          self.todo((rets, body))?;
          return Err(ElabError::new_e(
            try_get_span_from(&self.fsp, proc.span.as_ref()), "unimplemented"))
        }
      }
      AST::Global {lhs, rhs} => self.todo((lhs, rhs))?,
      AST::Const {lhs, rhs} => self.todo((lhs, rhs))?,
      &AST::Typedef {name, ref span, ref args, ref val} => {
        self.add_args_to_context(args, true, false)?;
        let val = self.check_ty(val)?;
        let dname = self.get_fresh_decl(name);
        // TODO: write def dname := val
        if let Entity::Type(ty @ NType::Unchecked) = self.mmc.names.get_mut(&name).unwrap() {
          *ty = NType::Checked(span.clone(), dname, Rc::new(val))
        } else {unreachable!()}
      },
      &AST::Struct {name, ref span, ref args, ref fields} => {
        self.add_args_to_context(args, true, false)?;
        self.add_args_to_context(fields, false, true)?;
        let fields = self.context.drain(args.len()..)
          .map(|v| match v.ty {
            GType::Star => unreachable!(),
            GType::Ty(g, ty, _) => Type::ghost_if(g, ty),
            GType::Prop(p) => Type::Prop(Box::new(p)),
          }).collect::<Vec<Type>>();
        let dname = self.get_fresh_decl(name);
        // TODO: write def dname := val
        if let Entity::Type(ty @ NType::Unchecked) = self.mmc.names.get_mut(&name).unwrap() {
          *ty = NType::Checked(span.clone(), dname, Rc::new(Type::Struct(fields.into())))
        } else {unreachable!()}
      }
    }
    Ok(())
  }
}
