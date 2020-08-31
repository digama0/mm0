//! MMC type checking pass.
use std::rc::Rc;
use std::collections::{HashMap, HashSet};
use std::str::FromStr;
use std::mem;
use itertools::Itertools;
use num::BigInt;
use crate::elab::{Result as EResult, Elaborator, Environment, ElabError,
  environment::{AtomID, AtomData},
  lisp::{Uncons, LispVal, LispKind}, local_context::{try_get_span_from, try_get_span}};
use crate::util::{Span, FileSpan, BoxError};
use super::{parser::{Proc, AST, Keyword, ProcKind, Arg}, Compiler,
  nameck::{Type as NType, PrimType, PrimProc, Intrinsic, Entity, GlobalTC, Operator, ProcTC}};

/// Possible sizes for integer operations and types.
#[derive(Copy, Clone, Debug)]
pub enum Size {
  /// 8 bits, or 1 byte. Used for `u8` and `i8`.
  S8,
  /// 16 bits, or 2 bytes. Used for `u16` and `i16`.
  S16,
  /// 32 bits, or 4 bytes. Used for `u32` and `i32`.
  S32,
  /// 64 bits, or 8 bytes. Used for `u64` and `i64`.
  S64,
  /// Unbounded size. Used for `nat` and `int`. (These types are only legal for
  /// ghost variables, but they are also used to indicate "correct to an unbounded model"
  /// for operations like `Unop::BitNot` when it makes sense. We do not actually support
  /// bignum compilation.)
  Inf,
}

/// (Elaborated) unary operations.
#[derive(Copy, Clone, Debug)]
pub enum Unop {
  /// Logical (boolean) NOT
  Not,
  /// Bitwise NOT. For fixed size this is the operation `2^n - x - 1`, and
  /// for infinite size this is `-x - 1`. Note that signed NOT
  BitNot(Size),
}

/// (Elaborated) binary operations.
#[derive(Copy, Clone, Debug)]
pub enum Binop {
  /// Integer addition
  Add,
  /// Integer multiplication
  Mul,
  /// Logical (boolean) AND
  And,
  /// Logical (boolean) OR
  Or,
  /// Bitwise AND, for signed or unsigned integers of any size
  BitAnd,
  /// Bitwise OR, for signed or unsigned integers of any size
  BitOr,
  /// Bitwise XOR, for signed or unsigned integers of any size
  BitXor,
  /// Less than, for signed or unsigned integers of any size
  Lt,
  /// Less than or equal, for signed or unsigned integers of any size
  Le,
  /// Equal, for signed or unsigned integers of any size
  Eq,
  /// Not equal, for signed or unsigned integers of any size
  Ne,
}

/// A proof expression, or "hypothesis".
#[derive(Debug)]
pub enum ProofExpr {
  /// An assertion expression `(assert p): p`.
  Assert(Box<PureExpr>),
}

/// Pure expressions in an abstract domain. The interpretation depends on the type,
/// but most expressions operate on the type of (signed unbounded) integers.
#[derive(Debug)]
pub enum PureExpr {
  /// A variable.
  Var(usize),
  /// An integer or natural number.
  Int(BigInt),
  /// The unit value `()`.
  Unit,
  /// A boolean literal.
  Bool(bool),
  /// A unary operation.
  Unop(Unop, Rc<PureExpr>),
  /// A binary operation.
  Binop(Binop, Rc<PureExpr>, Rc<PureExpr>),
  /// A tuple constructor.
  Tuple(Box<[PureExpr]>),
  /// An index operation `(index a i h): T` where `a: (array T n)`,
  /// `i: nat`, and `h: i < n`.
  Index(Box<PureExpr>, Rc<PureExpr>, Box<ProofExpr>),
  /// An deref operation `(* x): T` where `x: (own T)`.
  DerefOwn(Box<PureExpr>),
  /// An deref operation `(* x): T` where `x: (& T)`.
  Deref(Box<PureExpr>),
  /// An deref operation `(* x): T` where `x: (&mut T)`.
  DerefMut(Box<PureExpr>),
}

/// A type, which classifies regular variables (not type variables, not hypotheses).
#[derive(Debug)]
pub enum Type {
  /// A type variable.
  Var(usize),
  /// `()` is the type with one element; `sizeof () = 0`.
  Unit,
  /// `bool` is the type of booleans, that is, bytes which are 0 or 1; `sizeof bool = 1`.
  Bool,
  /// `i(8*N)` is the type of N byte signed integers `sizeof i(8*N) = N`.
  Int(Size),
  /// `u(8*N)` is the type of N byte unsigned integers; `sizeof u(8*N) = N`.
  UInt(Size),
  /// The type `(array T n)` is an array of `n` elements of type `T`;
  /// `sizeof (array T n) = sizeof T * n`.
  Array(Box<Type>, Rc<PureExpr>),
  /// `(own T)` is a type of owned pointers. The typehood predicate is
  /// `x :> own T` iff `E. v (x |-> v) * v :> T`.
  Own(Box<Type>),
  /// `(& T)` is a type of borrowed pointers. This type is treated specially;
  /// the `x |-> v` assumption is stored separately from regular types, and
  /// `(* x)` is treated as sugar for `v`.
  Ref(Box<Type>),
  /// `(&mut T)` is a type of mutable pointers. This is also treated specially;
  /// it is sugar for `(mut {x : (own T)})`, which is to say `x` has
  /// type `own T` in the function but must also be passed back out of the
  /// function.
  RefMut(Box<Type>),
  /// `(list A B C)` is a tuple type with elements `A, B, C`;
  /// `sizeof (list A B C) = sizeof A + sizeof B + sizeof C`.
  List(Box<[Type]>),
  /// `(inter A B C)` is an intersection type of `A, B, C`;
  /// `sizeof (inter A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (inter A B C)` iff
  /// `x :> A /\ x :> B /\ x :> C`. (Note that this is regular conjunction,
  /// not separating conjunction.)
  Inter(Box<[Type]>),
  /// `(union A B C)` is an undiscriminated anonymous union of types `A, B, C`.
  /// `sizeof (union A B C) = max (sizeof A, sizeof B, sizeof C)`, and
  /// the typehood predicate is `x :> (union A B C)` iff
  /// `x :> A \/ x :> B \/ x :> C`.
  Union(Box<[Type]>),
  /// A user-defined type-former.
  _User(AtomID, Box<[Type]>, Box<[PureExpr]>),
}

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

#[derive(Clone, Debug)]
enum Prop {
  /// An (executable) boolean expression, interpreted as a pure proposition
  Pure(Rc<PureExpr>),
}

#[derive(Debug)]
#[allow(variant_size_differences)]
enum GType {
  /// A type variable, of kind `*`
  Star,
  /// A regular variable, of unknown type
  Unknown,
  /// A regular variable, of the given type; the bool is true if this is ghost
  Ty(bool, Type),
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
  /// Maps names from the MMC source in scope to their internal indexes.
  user_locals: HashMap<AtomID, usize>,
  /// Maps internal indexes for variables in scope to their variable record.
  context: Vec<Variable>,
}

#[allow(variant_size_differences)]
enum ParseErr {
  UnknownVar(usize),
  ElabErr(ElabError),
}

impl From<usize> for ParseErr {
  fn from(u: usize) -> Self { Self::UnknownVar(u) }
}

impl From<ElabError> for ParseErr {
  fn from(u: ElabError) -> Self { Self::ElabErr(u) }
}

impl ParseErr {
  fn new_e(pos: impl Into<Span>, e: impl Into<BoxError>) -> ParseErr {
    ElabError::new_e(pos, e).into()
  }
}

fn get_fresh_name(env: &mut Environment, mut base: String, mut bad: impl FnMut(AtomID, &AtomData) -> bool) -> AtomID {
  if !base.is_empty() {
    let a = env.get_atom(&base);
    if !bad(a, &env.data[a]) {return a}
  }
  base.push('_');
  let n = base.len();
  for i in 1.. {
    use std::fmt::Write;
    write!(&mut base, "{}", i).unwrap();
    let a = env.get_atom(&base);
    if !bad(a, &env.data[a]) {return a}
    base.truncate(n);
  }
  unreachable!()
}

impl<'a> TypeChecker<'a> {
  /// Constructs a new `TypeChecker`, which can be used to typecheck many `AST` items
  /// via [`typeck`](struct.TypeChecker.html#method.typeck) and will reuse its internal buffers.
  pub fn new(mmc: &'a mut Compiler, elab: &'a mut Elaborator, fsp: FileSpan) -> Self {
    Self {mmc, elab, fsp,
      used_names: HashSet::new(),
      user_locals: HashMap::new(),
      context: Vec::new(),
    }
  }

  fn todo<T, U>(&self, _: U) -> EResult<T> { Err(ElabError::new_e(self.fsp.span, "unimplemented")) }

  fn try_get_span(&self, e: &LispVal) -> Span {
    try_get_span(&self.fsp, &e)
  }

  fn get_fresh_decl(&mut self, base: AtomID) -> AtomID {
    let mut s = self.mmc.prefix.clone();
    s += &self.elab.data[base].name;
    get_fresh_name(&mut self.elab, s, |_, ad| ad.decl.is_some())
  }

  fn get_fresh_local(&mut self, base: AtomID) -> AtomID {
    let s = if base == AtomID::UNDER {String::new()} else {(*self.elab.data[base].name).into()};
    let used_names = &self.used_names;
    get_fresh_name(&mut self.elab, s, |a, ad| used_names.contains(&a) || ad.decl.is_some())
  }

  fn infer_type(&'a self, e: &'a PureExpr) -> Result<InferType<'a>, usize> {
    Ok(match e {
      &PureExpr::Var(i) => match &self.context[i].ty {
        GType::Unknown => return Err(i),
        GType::Ty(_, ty) => InferType::ty(ty),
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
      PureExpr::Index(a, _, _) => match self.infer_type(a)? {
        InferType::Ty(Type::Array(ty, _)) => InferType::Ty(ty),
        _ => unreachable!(),
      },
      PureExpr::Tuple(es) => InferType::List(
        es.iter().map(|e| self.infer_type(e)).collect::<Result<Vec<_>, usize>>()?.into()),
      PureExpr::DerefOwn(e) => match self.infer_type(e)? {
        InferType::Ty(Type::Own(ty)) => InferType::Ty(ty),
        InferType::Own(ty) => InferType::Ty(ty),
        _ => unreachable!(),
      },
      PureExpr::Deref(e) => match self.infer_type(e)? {
        InferType::Ty(Type::Ref(ty)) => InferType::Ty(ty),
        InferType::Ref(ty) => InferType::Ty(ty),
        _ => unreachable!(),
      },
      PureExpr::DerefMut(e) => match self.infer_type(e)? {
        InferType::Ty(Type::RefMut(ty)) => InferType::Ty(ty),
        InferType::RefMut(ty) => InferType::Ty(ty),
        _ => unreachable!(),
      },
    })
  }

  fn probably_a_type(&self, e: &LispVal) -> bool {
    let mut u = Uncons::New(e.clone());
    let head = match u.next() {
      None if u.is_empty() => return true,
      None => u.into(),
      Some(head) => head,
    };
    let name = if let Some(name) = head.as_atom() {name} else {return false};
    if name == AtomID::UNDER { return false }
    matches!(self.mmc.names.get(&name), Some(Entity::Type(_)))
  }

  fn parse_ty(&self, e: &LispVal) -> Result<Type, ParseErr> {
    let mut u = Uncons::New(e.clone());
    let (head, args) = match u.next() {
      None if u.is_empty() => return Ok(Type::Unit),
      None => (u.into(), vec![]),
      Some(head) => (head, u.collect()),
    };
    macro_rules! parse_tys {($args:expr) => {{
      let mut tys = Vec::with_capacity($args.len());
      for e in $args { tys.push(self.parse_ty(e)?) }
      tys.into()
    }}}
    let name = head.as_atom().ok_or_else(||
      ElabError::new_e(self.try_get_span(&head), "expected an atom"))?;
    if name == AtomID::UNDER {
      return Err(ElabError::new_e(self.try_get_span(&head), "expecting a type"))?;
    }
    match self.mmc.names.get(&name) {
      Some(&Entity::Type(NType::Prim(prim))) => match (prim, &*args) {
        (PrimType::Array, [ty, n]) => Ok(Type::Array(
          Box::new(self.parse_ty(ty)?),
          Rc::new(self.parse_pure_expr(n, Some(&Type::UInt(Size::Inf)))?))),
        (PrimType::Bool, []) => Ok(Type::Bool),
        (PrimType::I8, []) => Ok(Type::Int(Size::S8)),
        (PrimType::I16, []) => Ok(Type::Int(Size::S16)),
        (PrimType::I32, []) => Ok(Type::Int(Size::S32)),
        (PrimType::I64, []) => Ok(Type::Int(Size::S64)),
        (PrimType::U8, []) => Ok(Type::UInt(Size::S8)),
        (PrimType::U16, []) => Ok(Type::UInt(Size::S16)),
        (PrimType::U32, []) => Ok(Type::UInt(Size::S32)),
        (PrimType::U64, []) => Ok(Type::UInt(Size::S64)),
        (PrimType::List, args) => Ok(Type::List(parse_tys!(args))),
        (PrimType::Inter, args) => Ok(Type::Inter(parse_tys!(args))),
        (PrimType::Union, args) => Ok(Type::Union(parse_tys!(args))),
        (PrimType::Own, [ty]) => Ok(Type::Own(Box::new(self.parse_ty(ty)?))),
        (PrimType::Ref, [ty]) => Ok(Type::Ref(Box::new(self.parse_ty(ty)?))),
        (PrimType::RefMut, [ty]) => Ok(Type::RefMut(Box::new(self.parse_ty(ty)?))),
        _ => Err(ParseErr::new_e(self.try_get_span(&e), "unexpected number of arguments"))
      }
      Some(Entity::Type(NType::Unchecked)) => Err(
        ParseErr::new_e(self.try_get_span(&head), "forward type references are not allowed")),
      Some(_) => Err(ParseErr::new_e(self.try_get_span(&head), "expected a type")),
      None => match self.user_locals.get(&name) {
        Some(&i) if matches!(self.context[i].ty, GType::Star) => Ok(Type::Var(i)),
        _ => Err(ParseErr::new_e(self.try_get_span(&head), "undeclared variable"))
      }
    }
  }

  fn parse_lassoc1_expr(&self,
    arg1: &LispVal,
    args: &[LispVal],
    binop: Binop,
    tgt: Option<&Type>,
  ) -> Result<PureExpr, ParseErr> {
    let mut e = self.parse_pure_expr(arg1, tgt)?;
    for arg in args {
      e = PureExpr::Binop(binop, Rc::new(e), Rc::new(self.parse_pure_expr(arg, tgt)?))
    }
    Ok(e)
  }

  fn parse_lassoc_expr(&self,
    args: &[LispVal],
    f0: impl FnOnce() -> Result<PureExpr, ParseErr>,
    f1: impl FnOnce(PureExpr) -> Result<PureExpr, ParseErr>,
    binop: Binop,
    tgt: Option<&Type>,
  ) -> Result<PureExpr, ParseErr> {
    if let Some((arg1, args)) = args.split_first() {
      f1(self.parse_lassoc1_expr(arg1, args, binop, tgt)?)
    } else {f0()}
  }

  fn parse_ineq(&self, args: &[LispVal], binop: Binop) -> Result<PureExpr, ParseErr> {
    if let Some((arg1, args)) = args.split_first() {
      let arg1 = self.parse_pure_expr(arg1, Some(&Type::Int(Size::Inf)))?;
      if let Some((arg2, args)) = args.split_first() {
        let mut arg2 = Rc::new(self.parse_pure_expr(arg2, Some(&Type::Int(Size::Inf)))?);
        let mut e = PureExpr::Binop(binop, Rc::new(arg1), arg2.clone());
        for arg3 in args {
          let arg3 = Rc::new(self.parse_pure_expr(arg3, Some(&Type::Int(Size::Inf)))?);
          e = PureExpr::Binop(Binop::And, Rc::new(e), Rc::new(PureExpr::Binop(binop, arg2, arg3.clone())));
          arg2 = arg3;
        }
        Ok(e)
      } else { Ok(arg1) }
    } else { Ok(PureExpr::Bool(true)) }
  }

  fn parse_pure_expr(&self, e: &LispVal, tgt: Option<&Type>) -> Result<PureExpr, ParseErr> {
    let mut u = Uncons::New(e.clone());
    let (head, args) = match u.next() {
      None if u.is_empty() => return Ok(PureExpr::Unit),
      None => (u.into(), vec![]),
      Some(head) => (head, u.collect()),
    };
    macro_rules! err {($($e:expr),*) => {
      Err(ParseErr::new_e(self.try_get_span(&head), format!($($e),*)))
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
      if name == AtomID::UNDER { return err!("expecting a type") }
      match self.mmc.names.get(&name) {
        Some(Entity::Const(GlobalTC::Unchecked)) => err!("forward referencing constants is not allowed"),
        Some(Entity::Op(Operator::Prim(prim))) => match (prim, &*args) {
          (PrimProc::Add, args) =>
            self.parse_lassoc_expr(args, || Ok(PureExpr::Int(0.into())), Ok, Binop::Add, Some(get_int_tgt!())),
          (PrimProc::And, args) => {
            check_tgt!(Type::Bool, "a bool");
            self.parse_lassoc_expr(args, || Ok(PureExpr::Bool(true)), Ok, Binop::And, Some(&Type::Bool))
          }
          (PrimProc::Assert, _) => err!("type error, expected a pure expr"),
          (PrimProc::BitAnd, args) =>
            self.parse_lassoc_expr(args, || Ok(PureExpr::Int((-1).into())), Ok, Binop::BitAnd, Some(get_int_tgt!())),
          (PrimProc::BitNot, args) => {
            let (sz, ty) = match tgt {
              None => (Size::Inf, &Type::Int(Size::Inf)),
              Some(ty) => match ty {
                Type::Int(_) => (Size::Inf, ty),
                &Type::UInt(sz) => (sz, ty),
                _ => return err!("type error, expected an integer"),
              }
            };
            self.parse_lassoc_expr(args, || Ok(PureExpr::Int((-1).into())),
              |e| Ok(PureExpr::Unop(Unop::BitNot(sz), Rc::new(e))), Binop::BitOr, Some(ty))
          }
          (PrimProc::BitOr, args) =>
            self.parse_lassoc_expr(args, || Ok(PureExpr::Int(0.into())), Ok, Binop::BitOr, Some(get_int_tgt!())),
          (PrimProc::BitXor, args) =>
            self.parse_lassoc_expr(args, || Ok(PureExpr::Int(0.into())), Ok, Binop::BitXor, Some(get_int_tgt!())),
          (PrimProc::Index, args) => {
            let (a, i, h) = match args {
              [a, i] => (a, i, None),
              [a, i, h] => (a, i, Some(h)),
              _ => return err!("expected 2 or 3 arguments"),
            };
            let mut a = self.parse_pure_expr(a, None)?;
            let i = Rc::new(self.parse_pure_expr(i, Some(&Type::UInt(Size::Inf)))?);
            let mut aty = self.infer_type(&a)?;
            enum AutoDeref { Own, Ref, Mut }
            let mut derefs = vec![];
            let n = loop {
              match aty {
                InferType::Own(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Own); }
                InferType::Ref(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Ref); }
                InferType::RefMut(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Mut); }
                InferType::Ty(Type::Array(_, n)) => break n.clone(),
                _ => return err!("type error, expcted an array"),
              }
            };
            for s in derefs {
              a = match s {
                AutoDeref::Own => PureExpr::DerefOwn(Box::new(a)),
                AutoDeref::Ref => PureExpr::Deref(Box::new(a)),
                AutoDeref::Mut => PureExpr::DerefMut(Box::new(a)),
              }
            }
            let prop = PureExpr::Binop(Binop::Lt, i.clone(), n.clone());
            let h = match h {
              Some(h) => self.parse_proof(h, Some(Prop::Pure(Rc::new(prop))))?,
              None => ProofExpr::Assert(Box::new(prop)),
            };
            Ok(PureExpr::Index(Box::new(a), i, Box::new(h)))
          }
          (PrimProc::List, args) => {
            let mut vec = Vec::with_capacity(args.len());
            match tgt {
              None => for e in args { vec.push(self.parse_pure_expr(e, None)?) }
              Some(Type::List(ts)) if ts.len() == args.len() =>
                for (e, ty) in (&*args).iter().zip(&**ts) {
                  vec.push(self.parse_pure_expr(e, Some(ty))?)
                },
                Some(ty) => return err!("type error, expected {:?}", ty),
            }
            Ok(PureExpr::Tuple(vec.into()))
          }
          (PrimProc::Mul, args) =>
            self.parse_lassoc_expr(args, || Ok(PureExpr::Int(1.into())), Ok, Binop::Mul, Some(get_int_tgt!())),
          (PrimProc::Not, args) => {
            check_tgt!(Type::Bool, "a bool");
            self.parse_lassoc_expr(args, || Ok(PureExpr::Bool(true)),
              |e| Ok(PureExpr::Unop(Unop::Not, Rc::new(e))), Binop::Or, Some(&Type::Bool))
          }
          (PrimProc::Or, args) => {
            check_tgt!(Type::Bool, "a bool");
            self.parse_lassoc_expr(args, || Ok(PureExpr::Bool(false)), Ok, Binop::Or, Some(&Type::Bool))
          }
          (PrimProc::Le, args) => { check_tgt!(Type::Bool, "a bool"); self.parse_ineq(args, Binop::Le) }
          (PrimProc::Lt, args) => { check_tgt!(Type::Bool, "a bool"); self.parse_ineq(args, Binop::Lt) }
          (PrimProc::Eq, args) => { check_tgt!(Type::Bool, "a bool"); self.parse_ineq(args, Binop::Eq) }
          (PrimProc::Ne, args) => { check_tgt!(Type::Bool, "a bool"); self.parse_ineq(args, Binop::Ne) }
          (PrimProc::Pun, _) |
          (PrimProc::Slice, _) |
          (PrimProc::TypeofBang, _) |
          (PrimProc::Typeof, _) =>
            return Err(ParseErr::new_e(self.try_get_span(&head), "not a pure operation")),
        }
        Some(Entity::Op(Operator::Proc(_, ProcTC::Unchecked))) => Err(ParseErr::new_e(
          self.try_get_span(&head), "forward referencing a procedure")),
        Some(_) => return Err(ParseErr::new_e(self.try_get_span(&head), "expected a function/operation")),
        None => match self.user_locals.get(&name) {
          Some(&i) => match &self.context[i].ty {
            GType::Ty(_, _ty) => match tgt {
              None => Ok(PureExpr::Var(i)),
              Some(_tgt) /* TODO: if *tgt == ty */ => Ok(PureExpr::Var(i)),
            },
            _ => return Err(ParseErr::new_e(self.try_get_span(&head), "expected a regular variable")),
          },
          _ => Err(ParseErr::new_e(self.try_get_span(&head), "undeclared variable"))
        }
      }
    } else {
      if !args.is_empty() {
        return Err(ParseErr::new_e(self.try_get_span(e), "unexpected arguments"))
      }
      head.unwrapped(|e| match *e {
        LispKind::Number(ref n) => Ok(PureExpr::Int(n.clone())),
        LispKind::Bool(b) => Ok(PureExpr::Bool(b)),
        _ => Err(ParseErr::new_e(self.try_get_span(&head), "unexpected expression")),
      })
    }
  }

  fn parse_prop(&self, e: &LispVal) -> Result<Prop, ParseErr> {
    self.parse_pure_expr(e, Some(&Type::Bool)).map(|e| Prop::Pure(Rc::new(e)))
  }

  fn parse_proof(&self, e: &LispVal, tgt: Option<Prop>) -> EResult<ProofExpr> {
    self.todo((e, tgt))
  }

  fn add_args_to_context(&mut self, args: &[Arg], tyvar_allowed: bool, hyp_allowed: bool) -> EResult<()> {
    self.context.reserve(args.len());
    let mut todo = vec![];
    for (i, arg) in args.iter().enumerate() {
      let user = match arg.name {
        Some((a, ref fsp)) if a != AtomID::UNDER => {
          if self.user_locals.insert(a, i).is_some() {
            return Err(ElabError::new_e(
              try_get_span_from(&self.fsp, Some(fsp)), "variable declared twice"))
          }
          a
        }
        _ => AtomID::UNDER
      };
      let decl = self.get_fresh_local(user);
      self.used_names.insert(decl);
      let is_ty = tyvar_allowed && arg.ty.as_atom().map_or(false, |a| a == AtomID::UNDER ||
        matches!(self.mmc.keywords.get(&a), Some(Keyword::Star)));
      self.context.push(Variable {user, decl, ty: if is_ty {GType::Star} else {GType::Unknown}});
      if !is_ty {todo.push(i)}
    }
    let mut n = todo.len();
    while n != 0 {
      for i in mem::take(&mut todo) {
        let ty = &args[i].ty;
        let ty = if !hyp_allowed || self.probably_a_type(ty) {
          self.parse_ty(&args[i].ty).map(|ty| GType::Ty(args[i].ghost, ty))
        } else {
          self.parse_prop(&args[i].ty).map(GType::Prop)
        };
        match ty {
          Ok(ty) => self.context[i].ty = ty,
          Err(ParseErr::UnknownVar(_)) => {todo.push(i)},
          Err(ParseErr::ElabErr(e)) => return Err(e),
        }
      }
      if n >= mem::replace(&mut n, todo.len()) {
        return Err(ElabError::new_e(
          try_get_span_from(&self.fsp, Some(&args[todo[0]].name.as_ref().unwrap().1)),
          format!("circular typing dependency in {{{}}}", todo.into_iter()
            .map(|i| &self.elab.data[args[i].name.as_ref().unwrap().0].name)
            .format(", "))))
      }
    }
    Ok(())
  }

  /// Performs type checking of the input AST.
  pub fn typeck(&mut self, item: &AST) -> EResult<()> {
    self.used_names.clear();
    self.user_locals.clear();
    self.context.clear();
    match item {
      AST::Proc(proc) => match proc.kind {
        ProcKind::Func =>
          return Err(ElabError::new_e(
            try_get_span_from(&self.fsp, proc.span.as_ref()), "func is not implemented, use proc")),
        ProcKind::ProcDecl => {}
        ProcKind::Intrinsic => {
          let intrinsic = Intrinsic::from_str(&self.elab.data[proc.name].name)
            .map_err(|_| ElabError::new_e(
              try_get_span_from(&self.fsp, proc.span.as_ref()), "unknown intrinsic"))?;
          // TODO: check intrinsic signature is correct?
          match self.mmc.names.get_mut(&proc.name) {
            Some(Entity::Op(Operator::Proc(_, tc @ ProcTC::Unchecked))) =>
              *tc = ProcTC::Intrinsic(intrinsic),
            _ => unreachable!()
          }
        }
        ProcKind::Proc => {
          let Proc {kind, name, ref span, ref args, ref rets, ref variant, ref body} = **proc;
          self.add_args_to_context(args, false, true)?;
          self.add_args_to_context(rets, false, true)?;
          let rets = self.context.drain(args.len()..).collect::<Vec<_>>();
          if let Some((e, _)) = variant {
            return Err(ElabError::new_e(self.try_get_span(e), "proc variants are not implemented"))
          }
          // println!("{:?}", proc);
          self.todo((kind, name, span, rets, body))?;
          return Err(ElabError::new_e(
            try_get_span_from(&self.fsp, proc.span.as_ref()), "unimplemented"))
        }
      }
      AST::Global {lhs, rhs} => self.todo((lhs, rhs))?,
      AST::Const {lhs, rhs} => self.todo((lhs, rhs))?,
      &AST::Typedef {name, ref span, ref args, ref val} => {
        self.add_args_to_context(args, true, false)?;
        let val = self.parse_ty(val).map_err(|e|
          if let ParseErr::ElabErr(e) = e {e} else {unreachable!()})?;
        let dname = self.get_fresh_decl(name);
        // TODO: write def dname := val
        if let Entity::Type(ty @ NType::Unchecked) = self.mmc.names.get_mut(&name).unwrap() {
          *ty = NType::Checked(span.clone(), dname, Rc::new(val))
        } else {unreachable!()}
      },
      AST::Struct {name, span, args, fields} => self.todo((name, span, args, fields))?,
    }
    Ok(())
  }
}
