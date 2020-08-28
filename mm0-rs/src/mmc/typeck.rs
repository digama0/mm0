//! MMC type checking pass.
use std::collections::{HashMap, HashSet};
use crate::elab::{Result, Elaborator, Environment, ElabError,
  environment::{AtomID, AtomData},
  lisp::{Uncons, LispVal, LispKind}, local_context::{try_get_span_from, try_get_span}};
use crate::util::{Span, FileSpan};
use super::{parser::{Proc, AST, Keyword}, Compiler,
  nameck::{Type as NType, PrimType, PrimProc, Entity, GlobalTC, Operator, ProcTC}};
use num::BigInt;

/// Possible sizes for integer operations and types.
#[derive(Copy, Clone, Debug)]
enum Size {
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
enum Unop {
  /// Bitwise negation. For fixed size this is the operation `2^n - x - 1`, and
  /// for infinite size this is `-x - 1`. Note that signed NOT
  BitNot(Size),
}

/// (Elaborated) binary operations.
#[derive(Copy, Clone, Debug)]
enum Binop {
  /// Logical (boolean) AND
  And,
  /// Bitwise AND, for signed or unsigned integers of any size
  BitAnd,
  /// Bitwise OR, for signed or unsigned integers of any size
  BitOr,
  /// Bitwise XOR, for signed or unsigned integers of any size
  BitXor,
}

/// A proof expression, or "hypothesis".
#[derive(Debug)]
enum ProofExpr {
  /// An assertion expression `(assert p): p`.
  _Assert(Box<PureExpr>),
}

/// Pure expressions in an abstract domain. The interpretation depends on the type,
/// but most expressions operate on the type of (signed unbounded) integers.
#[derive(Debug)]
enum PureExpr {
  /// A variable.
  _Var(usize),
  /// An integer or natural number.
  Int(BigInt),
  /// The unit value `()`.
  Unit,
  /// A boolean literal.
  Bool(bool),
  /// A unary operation.
  Unop(Unop, Box<PureExpr>),
  /// A binary operation.
  Binop(Binop, Box<(PureExpr, PureExpr)>),
  /// An owned index operation `(index a i h): (own T)` where `a: (own (array T n))`,
  /// `i: nat`, and `h: i < n`.
  _OwnIndex(Box<(PureExpr, PureExpr, ProofExpr)>),
  /// An index operation `(index a i h): (& T)` where `a: (& (array T n))`,
  /// `i: nat`, and `h: i < n`.
  _Index(Box<(PureExpr, PureExpr, ProofExpr)>),
}

#[derive(Debug)]
enum Type {
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
    Array(Box<(Type, PureExpr)>),
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

#[derive(Debug)]
enum Prop {
  /// An (executable) boolean expression, interpreted as a pure proposition
  _Pure(Box<PureExpr>),
}

#[derive(Debug)]
#[allow(variant_size_differences)]
enum GType {
  /// A type variable, of kind `*`
  Star,
  /// A regular variable, of unknown type
  Unknown,
  /// A regular variable, of the given type
  Ty(Type),
  /// A hypothesis, which proves the given separating proposition
  _Prop(Prop),
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

  fn todo<T, U>(&mut self, _: U) -> Result<T> { Err(ElabError::new_e(self.fsp.span, "unimplemented")) }

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

  fn parse_lassoc1_expr(&mut self,
    arg1: &LispVal,
    args: &[LispVal],
    binop: Binop,
    tgt: Option<&Type>,
  ) -> Result<PureExpr> {
    let mut e = self.parse_pure_expr(arg1, tgt)?;
    for arg in args {
      e = PureExpr::Binop(binop, Box::new((e, self.parse_pure_expr(arg, tgt)?)))
    }
    Ok(e)
  }

  fn parse_lassoc_expr(&mut self,
    args: &[LispVal],
    f0: impl FnOnce() -> Result<PureExpr>,
    f1: impl FnOnce(PureExpr) -> Result<PureExpr>,
    binop: Binop,
    tgt: Option<&Type>,
  ) -> Result<PureExpr> {
    if let Some((arg1, args)) = args.split_first() {
      f1(self.parse_lassoc1_expr(arg1, args, binop, tgt)?)
    } else {f0()}
  }

  fn parse_pure_expr(&mut self, e: &LispVal, tgt: Option<&Type>) -> Result<PureExpr> {
    let mut u = Uncons::New(e.clone());
    let (head, args) = match u.next() {
      None if u.is_empty() => return Ok(PureExpr::Unit),
      None => (u.into(), vec![]),
      Some(head) => (head, u.collect()),
    };
    macro_rules! err {($e:expr) => { Err(ElabError::new_e(self.try_get_span(&head), $e)) }}
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
              |e| Ok(PureExpr::Unop(Unop::BitNot(sz), Box::new(e))), Binop::BitOr, Some(ty))
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
            self.todo((a, i, h, args))?
          }
          (PrimProc::List, args) => self.todo(args)?,
          (PrimProc::Not, args) => self.todo(args)?,
          (PrimProc::Or, args) => self.todo(args)?,
          (PrimProc::Pun, args) => self.todo(args)?,
          (PrimProc::Slice, args) => self.todo(args)?,
          (PrimProc::TypeofBang, args) => self.todo(args)?,
          (PrimProc::Typeof, args) => self.todo(args)?,
        }
        Some(Entity::Op(Operator::Proc(_, ProcTC::Unchecked))) => Err(ElabError::new_e(
          self.try_get_span(&head), "forward referencing a procedure")),
        _ => return Err(ElabError::new_e(self.try_get_span(&head), "expected a function/operation"))
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

  fn parse_ty(&mut self, e: &LispVal) -> Result<Type> {
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
        (PrimType::Array, [ty, n]) => Ok(Type::Array(Box::new(
          (self.parse_ty(ty)?, self.parse_pure_expr(n, Some(&Type::UInt(Size::Inf)))?)))),
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
        _ => Err(ElabError::new_e(self.try_get_span(&e), "unexpected number of arguments"))
      }
      Some(Entity::Type(NType::Unchecked)) => Err(
        ElabError::new_e(self.try_get_span(&head), "forward type references are not allowed")),
      Some(_) => Err(ElabError::new_e(self.try_get_span(&head), "expected a type")),
      None => match self.user_locals.get(&name) {
        Some(&i) if matches!(self.context[i].ty, GType::Star) => Ok(Type::Var(i)),
        _ => Err(ElabError::new_e(self.try_get_span(&head), "undeclared variable"))
      }
    }
  }

  /// Performs type checking of the input AST.
  pub fn typeck(&mut self, item: &AST) -> Result<()> {
    self.used_names.clear();
    self.user_locals.clear();
    self.context.clear();
    match item {
      AST::Proc(proc) => {
        let Proc {kind, name, ref span, ref args, ref rets, ref variant, ref body} = **proc;
        self.todo((kind, name, span, args, rets, variant, body))?
      }
      AST::Global {lhs, rhs} => self.todo((lhs, rhs))?,
      AST::Const {lhs, rhs} => self.todo((lhs, rhs))?,
      &AST::Typedef {name, ref span, ref args, ref val} => {
        self.context.reserve(args.len());
        for (i, arg) in args.iter().enumerate() {
          assert!(!arg.ghost);
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
          let is_ty = arg.ty.as_atom().map_or(false, |a| a == AtomID::UNDER ||
            matches!(self.mmc.keywords.get(&a), Some(Keyword::Star)));
          self.context.push(Variable {user, decl, ty: if is_ty {GType::Star} else {GType::Unknown}})
        }
        for (i, arg) in args.iter().enumerate() {
          if matches!(self.context[i].ty, GType::Unknown) {
            self.context[i].ty = GType::Ty(self.parse_ty(&arg.ty)?)
          }
        }
        let val = self.parse_ty(val)?;
        let dname = self.get_fresh_decl(name);
        self.todo((span, dname, val))?
      },
      AST::Struct {name, span, args, fields} => self.todo((name, span, args, fields))?,
    }
    Ok(())
  }
}
