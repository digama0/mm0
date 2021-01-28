//! MMC type checking pass.
#![allow(unused)]

use std::rc::Rc;
use std::collections::{HashMap, HashSet, hash_map::Entry};
use std::convert::TryInto;
use crate::elab::{Result as EResult, Elaborator, Environment, ElabError,
  environment::{AtomID, AtomData},
  lisp::{Uncons, LispVal, LispKind, print::{EnvDisplay, FormatEnv}},
  local_context::{try_get_span_from, try_get_span}};
use crate::util::{Span, FileSpan};
use super::{Compiler,
  nameck::{Type as NType, Prim, PrimType, PrimOp, PrimProp,
    Intrinsic, Entity, GlobalTC, Operator, ProcTC},
  parser::{head_keyword, Parser, Expr as PExpr, TuplePattern as PTuplePattern},
  types::{AST, Binop, Expr, Keyword, MM0Expr, MM0ExprNode,
    ProcKind, Prop, PureExpr, Size, TuplePattern, Type, TypedTuplePattern, Unop}};

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
  PropPure(&'a Rc<PureExpr>),
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

  fn to_type(&self) -> Option<Type> {
    match *self {
      InferType::Int => Some(Type::Int(Size::Inf)),
      InferType::Unit => Some(Type::Unit),
      InferType::Bool => Some(Type::Bool),
      InferType::Star => None,
      InferType::Own(ty) => Some(Type::Own(Box::new(ty.clone()))),
      InferType::Ref(ty) => Some(Type::Ref(Box::new(ty.clone()))),
      InferType::RefMut(ty) => Some(Type::RefMut(Box::new(ty.clone()))),
      InferType::Ty(ty) => Some(ty.clone()),
      InferType::Prop(p) => Some(Type::Prop(Box::new(p.clone()))),
      InferType::PropPure(e) => Some(Type::Prop(Box::new(Prop::Pure(e.clone())))),
      InferType::List(ref tys) => Some(Type::List(tys.iter()
        .map(InferType::to_type).collect::<Option<Box<[_]>>>()?)),
    }
  }

  fn from_type(oty: &'a Option<Type>) -> Self {
    if let Some(ty) = oty {InferType::ty(ty)} else {InferType::Star}
  }
}

impl<'a> EnvDisplay for InferType<'a> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use std::fmt::Display;
    match *self {
      InferType::Int => "int".fmt(f),
      InferType::Unit => "()".fmt(f),
      InferType::Bool => "bool".fmt(f),
      InferType::Star => "*".fmt(f),
      InferType::Own(ty) => write!(f, "(own {})", fe.to(ty)),
      InferType::Ref(ty) => write!(f, "(& {})", fe.to(ty)),
      InferType::RefMut(ty) => write!(f, "(&mut {})", fe.to(ty)),
      InferType::Ty(ty) => ty.fmt(fe, f),
      InferType::Prop(p) => p.fmt(fe, f),
      InferType::PropPure(e) => e.fmt(fe, f),
      InferType::List(ref tys) => {
        use itertools::Itertools;
        write!(f, "(list {})", tys.iter().map(|ty| fe.to(ty)).format(" "))
      }
    }
  }
}

#[derive(Debug, Default, Copy, Clone)]
struct TypeTarget<'a>(Option<&'a Type>, Option<&'a TuplePattern>);

impl<'a> TypeTarget<'a> {
  const NONE: Self = TypeTarget(None, None);
}

impl<'a> From<&'a Type> for TypeTarget<'a> {
  fn from(t: &'a Type) -> Self { Self(Some(t), None) }
}

impl<'a> From<&'a TuplePattern> for TypeTarget<'a> {
  fn from(t: &'a TuplePattern) -> Self {
    if let TuplePattern::Typed(t) = t {
      TypeTarget(Some(&t.1), Some(&t.0))
    } else {
      TypeTarget(None, Some(t))
    }
  }
}

/// Like rust, types can either be `Copy` or non-`Copy`.
/// Unlike rust, non-copy types can still be used after they are moved
/// away, but their type changes to the `Moved` version of the type,
/// which represents the "copy core" of the type, essentially an integral
/// type of the same size as `sizeof(T)`.
///
/// We use `Option<Type>` to store the moved version, where `None` means
/// this is a copy type, and `Some(T)` means the moved version is `T`.
type CopyType = Option<Type>;

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
  Ty(bool, Type, CopyType),
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
  /// The vector contains shadowed variables in outer scopes.
  user_locals: HashMap<AtomID, (AtomID, Vec<AtomID>)>,
  /// The set of globals that are mutable in the current context (and their mapping to internal names).
  mut_globals: HashMap<AtomID, AtomID>,
  /// Maps internal indexes for variables in scope to their variable record.
  context: Vec<Variable>,
}

#[derive(Copy, Clone)]
enum ArgsContext {
  TypeArgs,
  StructFields,
  ProcArgs,
  Binder,
}
impl ArgsContext {
  fn tyvar_allowed(self) -> bool {
    matches!(self, ArgsContext::TypeArgs)
  }
  fn hyp_allowed(self) -> bool {
    !matches!(self, ArgsContext::TypeArgs)
  }
  fn default_value(self) -> Option<Type> {
    if let ArgsContext::Binder = self {
      Some(Type::UInt(Size::Inf))
    } else {None}
  }
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
      GType::Star |
      GType::Ty(_, _, None) => VariableState::Copy,
      _ => VariableState::Owned,
    }).collect())
  }

  fn parser(&self) -> Parser<'_> {
    Parser {fe: self.elab.format_env(), kw: &self.mmc.keywords, fsp: self.fsp.clone()}
  }

  fn todo<T, U>(&self, fsp: Option<&FileSpan>, s: &str, _: U) -> EResult<T> {
    Err(ElabError::new_e(try_get_span_from(&self.fsp, fsp), format!("unimplemented: {}", s)))
  }

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

  fn find_index(&self, a: AtomID) -> Option<usize> {
    self.context.iter().position(|v| v.decl == a)
  }

  fn find(&self, a: AtomID) -> Option<&Variable> {
    self.context.iter().find(|&v| v.decl == a)
  }

  fn copy_prop(&self, p: &Prop) -> Option<Prop> {
    fn list<A: Clone>(tys: &[A], f: impl Fn(&A) -> Option<A>) -> Option<Box<[A]>> {
      let opts = tys.iter().map(f).collect::<Vec<_>>();
      if opts.iter().all(Option::is_none) {return None}
      Some(opts.into_iter().zip(tys.iter())
        .map(|(opt, ty)| opt.unwrap_or_else(|| ty.clone()))
        .collect::<Box<[_]>>())
    }
    match p {
      Prop::True |
      Prop::False |
      Prop::Emp |
      Prop::Pure(_) |
      Prop::Eq(_, _) |
      Prop::Moved(_) |
      Prop::MM0(_) => None,
      &Prop::All(a, ref pr) => if self.copy_type(&pr.0).is_none() {
        self.copy_prop(&pr.1).map(|p| Prop::All(a, Box::new((pr.0.clone(), p))))
      } else { Some(Prop::Emp) },
      &Prop::Ex(a, ref pr) => match (self.copy_type(&pr.0), self.copy_prop(&pr.1)) {
        (None, None) => None,
        (ty, p) => {
          let ty = ty.unwrap_or_else(|| pr.0.clone());
          let p = p.unwrap_or_else(|| pr.1.clone());
          Some(Prop::Ex(a, Box::new((ty, p))))
        }
      },
      Prop::Imp(pr) => if self.copy_prop(&pr.0).is_none() {
        self.copy_prop(&pr.1).map(|p| Prop::Imp(Box::new((pr.0.clone(), p))))
      } else { Some(Prop::Emp) },
      Prop::Not(pr) => self.copy_prop(pr).map(|_| Prop::Emp),
      Prop::And(pr) => list(pr, |p| self.copy_prop(p)).map(Prop::And),
      Prop::Or(pr) => list(pr, |p| self.copy_prop(p)).map(Prop::And),
      Prop::Sep(pr) => list(pr, |p| self.copy_prop(p)).map(Prop::Sep),
      Prop::Wand(pr) => if self.copy_prop(&pr.0).is_none() {
        self.copy_prop(&pr.1).map(|p| Prop::Wand(Box::new((pr.0.clone(), p))))
      } else { Some(Prop::Emp) },
      Prop::Heap(_, _, _) => Some(Prop::Emp),
      Prop::HasTy(v, ty) => self.copy_type(ty).map(|ty| Prop::HasTy(v.clone(), Box::new(ty))),
      Prop::MVar(_) => Some(Prop::Moved(Box::new(p.clone()))),
    }
  }

  fn copy_type(&self, ty: &Type) -> CopyType {
    fn list<A: Clone>(tys: &[A], f: impl Fn(&A) -> Option<A>) -> Option<Box<[A]>> {
      let opts = tys.iter().map(f).collect::<Vec<_>>();
      if opts.iter().all(Option::is_none) {return None}
      Some(opts.into_iter().zip(tys.iter())
        .map(|(opt, ty)| opt.unwrap_or_else(|| ty.clone()))
        .collect::<Box<[_]>>())
    }
    match ty {
      Type::Unit |
      Type::Bool |
      Type::Int(_) |
      Type::UInt(_) |
      Type::Moved(_) => None,
      Type::Array(ty, n) => self.copy_type(ty)
        .map(|ty| Type::Array(Box::new(ty), n.clone())),
      Type::Own(_) |
      Type::Ref(_) |
      Type::RefMut(_) => Some(Type::UInt(Size::S64)),
      Type::List(tys) => list(tys, |ty| self.copy_type(ty)).map(Type::List),
      Type::Single(e, ty) => self.copy_type(ty).map(|ty| Type::Single(e.clone(), Box::new(ty))),
      Type::Struct(tys) => list(tys, |(a, ty)| Some((*a, self.copy_type(ty)?))).map(Type::Struct),
      Type::And(tys) => list(tys, |ty| self.copy_type(ty)).map(Type::And),
      Type::Or(tys) => list(tys, |ty| self.copy_type(ty)).map(Type::Or),
      Type::Ghost(ty) => Some(Type::Ghost(Box::new(self.copy_type(ty)?))),
      Type::Prop(p) => Some(Type::Prop(Box::new(self.copy_prop(p)?))),
      Type::Var(_) |
      Type::User(_, _, _) |
      Type::Input |
      Type::Output => Some(Type::Moved(Box::new(ty.clone()))),
    }
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
      PureExpr::Binop(Binop::Sub, _, _) |
      PureExpr::Binop(Binop::BitAnd, _, _) |
      PureExpr::Binop(Binop::BitOr, _, _) |
      PureExpr::Binop(Binop::BitXor, _, _) => InferType::Int,
      PureExpr::Index(a, _) => match self.infer_type(a) {
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
      PureExpr::Ghost(e) => self.infer_type(e),
      PureExpr::As(e) => InferType::ty(&e.1),
      PureExpr::Pure(e) => InferType::ty(&e.1),
    }
  }

  fn infer_expr_type(&'a self, e: &'a Expr) -> InferType<'a> {
    match e {
      &Expr::Var(i) => match &self.find(i).expect("variable not found").ty {
        GType::Ty(_, ty, _) => InferType::ty(ty),
        GType::Star => InferType::Star,
        GType::Prop(p) => InferType::Prop(p),
      },
      Expr::Unop(Unop::Not, _) |
      Expr::Binop(Binop::And, _, _) |
      Expr::Binop(Binop::Or, _, _) |
      Expr::Binop(Binop::Lt, _, _) |
      Expr::Binop(Binop::Le, _, _) |
      Expr::Binop(Binop::Eq, _, _) |
      Expr::Binop(Binop::Ne, _, _) => InferType::Bool,
      Expr::Unop(Unop::BitNot(_), _) |
      Expr::Binop(Binop::Add, _, _) |
      Expr::Binop(Binop::Mul, _, _) |
      Expr::Binop(Binop::Sub, _, _) |
      Expr::Binop(Binop::BitAnd, _, _) |
      Expr::Binop(Binop::BitOr, _, _) |
      Expr::Binop(Binop::BitXor, _, _) => InferType::Int,
      Expr::Index(a, _, _) => match self.infer_expr_type(a) {
        InferType::Ty(Type::Array(ty, _)) => InferType::Ty(ty),
        _ => unreachable!(),
      },
      Expr::Tuple(es) => InferType::List(
        es.iter().map(|e| self.infer_expr_type(e)).collect::<Vec<_>>().into()),
      Expr::DerefOwn(e) => match self.infer_expr_type(e) {
        InferType::Ty(Type::Own(ty)) => InferType::Ty(ty),
        InferType::Own(ty) => InferType::Ty(ty),
        _ => unreachable!(),
      },
      Expr::Deref(e) => match self.infer_expr_type(e) {
        InferType::Ty(Type::Ref(ty)) => InferType::Ty(ty),
        InferType::Ref(ty) => InferType::Ty(ty),
        _ => unreachable!(),
      },
      Expr::DerefMut(e) => match self.infer_expr_type(e) {
        InferType::Ty(Type::RefMut(ty)) => InferType::Ty(ty),
        InferType::RefMut(ty) => InferType::Ty(ty),
        _ => unreachable!(),
      },
      Expr::Ghost(e) => self.infer_expr_type(e),
      Expr::As(e) => InferType::ty(&e.1),
      Expr::Pure(e) => self.infer_type(e),
      Expr::Assert(p) => InferType::PropPure(p),
      Expr::Call {f, args, ..} => todo!("infer_expr_type Call"),
      // Expr::Entail(_, _) => todo!("infer_expr_type Entail"),
      Expr::Block(es) => if let Some(e) = es.last() {
        self.infer_expr_type(e)
      } else {InferType::Unit},
      // Expr::If(_) => todo!("infer_expr_type If"),
      // Expr::Switch(_, _) => todo!("infer_expr_type Switch"),
      // Expr::Hole(_) => todo!("infer_expr_type Hole"),
      Expr::Let {..} |
      Expr::While {..} |
      Expr::Label {..} => InferType::Unit,
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
    if name == AtomID::UNDER { return true }
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
    // println!("check_ty {}", self.elab.print(e));
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
        (PrimType::Input, []) => Ok(Type::Input),
        (PrimType::Output, []) => Ok(Type::Output),
        (PrimType::Own, [ty]) => Ok(Type::Own(Box::new(self.check_ty(ty)?))),
        (PrimType::Ref, [ty]) => Ok(Type::Ref(Box::new(self.check_ty(ty)?))),
        (PrimType::RefMut, [ty]) => Ok(Type::RefMut(Box::new(self.check_ty(ty)?))),
        (PrimType::List, args) => Ok(Type::List(check_tys!(args))),
        (PrimType::And, args) => Ok(Type::And(check_tys!(args))),
        (PrimType::Or, args) => Ok(Type::Or(check_tys!(args))),
        (PrimType::Ghost, [ty]) => Ok(Type::Ghost(Box::new(self.check_ty(ty)?))),
        (PrimType::Single, [e]) => {
          let pe = self.check_pure_expr(e, None)?;
          let ty = self.infer_type(&pe).to_type().ok_or_else(||
            ElabError::new_e(self.try_get_span(e), "type variables not allowed here"))?;
          Ok(Type::Single(Rc::new(pe), Box::new(ty)))
        },
        _ => Err(ElabError::new_e(self.try_get_span(e), "unexpected number of arguments"))
      }
      Some(Entity::Type(NType::Unchecked)) => Err(
        ElabError::new_e(self.try_get_span(&head), "forward type references are not allowed")),
      Some(&Entity::Type(NType::Checked(_, name, _))) => {
        if !args.is_empty() {
          return Err(ElabError::new_e(self.try_get_span(&head), "user defined type families are not supported"))
        }
        Ok(Type::User(name, Box::new([]), Rc::new([])))
      }
      Some(_) => Err(ElabError::new_e(self.try_get_span(&head), "expected a type")),
      None => match self.user_locals.get(&name) {
        Some(&(i, _)) if matches!(self.find(i), Some(Variable {ty: GType::Star, ..})) => Ok(Type::Var(i)),
        _ => Err(ElabError::new_e(self.try_get_span(e),
          format!("undeclared type {}", self.elab.print(&head))))
      }
    }
  }

  fn check_mm0_expr(&self, e: LispVal) -> Result<MM0Expr, ElabError> {
    fn list_opt<'a>(tc: &TypeChecker<'a>, subst: &mut (Vec<AtomID>, HashMap<AtomID, u32>),
      e: &LispVal, head: AtomID, args: Option<Uncons>
    ) -> Result<Option<MM0ExprNode>, ElabError> {
      let tid = tc.elab.term(head).ok_or_else(|| ElabError::new_e(tc.try_get_span(e),
        format!("term '{}' not declared", tc.elab.data[head].name)))?;
      tc.todo(e.fspan().as_ref(), "list_opt", args)
    }
    fn node_opt<'a>(tc: &TypeChecker<'a>, subst: &mut (Vec<AtomID>, HashMap<AtomID, u32>),
      e: &LispVal
    ) -> Result<Option<MM0ExprNode>, ElabError> {
      e.unwrapped(|r| Ok(match *r {
        LispKind::Atom(a) => match subst.1.entry(a) {
          Entry::Occupied(entry) => Some(MM0ExprNode::Var(*entry.get())),
          Entry::Vacant(entry) => match tc.user_locals.get(&a) {
            Some(&(v, _)) => {
              let n = subst.0.len().try_into().expect("overflow");
              entry.insert(n);
              subst.0.push(v);
              Some(MM0ExprNode::Var(n))
            }
            None => list_opt(tc, subst, e, a, None)?
          }
        },
        _ => {
          let mut u = Uncons::from(e.clone());
          let head = u.next().ok_or_else(|| ElabError::new_e(tc.try_get_span(e),
            format!("bad expression {}", tc.elab.print(e))))?;
          let a = head.as_atom().ok_or_else(|| ElabError::new_e(tc.try_get_span(&head),
            "expected an atom"))?;
          list_opt(tc, subst, &head, a, Some(u))?
        }
      }))
    }
    fn node<'a>(tc: &TypeChecker<'a>, e: LispVal,
      subst: &mut (Vec<AtomID>, HashMap<AtomID, u32>)
    ) -> Result<MM0ExprNode, ElabError> {
      Ok(node_opt(tc, subst, &e)?.unwrap_or_else(|| MM0ExprNode::Const(e)))
    }
    let mut subst = (vec![], HashMap::new());
    let expr = node(self, e, &mut subst)?;
    Ok(MM0Expr {subst: subst.0, expr})
  }

  fn check_lassoc1_pure_expr(&self,
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

  fn check_lassoc_pure_expr(&self,
    args: &[LispVal],
    f0: impl FnOnce() -> Result<PureExpr, ElabError>,
    f1: impl FnOnce(PureExpr) -> Result<PureExpr, ElabError>,
    binop: Binop,
    tgt: Option<&Type>,
  ) -> Result<PureExpr, ElabError> {
    if let Some((arg_1, rest)) = args.split_first() {
      f1(self.check_lassoc1_pure_expr(arg_1, rest, binop, tgt)?)
    } else {f0()}
  }

  fn check_lassoc1_expr(&mut self, ts: &mut TypeState,
    arg_1: LispVal,
    args: &[LispVal],
    binop: Binop,
    tgt: TypeTarget<'_>,
  ) -> Result<Expr, ElabError> {
    let mut e = self.check_expr(ts, arg_1, tgt)?;
    for arg in args {
      e = Expr::Binop(binop, Box::new(e), Box::new(self.check_expr(ts, arg.clone(), tgt)?))
    }
    Ok(e)
  }

  fn check_lassoc_expr(&mut self, ts: &mut TypeState,
    args: &[LispVal],
    f0: impl FnOnce() -> Result<Expr, ElabError>,
    f1: impl FnOnce(Expr) -> Result<Expr, ElabError>,
    binop: Binop,
    tgt: TypeTarget<'_>,
  ) -> Result<Expr, ElabError> {
    if let Some((arg_1, rest)) = args.split_first() {
      f1(self.check_lassoc1_expr(ts, arg_1.clone(), rest, binop, tgt)?)
    } else {f0()}
  }

  fn check_pure_ineq(&self, args: &[LispVal], binop: Binop) -> Result<PureExpr, ElabError> {
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

  fn check_ineq(&mut self, ts: &mut TypeState, args: &[LispVal], binop: Binop, sp: Option<&FileSpan>) -> Result<Expr, ElabError> {
    if let [lhs, rhs] = args {
      let lhs = self.check_expr(ts, lhs.clone(), TypeTarget(Some(&Type::Int(Size::Inf)), None))?;
      let rhs = self.check_expr(ts, rhs.clone(), TypeTarget(Some(&Type::Int(Size::Inf)), None))?;
      Ok(Expr::Binop(binop, Box::new(lhs), Box::new(rhs)))
    } else {
      Err(ElabError::new_e(try_get_span_from(&self.fsp, sp), "inequalities with != 2 arguments are not supported"))
    }
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
    // println!("check_pure_expr {}", self.elab.print(e));
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
            self.check_lassoc_pure_expr(args, || Ok(PureExpr::Int(0.into())), Ok, Binop::Add, Some(get_int_tgt!())),
          (PrimOp::And, args) => {
            check_tgt!(Type::Bool, "a bool");
            self.check_lassoc_pure_expr(args, || Ok(PureExpr::Bool(true)), Ok, Binop::And, Some(&Type::Bool))
          }
          (PrimOp::Or, args) => {
            check_tgt!(Type::Bool, "a bool");
            self.check_lassoc_pure_expr(args, || Ok(PureExpr::Bool(false)), Ok, Binop::Or, Some(&Type::Bool))
          }
          (PrimOp::BitAnd, args) =>
            self.check_lassoc_pure_expr(args, || Ok(PureExpr::Int((-1).into())), Ok, Binop::BitAnd, Some(get_int_tgt!())),
          (PrimOp::BitNot, args) => {
            let (sz, ty) = match tgt {
              None => (Size::Inf, &Type::Int(Size::Inf)),
              Some(ty) => match ty {
                Type::Int(_) => (Size::Inf, ty),
                &Type::UInt(sz) => (sz, ty),
                _ => return err!("type error, expected an integer"),
              }
            };
            self.check_lassoc_pure_expr(args, || Ok(PureExpr::Int((-1).into())),
              |e| Ok(PureExpr::Unop(Unop::BitNot(sz), Rc::new(e))), Binop::BitOr, Some(ty))
          }
          (PrimOp::BitOr, args) =>
            self.check_lassoc_pure_expr(args, || Ok(PureExpr::Int(0.into())), Ok, Binop::BitOr, Some(get_int_tgt!())),
          (PrimOp::BitXor, args) =>
            self.check_lassoc_pure_expr(args, || Ok(PureExpr::Int(0.into())), Ok, Binop::BitXor, Some(get_int_tgt!())),
          (PrimOp::Index, args) => {
            enum AutoDeref { Own, Ref, Mut }
            let (arr, idx) = match args {
              [arr, idx] => (arr, idx),
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
            Ok(PureExpr::Index(Box::new(arr), idx))
          }
          (PrimOp::List, args) => self.check_pure_expr_list(args, tgt, |err| ElabError::new_e(self.try_get_span(&head), err)),
          (PrimOp::Mul, args) =>
            self.check_lassoc_pure_expr(args, || Ok(PureExpr::Int(1.into())), Ok, Binop::Mul, Some(get_int_tgt!())),
          (PrimOp::Not, args) => {
            check_tgt!(Type::Bool, "a bool");
            self.check_lassoc_pure_expr(args, || Ok(PureExpr::Bool(true)),
              |e| Ok(PureExpr::Unop(Unop::Not, Rc::new(e))), Binop::Or, Some(&Type::Bool))
          }
          (PrimOp::Le, args) => { check_tgt!(Type::Bool, "a bool"); self.check_pure_ineq(args, Binop::Le) }
          (PrimOp::Lt, args) => { check_tgt!(Type::Bool, "a bool"); self.check_pure_ineq(args, Binop::Lt) }
          (PrimOp::Eq, args) => { check_tgt!(Type::Bool, "a bool"); self.check_pure_ineq(args, Binop::Eq) }
          (PrimOp::Ne, args) => { check_tgt!(Type::Bool, "a bool"); self.check_pure_ineq(args, Binop::Ne) }
          (PrimOp::Ghost, args) => Ok(PureExpr::Ghost(Rc::new({
            if let [e] = args {
              self.check_pure_expr(e, tgt)?
            } else {
              self.check_pure_expr_list(args, tgt, |err| ElabError::new_e(self.try_get_span(&head), err))?
            }
          }))),
          (PrimOp::Typed, [e, ty]) => {
            /* TODO: check ty == tgt */
            let ty = self.check_ty(ty)?;
            self.check_pure_expr(e, Some(&ty))
          }
          (PrimOp::As, [e, ty]) => {
            let ty = self.check_ty(ty)?;
            let e = self.check_pure_expr(e, None)?;
            Ok(PureExpr::As(Box::new((e, ty))))
          }
          (PrimOp::Typed, _) |
          (PrimOp::As, _) => return err!("expected 2 arguments"),
          (PrimOp::Pure, [e]) => {
            let ty = tgt.ok_or_else(|| ElabError::new_e(self.try_get_span(&head), "type ascription required"))?;
            let e = self.check_mm0_expr(e.clone())?;
            Ok(PureExpr::Pure(Box::new((e, ty.clone()))))
          }
          (PrimOp::Pure, _) => return err!("expected 1 argument"),
          (PrimOp::Assert, _) |
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
          Some(&(i, _)) => match &self.find(i) {
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

  fn check_binder(&mut self, e: &LispVal, args: &[LispVal],
      mut mk: impl FnMut(AtomID, Type, Prop) -> Prop) -> Result<Prop, ElabError> {
    let (last, bis) = args.split_last().expect("expected nonempty args");
    let bis = bis.iter().map(|bi| self.parser().parse_tuple_pattern(false, bi.clone()))
      .collect::<Result<Vec<_>, _>>()?;
    let depth = self.context.len();
    self.add_args_to_context(&bis, ArgsContext::Binder)?;
    let mut body = self.check_prop(last)?;
    for Variable {user, decl, ty} in self.context.drain(depth..).rev() {
      let ty = match ty {
        GType::Ty(_, ty, _) => ty,
        GType::Prop(p) => Type::Prop(Box::new(p)),
        GType::Star => return Err(
          ElabError::new_e(try_get_span(&self.fsp, e), "can't quantify over types")),
      };
      body = mk(decl, ty, body);
    }
    Ok(body)
  }

  fn check_prop(&mut self, e: &LispVal) -> Result<Prop, ElabError> {
    // println!("check_prop {}", self.elab.print(e));
    let mut u = Uncons::New(e.clone());
    let (head, args) = match u.next() {
      None if u.is_empty() =>
        return Err(ElabError::new_e(self.try_get_span(e), "expecting a proposition, got ()")),
      None => (u.into(), vec![]),
      Some(head) => (head, u.collect()),
    };
    match head.as_atom().and_then(|name| self.mmc.names.get(&name)) {
      Some(Entity::Prim(Prim {prop: Some(prim), ..})) => match (prim, &*args) {
        (PrimProp::All, args) if !args.is_empty() =>
          self.check_binder(e, args, |decl, ty, body| Prop::All(decl, Box::new((ty, body)))),
        (PrimProp::Ex, args) if !args.is_empty() =>
          self.check_binder(e, args, |decl, ty, body| Prop::Ex(decl, Box::new((ty, body)))),
        // TODO: n-ary And/Or/Sep
        (PrimProp::And, [e1, e2]) =>
          Ok(Prop::And(Box::new([self.check_prop(e1)?, self.check_prop(e2)?]))),
        (PrimProp::Or, [e1, e2]) =>
          Ok(Prop::Or(Box::new([self.check_prop(e1)?, self.check_prop(e2)?]))),
        (PrimProp::Imp, [e1, e2]) =>
          Ok(Prop::Imp(Box::new((self.check_prop(e1)?, self.check_prop(e2)?)))),
        (PrimProp::Star, [e1, e2]) =>
          Ok(Prop::Sep(Box::new([self.check_prop(e1)?, self.check_prop(e2)?]))),
        (PrimProp::Wand, [e1, e2]) =>
          Ok(Prop::Wand(Box::new((self.check_prop(e1)?, self.check_prop(e2)?)))),
        (PrimProp::Pure, [e]) => Ok(Prop::MM0(e.clone())),
        _ => Err(ElabError::new_e(self.try_get_span(&head), "incorrect number of arguments")),
      }
      _ => self.check_pure_expr(e, Some(&Type::Bool)).map(|e| Prop::Pure(Rc::new(e)))
    }
  }

  fn push_user_local(&mut self, user: AtomID, decl: AtomID) {
    match self.user_locals.entry(user) {
      Entry::Vacant(e) => {e.insert((decl, vec![]));}
      Entry::Occupied(mut e) => {
        let (head, vec) = e.get_mut();
        vec.push(std::mem::replace(head, decl))
      }
    }
  }
  /// Add a list of arguments to the context.
  fn add_args_to_context(&mut self, args: &[PTuplePattern], ctx: ArgsContext) -> EResult<()> {
    self.context.reserve(args.len());
    for arg in args {
      match arg {
        PTuplePattern::Name(_, _, _) => {}
        PTuplePattern::Typed(b, _) if matches!(**b, PTuplePattern::Name(_, _, _)) => {}
        _ => return Err(ElabError::new_e(self.fsp.span,
          "tuple patterns in argument position are not implemented")),
      }
      let user = arg.name();
      let decl = self.get_fresh_local(user);
      if user != AtomID::UNDER { self.push_user_local(user, decl) }
      self.used_names.insert(decl);
      let is_ty = ctx.tyvar_allowed() && arg.ty().as_atom().map_or(false, |a| a == AtomID::UNDER ||
        matches!(self.mmc.keywords.get(&a), Some(Keyword::Star)));
      let ty = if is_ty {GType::Star} else {
        let ty = arg.ty();
        if !ctx.hyp_allowed() || self.probably_a_type(&ty) {
          let ty = if ty.as_atom().map_or(false, |a| a == AtomID::UNDER) {
            if let Some(ty) = ctx.default_value() {ty}
            else {self.check_ty(&ty)?}
          } else {self.check_ty(&ty)?};
          let copy = self.copy_type(&ty);
          GType::Ty(arg.ghost(), ty, copy)
        } else {
          GType::Prop(self.check_prop(&ty)?)
        }
      };
      self.context.push(Variable {user, decl, ty});
    }
    Ok(())
  }

  fn check_tuple_pattern(&mut self, pat: PTuplePattern) -> EResult<TuplePattern> {
    Ok(match pat {
      PTuplePattern::Name(g, name, sp) => TuplePattern::Name(g, name, sp),
      PTuplePattern::Tuple(pats, sp) => TuplePattern::Tuple(
        pats.into_vec().into_iter().map(|pat| self.check_tuple_pattern(pat))
          .collect::<EResult<Box<[_]>>>()?, sp),
      PTuplePattern::Typed(pat, ty) => {
        let ty = self.check_ty(&ty)?;
        TuplePattern::Typed(Box::new((self.check_tuple_pattern(*pat)?, ty)))
      }
    })
  }

  fn add_tuple_pattern_to_context(&mut self,
      pat: TuplePattern, tgt: Option<InferType<'_>>) -> EResult<TypedTuplePattern> {
    match pat {
      TuplePattern::Typed(pat) => {
        let (pat, ty) = *pat;
        /* TODO: tgt = ty */
        self.add_tuple_pattern_to_context(pat, Some(InferType::ty(&ty)))
      }
      TuplePattern::Name(g, user, sp) => {
        let decl = self.get_fresh_local(user);
        if user != AtomID::UNDER { self.push_user_local(user, decl) }
        self.used_names.insert(decl);
        let ty = tgt.and_then(|tgt| tgt.to_type()).ok_or_else(|| ElabError::new_e(
          try_get_span_from(&self.fsp, sp.as_ref()), "could not infer type"))?;
        Ok(TypedTuplePattern::Name(g, decl, sp, Box::new(ty)))
      }
      TuplePattern::Tuple(pats, sp) => {
        match tgt {
          None => return Err(ElabError::new_e(
            try_get_span_from(&self.fsp, sp.as_ref()), "could not infer type")),
          Some(InferType::Unit) | Some(InferType::Ty(Type::Unit)) => {
            if !pats.is_empty() {
              return Err(ElabError::new_e(
                try_get_span_from(&self.fsp, sp.as_ref()), "expected 0 subpatterns"))
            }
            Ok(TypedTuplePattern::Unit)
          }
          Some(InferType::Ty(Type::Single(e, ty))) if pats.len() == 2 => {
            let mut pats = pats.into_vec();
            let mut it = pats.drain(..);
            if let (Some(p1), Some(p2), None) = (it.next(), it.next(), it.next()) {
              let x = self.add_tuple_pattern_to_context(p1, Some(InferType::ty(ty)))?;
              let p = Type::Prop(Box::new(Prop::Eq(Rc::new(x.to_expr()), e.clone())));
              let h = self.add_tuple_pattern_to_context(p2, Some(InferType::Ty(&p)))?;
              Ok(TypedTuplePattern::Single(Box::new((x, h))))
            } else {
              return Err(ElabError::new_e(
                try_get_span_from(&self.fsp, sp.as_ref()), "expected 2 subpatterns"))
            }
          }
          Some(tgt) => Err(ElabError::new_e(
            try_get_span_from(&self.fsp, sp.as_ref()),
            format!("could not pattern match at type {}", self.elab.print(&tgt)))),
        }
      }
    }
  }

  fn check_expr_list(&mut self, ts: &mut TypeState, args: &[LispVal],
      TypeTarget(tgt, pat): TypeTarget<'_>, sp: Span) -> Result<Expr, ElabError> {
    let mut vec = Vec::with_capacity(args.len());
    if let Some(TuplePattern::Tuple(pat, _)) = pat {
      if pat.len() != args.len() {
        return Err(ElabError::new_e(sp,
          format!("Can't pattern match, expected {} args, got {}", args.len(), pat.len())))
      }
    }
    match tgt {
      None => {
        if let Some(TuplePattern::Tuple(pat, _)) = pat {
          for (e, pat) in (&*args).iter().zip(&**pat) {
            vec.push(self.check_expr(ts, e.clone(), pat.into())?)
          }
        } else {
          for e in args { vec.push(self.check_expr(ts, e.clone(), TypeTarget::NONE)?) }
        }
      }
      Some(Type::List(tys)) if tys.len() == args.len() => {
        if let Some(TuplePattern::Tuple(pat, _)) = pat {
          for ((e, ty), pat) in (&*args).iter().zip(&**tys).zip(&**pat) {
            let mut tgt: TypeTarget<'_> = pat.into();
            if tgt.0.is_none() {tgt.0 = Some(ty)}
            vec.push(self.check_expr(ts, e.clone(), tgt)?)
          }
        } else {
          for (e, ty) in (&*args).iter().zip(&**tys) {
            vec.push(self.check_expr(ts, e.clone(), ty.into())?)
          }
        }
      }
      Some(ty) => return Err(ElabError::new_e(sp, format!("type error, expected {:?}", ty))),
    }
    Ok(Expr::Tuple(vec.into()))
  }

  fn check_expr(&mut self, ts: &mut TypeState, e: LispVal, tgt: TypeTarget<'_>) -> EResult<Expr> {
    let fsp = e.fspan();
    let fsp = fsp.as_ref();
    let sp = try_get_span_from(&self.fsp, fsp);
    Ok(match self.parser().parse_expr(e)? {
      PExpr::Nil => Expr::Pure(PureExpr::Unit),
      PExpr::Var(sp, user) => {
        let var = self.user_locals.get(&user).ok_or_else(||
          ElabError::new_e(try_get_span_from(&self.fsp, Some(&sp)),
          format!("unknown variable '{}'", self.elab.print(&user))))?.0;
        let t = &mut ts.0[self.find_index(var).expect("missing variable")];
        match t {
          VariableState::Owned => *t = VariableState::Moved,
          VariableState::Copy => {}
          VariableState::Moved => return Err(ElabError::new_e(
            try_get_span_from(&self.fsp, Some(&sp)), "type error: value already moved"))
        }
        Expr::Var(var)
      }
      PExpr::Number(n) => Expr::Pure(PureExpr::Int(n)),
      PExpr::Let {lhs, rhs} => {
        let lhs = self.check_tuple_pattern(lhs)?;
        if let Some(rhs) = rhs {
          let rhs = self.check_expr(ts, rhs, (&lhs).into())?;
          let ty = self.infer_expr_type(&rhs).to_type();
          let lhs = self.add_tuple_pattern_to_context(lhs, Some(InferType::from_type(&ty)))?;
          Expr::Let {lhs, rhs: Some(Box::new(rhs))}
        } else {
          let lhs = self.add_tuple_pattern_to_context(lhs, None)?;
          Expr::Let {lhs, rhs: None}
        }
      }
      PExpr::Call {f, fsp, args, variant} => {
        let name = self.mmc.names.get(&f).ok_or_else(|| ElabError::new_e(sp,
          format!("unknown function '{}'", self.elab.print(&f))))?;
        let fsp1 = try_get_span_from(&self.fsp, fsp.as_ref());
        macro_rules! err {($($e:expr),*) => {
          return Err(ElabError::new_e(fsp1, format!($($e),*)))
        }}
        // macro_rules! check_tgt {($ty:pat, $s:expr) => {
        //   if !tgt.map_or(true, |tgt| matches!(tgt, $ty)) {
        //     err!(concat!("type error, expected ", $s))
        //   }
        // }}
        macro_rules! get_int_tgt {() => {
          match tgt.0 {
            None => &Type::Int(Size::Inf),
            Some(ty@Type::Int(_)) => ty,
            Some(ty@Type::UInt(_)) => ty,
            Some(_) => err!("type error, expected an integer"),
          }.into()
        }}
        match self.mmc.names.get(&f) {
          None => err!("unknown function '{}'", self.elab.print(&f)),
          Some(Entity::Const(GlobalTC::Unchecked)) => err!("forward referencing constants is not allowed"),
          Some(Entity::Prim(Prim {op: Some(prim), ..})) => match (prim, &*args) {
            (PrimOp::Add, args) =>
              self.check_lassoc_expr(ts, args, || Ok(Expr::Pure(PureExpr::Int(0.into()))), Ok, Binop::Add, get_int_tgt!())?,
            (PrimOp::And, args) => {
              // check_tgt!(Type::Bool, "a bool");
              self.check_lassoc_expr(ts, args, || Ok(Expr::Pure(PureExpr::Bool(true))), Ok, Binop::And, (&Type::Bool).into())?
            }
            (PrimOp::Or, args) => {
              // check_tgt!(Type::Bool, "a bool");
              self.check_lassoc_expr(ts, args, || Ok(Expr::Pure(PureExpr::Bool(false))), Ok, Binop::Or, (&Type::Bool).into())?
            }
            (PrimOp::Assert, args) => Expr::Assert(Rc::new(
              self.check_lassoc_pure_expr(args, || Ok(PureExpr::Bool(true)), Ok, Binop::And, (&Type::Bool).into())?)),
            (PrimOp::BitAnd, args) =>
              self.check_lassoc_expr(ts, args, || Ok(Expr::Pure(PureExpr::Int((-1).into()))), Ok, Binop::BitAnd, get_int_tgt!())?,
            (PrimOp::BitNot, args) => {
              let (sz, ty) = match tgt.0 {
                None => (Size::Inf, &Type::Int(Size::Inf)),
                Some(ty) => match ty {
                  Type::Int(_) => (Size::Inf, ty),
                  &Type::UInt(sz) => (sz, ty),
                  _ => err!("type error, expected an integer"),
                },
                _ => err!("type error, expected an integer"),
              };
              self.check_lassoc_expr(ts, args, || Ok(Expr::Pure(PureExpr::Int((-1).into()))),
                |e| Ok(Expr::Unop(Unop::BitNot(sz), Box::new(e))), Binop::BitOr, ty.into())?
            }
            (PrimOp::BitOr, args) =>
              self.check_lassoc_expr(ts, args, || Ok(Expr::Pure(PureExpr::Int(0.into()))), Ok, Binop::BitOr, get_int_tgt!())?,
            (PrimOp::BitXor, args) =>
              self.check_lassoc_expr(ts, args, || Ok(Expr::Pure(PureExpr::Int(0.into()))), Ok, Binop::BitXor, get_int_tgt!())?,
            (PrimOp::Index, args) => {
              enum AutoDeref { Own, Ref, Mut }
              let (arr, idx, pf) = match args {
                [arr, idx] => (arr, idx, None),
                [arr, idx, pf] => (arr, idx, Some(pf)),
                _ => err!("expected 2 or 3 arguments"),
              };
              let mut arr = self.check_expr(ts, arr.clone(), TypeTarget::NONE)?;
              let idx = Rc::new(self.check_pure_expr(idx, Some(&Type::UInt(Size::Inf)))?);
              let mut aty = self.infer_expr_type(&arr);
              let mut derefs = vec![];
              let len = loop {
                match aty {
                  InferType::Own(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Own); }
                  InferType::Ref(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Ref); }
                  InferType::RefMut(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Mut); }
                  InferType::Ty(Type::Array(_, len)) => break len.clone(),
                  _ => err!("type error, expcted an array"),
                }
              };
              for s in derefs {
                arr = match s {
                  AutoDeref::Own => Expr::DerefOwn(Box::new(arr)),
                  AutoDeref::Ref => Expr::Deref(Box::new(arr)),
                  AutoDeref::Mut => Expr::DerefMut(Box::new(arr)),
                }
              }
              let prop = PureExpr::Binop(Binop::Lt, idx.clone(), len);
              let pf = match pf {
                Some(pf) => self.check_expr(ts, pf.clone(),
                  (&Type::Prop(Box::new(Prop::Pure(Rc::new(prop))))).into())?,
                None => Expr::Assert(Rc::new(prop)),
              };
              Expr::Index(Box::new(arr), idx, Box::new(pf))
            }
            (PrimOp::List, args) => self.check_expr_list(ts, args, tgt, fsp1)?,
            (PrimOp::Mul, args) =>
              self.check_lassoc_expr(ts, args, || Ok(Expr::Pure(PureExpr::Int(1.into()))), Ok, Binop::Mul, get_int_tgt!())?,
            (PrimOp::Not, args) => {
              // check_tgt!(Type::Bool, "a bool");
              self.check_lassoc_expr(ts, args, || Ok(Expr::Pure(PureExpr::Bool(true))),
                |e| Ok(Expr::Unop(Unop::Not, Box::new(e))), Binop::Or, (&Type::Bool).into())?
            }
            (PrimOp::Le, args) => { /*check_tgt!(Type::Bool, "a bool");*/ self.check_ineq(ts, args, Binop::Le, fsp.as_ref())? }
            (PrimOp::Lt, args) => { /*check_tgt!(Type::Bool, "a bool");*/ self.check_ineq(ts, args, Binop::Lt, fsp.as_ref())? }
            (PrimOp::Eq, args) => { /*check_tgt!(Type::Bool, "a bool");*/ self.check_ineq(ts, args, Binop::Eq, fsp.as_ref())? }
            (PrimOp::Ne, args) => { /*check_tgt!(Type::Bool, "a bool");*/ self.check_ineq(ts, args, Binop::Ne, fsp.as_ref())? }
            (PrimOp::Ghost, args) => Expr::Ghost(Box::new({
              if let [e] = args {
                self.check_expr(ts, e.clone(), tgt)?
              } else {
                self.check_expr_list(ts, args, tgt, fsp1)?
              }
            })),
            (PrimOp::Typed, [e, ty]) => {
              /* TODO: check ty == tgt */
              let ty = self.check_ty(ty)?;
              self.check_expr(ts, e.clone(), (&ty).into())?
            }
            (PrimOp::As, [e, ty]) => {
              let ty = self.check_ty(ty)?;
              let e = self.check_expr(ts, e.clone(), TypeTarget::NONE)?;
              Expr::As(Box::new((e, ty)))
            }
            (PrimOp::Typed, _) |
            (PrimOp::As, _) => err!("expected 2 arguments"),
            (PrimOp::Pure, [e]) => {
              let ty = tgt.0.ok_or_else(|| ElabError::new_e(
                try_get_span_from(&self.fsp, fsp.as_ref()), "type ascription required"))?;
              let e = self.check_mm0_expr(e.clone())?;
              Expr::Pure(PureExpr::Pure(Box::new((e, ty.clone()))))
            }
            (PrimOp::Pure, _) => return err!("expected 1 argument"),
            (PrimOp::Pun, _) => err!("check_expr pun"),
            (PrimOp::Slice, _) => err!("check_expr slice"),
            (PrimOp::TypeofBang, _) => err!("check_expr typeof!"),
            (PrimOp::Typeof, _) => err!("check_expr typeof"),
          }
          Some(Entity::Op(Operator::Proc(proc, _))) => {
            let args = args.into_iter().map(|e| self.check_expr(ts, e, TypeTarget::NONE))
              .collect::<EResult<Box<[_]>>>()?;
            let variant = if let Some(v) = variant {
              Some(Box::new(self.check_expr(ts, v, TypeTarget::NONE)?))
            } else {None};
            Expr::Call {f, fsp, args, variant}
          }
          Some(_) => err!("check_expr unimplemented entity type"),
        }
      }
      PExpr::Entail(_, _) => self.todo(fsp, "check_expr Entail", ())?,
      PExpr::Block(u) => {
        let es = self.check_stmts(ts, u, tgt)?;
        if es.is_empty() {Expr::Pure(PureExpr::Unit)}
        else {Expr::Block(es)}
      }
      PExpr::Label { name, args, variant, body } => self.todo(fsp, "check_expr Label", ())?,
      PExpr::If { muts, branches, els } => self.todo(fsp, "check_expr If", ())?,
      PExpr::Switch(_, _) => self.todo(fsp, "check_expr Switch", ())?,
      PExpr::While { hyp, cond, var, invar, body } => self.todo(fsp, "check_expr While", ())?,
      PExpr::Hole(_) => self.todo(fsp, "check_expr Hole", ())?,
    })
  }

  fn check_stmts(&mut self, ts: &mut TypeState, u: Uncons, mut tgt: TypeTarget<'_>) -> EResult<Box<[Expr]>> {
    Ok(match u.len().checked_sub(1) {
      // None if !tgt.map_or(true, |tgt| matches!(tgt, TypeTarget::Unit)) =>
      // return Err(ElabError::new_e(self.try_get_span(&u.as_lisp()), "expected a value, got empty block")),
      None => Box::new([]),
      Some(n) => u.enumerate()
        .map(|(i, e)| self.check_expr(ts, e, if i == n {tgt} else {TypeTarget::NONE}))
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
      AST::Proc(proc, body) => match proc.kind {
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
          self.add_args_to_context(&proc.args, ArgsContext::ProcArgs)?;
          self.add_args_to_context(&proc.rets, ArgsContext::ProcArgs)?;
          let rets = self.context.drain(proc.args.len()..).collect::<Vec<_>>();
          if let Some((e, _)) = &proc.variant {
            return Err(ElabError::new_e(self.try_get_span(e), "proc variants are not implemented"))
          }
          for &(a, ref fsp) in &*proc.muts {
            match self.mmc.names.get(&a) {
              Some(Entity::Global(GlobalTC::Unchecked)) =>
                return Err(ElabError::new_e(try_get_span_from(&self.fsp, fsp.as_ref()),
                  "forward referencing globals is supported")),
              Some(&Entity::Global(GlobalTC::Checked(_, decl, _, _))) =>
                {self.mut_globals.insert(a, decl);}
              _ => return Err(ElabError::new_e(try_get_span_from(&self.fsp, fsp.as_ref()),
                "unknown global")),
            }
          }
          let mut ts = self.new_type_state();
          let body = self.check_stmts(&mut ts, body.clone(), TypeTarget::NONE)?;
          println!("{:?}", body);
          // self.todo((rets, body))?;
          return Err(ElabError::new_e(
            try_get_span_from(&self.fsp, proc.span.as_ref()), "unimplemented: finish proc"))
        }
      }
      AST::Global {full, lhs, rhs} => {
        return Err(ElabError::new_e(
          try_get_span_from(&self.fsp, full.as_ref()), "unimplemented: global"))
      },
      AST::Const {full, lhs, rhs} => {
        match lhs {
          PTuplePattern::Name(_, _, _) => {}
          PTuplePattern::Typed(b, _) if matches!(**b, PTuplePattern::Name(_, _, _)) => {}
          _ => return Err(ElabError::new_e(self.fsp.span,
            "tuple patterns in constants are not implemented")),
        }
        let ty = lhs.ty();
        let (e, ty2);
        if ty.as_atom().map_or(false, |a| a == AtomID::UNDER) {
          e = self.check_pure_expr(rhs, None)?;
          ty2 = self.infer_type(&e).to_type().expect("pure exprs can't have type *")
        } else {
          ty2 = self.check_ty(&ty)?;
          e = self.check_pure_expr(rhs, Some(&ty2))?;
        };
        let user = lhs.name();
        if user != AtomID::UNDER {
          let decl = self.get_fresh_decl(user);
          self.push_user_local(user, decl);
          // TODO: write def dname := val
          if let Entity::Const(ty @ GlobalTC::Unchecked) = self.mmc.names.get_mut(&user).unwrap() {
            *ty = GlobalTC::Checked(full.clone(), decl, Rc::new(ty2), Rc::new(Expr::Pure(e)))
          } else {unreachable!()}
        }
      }
      &AST::Typedef {name, ref span, ref args, ref val} => {
        self.add_args_to_context(args, ArgsContext::TypeArgs)?;
        let val = self.check_ty(val)?;
        let dname = self.get_fresh_decl(name);
        // TODO: write def dname := val
        if let Entity::Type(ty @ NType::Unchecked) = self.mmc.names.get_mut(&name).unwrap() {
          *ty = NType::Checked(span.clone(), dname, Rc::new(val))
        } else {unreachable!()}
      }
      &AST::Struct {name, ref span, ref args, ref fields} => {
        self.add_args_to_context(args, ArgsContext::TypeArgs)?;
        self.add_args_to_context(fields, ArgsContext::StructFields)?;
        let fields = self.context.drain(args.len()..)
          .map(|v| (v.decl, match v.ty {
            GType::Star => unreachable!(),
            GType::Ty(g, ty, _) => Type::ghost_if(g, ty),
            GType::Prop(p) => Type::Prop(Box::new(p)),
          })).collect::<Vec<(AtomID, Type)>>();
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
