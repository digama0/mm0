//! MMC type checking pass.
#![allow(unused)]

use std::rc::Rc;
use std::collections::{HashMap, HashSet, hash_map::Entry};
use std::convert::TryInto;
use std::mem;
use crate::elab::{ElabError, Elaborator, Environment,
  Result as EResult,
  environment::{AtomId, AtomData, Type as EType},
  lisp::{LispKind, LispVal, Uncons, debug, print::{EnvDisplay, FormatEnv}},
  local_context::{try_get_span_from, try_get_span}};
use crate::{Span, FileSpan};
use super::{Compiler,
  nameck::{Type as NType, Prim, PrimType, PrimOp, PrimProp,
    Intrinsic, Entity, GlobalTc, Operator, ProcTc},
  parser::{Expr as PExpr, Parser, Rename, TuplePattern as PreTuplePattern, head_keyword},
  types::{Ast, Binop, Expr, Keyword, Lifetime, Place, Mm0Expr, Mm0ExprNode, VarId,
    ProcKind, Prop, PureExpr, Size, Type, TuplePattern, Unop}};

enum InferType<'a> {
  Unit,
  Bool,
  Int,
  Own(&'a Type),
  // Ref(Lifetime, &'a Type),
  // RefMut(&'a Type),
  Ty(&'a Type),
  Prop(&'a Prop),
  PropPure(&'a Rc<PureExpr>),
  Subst(Box<InferType<'a>>, VarId, &'a Rc<PureExpr>),
}

impl<'a> Default for InferType<'a> {
  fn default() -> Self { Self::Unit }
}
impl<'a> InferType<'a> {
  fn ty(ty: &'a Type) -> Self {
    match ty {
      Type::Own(ty) => Self::Own(ty),
      // Type::Ref(lft, ty) => Self::Ref(*lft, ty),
      // Type::RefMut(ty) => Self::RefMut(ty),
      ty => Self::Ty(ty),
    }
  }

  fn subst(&mut self, v: VarId, e: &'a Rc<PureExpr>) {
    match self {
      InferType::Int | InferType::Unit | InferType::Bool => {},
      _ => *self = Self::Subst(Box::new(mem::take(self)), v, e),
    }
  }

  fn to_type(&self) -> Type {
    match *self {
      InferType::Int => Type::Int(Size::Inf),
      InferType::Unit => Type::Unit,
      InferType::Bool => Type::Bool,
      InferType::Own(ty) => Type::Own(Box::new(ty.clone())),
      // InferType::Ref(lft, ty) => Type::Ref(Box::new(ty.clone())),
      // InferType::RefMut(ty) => Type::RefMut(Box::new(ty.clone())),
      InferType::Ty(ty) => ty.clone(),
      InferType::Prop(p) => Type::Prop(Box::new(p.clone())),
      InferType::PropPure(e) => Type::Prop(Box::new(Prop::Pure(e.clone()))),
      InferType::Subst(ref ty, v, e) => Type::Subst(Box::new(ty.to_type()), v, e.clone()),
    }
  }

  fn proj_type(self, i: u32) -> Self {
    match self {
      InferType::Ty(Type::List(tys)) => InferType::Ty(&tys[i as usize]),
      InferType::Ty(Type::Struct(_)) |
      InferType::Subst(..) => todo!(),
      _ => unreachable!(),
    }
  }

  fn index_type(self) -> Self {
    match self {
      InferType::Ty(Type::Array(ty, _)) => InferType::Ty(ty),
      _ => unreachable!(),
    }
  }
}

impl<'a> EnvDisplay for InferType<'a> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use std::fmt::Display;
    match *self {
      InferType::Int => "int".fmt(f),
      InferType::Unit => "()".fmt(f),
      InferType::Bool => "bool".fmt(f),
      // InferType::Star => "*".fmt(f),
      InferType::Own(ty) => write!(f, "(own {})", fe.to(ty)),
      // InferType::Ref(ty) => write!(f, "(& {})", fe.to(ty)),
      // InferType::RefMut(ty) => write!(f, "(&mut {})", fe.to(ty)),
      InferType::Ty(ty) => ty.fmt(fe, f),
      InferType::Prop(p) => p.fmt(fe, f),
      InferType::PropPure(e) => e.fmt(fe, f),
      InferType::Subst(ref ty, v, e) => write!(f, "({})[{} -> {}]", fe.to(ty), v, fe.to(e)),
    }
  }
}

impl Default for PreTuplePattern {
  fn default() -> Self { Self::Ready(TuplePattern::Unit) }
}

impl PreTuplePattern {
  /// The name of a variable binding (or `_` for a tuple pattern)
  #[must_use] fn name(&self) -> AtomId {
    match self {
      &PreTuplePattern::Name(_, a, _) => a,
      PreTuplePattern::Typed(p, _) => p.name(),
      _ => AtomId::UNDER
    }
  }

  /// The span of a variable binding or tuple pattern.
  #[must_use] fn fspan(&self) -> Option<&FileSpan> {
    match self {
      PreTuplePattern::Name(_, _, fsp) |
      PreTuplePattern::Tuple(_, fsp) => fsp.as_ref(),
      PreTuplePattern::Typed(p, _) => p.fspan(),
      PreTuplePattern::Ready(_) => None,
    }
  }

  /// True if all the bindings in this pattern are ghost.
  #[must_use] fn ghost(&self) -> bool {
    match self {
      &PreTuplePattern::Name(g, _, _) => g,
      PreTuplePattern::Typed(p, _) => p.ghost(),
      PreTuplePattern::Tuple(ps, _) => ps.iter().all(PreTuplePattern::ghost),
      PreTuplePattern::Ready(p) => p.ghost(),
    }
  }

  /// The type of this binding, or `_` if there is no explicit type.
  #[must_use] fn ty(&self) -> LispVal {
    match self {
      PreTuplePattern::Typed(_, ty) => ty.clone(),
      _ => LispVal::atom(AtomId::UNDER)
    }
  }
}

#[derive(Debug, Default)]
struct TypeTarget<'a>(Option<&'a Type>, Option<&'a mut PreTuplePattern>);

impl<'a> TypeTarget<'a> {
  const NONE: Self = TypeTarget(None, None);

  fn reborrow(&mut self) -> TypeTarget<'_> {
    TypeTarget(self.0, self.1.as_deref_mut())
  }
}

impl<'a> From<&'a Type> for TypeTarget<'a> {
  fn from(t: &'a Type) -> Self { Self(Some(t), None) }
}

// impl<'a> From<&'a TuplePattern> for TypeTarget<'a> {
//   fn from(t: &'a TuplePattern) -> Self {
//     if let TuplePattern::Typed(t) = t {
//       TypeTarget(Some(&t.1), Some(&t.0))
//     } else {
//       TypeTarget(None, Some(t))
//     }
//   }
// }

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
  user: AtomId,
  /// The target name of this variable.
  decl: VarId,
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
  /// The first unused variable ID.
  next_var: VarId,
  /// Maps names from the MMC source in scope to their internal names.
  /// The vector contains shadowed variables in outer scopes.
  user_locals: HashMap<AtomId, Vec<VarId>>,
  /// The set of globals that are mutable in the current context (and their mapping to internal names).
  mut_globals: HashMap<AtomId, VarId>,
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

fn get_fresh_name(env: &mut Environment, mut base: Vec<u8>, mut bad: impl FnMut(AtomId, &AtomData) -> bool) -> AtomId {
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

fn pop_user_local(m: &mut HashMap<AtomId, Vec<VarId>>, user: AtomId) -> Option<()> {
  if user != AtomId::UNDER {
    if let Some(vec) = m.get_mut(&user) { vec.pop()?; }
  }
  Some(())
}

impl<'a> TypeChecker<'a> {
  /// Constructs a new [`TypeChecker`], which can be used to typecheck many `AST` items
  /// via [`typeck`](Self::typeck) and will reuse its internal buffers.
  pub fn new(mmc: &'a mut Compiler, elab: &'a mut Elaborator, fsp: FileSpan) -> Self {
    Self {mmc, elab, fsp,
      next_var: VarId::default(),
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

  fn get_fresh_decl(&mut self, base: AtomId) -> AtomId {
    let mut s = self.mmc.prefix.clone();
    s.extend_from_slice(&self.elab.data[base].name);
    get_fresh_name(&mut self.elab, s, |_, ad| ad.decl.is_some())
  }

  #[inline] fn get_fresh_local(&mut self) -> VarId {
    let n = self.next_var;
    self.next_var.0 += 1;
    n
  }

  fn find_index(&self, a: VarId) -> Option<usize> {
    self.context.iter().position(|v| v.decl == a)
  }

  fn find(&self, a: VarId) -> Option<&Variable> {
    self.context.iter().find(|&v| v.decl == a)
  }

  fn apply_rename<E>(&mut self,
    it: impl Iterator<Item=(AtomId, AtomId)>,
    err: impl FnOnce(String) -> E
  ) -> Result<(), E> {
    let mut vec = vec![];
    for (from, to) in it {
      if from == AtomId::UNDER { return Err(err("can't rename variable '_'".into())) }
      let var =
        if let Some(v) = self.user_locals.get_mut(&from).and_then(Vec::pop) { v }
        else { return Err(err(format!("unknown variable '{}'", self.elab.print(&from)))) };
      vec.push((var, to));
    }
    for (var, to) in vec {
      self.user_locals.entry(to).or_default().push(var);
      self.context.iter_mut().find(|v| v.decl == var)
        .expect("unknown variable").user = to;
    }
    Ok(())
  }

  fn with_rename<T>(&mut self, with: &[Rename], sp: Span,
    f: impl FnOnce(&mut Self) -> Result<T, ElabError>,
  ) -> Result<T, ElabError> {
    if !with.is_empty() {
      self.apply_rename(
        with.iter().filter_map(|x| if let Rename::Old {from, to} = *x {Some((from, to))} else {None}),
        |e| ElabError::new_e(sp, e))?;
    }
    let res = f(self)?;
    if !with.is_empty() {
      self.apply_rename(
        with.iter().filter_map(|x| if let Rename::New {from, to} = *x {Some((from, to))} else {None}),
        |e| ElabError::new_e(sp, e))?;
    }
    Ok(res)
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
      Prop::Mm0(_) => None,
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
      Prop::Heap(..) => Some(Prop::Emp),
      Prop::HasTy(v, ty) => self.copy_type(ty).map(|ty| Prop::HasTy(v.clone(), Box::new(ty))),
      // Prop::MVar(_) => Some(Prop::Moved(Box::new(p.clone()))),
      Prop::Subst(ty, v, e) => unreachable!("unapplied substitution in context")
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
      Type::Moved(_) |
      Type::Ref(..) |
      Type::RefSn(_) => None,
      Type::Array(ty, n) => self.copy_type(ty)
        .map(|ty| Type::Array(Box::new(ty), n.clone())),
      Type::Own(_) |
      Type::Shr(_, _) => Some(Type::UInt(Size::S64)),
      Type::List(tys) => list(tys, |ty| self.copy_type(ty)).map(Type::List),
      Type::Single(e, ty) => self.copy_type(ty).map(|ty| Type::Single(e.clone(), Box::new(ty))),
      Type::Struct(tys) => list(tys, |(a, ty)| Some((*a, self.copy_type(ty)?))).map(Type::Struct),
      Type::And(tys) => list(tys, |ty| self.copy_type(ty)).map(Type::And),
      Type::Or(tys) => list(tys, |ty| self.copy_type(ty)).map(Type::Or),
      Type::Ghost(ty) => Some(Type::Ghost(Box::new(self.copy_type(ty)?))),
      Type::Prop(p) => Some(Type::Prop(Box::new(self.copy_prop(p)?))),
      Type::Var(_) |
      Type::User(..) |
      Type::Input |
      Type::Output => Some(Type::Moved(Box::new(ty.clone()))),
      &Type::Subst(ref ty, v, ref e) => self.copy_type(ty)
        .map(|ty| Type::Subst(Box::new(ty), v, e.clone())),
    }
  }

  fn infer_var_type(&'a self, i: VarId) -> InferType<'a> {
    match &self.find(i).expect("variable not found").ty {
      GType::Ty(_, ty, _) => InferType::ty(ty),
      GType::Star => panic!("unexpected type variable"),
      GType::Prop(p) => InferType::Prop(p),
    }
  }

  fn infer_place_type(&'a self, e: &'a Place) -> InferType<'a> {
    match e {
      &Place::Var(i) => self.infer_var_type(i),
      &Place::Proj(ref e, i) => self.infer_place_type(e).proj_type(i),
      Place::Index(a, _) => self.infer_place_type(a).index_type(),
    }
  }

  fn infer_type(&'a self, e: &'a PureExpr) -> InferType<'a> {
    match e {
      &PureExpr::Var(i) => self.infer_var_type(i),
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
      PureExpr::Index(a, _) => self.infer_type(e).index_type(),
      PureExpr::Tuple(es, ty) => InferType::ty(ty),
      &PureExpr::Proj(ref e, i) => self.infer_type(e).proj_type(i),
      PureExpr::Deref(e) => match self.infer_type(e) {
        InferType::Ty(Type::RefSn(x)) => self.infer_place_type(x),
        _ => unreachable!(),
      },
      PureExpr::Ghost(e) => self.infer_type(e),
      PureExpr::As(e) => InferType::ty(&e.1),
      PureExpr::Pure(e) => InferType::ty(&e.1),
      &PureExpr::Subst(ref x, v, ref e) => {
        let mut ty = self.infer_type(x);
        ty.subst(v, e);
        ty
      }
    }
  }

  fn infer_expr_type(&'a self, e: &'a Expr) -> InferType<'a> {
    match e {
      &Expr::Var(i) => self.infer_var_type(i),
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
      Expr::Index(a, _, _) => self.infer_expr_type(e).index_type(),
      Expr::Tuple(es, ty) => InferType::ty(ty),
      &Expr::Proj(ref e, i) => self.infer_expr_type(e).proj_type(i),
      Expr::Deref(e) => match self.infer_expr_type(e) {
        InferType::Ty(Type::RefSn(x)) => self.infer_place_type(x),
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
    if name == AtomId::UNDER { return true }
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
    if name == AtomId::UNDER {
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
        (PrimType::Ref, [ty]) => Ok(Type::Shr(Lifetime::Unknown, Box::new(self.check_ty(ty)?))),
        (PrimType::List, args) => Ok(Type::List(check_tys!(args))),
        (PrimType::And, args) => Ok(Type::And(check_tys!(args))),
        (PrimType::Or, args) => Ok(Type::Or(check_tys!(args))),
        (PrimType::Ghost, [ty]) => Ok(Type::Ghost(Box::new(self.check_ty(ty)?))),
        (PrimType::Single, [e]) => {
          let pe = self.check_pure_expr(e, None)?;
          let ty = self.infer_type(&pe).to_type();
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
        Ok(Type::User(name, Box::new([]), Box::new([])))
      }
      Some(_) => Err(ElabError::new_e(self.try_get_span(&head), "expected a type")),
      None => match self.context.iter().rfind(|v| v.user == name) {
        Some(v) if matches!(v.ty, GType::Star) => Ok(Type::Var(v.decl)),
        _ => Err(ElabError::new_e(self.try_get_span(e),
          format!("undeclared type {}", self.elab.print(&head))))
      }
    }
  }

  fn check_mm0_expr(&self, e: LispVal) -> Result<Mm0Expr, ElabError> {
    type Subst = (Vec<PureExpr>, HashMap<AtomId, u32>, Vec<AtomId>);
    fn list_opt<'a>(tc: &TypeChecker<'a>, subst: &mut Subst,
      e: &LispVal, head: AtomId, args: Option<Uncons>
    ) -> Result<Option<Mm0ExprNode>, ElabError> {
      let tid = tc.elab.term(head).ok_or_else(|| ElabError::new_e(tc.try_get_span(e),
        format!("term '{}' not declared", tc.elab.data[head].name)))?;
      let term = &tc.elab.terms[tid];
      if args.as_ref().map_or(0, Uncons::len) != term.args.len() {
        return Err(ElabError::new_e(tc.try_get_span(e),
          format!("expected {} arguments", term.args.len())));
      }
      Ok(if let Some(u) = args {
        let mut cnst = true;
        let mut vec = Vec::with_capacity(u.len());
        let len = subst.2.len();
        for (e, (_, arg)) in u.zip(&*term.args) {
          match *arg {
            EType::Bound(s) => {
              let a = e.as_atom().ok_or_else(||
                ElabError::new_e(tc.try_get_span(&e), "expected an atom"))?;
              subst.2.push(a);
              vec.push(Mm0ExprNode::Const(e))
            }
            EType::Reg(s, deps) => {
              let n = node(tc, subst, e)?;
              cnst &= matches!(n, Mm0ExprNode::Const(_));
              vec.push(n)
            }
          }
        }
        subst.2.truncate(len);
        if cnst {None} else {Some(Mm0ExprNode::Expr(tid, vec))}
      } else {None})
    }

    fn node_opt<'a>(
      tc: &TypeChecker<'a>, subst: &mut Subst, e: &LispVal
    ) -> Result<Option<Mm0ExprNode>, ElabError> {
      e.unwrapped(|r| Ok(if let LispKind::Atom(a) = *r {
        if subst.2.contains(&a) {return Ok(None)}
        match subst.1.entry(a) {
          Entry::Occupied(entry) => Some(Mm0ExprNode::Var(*entry.get())),
          Entry::Vacant(entry) => if let Some(&v) = tc.user_locals.get(&a).and_then(|v| v.last()) {
            let n = subst.0.len().try_into().expect("overflow");
            entry.insert(n);
            subst.0.push(PureExpr::Var(v));
            Some(Mm0ExprNode::Var(n))
          } else {
            list_opt(tc, subst, e, a, None)?
          }
        }
      } else {
        let mut u = Uncons::from(e.clone());
        let head = u.next().ok_or_else(|| ElabError::new_e(tc.try_get_span(e),
          format!("bad expression {}", tc.elab.print(e))))?;
        let a = head.as_atom().ok_or_else(|| ElabError::new_e(tc.try_get_span(&head),
          "expected an atom"))?;
        list_opt(tc, subst, &head, a, Some(u))?
      }))
    }

    #[allow(clippy::unnecessary_lazy_evaluations)]
    fn node<'a>(
      tc: &TypeChecker<'a>, subst: &mut Subst, e: LispVal
    ) -> Result<Mm0ExprNode, ElabError> {
      Ok(node_opt(tc, subst, &e)?.unwrap_or_else(|| Mm0ExprNode::Const(e)))
    }

    let mut subst = (vec![], HashMap::new(), vec![]);
    let expr = Rc::new(node(self, &mut subst, e)?);
    Ok(Mm0Expr {subst: subst.0, expr})
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
    mut tgt: TypeTarget<'_>,
  ) -> Result<Expr, ElabError> {
    let mut e = self.check_expr(ts, arg_1, tgt.reborrow())?;
    for arg in args {
      e = Expr::Binop(binop, Box::new(e),
        Box::new(self.check_expr(ts, arg.clone(), tgt.reborrow())?))
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
    let ty = if let Some(tgt) = tgt { tgt.clone() } else {
      Type::List(vec.iter().map(|e| self.infer_type(e).to_type()).collect())
    };
    Ok(PureExpr::Tuple(vec.into(), Box::new(ty)))
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
      if name == AtomId::UNDER { return err!("holes not implemented") }
      match self.mmc.names.get(&name) {
        Some(Entity::Const(GlobalTc::Unchecked)) => err!("forward referencing constants is not allowed"),
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
            self.todo(e.fspan().as_ref(), "Index", args)
            // enum AutoDeref { Own, Ref, Mut }
            // let (arr, idx) = match args {
            //   [arr, idx] => (arr, idx),
            //   _ => return err!("expected 2 or 3 arguments"),
            // };
            // let mut arr = self.check_pure_expr(arr, None)?;
            // let idx = Rc::new(self.check_pure_expr(idx, Some(&Type::UInt(Size::Inf)))?);
            // let mut aty = self.infer_type(&arr);
            // let mut derefs = vec![];
            // let len = loop {
            //   match aty {
            //     InferType::Own(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Own); }
            //     // InferType::Ref(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Ref); }
            //     // InferType::RefMut(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Mut); }
            //     InferType::Ty(Type::Array(_, len)) => break len.clone(),
            //     _ => return err!("type error, expcted an array"),
            //   }
            // };
            // for s in derefs {
            //   arr = match s {
            //     // AutoDeref::Own => PureExpr::DerefOwn(Box::new(arr)),
            //     AutoDeref::Ref => PureExpr::Deref(Box::new(arr)),
            //     // AutoDeref::Mut => PureExpr::DerefMut(Box::new(arr)),
            //   }
            // }
            // Ok(PureExpr::Index(Box::new(arr), idx))
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
        Some(Entity::Op(Operator::Proc(_, ProcTc::Unchecked))) => Err(ElabError::new_e(
          self.try_get_span(&head), "forward referencing a procedure")),
        Some(_) => Err(ElabError::new_e(self.try_get_span(&head), "expected a function/operation")),
        None => if let Some(&i) = self.user_locals.get(&name).and_then(|v| v.last()) {
          match &self.find(i) {
            Some(Variable {ty: GType::Ty(_, ty, _), ..}) => match tgt {
              None |
              Some(_) /* TODO: if *tgt == ty */ => Ok(PureExpr::Var(i)),
            },
            _ => Err(ElabError::new_e(self.try_get_span(&head), "expected a regular variable")),
          }
        } else {
          Err(ElabError::new_e(self.try_get_span(&head),
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
      mut mk: impl FnMut(VarId, Type, Prop) -> Prop) -> Result<Prop, ElabError> {
    let (last, bis) = args.split_last().expect("expected nonempty args");
    let bis = bis.iter().map(|bi| self.parser().parse_tuple_pattern(false, bi.clone()))
      .collect::<Result<Vec<_>, _>>()?;
    let depth = self.context.len();
    self.add_args_to_context(&bis, ArgsContext::Binder)?;
    let mut body = self.check_prop(last)?;
    for Variable {user, decl, ty} in self.context.drain(depth..).rev() {
      pop_user_local(&mut self.user_locals, user).expect("stack underflow");
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
        (PrimProp::Pure, [e]) => Ok(Prop::Mm0(self.check_mm0_expr(e.clone())?)),
        _ => Err(ElabError::new_e(self.try_get_span(&head), "incorrect number of arguments")),
      }
      _ => self.check_pure_expr(e, Some(&Type::Bool)).map(|e| Prop::Pure(Rc::new(e)))
    }
  }

  fn push_user_local(&mut self, user: AtomId, decl: VarId) {
    self.user_locals.entry(user).or_default().push(decl)
  }

  /// Add a list of arguments to the context.
  fn add_args_to_context(&mut self, args: &[PreTuplePattern], ctx: ArgsContext) -> EResult<()> {
    self.context.reserve(args.len());
    for arg in args {
      match arg {
        PreTuplePattern::Name(_, _, _) => {}
        PreTuplePattern::Typed(b, _) if matches!(**b, PreTuplePattern::Name(_, _, _)) => {}
        _ => return Err(ElabError::new_e(try_get_span_from(&self.fsp, arg.fspan()),
          "tuple patterns in argument position are not implemented")),
      }
      let user = arg.name();
      let decl = self.get_fresh_local();
      if user != AtomId::UNDER { self.push_user_local(user, decl) }
      let is_ty = ctx.tyvar_allowed() && arg.ty().as_atom().map_or(false, |a| a == AtomId::UNDER ||
        matches!(self.mmc.keywords.get(&a), Some(Keyword::Star)));
      let ty = if is_ty {GType::Star} else {
        let ty = arg.ty();
        if !ctx.hyp_allowed() || self.probably_a_type(&ty) {
          let ty = if ty.as_atom().map_or(false, |a| a == AtomId::UNDER) {
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

  fn tuple_pattern_type(&mut self, pat: &mut PreTuplePattern) -> EResult<Option<Type>> {
    Ok(if let PreTuplePattern::Typed(pat2, ty) = pat {
      let ty = self.check_ty(&ty)?;
      *pat = PreTuplePattern::Ready(
        self.check_tuple_pattern(mem::take(&mut **pat2), InferType::ty(&ty))?);
      Some(ty)
    } else {
      None
    })
  }

  fn try_type_tuple_pattern(&mut self, pat: &mut PreTuplePattern) -> EResult<Option<Type>> {
    if let PreTuplePattern::Typed(pat2, ty) = pat {
      let ty = self.check_ty(ty)?;
      *pat = mem::take(&mut **pat2);
      self.type_tuple_pattern(pat, InferType::ty(&ty))?;
      Ok(Some(ty))
    } else {
      Ok(None)
    }
  }

  fn type_tuple_pattern<'b>(&mut self, pat: &'b mut PreTuplePattern, tgt: InferType<'b>) -> EResult<&'b mut TuplePattern> {
    if let PreTuplePattern::Ready(pat) = pat { return Ok(pat) }
    *pat = PreTuplePattern::Ready(self.check_tuple_pattern(std::mem::take(pat), tgt)?);
    let_unchecked!(PreTuplePattern::Ready(pat) = pat, Ok(pat))
  }

  fn check_tuple_pattern(&mut self, pat: PreTuplePattern, tgt: InferType<'_>) -> EResult<TuplePattern> {
    let len = self.context.len();
    let pat = self.add_tuple_pattern_to_context(pat, tgt)?;
    for v in self.context.drain(len..).rev() {
      pop_user_local(&mut self.user_locals, v.user).expect("stack underflow")
    }
    Ok(pat)
  }

  #[allow(clippy::needless_pass_by_value)]
  fn add_tuple_pattern_to_context(&mut self, pat: PreTuplePattern, tgt: InferType<'_>) -> EResult<TuplePattern> {
    Ok(match pat {
      PreTuplePattern::Name(g, user, sp) => {
        let decl = self.get_fresh_local();
        if user != AtomId::UNDER { self.push_user_local(user, decl) }
        let ty = tgt.to_type();
        let copy = self.copy_type(&ty);
        self.context.push(Variable {decl, user, ty: GType::Ty(g, ty.clone(), copy)});
        TuplePattern::Name(g, decl, sp, Box::new(ty))
      }
      PreTuplePattern::Typed(pat, ty) => {
        let ty = self.check_ty(&ty)?;
        /* TODO: tgt = ty */
        self.add_tuple_pattern_to_context(*pat, InferType::ty(&ty))?
      }
      PreTuplePattern::Ready(pat) => pat,
      PreTuplePattern::Tuple(pats, sp) => match tgt {
        InferType::Unit | InferType::Ty(Type::Unit) => {
          if !pats.is_empty() {
            return Err(ElabError::new_e(
              try_get_span_from(&self.fsp, sp.as_ref()), "expected 0 subpatterns"))
          }
          TuplePattern::Unit
        }
        InferType::Ty(Type::Single(e, ty)) if pats.len() == 2 => {
          let mut pats = pats.into_vec();
          let mut it = pats.drain(..);
          if let (Some(p1), Some(p2), None) = (it.next(), it.next(), it.next()) {
            let x = self.add_tuple_pattern_to_context(p1, InferType::ty(ty))?;
            let p = Type::Prop(Box::new(Prop::Eq(Rc::new(x.to_expr()), e.clone())));
            let h = self.add_tuple_pattern_to_context(p2, InferType::Ty(&p))?;
            TuplePattern::Single(Box::new((x, h)))
          } else {
            return Err(ElabError::new_e(
              try_get_span_from(&self.fsp, sp.as_ref()), "expected 2 subpatterns"))
          }
        }
        _ => return Err(ElabError::new_e(
          try_get_span_from(&self.fsp, sp.as_ref()),
          format!("could not pattern match at type {}", self.elab.print(&tgt)))),
      }
    })
  }

  fn check_expr_list(&mut self, ts: &mut TypeState, args: &[LispVal],
      TypeTarget(tgt, pat): TypeTarget<'_>, sp: Span) -> Result<Expr, ElabError> {
    let mut vec = Vec::with_capacity(args.len());
    if let Some(PreTuplePattern::Tuple(pat, _)) = pat {
      if pat.len() != args.len() {
        return Err(ElabError::new_e(sp,
          format!("Can't pattern match, expected {} args, got {}", args.len(), pat.len())))
      }
    }
    let ty = match tgt {
      None => {
        if let Some(PreTuplePattern::Tuple(pat, _)) = pat {
          for (e, pat) in (&*args).iter().zip(&mut **pat) {
            let tgt = self.try_type_tuple_pattern(pat)?;
            vec.push(self.check_expr(ts, e.clone(), TypeTarget(tgt.as_ref(), Some(pat)))?)
          }
        } else {
          for e in args { vec.push(self.check_expr(ts, e.clone(), TypeTarget::NONE)?) }
        }
        Type::List(vec.iter().map(|e| self.infer_expr_type(e).to_type()).collect())
      }
      Some(Type::List(tys)) if tys.len() == args.len() => {
        if let Some(PreTuplePattern::Tuple(pat, _)) = pat {
          for ((e, ty), pat) in (&*args).iter().zip(&**tys).zip(&mut **pat) {
            self.type_tuple_pattern(pat, InferType::Ty(ty))?;
            vec.push(self.check_expr(ts, e.clone(), TypeTarget(Some(ty), Some(pat)))?)
          }
        } else {
          for (e, ty) in (&*args).iter().zip(&**tys) {
            vec.push(self.check_expr(ts, e.clone(), ty.into())?)
          }
        }
        Type::List(tys.clone())
      }
      Some(ty) => return Err(ElabError::new_e(sp, format!("type error, expected {:?}", ty))),
    };
    Ok(Expr::Tuple(vec.into(), Box::new(ty)))
  }

  fn check_expr(&mut self, ts: &mut TypeState, e: LispVal, tgt: TypeTarget<'_>) -> EResult<Expr> {
    let fsp = e.fspan();
    let fsp = fsp.as_ref();
    let sp = try_get_span_from(&self.fsp, fsp);
    Ok(match self.parser().parse_expr(e)? {
      PExpr::Nil => Expr::Pure(PureExpr::Unit),
      PExpr::Var(sp, user) => {
        let var = *self.user_locals.get(&user).and_then(|v| v.last()).ok_or_else(||
          ElabError::new_e(try_get_span_from(&self.fsp, Some(&sp)),
          format!("unknown variable '{}'", self.elab.print(&user))))?;
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
      PExpr::Let {mut lhs, rhs, with} => {
        let ty = self.tuple_pattern_type(&mut lhs)?;
        let rhs = self.check_expr(ts, rhs, TypeTarget(ty.as_ref(), Some(&mut lhs)))?;
        let ty = self.infer_expr_type(&rhs).to_type();
        let lhs = self.with_rename(&with, sp,
          |tc| tc.add_tuple_pattern_to_context(lhs, InferType::ty(&ty)))?;
        Expr::Let {lhs, rhs: Box::new(rhs)}
      }
      PExpr::Assign {lhs, rhs, with} => {
        self.todo(fsp, "check_expr Assign", (lhs, rhs, with))?
      },
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
          Some(Entity::Const(GlobalTc::Unchecked)) => err!("forward referencing constants is not allowed"),
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
              self.todo(fsp.as_ref(), "Index", args)?
              // enum AutoDeref { Own, Ref, Mut }
              // let (arr, idx, pf) = match args {
              //   [arr, idx] => (arr, idx, None),
              //   [arr, idx, pf] => (arr, idx, Some(pf)),
              //   _ => err!("expected 2 or 3 arguments"),
              // };
              // let mut arr = self.check_expr(ts, arr.clone(), TypeTarget::NONE)?;
              // let idx = Rc::new(self.check_pure_expr(idx, Some(&Type::UInt(Size::Inf)))?);
              // let mut aty = self.infer_expr_type(&arr);
              // let mut derefs = vec![];
              // let len = loop {
              //   match aty {
              //     InferType::Own(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Own); }
              //     InferType::Ref(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Ref); }
              //     InferType::RefMut(ty) => { aty = InferType::ty(ty); derefs.push(AutoDeref::Mut); }
              //     InferType::Ty(Type::Array(_, len)) => break len.clone(),
              //     _ => err!("type error, expcted an array"),
              //   }
              // };
              // for s in derefs {
              //   arr = match s {
              //     AutoDeref::Own => Expr::DerefOwn(Box::new(arr)),
              //     AutoDeref::Ref => Expr::Deref(Box::new(arr)),
              //     AutoDeref::Mut => Expr::DerefMut(Box::new(arr)),
              //   }
              // }
              // let prop = PureExpr::Binop(Binop::Lt, idx.clone(), len);
              // let pf = match pf {
              //   Some(pf) => self.check_expr(ts, pf.clone(),
              //     (&Type::Prop(Box::new(Prop::Pure(Rc::new(prop))))).into())?,
              //   None => Expr::Assert(Rc::new(prop)),
              // };
              // Expr::Index(Box::new(arr), idx, Box::new(pf))
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
      PExpr::While { hyp, cond, var, body } => self.todo(fsp, "check_expr While", ())?,
      PExpr::Hole(_) => self.todo(fsp, "check_expr Hole", ())?,
    })
  }

  fn check_stmts(&mut self, ts: &mut TypeState, u: Uncons, mut tgt: TypeTarget<'_>) -> EResult<Box<[Expr]>> {
    Ok(match u.len().checked_sub(1) {
      // None if !tgt.map_or(true, |tgt| matches!(tgt, TypeTarget::Unit)) =>
      // return Err(ElabError::new_e(self.try_get_span(&u.as_lisp()), "expected a value, got empty block")),
      None => Box::new([]),
      Some(n) => u.enumerate()
        .map(|(i, e)| self.check_expr(ts, e, if i == n {tgt.reborrow()} else {TypeTarget::NONE}))
        .collect::<EResult<Vec<_>>>()?.into()
    })
  }

  /// Performs type checking of the input AST.
  pub fn typeck(&mut self, item: &Ast) -> EResult<()> {
    self.next_var = Default::default();
    self.user_locals.clear();
    self.context.clear();
    self.mut_globals.clear();
    match item {
      Ast::Proc(proc, body) => match proc.kind {
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
            Some(Entity::Op(Operator::Proc(_, tc @ ProcTc::Unchecked))) =>
              *tc = ProcTc::Intrinsic(intrinsic),
            _ => unreachable!()
          }
        }
        ProcKind::Proc => {
          // let Proc {kind, name,
          //   ref span, ref args, ref rets, ref variant,
          //   body: Body {ref muts, ref stmts}} = **proc;
          self.add_args_to_context(&proc.args.1, ArgsContext::ProcArgs)?;
          self.add_args_to_context(&proc.rets.1, ArgsContext::ProcArgs)?;
          let rets = self.context.drain(proc.args.1.len()..).collect::<Vec<_>>();
          for v in rets.iter().rev() {
            pop_user_local(&mut self.user_locals, v.user).expect("stack underflow")
          }
          if let Some((e, _)) = &proc.variant {
            return Err(ElabError::new_e(self.try_get_span(e), "proc variants are not implemented"))
          }
          // for &(a, ref fsp) in &*proc.muts {
          //   match self.mmc.names.get(&a) {
          //     Some(Entity::Global(GlobalTC::Unchecked)) =>
          //       return Err(ElabError::new_e(try_get_span_from(&self.fsp, fsp.as_ref()),
          //         "forward referencing globals is supported")),
          //     Some(&Entity::Global(GlobalTC::Checked(_, decl, _, _))) =>
          //       {self.mut_globals.insert(a, decl);}
          //     _ => return Err(ElabError::new_e(try_get_span_from(&self.fsp, fsp.as_ref()),
          //       "unknown global")),
          //   }
          // }
          let mut ts = self.new_type_state();
          let body = self.check_stmts(&mut ts, body.clone(), TypeTarget::NONE)?;
          println!("{:?}", body);
          // self.todo((rets, body))?;
          return Err(ElabError::new_e(
            try_get_span_from(&self.fsp, proc.span.as_ref()), "unimplemented: finish proc"))
        }
      }
      Ast::Global {full, lhs, rhs} => {
        return Err(ElabError::new_e(
          try_get_span_from(&self.fsp, full.as_ref()), "unimplemented: global"))
      },
      Ast::Const {full, lhs, rhs} => {
        match lhs {
          PreTuplePattern::Name(_, _, _) => {}
          PreTuplePattern::Typed(b, _) if matches!(**b, PreTuplePattern::Name(_, _, _)) => {}
          _ => return Err(ElabError::new_e(self.fsp.span,
            "tuple patterns in constants are not implemented")),
        }
        let ty = lhs.ty();
        let (e, ty2);
        if ty.as_atom().map_or(false, |a| a == AtomId::UNDER) {
          e = self.check_pure_expr(rhs, None)?;
          ty2 = self.infer_type(&e).to_type()
        } else {
          ty2 = self.check_ty(&ty)?;
          e = self.check_pure_expr(rhs, Some(&ty2))?;
        };
        let user = lhs.name();
        if user != AtomId::UNDER {
          let decl = self.get_fresh_decl(user);
          if let Entity::Const(ty @ GlobalTc::Unchecked) = self.mmc.names.get_mut(&user).unwrap() {
            *ty = GlobalTc::Checked(full.clone(), decl, Rc::new(ty2), Rc::new(Expr::Pure(e)))
          } else {unreachable!()}
        }
      }
      &Ast::Typedef {name, ref span, ref args, ref val} => {
        self.add_args_to_context(args, ArgsContext::TypeArgs)?;
        let val = self.check_ty(val)?;
        let dname = self.get_fresh_decl(name);
        if let Entity::Type(ty @ NType::Unchecked) = self.mmc.names.get_mut(&name).unwrap() {
          *ty = NType::Checked(span.clone(), dname, Rc::new(val))
        } else {unreachable!()}
      }
      &Ast::Struct {name, ref span, ref args, ref fields} => {
        self.add_args_to_context(args, ArgsContext::TypeArgs)?;
        self.add_args_to_context(fields, ArgsContext::StructFields)?;
        let fields = self.context.drain(args.len()..)
          .map(|v| (v.decl, match v.ty {
            GType::Star => unreachable!(),
            GType::Ty(g, ty, _) => Type::ghost_if(g, ty),
            GType::Prop(p) => Type::Prop(Box::new(p)),
          })).collect::<Vec<(VarId, Type)>>();
        let dname = self.get_fresh_decl(name);
        if let Entity::Type(ty @ NType::Unchecked) = self.mmc.names.get_mut(&name).unwrap() {
          *ty = NType::Checked(span.clone(), dname, Rc::new(Type::Struct(fields.into())))
        } else {unreachable!()}
      }
    }
    Ok(())
  }
}
