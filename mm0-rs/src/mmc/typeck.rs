//! MMC type checking pass.
use std::collections::{HashMap, HashSet};
use itertools::Itertools;
use crate::elab::{Result, Elaborator, Environment, ElabError,
  environment::{AtomID, AtomData},
  lisp::{Uncons, LispVal}, local_context::{try_get_span_from, try_get_span}};
use crate::util::{Span, FileSpan};
use super::{parser::{Proc, AST, Keyword}, Compiler,
  nameck::{Type as NType, PrimType, Entity}};

/// The type checker temporary.
#[derive(Debug)]
pub struct TypeCheck<'a> {
  /// A reference to the parent MMC compiler.
  pub mmc: &'a mut Compiler,
  /// A reference to the parent elaborator
  pub elab: &'a mut Elaborator,
  /// The base file span, for error reporting.
  pub fsp: FileSpan,
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

enum Size { S8, S16, S32, S64 }

enum Type {
    /// A type variable.
    Var(AtomID),
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
    Array(Box<Type>, LispVal),
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
}

impl<'a> TypeCheck<'a> {
  fn todo<T, U>(&mut self, _: U) -> Result<T> { Err(ElabError::new_e(self.fsp.span, "unimplemented")) }

  fn try_get_span(&self, e: &LispVal) -> Span {
    try_get_span(&self.fsp, &e)
  }

  fn get_fresh_decl(&mut self, base: AtomID) -> AtomID {
    let mut s = self.mmc.prefix.clone();
    s += &self.elab.data[base].name;
    get_fresh_name(&mut self.elab, s, |_, ad| ad.decl.is_some())
  }

  fn get_fresh_local<T>(&mut self, base: AtomID, locals: &HashMap<AtomID, T>) -> AtomID {
    let s = if base == AtomID::UNDER {String::new()} else {(*self.elab.data[base].name).into()};
    get_fresh_name(&mut self.elab, s, |a, ad| locals.contains_key(&a) || ad.decl.is_some())
  }

  fn parse_ty(&mut self, frees: &mut HashSet<AtomID>, e: &LispVal) -> Result<Type> {
    let mut u = Uncons::New(e.clone());
    let (head, args) = match u.next() {
      None if u.is_empty() => return Ok(Type::Unit),
      None => (u.into(), vec![]),
      Some(head) => (head, u.collect()),
    };
    macro_rules! parse_tys {($args:expr) => {{
      let mut tys = Vec::with_capacity($args.len());
      for e in $args { tys.push(self.parse_ty(frees, e)?) }
      tys.into()
    }}}
    let name = head.as_atom().ok_or_else(||
      ElabError::new_e(self.try_get_span(&head), "expected an atom"))?;
    match self.mmc.names.get(&name) {
      Some(&Entity::Type(NType::Prim(prim))) => match (prim, &*args) {
        (PrimType::Array, [ty, n]) => Ok(Type::Array(Box::new(self.parse_ty(frees, ty)?), n.clone())),
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
        (PrimType::Own, [ty]) => Ok(Type::Own(Box::new(self.parse_ty(frees, ty)?))),
        (PrimType::Ref, [ty]) => Ok(Type::Ref(Box::new(self.parse_ty(frees, ty)?))),
        (PrimType::RefMut, [ty]) => Ok(Type::RefMut(Box::new(self.parse_ty(frees, ty)?))),
        _ => Err(ElabError::new_e(self.try_get_span(&e), "unexpected number of arguments"))
      }
      Some(Entity::Type(NType::Unchecked)) => Err(
        ElabError::new_e(self.try_get_span(&head), "forward type references are not allowed")),
      Some(_) => Err(ElabError::new_e(self.try_get_span(&head), "expected a type")),
      None => { frees.insert(name); Ok(Type::Var(name)) }
    }
  }

  /// Performs type checking of the input AST.
  pub fn typeck(&mut self, ast: &[AST]) -> Result<()> {
    for item in ast {
      match item {
        AST::Proc(proc) => {
          let Proc {kind, name, ref span, ref args, ref rets, ref variant, ref body} = **proc;
          self.todo((kind, name, span, args, rets, variant, body))?
        }
        AST::Global { lhs, rhs } => self.todo((lhs, rhs))?,
        AST::Const { lhs, rhs } => self.todo((lhs, rhs))?,
        AST::Typedef { name, span, args, val } => {
          let mut localmap = HashMap::new();
          let mut locals = vec![];
          let mut frees = HashSet::new();
          for arg in &**args {
            assert!(!arg.ghost);
            let is_ty = arg.ty.as_atom().map_or(false, |a| a == AtomID::UNDER ||
              matches!(self.mmc.keywords.get(&a), Some(Keyword::Star)));
            let name = self.get_fresh_local(arg.name.as_ref().map_or(AtomID::UNDER, |&(a, _)| a), &localmap);
            localmap.insert(name, locals.len());
            let ty = if is_ty {None} else {Some(self.parse_ty(&mut frees, &arg.ty)?)};
            locals.push((name, ty));
          }
          let mut frees: Vec<_> = frees.iter().copied()
            .filter(|&a| !localmap.get(&a).map_or(false, |&i| matches!(locals[i], (b, None) if b == a)))
            .collect();
          if !frees.is_empty() {
            frees.sort_by_key(|&a| &*self.elab.data[a].name);
            return Err(ElabError::new_e(try_get_span_from(&self.fsp, span.as_ref()),
              format!("undeclared free variable(s) {{{}}}",
                frees.iter().map(|&a| &self.elab.data[a].name).format(", "))))
          }
          let dname = self.get_fresh_decl(*name);
          self.todo((dname, val))?
        },
        AST::Struct { name, span, args, fields } => self.todo((name, span, args, fields))?,
      }
    }
    Ok(())
  }
}
