use std::sync::Arc;
use std::collections::{HashMap, hash_map::Entry};
use std::result::Result as StdResult;
use crate::elab::{
  Result, ElabError,
  local_context::try_get_span_from,
  environment::{AtomID, Environment}};
use crate::util::FileSpan;
use super::{Compiler, parser::{AST, Proc, ProcKind, TuplePattern}};

macro_rules! make_prims {
  {$name:ident: $($x:ident: $e:expr,)*} => {
    #[derive(Debug, PartialEq, Eq, Copy, Clone)]
    pub enum $name { $($x),* }

    impl $name {
      fn scan(mut f: impl FnMut(&'static str, Self)) {
        $(f($e, $name::$x);)*
      }
    }
  }
}

make_prims! { PrimProc:
  And: "and",
  Assert: "assert",
  BAnd: "band",
  Bool: "bool",
  BNot: "bnot",
  BOr: "bor",
  BXor: "bxor",
  Index: "index",
  List: "list",
  Not: "not",
  Pun: "pun",
  Slice: "slice",
  TypeofBang: "typeof!",
  Typeof: "typeof",
}

make_prims! { PrimType:
  Array: "array",
  I8: "i8",
  I16: "i16",
  I32: "i32",
  I64: "i64",
  List: "list",
  Own: "own",
  Ref: "&",
  RefMut: "&mut",
  U8: "u8",
  U16: "u16",
  U32: "u32",
  U64: "u64",
  Union: "union",
}

#[derive(Copy, Clone, Debug)]
pub enum Type {
  Prim(PrimType),
  Unchecked,
}

#[derive(Copy, Clone, Debug)]
pub enum ProcTC { Unchecked }

#[derive(Clone, Debug)]
#[allow(variant_size_differences)]
pub enum Operator {
  Prim(PrimProc),
  Proc(Arc<Proc>, ProcTC),
}

#[derive(Copy, Clone, Debug)]
pub enum GlobalTC {
  Unchecked,
}

#[derive(Clone, Debug)]
#[allow(variant_size_differences)]
pub enum Entity {
  Type(Type),
  Op(Operator),
  Global(GlobalTC),
  Const(GlobalTC),
}

impl TuplePattern {
  fn on_names<E>(&self, f: &mut impl FnMut(AtomID, &Option<FileSpan>) -> StdResult<(), E>) -> StdResult<(), E> {
    match self {
      &TuplePattern::Name(n, ref sp) => if n != AtomID::UNDER { f(n, sp)? },
      TuplePattern::Typed(p, _) => p.on_names(f)?,
      TuplePattern::Tuple(ps) => for p in &**ps { p.on_names(f)? }
    }
    Ok(())
  }
}

impl Compiler {
  pub fn make_names(env: &mut Environment) -> HashMap<AtomID, Entity> {
    let mut names = HashMap::new();
    PrimType::scan(|s, p| {names.insert(env.get_atom(s), Entity::Type(Type::Prim(p)));});
    PrimProc::scan(|s, p| {names.insert(env.get_atom(s), Entity::Op(Operator::Prim(p)));});
    names
  }

  pub fn nameck(&mut self, fsp: &FileSpan, a: &AST) -> Result<()> {
    match a {
      AST::Proc(p) => {
        let sp = try_get_span_from(fsp, p.span.as_ref());
        match self.names.entry(p.name) {
          Entry::Vacant(e) => {e.insert(Entity::Op(Operator::Proc(p.clone(), ProcTC::Unchecked)));}
          Entry::Occupied(mut e) => match e.get() {
            Entity::Op(Operator::Proc(p1, _)) => {
              if !p.eq_decl(p1) {
                return Err(ElabError::with_info(sp, "declaration mismatch".into(),
                  p1.span.iter().map(|fsp| (fsp.clone(), "previously declared here".into())).collect()))
              }
              match (p1.kind, p.kind) {
                (_, ProcKind::ProcDecl) => {}
                (ProcKind::ProcDecl, _) => {
                  e.insert(Entity::Op(Operator::Proc(p.clone(), ProcTC::Unchecked)));
                }
                _ => return Err(ElabError::new_e(sp, "name already in use"))
              }
            }
            _ => return Err(ElabError::new_e(sp, "name already in use"))
          }
        }
      }
      AST::Global {lhs, ..} => lhs.on_names(&mut |a, sp| -> Result<()> {
        if self.names.insert(a, Entity::Global(GlobalTC::Unchecked)).is_some() {
          return Err(ElabError::new_e(try_get_span_from(fsp, sp.as_ref()), "name already in use"))
        }
        Ok(())
      })?,
      AST::Const {lhs, ..} => lhs.on_names(&mut |a, sp| -> Result<()> {
        if self.names.insert(a, Entity::Const(GlobalTC::Unchecked)).is_some() {
          return Err(ElabError::new_e(try_get_span_from(fsp, sp.as_ref()), "name already in use"))
        }
        Ok(())
      })?,
      &AST::Typedef(name, ref sp, _, _) |
      &AST::Struct(name, ref sp, _, _) =>
        if self.names.insert(name, Entity::Type(Type::Unchecked)).is_some() {
          return Err(ElabError::new_e(try_get_span_from(fsp, sp.as_ref()), "name already in use"))
        },
    }
    Ok(())
  }
}