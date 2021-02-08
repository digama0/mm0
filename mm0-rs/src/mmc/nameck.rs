//! MMC name resolution pass.
use std::sync::Arc;
use std::collections::{HashMap, hash_map::Entry};
use std::{rc::Rc, result::Result as StdResult};
use crate::elab::{
  Result, ElabError,
  local_context::try_get_span_from,
  environment::{AtomId, Environment}};
use crate::util::FileSpan;
use super::{Compiler, types::{self, Ast, Proc, ProcKind}, parser::TuplePattern};

impl Compiler {
  /// Construct the initial list of primitive entities.
  pub fn make_names(env: &mut Environment) -> HashMap<AtomId, Entity> {
    fn get(names: &mut HashMap<AtomId, Entity>, a: AtomId) -> &mut Prim {
      let e = names.entry(a).or_insert_with(|| Entity::Prim(Prim::default()));
      if let Entity::Prim(p) = e {p} else {unreachable!()}
    }
    let mut names = HashMap::new();
    PrimType::scan(|p, s| get(&mut names, env.get_atom(s.as_bytes())).ty = Some(p));
    PrimOp::scan(|p, s| get(&mut names, env.get_atom(s.as_bytes())).op = Some(p));
    PrimProp::scan(|p, s| get(&mut names, env.get_atom(s.as_bytes())).prop = Some(p));
    names
  }

  /// Performs name resolution on the given AST, updating the compiler state with
  /// unchecked entities. This function is also responsible for checking for duplicate
  /// procedure declarations.
  pub fn nameck(&mut self, fsp: &FileSpan, a: &Ast) -> Result<()> {
    match a {
      Ast::Proc(p, _) => {
        let sp = try_get_span_from(fsp, p.span.as_ref());
        match self.names.entry(p.name) {
          Entry::Vacant(e) => {e.insert(Entity::Op(Operator::Proc(p.clone(), ProcTc::Unchecked)));}
          Entry::Occupied(mut e) => match e.get() {
            Entity::Op(Operator::Proc(p1, _)) => {
              if !p.eq_decl(p1) {
                return Err(ElabError::with_info(sp, "declaration mismatch".into(),
                  p1.span.iter().map(|fsp| (fsp.clone(), "previously declared here".into())).collect()))
              }
              match (p1.kind, p.kind) {
                (_, ProcKind::ProcDecl) => {}
                (ProcKind::ProcDecl, _) => {
                  e.insert(Entity::Op(Operator::Proc(p.clone(), ProcTc::Unchecked)));
                }
                _ => return Err(ElabError::new_e(sp, "name already in use"))
              }
            }
            _ => return Err(ElabError::new_e(sp, "name already in use"))
          }
        }
      }
      Ast::Global {lhs, ..} => lhs.on_names(&mut |_, a, sp| -> Result<()> {
        if self.names.insert(a, Entity::Global(GlobalTc::Unchecked)).is_some() {
          return Err(ElabError::new_e(try_get_span_from(fsp, sp.as_ref()), "name already in use"))
        }
        Ok(())
      })?,
      Ast::Const {lhs, ..} => lhs.on_names(&mut |_, a, sp| -> Result<()> {
        if self.names.insert(a, Entity::Const(GlobalTc::Unchecked)).is_some() {
          return Err(ElabError::new_e(try_get_span_from(fsp, sp.as_ref()), "name already in use"))
        }
        Ok(())
      })?,
      &Ast::Typedef {name, ref span, ..} |
      &Ast::Struct {name, ref span, ..} =>
        if self.names.insert(name, Entity::Type(Type::Unchecked)).is_some() {
          return Err(ElabError::new_e(try_get_span_from(fsp, span.as_ref()), "name already in use"))
        },
    }
    Ok(())
  }
}