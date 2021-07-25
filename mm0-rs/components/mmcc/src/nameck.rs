//! MMC name resolution pass.
use crate::{FileSpan, Symbol, Compiler, types::{Spanned,
  entity::{Entity, ConstTc, GlobalTc, ProcTc, TypeTc}}};

/// The error type for functions that add a declaration to the environment.
#[derive(Debug)]
pub enum DeclarationError {
  /// The name is taken by a previous declaration. The second span is the other declaration.
  AlreadyDeclared(FileSpan, FileSpan),
  /// The name is reserved by a primitive operator.
  Keyword(FileSpan),
}

impl DeclarationError {
  /// The description of the error.
  pub fn desc(&self) -> &'static str {
    match self {
      DeclarationError::AlreadyDeclared(_, _) => "an item by this name has already been declared",
      DeclarationError::Keyword(_) => "this name is reserved for a primitive operator",
    }
  }
  /// The main span of the error.
  pub fn span(&self) -> &FileSpan {
    match self {
      DeclarationError::AlreadyDeclared(sp, _) |
      DeclarationError::Keyword(sp) => sp,
    }
  }
  /// The auxiliary span of the error.
  pub fn related(&self) -> Option<&FileSpan> {
    match self {
      DeclarationError::AlreadyDeclared(_, sp) => Some(sp),
      DeclarationError::Keyword(_) => None,
    }
  }
}

impl<C> Compiler<C> {
  fn add_item(&mut self, span: &FileSpan, name: Symbol, val: impl FnOnce() -> Entity
  ) -> Result<(), DeclarationError> {
    use std::collections::hash_map::Entry;
    match self.names.entry(name) {
      Entry::Vacant(e) => { e.insert(val()); Ok(()) }
      Entry::Occupied(e) => if let Some(sp2) = e.get().span() {
        Err(DeclarationError::AlreadyDeclared(span.clone(), sp2.clone()))
      } else {
        Err(DeclarationError::Keyword(span.clone()))
      }
    }
  }

  /// Forward declare a procedure, for use before elaborating the body of a recursive procedure
  /// or a group of mutually recursive procedures.
  pub fn forward_declare_proc(&mut self, span: &FileSpan, name: Symbol
  ) -> Result<(), DeclarationError> {
    self.add_item(span, name,
      || Entity::Proc(Spanned {span: span.clone(), k: ProcTc::ForwardDeclared}))
  }
  /// Forward declare a global variable.
  /// Recursive globals are not supported but this allows us to detect the recursive use.
  pub fn forward_declare_global(&mut self, span: &FileSpan, name: Symbol
  ) -> Result<(), DeclarationError> {
    self.add_item(span, name,
      || Entity::Global(Spanned {span: span.clone(), k: GlobalTc::ForwardDeclared}))
  }
  /// Forward declare a constant.
  /// Recursive constants are not supported but this allows us to detect the recursive use.
  pub fn forward_declare_const(&mut self, span: &FileSpan, name: Symbol
  ) -> Result<(), DeclarationError> {
    self.add_item(span, name,
      || Entity::Const(Spanned {span: span.clone(), k: ConstTc::ForwardDeclared}))
  }
  /// Forward declare a type.
  /// Recursive type declarations are not supported but this allows us to detect the recursive use.
  pub fn forward_declare_type(&mut self, span: &FileSpan, name: Symbol
  ) -> Result<(), DeclarationError> {
    self.add_item(span, name,
      || Entity::Type(Spanned {span: span.clone(), k: TypeTc::ForwardDeclared}))
  }
}