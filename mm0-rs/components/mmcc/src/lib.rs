// This module may become a plugin in the future, but for now let's avoid the complexity
// of dynamic loading.

//! Compiler tactic for the metamath C language.
//!
//! See [`mmc.md`] for information on the MMC format.
//!
//! [`mmc.md`]: https://github.com/digama0/mm0/blob/master/mm0-rs/mmc.md

// rust lints we want
#![warn(
  bare_trait_objects,
  elided_lifetimes_in_paths,
  missing_copy_implementations,
  missing_debug_implementations,
  future_incompatible,
  rust_2018_idioms,
  trivial_numeric_casts,
  variant_size_differences,
  unreachable_pub,
  unused,
  missing_docs
)]
// all the clippy
#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
// all the clippy::restriction lints we want
#![warn(
  clippy::float_arithmetic,
  clippy::get_unwrap,
  clippy::inline_asm_x86_att_syntax,
  clippy::integer_division,
  clippy::rc_buffer,
  clippy::rest_pat_in_fully_bound_structs,
  clippy::string_add,
  clippy::unwrap_used,
)]
// all the clippy lints we don't want
#![allow(
  clippy::cognitive_complexity,
  clippy::comparison_chain,
  clippy::default_trait_access,
  clippy::enum_glob_use,
  clippy::inline_always,
  clippy::manual_map,
  clippy::map_err_ignore,
  clippy::match_bool,
  clippy::missing_const_for_fn,
  clippy::missing_errors_doc,
  clippy::missing_panics_doc,
  clippy::module_name_repetitions,
  clippy::multiple_crate_versions,
  clippy::option_if_let_else,
  clippy::redundant_pub_crate,
  clippy::semicolon_if_nothing_returned,
  clippy::shadow_unrelated,
  clippy::too_many_lines,
  clippy::use_self
)]

#![allow(unused)]

macro_rules! mk_id {($($(#[$attr:meta])* $id:ident),* $(,)?) => {$(
  $(#[$attr])*
  #[derive(Clone, Copy, Default, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct $id(pub u32);
  #[cfg(feature = "memory")] mm0_deepsize::deep_size_0!($id);
  impl $id {
    /// Generate a fresh variable from a `&mut ID` counter.
    #[must_use] #[inline] pub fn fresh(&mut self) -> Self {
      let n = *self;
      self.0 += 1;
      n
    }
  }
  impl From<$id> for usize {
    fn from(id: $id) -> usize { crate::u32_as_usize(id.0) }
  }
  impl crate::Idx for $id {
    fn into_usize(self) -> usize { self.into() }
    fn from_usize(n: usize) -> Self { $id(std::convert::TryFrom::try_from(n).expect("overflow")) }
  }
)*}}

#[macro_use] extern crate mm0_util;
#[macro_use] extern crate bitflags;
#[macro_use] extern crate if_chain;
#[macro_use] extern crate lazy_static;

pub mod types;
mod predef;
pub mod build_ast;
mod union_find;
pub mod infer;
mod nameck;
mod build_mir;
mod mir_opt;
mod symbol;
mod build_vcode;
mod arch;

use std::collections::HashMap;
use {types::{entity::Entity, mir}, predef::PredefMap};
use bumpalo::Bump;
use infer::TypeError;
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;

pub use mm0_util::*;
pub use types::Idx;
pub use symbol::{Symbol, Interner, intern, init_dense_symbol_map};
pub use nameck::DeclarationError;
pub use ty::{CtxPrint, CtxDisplay, DisplayCtx};
use types::{IdxVec, VarId, LambdaId, ty, ast, hir};

/// Global configuration for the compiler.
pub trait Config {
  /// The error type for user methods.
  type Error;
}

impl Config for () {
  type Error = std::convert::Infallible;
}

/// The context for calls to [`Compiler::add`].
pub trait ItemContext<C: Config + ?Sized> {
  /// A type to print external lambda expressions embedded in the code.
  type Printer: PrintLambda + Sized;

  /// Return a new lambda printer.
  fn print(&mut self) -> Self::Printer;

  /// This function is called if errors are produced during typechecking.
  /// If the function returns false (the default),
  /// then the remainder of compilation will be skipped.
  fn emit_type_errors<'a>(&mut self, _ctx: &mut C,
    _errs: Vec<hir::Spanned<'a, TypeError<'a>>>,
    _print: &impl DisplayCtx<'a>,
  ) -> Result<bool, C::Error> { Ok(false) }
}

impl<C: Config> ItemContext<C> for () {
  type Printer = ();
  fn print(&mut self) {}
}

/// A trait for printing lambda expressions embedded in the code.
pub trait PrintLambda {
  /// Format a lambda expression.
  /// The default implementation just prints the ID of the lambda and the substitutions.
  fn fmt<'a, P: ty::DisplayCtx<'a>>(&self,
    ctx: &P, v: LambdaId, subst: &[ty::Expr<'a>], f: &mut std::fmt::Formatter<'_>
  ) -> std::fmt::Result {
    write!(f, "(L{}", v.0)?;
    for &e in subst { write!(f, " {}", CtxPrint(ctx, e))? }
    write!(f, ")")
  }
}

impl PrintLambda for () {}

/// The MMC compiler, which contains local state for the functions that have been
/// loaded and typechecked thus far.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "memory", derive(DeepSizeOf))]
pub struct Compiler<C> {
  /// The configuration of the compiler, which users can use to type-specialize
  /// the compiler itself.
  pub config: C,
  /// The map of atoms for defined entities (operations and types).
  pub names: HashMap<Symbol, Entity>,
  /// The compiled MIR representation of pre-monomorphization functions.
  mir: HashMap<Symbol, mir::Proc>,
  /// The accumulated global initializers, to be placed in the start routine.
  init: build_mir::Initializer,
  /// The map from [`Predef`](predef::Predef) to atoms, used for constructing proofs and referencing
  /// compiler lemmas.
  predef: PredefMap<Symbol>,
}

impl<C: Default> Default for Compiler<C> {
  fn default() -> Self { Compiler::new(C::default()) }
}

impl<C> Compiler<C> {
  /// Create a new [`Compiler`] object. This mutates the elaborator because
  /// it needs to allocate atoms for MMC keywords.
  pub fn new(config: C) -> Compiler<C> {
    symbol::Interner::with(|i| Compiler {
      names: Self::make_names(i),
      mir: Default::default(),
      init: Default::default(),
      predef: PredefMap::new(|_, s| i.intern(s)),
      config,
    })
  }
}

impl<C: Config> Compiler<C> {
  /// Add the given AST item to the compiler state,
  /// performing typehecking but not code generation.
  /// This should be called repeatedly to add all top level function items,
  /// finally calling [`finish`](Self::finish) to complete code generation.
  pub fn add(&mut self, item: &ast::Item, var_names: IdxVec<VarId, Symbol>,
    mut ic: impl ItemContext<C>
  ) -> Result<(), C::Error> {
    let Compiler {names, mir, init, ..} = self;
    let hir_alloc = Bump::new();
    let mut ctx = infer::InferCtx::new(&hir_alloc, names, var_names);
    let item = ctx.lower_item(item);
    if !ctx.errors.is_empty() {
      let errs = std::mem::take(&mut ctx.errors);
      let pr = ctx.print(&mut ic);
      if !ic.emit_type_errors(&mut self.config, errs, &pr)? { return Ok(()) }
    }
    if let Some(item) = item {
      if let Some(n) = build_mir::BuildMir::default().build_item(mir, init, item) {
        mir_opt::optimize(mir.get_mut(&n).expect("missing"), names);
      }
    }
    Ok(())
  }

  /// Once we are done adding functions, this function performs final linking to produce an executable.
  #[allow(clippy::unused_self)]
  pub fn finish(&mut self) -> Result<(), C::Error> {
    Ok(())
  }
}