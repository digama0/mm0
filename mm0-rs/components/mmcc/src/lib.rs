// This module may become a plugin in the future, but for now let's avoid the complexity
// of dynamic loading.

//! Compiler tactic for the metamath C language.
//!
//! See [`mmc.md`] for information on the MMC language.
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

macro_rules! mk_id {
  (@ImplDebug $id:ident) => {
    impl std::fmt::Debug for $id {
      fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({})", stringify!($id), self.0)
      }
    }
  };
  (@ImplDebug $id:ident !Debug) => {};
  (@ImplDebug $id:ident Debug($l:expr)) => {
    impl std::fmt::Debug for $id {
      fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", $l, self.0)
      }
    }
  };
  ($($(#[$attr:meta])* $id:ident $(($($lit:tt)*))?),* $(,)?) => {$(
    $(#[$attr])*
    #[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct $id(pub u32);
    #[cfg(feature = "memory")] mm0_deepsize::deep_size_0!($id);
    mk_id!(@ImplDebug $id $($($lit)*)?);
    impl From<$id> for usize {
      fn from(id: $id) -> usize { crate::u32_as_usize(id.0) }
    }
    impl crate::Idx for $id {
      fn into_usize(self) -> usize { self.into() }
      fn from_usize(n: usize) -> Self { $id(std::convert::TryFrom::try_from(n).expect("overflow")) }
      fn fresh(&mut self) -> Self {
        let n = *self;
        self.0 += 1;
        n
      }
    }
  )*}
}

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
mod regalloc;
mod linker;
mod codegen;

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
pub use linker::LinkedCode;
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
  /// If the main function has been provided, this is a pointer to it.
  main: Option<Symbol>,
}

impl<C: Default> Default for Compiler<C> {
  fn default() -> Self { Compiler::new(C::default()) }
}

impl<C> Compiler<C> {
  /// Create a new [`Compiler`] object.
  pub fn new(config: C) -> Compiler<C> {
    symbol::Interner::with(|i| Compiler {
      names: Self::make_names(i),
      mir: Default::default(),
      init: Default::default(),
      predef: PredefMap::new(|_, s| i.intern(s)),
      main: None,
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
    let Compiler {names, mir, init, main, ..} = self;
    let hir_alloc = Bump::new();
    let mut ctx = infer::InferCtx::new(&hir_alloc, names, var_names);
    if let ast::ItemKind::Proc {kind: ast::ProcKind::Main, ref name, ..} = item.k {
      if main.is_some() {
        ctx.errors.push(hir::Spanned {span: &name.span, k: TypeError::DoubleMain});
      } else {
        *main = Some(name.k)
      }
    }
    let item = ctx.lower_item(item);
    if !ctx.errors.is_empty() {
      let errs = std::mem::take(&mut ctx.errors);
      let pr = ctx.print(&mut ic);
      if !ic.emit_type_errors(&mut self.config, errs, &pr)? { return Ok(()) }
    }
    if let Some(item) = item {
      if let Some(n) = build_mir::BuildMir::default().build_item(mir, init, item) {
        mir.get_mut(&n).expect("missing").optimize(names);
      }
    }
    Ok(())
  }

  /// Once we are done adding functions, this function performs final linking to produce an
  /// executable.
  /// The compiler is reset to the initial state after this operation, except for the user state
  /// [`Compiler::config`], so it can be used to compile another program but the library functions
  /// must first be loaded in again.
  pub fn finish(&mut self) -> LinkedCode {
    let names = std::mem::replace(&mut self.names, symbol::Interner::with(Self::make_names));
    let mir = std::mem::take(&mut self.mir);
    let (mut init, globals) = std::mem::take(&mut self.init).finish(&mir, self.main.take());
    init.optimize(&[]);
    let allocs = init.storage(&names);
    LinkedCode::link(&names, &mir, &init, &allocs, &globals)
  }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::wildcard_imports)]
mod test {
  use std::fs::File;
use std::{collections::HashMap, rc::Rc};
  use crate::LinkedCode;
use crate::{Idx, linker::ConstData, regalloc::regalloc_vcode};
  use crate::types::{IdxVec, IntTy, Size, Spanned, hir::ProcKind, mir::*};

  fn assert_eq_hex(data: &[u8], hex: &str) {
    let mut result = String::from(hex);
    result.retain(|c| c.is_ascii_hexdigit());
    assert_eq!(hex::encode(data), result);
  }

  #[test] fn two_plus_two() {
    let names = HashMap::new();
    let consts = ConstData::default();
    let mut fresh_var = VarId::default();
    let u8 = IntTy::UInt(Size::S8);
    let u8ty = Rc::new(TyKind::Int(u8));
    let mir = HashMap::default();
    let mut cfg = Cfg::default();

    let bl1 = cfg.new_block(CtxId::ROOT);
    let [x1, x2] = [(); 2].map(|_| {
      let x = fresh_var.fresh();
      cfg[bl1].stmts.push(Statement::Let(
        LetKind::Let(x, true, None),
        Rc::new(TyKind::Int(u8)),
        Constant::int(u8, 2.into()).into()));
      x
    });
    let sum = fresh_var.fresh();
    cfg[bl1].stmts.push(Statement::Let(
      LetKind::Let(sum, true, None),
      Rc::new(TyKind::Int(u8)),
      RValue::Binop(Binop::Add(u8),
        Operand::Copy(Place::local(x1)),
        Operand::Copy(Place::local(x2)))));
    let eq = fresh_var.fresh();
    cfg[bl1].stmts.push(Statement::Let(
      LetKind::Let(eq, true, None),
      Rc::new(TyKind::Bool),
      RValue::Binop(Binop::Eq(u8),
        Operand::Copy(Place::local(sum)),
        Constant::int(u8, 4.into()).into())));
    let y = fresh_var.fresh();
    let bl2ctx = cfg.ctxs.extend(CtxId::ROOT, y, true, (None,
      Rc::new(TyKind::Pure(Rc::new(ExprKind::Var(eq))))));
    let bl2 = cfg.new_block(bl2ctx);
    cfg[bl1].terminate(Terminator::Assert(eq.into(), y, true, bl2));
    cfg[bl2].terminate(Terminator::Exit(Constant::unit().into()));

    // println!("before opt:\n{:#?}", cfg);
    cfg.optimize(&[]);
    // println!("after opt:\n{:#?}", cfg);
    let allocs = cfg.storage(&names);
    // println!("allocs = {:#?}", allocs);
    let code = LinkedCode::link(&names, &mir, &cfg, &allocs, &[]);
    // println!("code = {:#?}", code);
    // code.write_elf(&mut File::create("two_plus_two").unwrap());
    let mut out = Vec::new();
    code.write_elf(&mut out).unwrap();
    assert_eq_hex(&out, "\
      7f45 4c46 0201 0100 0000 0000 0000 0000\
      0200 3e00 0100 0000 7800 4000 0000 0000\
      4000 0000 0000 0000 0000 0000 0000 0000\
      0000 0000 4000 3800 0100 4000 0000 0000\
      0100 0000 0700 0000 7800 0000 0000 0000\
      7800 4000 0000 0000 0000 0000 0000 0000\
      2800 0000 0000 0000 2800 0000 0000 0000\
      0000 2000 0000 0000 ba02 0000 00be 0200\
      0000 4002 d680 fa04 400f 94c6 4080 fe00\
      7502 0f0b b83c 0000 0033 ff0f 0500 0000\
    ");
  }
}
