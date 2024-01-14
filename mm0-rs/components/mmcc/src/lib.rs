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
#![deny(unsafe_op_in_unsafe_fn)]
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
  clippy::undocumented_unsafe_blocks,
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
  clippy::single_match_else,
  clippy::too_many_lines,
  clippy::trait_duplication_in_bounds, // rust-clippy#8757, rust-clippy#8771
  clippy::type_repetition_in_bounds, // rust-clippy#8771
  clippy::uninhabited_references, // rust-clippy#11984
  clippy::use_self
)]

/// Construct an identifier type wrapping a `u32`.
#[macro_export] macro_rules! mk_id {
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
    #[allow(unreachable_pub)]
    pub struct $id(pub u32);
    #[cfg(feature = "memory")] mm0_deepsize::deep_size_0!($id);
    mk_id!(@ImplDebug $id $($($lit)*)?);
    impl From<$id> for usize {
      fn from(id: $id) -> usize { $crate::u32_as_usize(id.0) }
    }
    impl $crate::Idx for $id {
      fn into_usize(self) -> usize { self.into() }
      fn from_usize(n: usize) -> Self { $id(TryFrom::try_from(n).expect("overflow")) }
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

pub mod types;
pub mod build_ast;
mod union_find;
pub mod infer;
mod nameck;
mod build_mir;
mod mir_opt;
mod symbol;
mod build_vcode;
pub mod arch;
mod regalloc;
mod linker;
mod codegen;
pub mod proof;

use std::collections::HashMap;
use types::{entity::Entity, mir, Spanned};
use bumpalo::Bump;
use infer::TypeError;
#[cfg(feature = "memory")] use mm0_deepsize_derive::DeepSizeOf;

pub use mm0_util::*;
pub use types::Idx;
pub use symbol::{Symbol, Interner, intern, init_dense_symbol_map};
pub use nameck::DeclarationError;
pub use ty::{CtxPrint, CtxDisplay, DisplayCtx};
pub use build_vcode::LowerErr;
pub use linker::{LinkedCode, LinkerErr, TEXT_START};
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
  fn emit_type_errors<'a>(&mut self, _ctx: &mut C,
    _errs: Vec<hir::Spanned<'a, TypeError<'a>>>,
    _print: &impl DisplayCtx<'a>,
  ) -> Result<(), C::Error> { Ok(()) }
}

impl<C: Config> ItemContext<C> for () {
  type Printer = ();
  fn print(&mut self) {}

  fn emit_type_errors<'a>(&mut self, _ctx: &mut C,
    errs: Vec<hir::Spanned<'a, TypeError<'a>>>,
    pr: &impl DisplayCtx<'a>,
  ) -> Result<(), C::Error> {
    use std::fmt::Write;
    let mut out = String::new();
    for err in errs {
      writeln!(out, "at {:?}: {}", err.span, CtxPrint(pr, &err.k)).expect("impossible");
    }
    panic!("type errors:\n{out}")
  }
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
  /// If the main function has been provided, this is a pointer to it.
  main: Option<Symbol>,
  /// If true, some items have not been generated correctly, so compilation cannot proceed.
  has_type_errors: bool,
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
      main: None,
      has_type_errors: false,
      config,
    })
  }
}

impl<C: Config> Compiler<C> {
  /// Add the given AST item to the compiler state,
  /// performing typehecking but not code generation.
  /// This should be called repeatedly to add all top level function items,
  /// finally calling [`finish`](Self::finish) to complete code generation.
  pub fn add(&mut self, item: &ast::Item, var_names: IdxVec<VarId, Spanned<Symbol>>,
    mut ic: impl ItemContext<C>
  ) -> Result<(), C::Error> {
    let Compiler {names, mir, init, main, has_type_errors, ..} = self;
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
    let item_errors = ctx.has_ast_errors || !ctx.errors.is_empty();
    *has_type_errors |= item_errors;
    if !ctx.errors.is_empty() {
      let errs = std::mem::take(&mut ctx.errors);
      let pr = ctx.print(&mut ic);
      ic.emit_type_errors(&mut self.config, errs, &pr)?;
    }
    if let Some(item) = item.filter(|_| !item_errors) {
      if let Some(n) = build_mir::BuildMir::new(Some(&mut ctx.mvars)).build_item(mir, init, item) {
        mir.get_mut(&n).expect("missing").optimize(names);
      }
    }
    Ok(())
  }

  /// If true, then `finish` will panic.
  pub fn has_type_errors(&self) -> bool { self.has_type_errors }

  /// Reset the compiler to the initial state.
  pub fn clear(&mut self) {
    self.names = symbol::Interner::with(Self::make_names);
    self.mir = Default::default();
    self.init = Default::default();
    self.main = None;
    self.has_type_errors = false;
  }

  /// Once we are done adding functions, this function performs final linking to produce an
  /// executable.
  /// The compiler is reset to the initial state after this operation, except for the user state
  /// [`Compiler::config`], so it can be used to compile another program but the library functions
  /// must first be loaded in again.
  pub fn finish(&mut self) -> Result<Box<LinkedCode>, LinkerErr> {
    let names = std::mem::replace(&mut self.names, symbol::Interner::with(Self::make_names));
    let mir = std::mem::take(&mut self.mir);
    assert!(!self.has_type_errors);
    // eprintln!("{:#?}", mir);
    let (mut init, globals) = std::mem::take(&mut self.init).finish(&mir, self.main.take());
    init.optimize(&[]);
    let allocs = init.storage(&names);
    LinkedCode::link(&names, mir, init, &allocs, &globals)
  }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::wildcard_imports)]
mod test {
  use std::fs::File;
  use std::io::{self, Write};
  use crate::types::ast::{
    ArgAttr, ArgKind, Block, ExprKind, ItemKind, StmtKind, TuplePatternKind, TypeKind};
  use crate::{Compiler, Idx, Symbol, intern};
  use crate::types::{Binop, Size, Spanned, VarId, hir::ProcKind, entity::IntrinsicProc};

  fn assert_eq_hex(test_name: &str, data: &[u8], hex: &str) {
    let mut result = String::from(hex);
    result.retain(|c| c.is_ascii_hexdigit());
    if hex::encode(data) != result {
      fn write_file(name: &str, data: &[u8]) -> io::Result<()> {
        File::create(name)?.write_all(data)
      }
      drop(write_file(&format!("{test_name}.expected"), &hex::decode(result).unwrap()));
      drop(write_file(&format!("{test_name}.produced"), data));
      let mut msg = String::new();
      for (i, &c) in data.iter().enumerate() {
        use std::fmt::Write;
        if i % 16 == 0 { msg += "\\\n     " }
        if i % 2 == 0 { msg += " " }
        write!(msg, "{c:02x}").unwrap();
      }
      if data.len() % 16 == 0 { msg += "\\\n    " }
      panic!("Binary comparison failed.\n\
        Outputs produced at {test_name}.expected and {test_name}.produced\n\
        To bless new test:\n\n    \
        assert_eq_hex(\"{test_name}\", &out, \"{msg}\");\n\n");
    }
  }

  #[test] fn trivial_ir() {
    use crate::{LinkedCode, mir::*};
    let names = Default::default();
    let mut cfg = Cfg::default();
    let bl = cfg.new_block(CtxId::ROOT, 0);
    cfg[bl].terminate(Terminator::Exit(Constant::unit().into()));
    // println!("before opt:\n{:#?}", cfg);
    cfg.optimize(&[]);
    // println!("after opt:\n{:#?}", cfg);
    let allocs = cfg.storage(&names);
    // println!("allocs = {:#?}", allocs);
    let code = LinkedCode::link(&names, Default::default(), cfg, &allocs, &[]).unwrap();
    println!("code = {code:#?}");
    // code.write_elf(&mut std::fs::File::create("trivial").unwrap());
    let mut out = Vec::new();
    code.write_elf(&mut out).unwrap();
    assert_eq_hex("trivial_ir", &out, "\
      7f45 4c46 0201 0100 0000 0000 0000 0000\
      0200 3e00 0100 0000 7800 4000 0000 0000\
      4000 0000 0000 0000 0000 0000 0000 0000\
      0000 0000 4000 3800 0100 4000 0000 0000\
      0100 0000 0700 0000 7800 0000 0000 0000\
      7800 4000 0000 0000 0000 0000 0000 0000\
      1800 0000 0000 0000 1800 0000 0000 0000\
      0000 2000 0000 0000 b83c 0000 0033 ff0f\
      0500 0000 0000 0000 0000 0000 0000 0000\
    ");
  }

  #[test] fn two_plus_two_ir() {
    use std::{collections::HashMap, rc::Rc};
    use crate::{LinkedCode, types::IntTy, mir::*};

    let names = HashMap::new();
    let mut fresh_var = VarId::default();
    let u8 = IntTy::UInt(Size::S8);
    let mir = HashMap::default();
    let mut cfg = Cfg::default();

    let bl1 = cfg.new_block(CtxId::ROOT, 0);
    let [x1, x2] = [(); 2].map(|_| {
      let x = fresh_var.fresh();
      cfg[bl1].stmts.push(Statement::Let(
        LetKind::Let(Spanned::dummy(x), None), true,
        Rc::new(TyKind::Int(u8)),
        Constant::int(u8, 2.into()).into()));
      x
    });
    let sum = fresh_var.fresh();
    cfg[bl1].stmts.push(Statement::Let(
      LetKind::Let(Spanned::dummy(sum), None), true,
      Rc::new(TyKind::Int(u8)),
      RValue::Binop(Binop::Add(u8),
        Operand::Copy(Place::local(x1)),
        Operand::Copy(Place::local(x2)))));
    let eq = fresh_var.fresh();
    cfg[bl1].stmts.push(Statement::Let(
      LetKind::Let(Spanned::dummy(eq), None), true,
      Rc::new(TyKind::Bool),
      RValue::Binop(Binop::Eq(u8),
        Operand::Copy(Place::local(sum)),
        Constant::int(u8, 4.into()).into())));
    let y = fresh_var.fresh();
    let bl2ctx = cfg.ctxs.extend(CtxId::ROOT, Spanned::dummy(y), true, (None,
      Rc::new(TyKind::Pure(Rc::new(ExprKind::Var(eq))))));
    let bl2 = cfg.new_block(bl2ctx, 0);
    cfg[bl1].terminate(Terminator::Assert(eq.into(), y, bl2));
    cfg[bl2].terminate(Terminator::Exit(Constant::unit().into()));

    // println!("before opt:\n{:#?}", cfg);
    cfg.optimize(&[]);
    // println!("after opt:\n{:#?}", cfg);
    let allocs = cfg.storage(&names);
    // println!("allocs = {:#?}", allocs);
    let code = LinkedCode::link(&names, mir, cfg, &allocs, &[]).unwrap();
    // println!("code = {:#?}", code);
    // code.write_elf(&mut File::create("two_plus_two_ir").unwrap());
    let mut out = Vec::new();
    code.write_elf(&mut out).unwrap();
    assert_eq_hex("two_plus_two_ir", &out, "\
      7f45 4c46 0201 0100 0000 0000 0000 0000\
      0200 3e00 0100 0000 7800 4000 0000 0000\
      4000 0000 0000 0000 0000 0000 0000 0000\
      0000 0000 4000 3800 0100 4000 0000 0000\
      0100 0000 0700 0000 7800 0000 0000 0000\
      7800 4000 0000 0000 0000 0000 0000 0000\
      2800 0000 0000 0000 2800 0000 0000 0000\
      0000 2000 0000 0000 ba02 0000 00b9 0200\
      0000 02d1 80fa 0441 0f94 c041 80f8 0075\
      020f 0bb8 3c00 0000 33ff 0f05 0000 0000\
    ");
  }

  #[test] fn two_plus_two() {
    let mut compiler = Compiler::new(());
    let main = Spanned::dummy(ItemKind::Proc {
      intrinsic: None,
      kind: ProcKind::Main,
      name: Spanned::dummy(intern("main")),
      tyargs: 0,
      args: Box::new([]),
      outs: Box::new([]),
      rets: Box::new([]),
      variant: None,
      body: Block {
        stmts: vec![Spanned::dummy(StmtKind::Expr(ExprKind::Assert(
          Box::new(Spanned::dummy(ExprKind::Binop(Binop::Eq,
            Box::new(Spanned::dummy(ExprKind::Typed(
              Box::new(Spanned::dummy(ExprKind::Binop(Binop::Add,
                Box::new(Spanned::dummy(ExprKind::Int(2.into()))),
                Box::new(Spanned::dummy(ExprKind::Int(2.into())))
              ))),
              Box::new(Spanned::dummy(TypeKind::UInt(Size::S8)))
            ))),
            Box::new(Spanned::dummy(ExprKind::Int(4.into())))
          )))
        )))],
        expr: None,
      },
    });
    compiler.add(&main, Default::default(), ()).unwrap();
    let code = compiler.finish().unwrap();
    // println!("code = {:#?}", code);
    // code.write_elf(&mut File::create("two_plus_two").unwrap());
    let mut out = Vec::new();
    code.write_elf(&mut out).unwrap();
    assert_eq_hex("two_plus_two", &out, "\
      7f45 4c46 0201 0100 0000 0000 0000 0000\
      0200 3e00 0100 0000 7800 4000 0000 0000\
      4000 0000 0000 0000 0000 0000 0000 0000\
      0000 0000 4000 3800 0100 4000 0000 0000\
      0100 0000 0700 0000 7800 0000 0000 0000\
      7800 4000 0000 0000 0000 0000 0000 0000\
      3800 0000 0000 0000 3800 0000 0000 0000\
      0000 2000 0000 0000 e813 0000 00b8 3c00\
      0000 33ff 0f05 0000 0000 0000 0000 0000\
      ba02 0000 00b9 0200 0000 02d1 b904 0000\
      003a d10f 94c0 3c00 7502 0f0b c300 0000\
    ");
  }

  #[test] fn hello_world() {
    let mut compiler = Compiler::new(());
    let hello = b"hello world";
    let write = intern("write");

    // Add write intrinsic:
    // intrinsic proc write(fd: u32, count: u32, ghost mut buf: [u8; count], p: &sn buf) -> u32;
    let mut fresh = VarId::default();
    let fd = fresh.fresh();
    let count = fresh.fresh();
    let buf = fresh.fresh();
    compiler.add(
      &Spanned::dummy(ItemKind::Proc {
        intrinsic: Some(IntrinsicProc::Write),
        kind: ProcKind::Proc,
        name: Spanned::dummy(write),
        tyargs: 0,
        args: Box::new([
          // fd: u32
          Spanned::dummy((ArgAttr::empty(), ArgKind::Lam(TuplePatternKind::Typed(
            Box::new(Spanned::dummy(TuplePatternKind::Name(false, intern("fd"), fd))),
            Box::new(Spanned::dummy(TypeKind::UInt(Size::S32))),
          )))),
          // count: u32
          Spanned::dummy((ArgAttr::empty(), ArgKind::Lam(TuplePatternKind::Typed(
            Box::new(Spanned::dummy(TuplePatternKind::Name(false, intern("count"), count))),
            Box::new(Spanned::dummy(TypeKind::UInt(Size::S32))),
          )))),
          // ghost mut buf: ref [u8; count]
          Spanned::dummy((ArgAttr::GHOST | ArgAttr::MUT, ArgKind::Lam(TuplePatternKind::Typed(
              Box::new(Spanned::dummy(TuplePatternKind::Name(false, intern("buf"), buf))),
              Box::new(Spanned::dummy(TypeKind::Ref(None,
                Box::new(Spanned::dummy(TypeKind::Array(
                  Box::new(Spanned::dummy(TypeKind::UInt(Size::S8))),
                  Box::new(Spanned::dummy(ExprKind::Var(count))),
                ))),
              ))),
            )))),
          // p: &sn buf
          Spanned::dummy((ArgAttr::empty(), ArgKind::Lam(TuplePatternKind::Typed(
            Box::new(Spanned::dummy(TuplePatternKind::Name(false, intern("p"), fresh.fresh()))),
            Box::new(Spanned::dummy(TypeKind::RefSn(
              Box::new(Spanned::dummy(ExprKind::Var(buf)))
            ))),
          )))),
        ]),
        outs: Box::new([]),
        rets: Box::new([
          // -> u32
          Spanned::dummy(TuplePatternKind::Typed(
            Box::new(Spanned::dummy(TuplePatternKind::Name(false, Symbol::UNDER, fresh.fresh()))),
            Box::new(Spanned::dummy(TypeKind::UInt(Size::S32))),
          ))
        ]),
        variant: None,
        body: Block::default()
      }),
      Default::default(), ()).unwrap();

    // main() {
    //   let hello: [u8; 11] = ['h', 'e', 'l', 'l', 'o', ...];
    //   write(1, 11, ref hello, &hello);
    // }
    let mut fresh = VarId::default();
    let v = fresh.fresh();
    compiler.add(
      &Spanned::dummy(ItemKind::Proc {
        intrinsic: None,
        kind: ProcKind::Main,
        name: Spanned::dummy(intern("main")),
        tyargs: 0,
        args: Box::new([]),
        outs: Box::new([]),
        rets: Box::new([]),
        variant: None,
        body: Block {
          stmts: vec![
            Spanned::dummy(StmtKind::Let {
              lhs: Spanned::dummy(TuplePatternKind::Typed(
                Box::new(Spanned::dummy(TuplePatternKind::Name(false, intern("hello"), v))),
                Box::new(Spanned::dummy(TypeKind::Array(
                  Box::new(Spanned::dummy(TypeKind::UInt(Size::S8))),
                  Box::new(Spanned::dummy(ExprKind::Int(hello.len().into()))),
                ))),
              )),
              rhs: Spanned::dummy(ExprKind::List(hello.iter().map(|&c| {
                Spanned::dummy(ExprKind::Int(c.into()))
              }).collect()))
            }),
            Spanned::dummy(StmtKind::Expr(ExprKind::Call {
              f: Spanned::dummy(write),
              tys: vec![],
              args: vec![
                Spanned::dummy(ExprKind::Int(1.into())),
                Spanned::dummy(ExprKind::Int(hello.len().into())),
                Spanned::dummy(ExprKind::Var(v)),
                Spanned::dummy(ExprKind::Borrow(Box::new(Spanned::dummy(ExprKind::Var(v))))),
              ],
              variant: None,
            }))
          ],
          expr: None,
        },
      }),
      Default::default(), ()).unwrap();
    let code = compiler.finish().unwrap();
    // println!("code = {:#?}", code);
    // code.write_elf(&mut File::create("hello_world").unwrap());
    let mut out = Vec::new();
    code.write_elf(&mut out).unwrap();
    assert_eq_hex("hello_world", &out, "\
      7f45 4c46 0201 0100 0000 0000 0000 0000\
      0200 3e00 0100 0000 7800 4000 0000 0000\
      4000 0000 0000 0000 0000 0000 0000 0000\
      0000 0000 4000 3800 0100 4000 0000 0000\
      0100 0000 0700 0000 7800 0000 0000 0000\
      7800 4000 0000 0000 0000 0000 0000 0000\
      b800 0000 0000 0000 b800 0000 0000 0000\
      0000 2000 0000 0000 e813 0000 00b8 3c00\
      0000 33ff 0f05 0000 0000 0000 0000 0000\
      4883 ec0b b868 0000 0040 8804 24ba 6500\
      0000 4088 5424 0141 b96c 0000 0044 884c\
      2402 bf6c 0000 0040 887c 2403 b96f 0000\
      0040 884c 2404 41ba 2000 0000 4488 5424\
      05be 7700 0000 4088 7424 0641 b86f 0000\
      0044 8844 2407 b872 0000 0040 8844 2408\
      ba6c 0000 0040 8854 2409 41b9 6400 0000\
      4488 4c24 0a48 8d34 24b8 0100 0000 48c7\
      c701 0000 0048 c7c2 0b00 0000 0f05 4883\
      c40b c300 0000 0000 0000 0000 0000 0000\
    ");
  }
}
