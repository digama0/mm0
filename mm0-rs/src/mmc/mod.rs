// This module may become a plugin in the future, but for now let's avoid the complexity
// of dynamic loading.

//! Compiler tactic for the metamath C language.
//!
//! See [`mmc.md`] for information on the MMC format.
//!
//! [`mmc.md`]: https://github.com/digama0/mm0/blob/master/mm0-rs/mmc.md

mod parser;
mod proof;

use std::{collections::HashMap, rc::Rc};
// use bumpalo::Bump;
use mmcc::{infer::TypeError, types::{IdxVec, LambdaId, hir, ty::CtxPrint}};
use parser::{ItemIter, Parser, Keyword};
use crate::{FileSpan, Span, AtomId, Remap, Remapper, Elaborator, ElabError,
  elab::Result, LispVal, EnvDebug, FormatEnv};

use self::parser::Mm0ExprNode;

struct PrintLambda<'a> {
  fe: FormatEnv<'a>,
  lambdas: &'a IdxVec<LambdaId, Mm0ExprNode>
}

impl PrintLambda<'_> {
  fn fmt_node<'a>(&self,
    node: &Mm0ExprNode,
    ctx: &impl mmcc::DisplayCtx<'a>,
    subst: &[mmcc::types::ty::Expr<'a>],
    f: &mut std::fmt::Formatter<'_>
  ) -> std::fmt::Result {
    use crate::elab::lisp::print::EnvDisplay;
    use mmcc::CtxDisplay;
    match node {
      Mm0ExprNode::Const(e) => e.fmt(self.fe, f),
      &Mm0ExprNode::Var(i) => subst[i as usize].fmt(ctx, f),
      Mm0ExprNode::Expr(t, es) => {
        write!(f, "({}", self.fe.to(t))?;
        for expr in es { write!(f, " ")?; self.fmt_node(expr, ctx, subst, f)? }
        write!(f, ")")
      }
    }
  }
}

impl mmcc::PrintLambda for PrintLambda<'_> {
  fn fmt<'a, P: mmcc::DisplayCtx<'a>>(&self,
    ctx: &P, v: LambdaId, subst: &[mmcc::types::ty::Expr<'a>], f: &mut std::fmt::Formatter<'_>
  ) -> std::fmt::Result {
    self.fmt_node(&self.lambdas[v], ctx, subst, f)
  }
}

#[derive(Default, DeepSizeOf)]
struct Config;
struct ItemContext<'a> {
  elab: &'a Elaborator,
  lambdas: &'a IdxVec<LambdaId, Mm0ExprNode>,
  errors: &'a mut Vec<ElabError>,
}

impl Clone for Config {
  /// Clone is used when copying a compiler struct from one file to another.
  /// In this case, we don't need to preserve the error list.
  fn clone(&self) -> Self { Self::default() }
}

impl mmcc::Config for Config {
  type Error = ElabError;
}

impl<'a> mmcc::ItemContext<Config> for ItemContext<'a> {
  type Printer = PrintLambda<'a>;
  fn print(&mut self) -> Self::Printer {
    PrintLambda { fe: self.elab.format_env(), lambdas: self.lambdas }
  }

  fn emit_type_errors<'b>(&mut self, _: &mut Config,
    errs: Vec<hir::Spanned<'b, TypeError<'b>>>,
    pr: &impl mmcc::DisplayCtx<'b>,
  ) -> Result<bool> {
    self.errors.extend(errs.into_iter().map(|err| match err.k {
      TypeError::ExpectedPure(sp) =>
        ElabError::with_info(err.span, format!("{}", CtxPrint(pr, &err.k)).into(),
          vec![(sp.clone(), "Needed for this operation".into())]),
      _ => ElabError::new_e(err.span, format!("{}", CtxPrint(pr, &err.k))),
    }));
    Ok(false)
  }
}

/// The MMC compiler, which contains local state for the functions that have been
/// loaded and typechecked thus far.
#[derive(Clone, DeepSizeOf, Serialize, Deserialize)]
pub struct Compiler {
  #[serde(skip)]
  inner: Rc<mmcc::Compiler<Config>>,
  /// The map from [`Predef`](predef::Predef) to atoms, used for constructing proofs and referencing
  /// compiler lemmas.
  predef: proof::Predefs,
}

impl std::fmt::Debug for Compiler {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "#<mmc-compiler>")
  }
}
impl EnvDebug for Compiler {
  fn env_dbg<'a>(&self, _: FormatEnv<'a>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    std::fmt::Debug::fmt(self, f)
  }
}

impl Remap for Compiler {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Compiler {
      inner: self.inner.clone(),
      predef: self.predef.remap(r),
    }
  }
}

impl Compiler {
  /// Construct a new compiler object.
  pub fn new(elab: &mut Elaborator) -> Self {
    Self {
      inner: Default::default(),
      predef: proof::Predefs::new(elab)
    }
  }

  /// Add the given MMC text (as a list of lisp literals) to the compiler state,
  /// performing typehecking but not code generation. This can be called multiple
  /// times to add multiple functions, but each lisp literal is already a list of
  /// top level items that are typechecked as a unit.
  pub fn add(&mut self,
    elab: &mut Elaborator, sp: Span, it: impl Iterator<Item=LispVal>
  ) -> Result<()> {
    let compiler = Rc::make_mut(&mut self.inner);
    let fsp = FileSpan {file: elab.path.clone(), span: sp};
    let mut cache = HashMap::default();
    for e in it {
      let mut it = ItemIter::new(e);
      loop {
        let mut p = Parser::new(elab, &mut cache, compiler);
        let item = match p.parse_next_item(&fsp, &mut it) {
          Err(e) => { elab.report(e); continue }
          Ok(Some(item)) => item,
          Ok(None) => break,
        };
        let (var_names, lambdas) = p.finish();
        let mut errors = vec![];
        compiler.add(&item, var_names, ItemContext {
          elab,
          lambdas: &lambdas,
          errors: &mut errors
        })?;
        for e in errors { elab.report(e) }
      }
    }
    Ok(())
  }

  /// Once we are done adding functions, this function performs final linking to produce an executable.
  pub fn finish(&mut self, elab: &mut Elaborator, sp: Span, name: AtomId) -> Result<()> {
    let compiler = Rc::make_mut(&mut self.inner);
    if compiler.has_type_errors() {
      return Err(ElabError::new_e(sp, "Compilation failed due to previous errors"))
    }
    proof::render_proof(&self.predef, elab, sp, name, &compiler.finish().proof())
  }

  /// Main entry point to the compiler. Does basic parsing and forwards to
  /// [`add`](Self::add) and [`finish`](Self::finish).
  pub fn call(&mut self, elab: &mut Elaborator, sp: Span, args: Vec<LispVal>) -> Result<LispVal> {
    let mut it = args.into_iter();
    let e = it.next().expect("expected 1 argument");
    match e.as_atom().and_then(|a| Keyword::from_str(elab.data[a].name.as_str())) {
      Some(Keyword::Add) => {
        self.add(elab, sp, it)?;
        Ok(LispVal::undef())
      }
      Some(Keyword::Finish) => {
        let name = it.next().and_then(|e| e.as_atom()).ok_or_else(||
          ElabError::new_e(sp, "mmc-finish: syntax error"))?;
        self.add(elab, sp, it)?;
        self.finish(elab, sp, name)?;
        Ok(LispVal::undef())
      }
      _ => Err(ElabError::new_e(sp,
        format!("mmc-compiler: unknown subcommand '{}'", elab.print(&e))))
    }
  }
}