//! The MMC parser, which takes lisp literals and maps them to MMC AST.
use std::mem;
use std::convert::TryInto;
use std::collections::{HashMap, hash_map::Entry};
use crate::{Elaborator, EnvDisplay};
use crate::{FileSpan, AtomId, Type as EType, elab::Result, Environment, ElabError,
  LispKind, LispVal, Uncons, FormatEnv, try_get_span};
use crate::elab::lisp::Syntax;
use mm0_util::{BoxError, TermId, u32_as_usize};
use mmcc::{Idx, init_dense_symbol_map};
use mmcc::build_ast::{BadBinding, BuildAst, BuildMatch, Incomplete, Pattern, PatternBuilder,
  RenameError, Renames, UnreachablePattern};
use mmcc::types::{Binop, IdxVec, LambdaId, ProofId, Unop, VarId};
use mmcc::{Symbol, intern, types::{FieldName, Mm0Expr, Size, Spanned, global}};
use mmcc::types::entity::{Entity, Prim, PrimType, PrimOp, TypeTy,
  IntrinsicProc, IntrinsicConst, IntrinsicGlobal, IntrinsicType};
#[allow(clippy::wildcard_imports)] use mmcc::types::ast::{self, *};

macro_rules! make_keywords {
  {$($(#[$attr:meta])* $x:ident: $e:expr,)*} => {
    make_keywords! {@IMPL $($(#[$attr])* $x concat!("The keyword `", $e, "`.\n"), $e,)*}
  };
  {@IMPL $($(#[$attr:meta])* $x:ident $doc0:expr, $e:expr,)*} => {
    /// The type of MMC keywords, which are atoms with a special role in the MMC parser.
    #[derive(Debug, EnvDebug, PartialEq, Eq, Copy, Clone)]
    pub enum Keyword { $(#[doc=$doc0] $(#[$attr])* $x),* }
    crate::deep_size_0!(Keyword);

    lazy_static! {
      static ref SYNTAX_MAP: Box<[Option<Keyword>]> = {
        let mut vec = vec![];
        Syntax::for_each(|_, name| vec.push(Keyword::from_str(name)));
        vec.into()
      };

      static ref INTERNED: [Symbol; [$(Keyword::$x),*].len()] = [$(intern($e)),*];
      static ref SYMBOL_MAP: Box<[Option<Keyword>]> =
        init_dense_symbol_map(&[$((intern($e), Keyword::$x)),*]);
    }

    impl Keyword {
      #[must_use] pub fn from_str(s: &str) -> Option<Self> {
        match s {
          $($e => Some(Self::$x),)*
          _ => None
        }
      }

      /// Get the MMC keyword corresponding to a lisp [`Syntax`].
      #[must_use] pub fn from_syntax(s: Syntax) -> Option<Self> {
        SYNTAX_MAP[s as usize]
      }

      /// Get the MMC keyword for a symbol.
      #[must_use] pub fn from_symbol(s: Symbol) -> Option<Self> {
        SYMBOL_MAP.get(s.into_usize()).map_or(None, |x| *x)
      }

      /// Get the symbol for an MMC keyword.
      #[must_use] pub fn as_symbol(self) -> Symbol { INTERNED[self as usize] }
    }

    impl Environment {
      /// Make the initial MMC keyword map in the given environment.
      #[allow(clippy::string_lit_as_bytes)]
      #[must_use] pub fn make_keywords() -> HashMap<Symbol, Keyword> {
        let mut atoms = HashMap::new();
        mmcc::Interner::with(|i| {
          $(if Syntax::from_str($e).is_none() {
            atoms.insert(i.intern($e), Keyword::$x);
          })*
        });
        atoms
      }
    }
  }
}

make_keywords! {
  Add: "+",
  Arrow: "=>",
  ArrowL: "<-",
  ArrowR: "->",
  Begin: "begin",
  Colon: ":",
  ColonEq: ":=",
  Const: "const",
  Else: "else",
  Entail: "entail",
  Func: "func",
  Finish: "finish",
  Ghost: "ghost",
  Global: "global",
  Implicit: "implicit",
  Intrinsic: "intrinsic",
  If: "if",
  Le: "<=",
  Lt: "<",
  Main: "main",
  Match: "match",
  Mut: "mut",
  Or: "or",
  Out: "out",
  Proc: "proc",
  Star: "*",
  Struct: "struct",
  Typedef: "typedef",
  Variant: "variant",
  While: "while",
  With: "with",
}

/// An embedded MM0 expression inside MMC. This representation is designed to make it easy
/// to produce substitutions of the free variables.
#[derive(Clone, Debug, DeepSizeOf)]
#[allow(variant_size_differences)]
pub(crate) enum Mm0ExprNode {
  /// A constant expression, containing no free variables,
  /// or a dummy variable that will not be substituted.
  Const(LispVal),
  /// A free variable. This is an index into the [`Mm0Expr::subst`] array.
  Var(u32),
  /// A term constructor, where at least one subexpression is non-constant
  /// (else we would use [`Const`](Self::Const)).
  Expr(TermId, Vec<Mm0ExprNode>),
}

struct Mm0ExprNodePrint<'a, T>(&'a [T], &'a Mm0ExprNode);
impl<'a, T: EnvDisplay> EnvDisplay for Mm0ExprNodePrint<'a, T> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self.1 {
      Mm0ExprNode::Const(e) => e.fmt(fe, f),
      &Mm0ExprNode::Var(i) => self.0[i as usize].fmt(fe, f),
      Mm0ExprNode::Expr(t, es) => {
        write!(f, "({}", fe.to(t))?;
        for e in es {
          write!(f, " {}", fe.to(&Self(self.0, e)))?
        }
        write!(f, ")")
      }
    }
  }
}

// impl<'a, C, E: CtxDisplay<C>> CtxDisplay<(&'a C, &'a [E])> for Mm0ExprNode {
//   fn fmt(&self, ctx: &(&'a C, &'a [E]), f: &mut std::fmt::Formatter<'_>
//   ) -> std::fmt::Result {
//     match self {
//       Mm0ExprNode::Const(e) => e.fmt(ctx.0.format_env(), f),
//       &Mm0ExprNode::Var(i) => ctx.1[i as usize].fmt(ctx.0, f),
//       Mm0ExprNode::Expr(t, es) => {
//         write!(f, "({}", ctx.0.format_env().to(t))?;
//         for expr in es { write!(f, " {}", CtxPrint(ctx, expr))? }
//         write!(f, ")")
//       }
//     }
//   }
// }

impl From<mmcc::DeclarationError> for ElabError {
  fn from(e: mmcc::DeclarationError) -> Self {
    ElabError::with_info(e.span(), e.desc().into(),
      e.related().into_iter().map(|sp| {
        (sp.clone(), "previously declared here".into())
      }).collect())
  }
}

/// The annotations that can appear on function arguments.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct PArgAttr {
  /// `(mut {x : T})` in function arguments means that `x` will be mutated
  /// as a side effect of the call. It should be paired with `out` in the function
  /// returns to indicate the resulting name; otherwise it will be prepended to
  /// the function returns as an `out` with the same name.
  pub(crate) mut_: bool,
  /// `(global {x : T})` in function arguments means that `x` is the name of a global
  /// variable that will be used in the function.
  pub(crate) global: bool,
  /// `(implicit {x : T})` in function arguments means that applications will
  /// use `_` for this argument instead of supplying a value.
  pub(crate) implicit: bool,
  /// `(out x {x' : T})` in function returns means that the variable `x`
  /// (which must be a `(mut x)` in the function arguments) is being mutated to
  /// `x'`; this acts as a binder declaring variable `x'`, and both `x` and `x'`
  /// can be used in subsequent types.
  pub(crate) out: Option<Symbol>,
}
crate::deep_size_0!(PArgAttr);

impl From<PArgAttr> for ArgAttr {
  fn from(PArgAttr {mut_, global, implicit, out: _}: PArgAttr) -> Self {
    let mut ret = ArgAttr::empty();
    if mut_ {ret |= ArgAttr::MUT}
    if global {ret |= ArgAttr::GLOBAL}
    if implicit {ret |= ArgAttr::IMPLICIT}
    ret
  }
}

/// A parsed label expression `((begin (lab x y)) body)`.
#[derive(Debug, DeepSizeOf)]
struct PLabel {
  /// The name of the label
  name: Symbol,
  /// The unparsed label header
  args: Uncons,
  /// The code that is executed when you jump to the label
  body: Uncons,
}

#[derive(Debug, DeepSizeOf)]
#[allow(variant_size_differences)]
enum ItemGroup {
  Item(Item),
  Global(Uncons),
  Const(Uncons),
  Intrinsic(Uncons),
}

#[derive(Debug, DeepSizeOf)]
enum ItemIterInner {
  New,
  Global(Uncons),
  Const(Uncons),
  Intrinsic(Box<ItemIter>),
}

/// An iterator over items. This is not a proper iterator in the sense of implementing `Iterator`,
/// but it can be used with the [`Parser::parse_next_item`] method to extract a stream of items.
#[derive(Debug, DeepSizeOf)]
pub(crate) struct ItemIter {
  group: ItemIterInner,
  u: Uncons,
  intrinsic: bool
}

impl ItemIter {
  /// Construct a new iterator from an `I: Iterator<Item=LispVal>`.
  #[must_use] pub(crate) fn new(e: LispVal) -> Self {
    Self { group: ItemIterInner::New, u: Uncons::New(e), intrinsic: false }
  }
}

/// The parser, which has no real state of its own but needs access to the
/// formatting environment for printing, and the keyword list.
#[derive(Debug)]
pub(crate) struct Parser<'a, C> {
  /// The formatting environment.
  fe: FormatEnv<'a>,
  symbols: &'a mut HashMap<AtomId, Symbol>,
  proofs: IdxVec<ProofId, LispVal>,
  lambdas: IdxVec<LambdaId, Mm0ExprNode>,
  ba: mmcc::build_ast::BuildAst,
  compiler: &'a mut mmcc::Compiler<C>,
}

/// Gets the span from a lisp expression, with the given fallback.
#[must_use] fn try_get_fspan(fsp: &FileSpan, e: &LispVal) -> FileSpan {
  FileSpan { file: fsp.file.clone(), span: try_get_span(fsp, e) }
}

/// Uses the span of the [`LispVal`] to construct a [`Spanned`]`<T>`.
#[must_use] fn spanned<T>(fsp: &FileSpan, e: &LispVal, k: T) -> Spanned<T> {
  Spanned {span: try_get_fspan(fsp, e), k}
}

fn get_intrinsic<T>(sp: &FileSpan, name: Symbol, f: impl FnOnce(Symbol) -> Option<T>) -> Result<T> {
  f(name).ok_or_else(|| ElabError::new_e(sp, "unknown intrinsic"))
}

enum DeclAssign {
  Let(LispVal, LispVal),
  Assign(LispVal, LispVal),
}

enum ExprOrStmt {
  Expr(Expr),
  Label(Spanned<PLabel>),
  Let(FileSpan, LispVal, LispVal, Renames),
}

impl From<(&FileSpan, RenameError)> for ElabError {
  fn from((span, e): (&FileSpan, RenameError)) -> ElabError {
    match e {
      RenameError::RenameUnder => ElabError::new_e(span, "can't rename variable '_'"),
      RenameError::MissingVar(v) => ElabError::new_e(span, format!("unknown variable '{}'", v)),
    }
  }
}

impl<'a, C> Parser<'a, C> {
  pub(crate) fn new(elab: &'a Elaborator,
    symbols: &'a mut HashMap<AtomId, Symbol>,
    compiler: &'a mut mmcc::Compiler<C>,
  ) -> Self {
    Self {
      fe: elab.format_env(), symbols,
      proofs: IdxVec::default(),
      lambdas: IdxVec::default(),
      ba: BuildAst::default(),
      compiler,
    }
  }

  pub(crate) fn finish(self) -> (IdxVec<VarId, Symbol>, IdxVec<LambdaId, Mm0ExprNode>) {
    (self.ba.var_names, self.lambdas)
  }

  /// Try to parse an atom or syntax object into a keyword.
  #[must_use] fn as_keyword(&mut self, e: &LispVal) -> Option<Keyword> {
    e.unwrapped(|e| match *e {
      LispKind::Atom(a) => Keyword::from_symbol(self.as_symbol(a)),
      LispKind::Syntax(s) => Keyword::from_syntax(s),
      _ => None
    })
  }

  /// Try to parse the head keyword of an expression `(KEYWORD args..)`,
  /// and return the pair `(KEYWORD, args)` on success.
  fn head_keyword(&mut self, e: &LispVal) -> Option<(Keyword, Uncons)> {
    let mut u = Uncons::from(e.clone());
    Some((self.as_keyword(&u.next()?)?, u))
  }

  fn with_ctx<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
    let sc = self.ba.scope();
    let res = f(self);
    sc.close(&mut self.ba);
    res
  }

  /// Same as `as_symbol`, but does not require mutable access (and does not update the cache).
  fn as_symbol_ref(&self, a: AtomId) -> Symbol {
    self.symbols.get(&a).map_or_else(|| intern(self.fe.env.data[a].name.as_str()), |a| *a)
  }

  fn as_symbol(&mut self, a: AtomId) -> Symbol {
    let env = self.fe.env;
    *self.symbols.entry(a).or_insert_with(|| intern(env.data[a].name.as_str()))
  }

  fn as_symbol_or<I: Into<BoxError>>(&mut self,
    base: &FileSpan, e: &LispVal, f: impl FnOnce() -> I) -> Result<Symbol> {
    let f = e.as_atom().ok_or_else(|| ElabError::new_e(&try_get_fspan(base, e), f()))?;
    Ok(self.as_symbol(f))
  }

  fn get_var(&mut self, sp: &FileSpan, name: Symbol) -> Result<VarId> {
    self.ba.get_var(name).ok_or_else(||
      ElabError::new_e(sp, format!("unknown variable '{}'", name)))
  }

  fn parse_variant(&mut self, base: &FileSpan, e: &LispVal) -> Result<Option<Box<Variant>>> {
    Ok(if let Some((Keyword::Variant, mut u)) = self.head_keyword(e) {
      let span = try_get_fspan(base, e);
      let e = u.next().ok_or_else(|| ElabError::new_e(&span, "variant: parse error"))?;
      let e = self.parse_expr(&span, e)?;
      let vt = match u.next() {
        None => VariantType::Down,
        Some(e) => match self.as_keyword(&e) {
          Some(Keyword::Lt) => {
            let e = u.next().ok_or_else(|| ElabError::new_e(&span, "variant: parse error"))?;
            VariantType::UpLt(self.parse_expr(&span, e)?)
          }
          Some(Keyword::Le) => {
            let e = u.next().ok_or_else(|| ElabError::new_e(&span, "variant: parse error"))?;
            VariantType::UpLe(self.parse_expr(&span, e)?)
          }
          _ => return Err(ElabError::new_e(try_get_span(&span, &e), "variant: expecting < or <=")),
        }
      };
      Some(Box::new(Spanned {span, k: (e, vt)}))
    } else {None})
  }

  fn push_args(&mut self, base: &FileSpan,
    allow_mut: bool, e: LispVal, args: &mut Vec<Arg>,
  ) -> Result<()> {
    self.push_args_core(base, Default::default(), e, &mut |span, attr, pat| {
      if attr.out.is_some() {
        return Err(ElabError::new_e(&span, "'out' not expected here"))
      }
      if !allow_mut && attr.mut_ {
        return Err(ElabError::new_e(&span, "'mut' not expected here"))
      }
      args.push(Spanned {span, k: (attr.into(), pat)});
      Ok(())
    })
  }

  fn push_args_core(&mut self, base: &FileSpan, mut attr: (PArgAttr, bool), e: LispVal,
    push: &mut impl FnMut(FileSpan, PArgAttr, ArgKind) -> Result<()>
  ) -> Result<()> {
    match self.head_keyword(&e) {
      Some((Keyword::Mut, u)) => {
        attr.0.mut_ = true;
        for e in u { self.push_args_core(base, attr, e, push)? }
      }
      Some((Keyword::Global, u)) => {
        attr.0.global = true;
        for e in u { self.push_args_core(base, attr, e, push)? }
      }
      Some((Keyword::Implicit, u)) => {
        attr.0.implicit = true;
        for e in u { self.push_args_core(base, attr, e, push)? }
      }
      Some((Keyword::Ghost, u)) => {
        attr.1 = true;
        for e in u { self.push_args_core(base, attr, e, push)? }
      }
      Some((Keyword::Out, mut u)) => {
        let (a, e) = match (u.next(), u.next(), u.is_empty()) {
          (Some(e), None, _) => (Symbol::UNDER, e),
          (Some(e1), Some(e), true) => {
            let a = self.as_symbol_or(base, &e1, || "'out' syntax error")?;
            (a, e)
          }
          _ => return Err(ElabError::new_e(try_get_span(base, &e), "'out' syntax error")),
        };
        attr.0.out = Some(a);
        self.push_args_core(base, attr, e, push)?
      }
      Some((Keyword::Colon, _)) => {
        let Spanned {span, k: pat} = self.push_tuple_pattern(base, false, e)?;
        push(span, attr.0, ArgKind::Lam(pat))?
      }
      Some((Keyword::ColonEq, mut u)) => {
        let span = try_get_fspan(base, &e);
        if let (Some(lhs), Some(rhs), true) = (u.next(), u.next(), u.is_empty()) {
          let rhs = Box::new(self.parse_expr(&span, rhs)?);
          let lhs = self.push_tuple_pattern(&span, attr.1, lhs)?;
          push(span, attr.0, ArgKind::Let(lhs, rhs))?
        } else { return Err(ElabError::new_e(&span, "':=' argument syntax error")) }
      }
      _ => {
        let span = try_get_fspan(base, &e);
        let k = if_chain! {
          if attr.0.global;
          if let Some(name) = e.as_atom();
          then {
            let name = self.as_symbol(name);
            let v = self.ba.fresh_var(name);
            ArgKind::Lam(TuplePatternKind::Name(false, name, v))
          } else {
            let v = self.ba.fresh_var(Symbol::UNDER);
            let under = Box::new(Spanned {
              span: span.clone(), k: TuplePatternKind::Name(true, Symbol::UNDER, v)});
            let ty = Box::new(self.parse_ty(&span, &e)?);
            ArgKind::Lam(TuplePatternKind::Typed(under, ty))
          }
        };
        push(span, attr.0, k)?
      }
    }
    Ok(())
  }

  fn push_tuple_pattern_args(&mut self,
    base: &FileSpan, ghost: bool, u: Uncons
  ) -> Result<Box<[(VarId, TuplePattern)]>> {
    u.map(|e| {
      let pat = self.push_tuple_pattern(base, ghost, e)?;
      let v = pat.k.as_single_name()
        .map_or_else(|| self.ba.fresh_var(Symbol::UNDER), |(_, _, v)| v);
      Ok((v, pat))
    }).collect::<Result<_>>()
  }

  /// Simplified version of `push_tuple_pattern` that visits the names of the
  /// tuple pattern without otherwise changing the parser state.
  fn on_names(&mut self, base: &FileSpan, e: &LispVal,
    f: &mut impl FnMut(&mut Self, FileSpan, Symbol) -> Result<()>
  ) -> Result<()> {
    if let Some(a) = e.as_atom() {
      if a != AtomId::UNDER {
        let name = self.as_symbol(a);
        f(self, try_get_fspan(base, e), name)?
      }
    } else if e.is_list() {
      match self.head_keyword(e) {
        Some((Keyword::Colon, mut u)) => if let Some(e) = u.next() {
          self.on_names(base, &e, f)?
        }
        Some((Keyword::Ghost, mut u)) => u.try_for_each(|e| self.on_names(base, &e, f))?,
        _ => Uncons::from(e.clone()).try_for_each(|e| self.on_names(base, &e, f))?,
      }
    } else {}
    Ok(())
  }

  /// Parse a tuple pattern.
  fn push_tuple_pattern(&mut self, base: &FileSpan, ghost: bool, e: LispVal
  ) -> Result<TuplePattern> {
    let span = try_get_fspan(base, &e);
    let k = if let Some(a) = e.as_atom() {
      let name = self.as_symbol(a);
      let v = self.ba.push_fresh(name);
      TuplePatternKind::Name(ghost || name == Symbol::UNDER, name, v)
    } else if e.is_list() {
      match self.head_keyword(&e) {
        Some((Keyword::Colon, mut u)) => {
          if let (Some(e), Some(ty), true) = (u.next(), u.next(), u.is_empty()) {
            let ty = self.parse_ty(&span, &ty)?;
            let pat = self.push_tuple_pattern(&span, ghost, e)?;
            TuplePatternKind::Typed(Box::new(pat), Box::new(ty))
          } else {
            return Err(ElabError::new_e(try_get_span(base, &e), "':' syntax error"))
          }
        }
        Some((Keyword::Ghost, mut u)) if u.len() == 1 =>
          return self.push_tuple_pattern(&span, true, u.next().expect("nonempty")),
        Some((Keyword::Ghost, u)) => {
          TuplePatternKind::Tuple(self.push_tuple_pattern_args(&span, true, u)?)
        }
        _ => TuplePatternKind::Tuple(self.push_tuple_pattern_args(&span, ghost, Uncons::from(e))?),
      }
    } else {
      return Err(ElabError::new_e(try_get_span(base, &e),
        format!("tuple pattern syntax error: {}", self.fe.to(&e))))
    };
    Ok(Spanned {span, k})
  }

  fn parse_decl_asgn(&mut self, span: &FileSpan, e: &LispVal) -> Result<DeclAssign> {
    match self.head_keyword(e) {
      Some((Keyword::ColonEq, mut u)) =>
        if let (Some(lhs), Some(rhs), true) = (u.next(), u.next(), u.is_empty()) {
          return Ok(DeclAssign::Let(lhs, rhs))
        },
      Some((Keyword::ArrowL, mut u)) =>
        if let (Some(lhs), Some(rhs), true) = (u.next(), u.next(), u.is_empty()) {
          return Ok(DeclAssign::Assign(lhs, rhs))
        },
      _ => {}
    }
    Err(ElabError::new_e(span, "decl: syntax error"))
  }

  fn push_decl(&mut self,
    base: &FileSpan, e: &LispVal, is_const: bool, intrinsic: bool,
  ) -> Result<Item> {
    let span = try_get_fspan(base, e);
    if let DeclAssign::Let(lhs, rhs) = self.parse_decl_asgn(&span, e)? {
      self.on_names(&span, &lhs, &mut |this, span, name| {
        if is_const {
          this.compiler.forward_declare_const(&span, name)?
        } else {
          this.compiler.forward_declare_global(&span, name)?
        }
        Ok(())
      })?;
      let rhs = self.parse_expr(&span, rhs)?;
      let lhs = self.push_tuple_pattern(&span, false, lhs)?;
      macro_rules! get_intrinsic {($f:ident) => {
        if intrinsic {
          if let Some((_, name, _)) = lhs.k.as_single_name() {
            Some(get_intrinsic(&lhs.span, name, $f::from_symbol)?)
          } else {
            return Err(ElabError::new_e(&lhs.span, "pattern matching is not allowed in intrinsics"))
          }
        } else { None }
      }}
      let k = if is_const {
        ItemKind::Const(get_intrinsic!(IntrinsicConst), lhs, rhs)
      } else {
        ItemKind::Global(get_intrinsic!(IntrinsicGlobal), lhs, rhs)
      };
      Ok(Spanned {span, k})
    } else {
      Err(ElabError::new_e(&span, "decl: assignment not allowed here"))
    }
  }

  fn parse_rename(&mut self, base: &FileSpan, e: &LispVal, with: &mut Renames) -> Result<bool> {
    match self.head_keyword(e) {
      Some((Keyword::ArrowL, mut u)) => if let (Some(to), Some(from), true) =
        (u.next().and_then(|e| e.as_atom()), u.next().and_then(|e| e.as_atom()), u.is_empty()) {
        with.new.push((self.as_symbol(from), self.as_symbol(to)));
        return Ok(true)
      },
      Some((Keyword::ArrowR, mut u)) => if let (Some(from), Some(to), true) =
        (u.next().and_then(|e| e.as_atom()), u.next().and_then(|e| e.as_atom()), u.is_empty()) {
        with.old.push((self.as_symbol(from), self.as_symbol(to)));
        return Ok(true)
      },
      _ => if let Some(a) = e.as_atom() {
        let a = self.as_symbol(a);
        with.new.push((a, a));
        return Ok(true)
      } else { return Ok(false) }
    }
    Err(ElabError::new_e(try_get_span(base, e), "with: expected {old -> old'} or {new' <- new}"))
  }

  /// Parse an MMC expression (shallowly), returning a [`parser::Expr`](Expr)
  /// containing [`LispVal`]s for subexpressions.
  fn parse_expr(&mut self, base: &FileSpan, e: LispVal) -> Result<Expr> {
    self.with_ctx(|this| {
      match this.push_expr_or_stmt(base, e)? {
        ExprOrStmt::Expr(e) => Ok(e),
        ExprOrStmt::Label(lab) if lab.k.args.is_empty() => {
          let k = ExprKind::Block(this.parse_block(&lab.span, lab.k.body)?);
          Ok(Spanned {span: lab.span, k})
        }
        ExprOrStmt::Label(lab) =>
          Err(ElabError::new_e(&lab.span, "a labeled block is a statement, not an expression")),
        ExprOrStmt::Let(span, ..) =>
          Err(ElabError::new_e(&span, "a let statement is not an expression")),
      }
    })
  }

  fn parse_decl_asgn_expr_or_stmt(&mut self, base: &FileSpan, e: &LispVal, with: Renames) -> Result<ExprOrStmt> {
    let span = try_get_fspan(base, e);
    match self.parse_decl_asgn(&span, e)? {
      DeclAssign::Let(lhs, rhs) => Ok(ExprOrStmt::Let(span, lhs, rhs, with)),
      DeclAssign::Assign(lhs, rhs) => {
        // let rhs = self.parse_expr(&span, rhs)?;
        // let lhs = self.push_tuple_pattern(&span, false, lhs, None)?;
        let lhs = Box::new(self.parse_expr(&span, lhs)?);
        let rhs = Box::new(self.parse_expr(&span, rhs)?);
        let oldmap = self.ba.mk_oldmap(&lhs, with).map_err(|e| (&span, e))?;
        Ok(ExprOrStmt::Expr(Spanned {span, k: ExprKind::Assign {lhs, rhs, oldmap}}))
      }
    }
  }

  fn push_expr_or_stmt(&mut self, base: &FileSpan, e: LispVal) -> Result<ExprOrStmt> {
    let span = try_get_fspan(base, &e);
    let k = match &*e.unwrapped_arc() {
      &LispKind::Atom(AtomId::UNDER) => ExprKind::Infer(true),
      &LispKind::Atom(a) => {
        let name = self.as_symbol(a);
        if let Some(v) = self.ba.get_var(name) { ExprKind::Var(v) } else {
          return self.parse_call(span.clone(), span.clone(), name, vec![], None).map_err(|_|
            ElabError::new_e(&span, format!("unknown variable '{}'", name))).map(ExprOrStmt::Expr)
        }
      }
      &LispKind::Bool(b) => ExprKind::Bool(b),
      LispKind::Number(n) => ExprKind::Int(n.clone()),
      LispKind::DottedList(es, r) if !r.is_list() && es.len() == 1 => {
        let head = Box::new(self.parse_expr(&span, es[0].clone())?);
        if let Some(a) = r.as_atom() {
          ExprKind::Proj(head, spanned(&span, r, FieldName::Named(self.as_symbol(a))))
        } else {
          match r.as_int(|n| n.try_into()) {
            Some(Ok(i)) => ExprKind::Proj(head, spanned(&span, r, FieldName::Number(i))),
            Some(Err(_)) => return Err(ElabError::new_e(&span, "field access: index out of range")),
            None => return Err(ElabError::new_e(&span, "field access syntax error")),
          }
        }
      }
      LispKind::List(_) | LispKind::DottedList(_, _) => match self.head_keyword(&e) {
        Some((Keyword::ColonEq | Keyword::ArrowL, _)) =>
          return self.parse_decl_asgn_expr_or_stmt(base, &e, Renames::default()),
        Some((Keyword::With, mut u)) => {
          let head = u.next().ok_or_else(||
            ElabError::new_e(&span, "'with' syntax error"))?;
          let mut with = Renames::default();
          for e in u {
            if !self.parse_rename(base, &e, &mut with)? {
              for e in Uncons::New(e) {
                if !self.parse_rename(base, &e, &mut with)? {
                  return Err(ElabError::new_e(&span,
                    "with: expected {old -> old'} or {new' <- new}"))
                }
              }
            }
          }
          return self.parse_decl_asgn_expr_or_stmt(base, &head, with)
        }
        Some((Keyword::If, mut u)) => {
          let err = || ElabError::new_e(&span, "if: syntax error");
          let mut branches = vec![];
          let mut push = |this: &mut Parser<'_, _>, (cond, then)| {
            let (hyp, cond) = match this.head_keyword(&cond) {
              Some((Keyword::Colon, mut u)) =>
                if let (Some(h), Some(cond), true) = (u.next(), u.next(), u.is_empty()) {
                  let h = h.as_atom().ok_or_else(||
                    ElabError::new_e(try_get_span(&span, &h), "expecting hypothesis name"))?;
                  (if h == AtomId::UNDER {None} else {Some(this.as_symbol(h))}, cond)
                } else {
                  return Err(ElabError::new_e(try_get_span(&span, &cond), "':' syntax error"))
                },
              _ => (None, cond),
            };
            let cond = Box::new(this.parse_expr(&span, cond)?);
            branches.push(if let Some(h) = hyp {
              let (h1, then) = this.with_ctx(|this| {
                let h1 = this.ba.push_fresh(h);
                this.parse_expr(&span, then).map(|then| (h1, Box::new(then)))
              })?;
              (Some([h1, this.ba.push_fresh(h)]), cond, then)
            } else {
              (None, cond, Box::new(this.parse_expr(&span, then)?))
            });
            Ok(())
          };
          let mut cond_tru = (u.next().ok_or_else(err)?, u.next().ok_or_else(err)?);
          let mut els;
          loop {
            els = u.next();
            if els.as_ref().and_then(|e| self.as_keyword(e)) == Some(Keyword::Else) {
              els = u.next()
            }
            if els.as_ref().and_then(|e| self.as_keyword(e)) == Some(Keyword::If) {
              push(self, mem::replace(&mut cond_tru,
                (u.next().ok_or_else(err)?, u.next().ok_or_else(err)?)))?;
            } else {break}
          }
          push(self, cond_tru)?;
          let mut ret = if let Some(els) = els { self.parse_expr(&span, els)?.k }
            else { ExprKind::Unit };
          for (hyp, cond, then) in branches.into_iter().rev() {
            let els = Box::new(Spanned {span: span.clone(), k: ret});
            ret = ExprKind::If {ik: IfKind::If, hyp, cond, then, els};
          }
          ret
        }
        Some((Keyword::Match, u)) =>
          self.parse_match(&span, u, |this, e| this.parse_expr(&span, e))?.k,
        Some((Keyword::While, mut u)) => {
          let cond = u.next().ok_or_else(||
            ElabError::new_e(&span, "while: syntax error"))?;
          let (hyp, cond) = if let Some((Keyword::Colon, mut u)) = self.head_keyword(&cond) {
            let h = u.next().and_then(|e| Some(spanned(&span, &e, self.as_symbol(e.as_atom()?))));
            if let (Some(h), Some(c), true) = (h, u.next(), u.is_empty()) {
              (Some(h), c)
            } else {
              return Err(ElabError::new_e(&span, "while: bad pattern"))
            }
          } else {(None, cond)};
          let mut var = None;
          let mut muts = Vec::new();
          while let Some(e) = u.head() {
            if let Some(v) = self.parse_variant(&span, &e)? {
              if mem::replace(&mut var, Some(v)).is_some() {
                return Err(ElabError::new_e(&span, "while: two variants"))
              }
            } else if let Some((Keyword::Mut, u)) = self.head_keyword(&e) {
              for e in u {
                let span = try_get_fspan(&span, &e);
                let a = e.as_atom().ok_or_else(|| ElabError::new_e(&span, "mut: expected an atom"))?;
                let name = self.as_symbol(a);
                let v = self.get_var(&span, name)?;
                if muts.contains(&v) { return Err(ElabError::new_e(&span, "duplicate mut")) }
                muts.push(v);
              }
            } else {break}
            u.next();
          }
          let mk = self.ba.build_while(muts.into());
          let cond = Box::new(self.parse_expr(&span, cond)?);
          let (hyp, body) = self.with_ctx(|this| -> Result<_> { Ok((
            hyp.as_ref().map(|h| this.ba.push_fresh(h.k)),
            Box::new(this.parse_block(&span, u)?),
          ))})?;
          mk.finish(&mut self.ba, var, cond, hyp, body)
        }
        Some((Keyword::Begin, u)) => ExprKind::Block(self.parse_block(&span, u)?),
        Some((Keyword::Entail, u)) => {
          let mut args = u.collect::<Vec<_>>();
          let last = args.pop().ok_or_else(||
            ElabError::new_e(&span, "entail: expected proof"))?;
          let pf = Spanned {span: try_get_fspan(&span, &last), k: self.proofs.push(last)};
          let args = args.into_iter().map(|e| self.parse_expr(&span, e)).collect::<Result<_>>()?;
          ExprKind::Entail(pf, args)
        }
        _ => {
          let mut u = Uncons::from(e);
          match u.next() {
            None => ExprKind::Unit,
            Some(e) => if let Some((Keyword::Begin, mut u1)) = self.head_keyword(&e) {
              let name = u1.next().and_then(|e| e.as_atom()).ok_or_else(||
                ElabError::new_e(&span, "label: expected label name"))?;
              let name = self.as_symbol(name);
              let k = PLabel {name, args: u1, body: u};
              return Ok(ExprOrStmt::Label(Spanned {span, k}))
            } else {
              let fsp = try_get_fspan(&span, &e);
              let f = e.as_atom().ok_or_else(|| ElabError::new_e(fsp.span,
                "only variables can be called like functions"))?;
              let f = self.as_symbol(f);
              let mut args = vec![];
              let mut variant = None;
              for e in u {
                if let Some((Keyword::Variant, mut u)) = self.head_keyword(&e) {
                  if let (Some(v), true) = (u.next(), u.is_empty()) {
                    if mem::replace(&mut variant, Some(v)).is_some() {
                      return Err(ElabError::new_e(&span, "call: two variants"))
                    }
                  } else {
                    return Err(ElabError::new_e(&span, "variant: expected 1 argument"))
                  }
                } else {
                  args.push(e)
                }
              }
              self.parse_call(span.clone(), fsp, f, args, variant)?.k
            }
          }
        }
      },
      _ => return Err(ElabError::new_e(&span, "unknown expression"))
    };
    Ok(ExprOrStmt::Expr(Spanned {span, k}))
  }

  fn push_jumps(&mut self, jumps: Vec<Spanned<PLabel>>) -> Result<(VarId, Box<[Label]>)> {
    let group = self.ba.push_label_group(jumps.iter().map(|j| j.k.name));
    let jumps = jumps.into_iter().map(|Spanned {span, k: PLabel {name: _, args: u1, body}}| {
      self.with_ctx(|this| {
        let mut args = vec![];
        let mut variant = None;
        for e in u1 {
          if let Some(v) = this.parse_variant(&span, &e)? {
            if mem::replace(&mut variant, Some(v)).is_some() {
              return Err(ElabError::new_e(&span, "label: two variants"))
            }
          } else {
            this.push_args(&span, false, e, &mut args)?
          }
        }
        let body = this.parse_block(&span, body)?;
        Ok(Label {args: args.into(), variant, body: Spanned {span, k: body}})
      })
    }).collect::<Result<_>>()?;
    Ok((group, jumps))
  }

  fn parse_block(&mut self, span: &FileSpan, es: Uncons) -> Result<Block> {
    self.with_ctx(|this| {
      let mut stmts = Vec::with_capacity(es.len());
      let mut jumps: Vec<Spanned<PLabel>> = vec![];
      macro_rules! clear_jumps {() => {if !jumps.is_empty() {
        let (v, labels) = (this.push_jumps(std::mem::take(&mut jumps))?);
        stmts.push(Spanned {span: span.clone(), k: ast::StmtKind::Label(v, labels)});
      }}}
      for e in es {
        match this.push_expr_or_stmt(span, e)? {
          ExprOrStmt::Label(Spanned {span: e_span, k: lab}) => {
            if jumps.iter().any(|l| l.k.name == lab.name) { clear_jumps!() }
            jumps.push(Spanned {span: e_span, k: lab})
          }
          ExprOrStmt::Let(e_span, lhs, rhs, Renames {old, new}) => {
            clear_jumps!();
            let rhs = this.parse_expr(span, rhs)?;
            this.ba.apply_rename(&old).map_err(|e| (span, e))?;
            let lhs = this.push_tuple_pattern(span, false, lhs)?;
            this.ba.apply_rename(&new).map_err(|e| (span, e))?;
            stmts.push(Spanned {span: e_span, k: ast::StmtKind::Let {lhs, rhs}})
          }
          ExprOrStmt::Expr(e) => {
            clear_jumps!();
            stmts.push(e.map_into(StmtKind::Expr))
          }
        }
      }
      if let Some(Spanned {span, ..}) = jumps.first() {
        return Err(ElabError::new_e(span, "a labeled block is a statement, not an expression"))
      }
      let expr = if let Some(Spanned {k: ast::StmtKind::Expr(_), ..}) = stmts.last() {
        let_unchecked!(Some(Spanned {span, k: ast::StmtKind::Expr(expr)}) = stmts.pop(),
          Some(Box::new(Spanned {span, k: expr})))
      } else {
        None
      };
      Ok(ast::Block {stmts, expr})
    })
  }

  fn parse_proc(&mut self,
    span: FileSpan,
    kind: &dyn Fn(Symbol) -> Result<ProcKind>,
    mut u: Uncons,
    intrinsic: bool,
  ) -> Result<Item> {
    struct OutVal {
      index: u32,
      name: Symbol,
      used: bool,
    }
    let e = match u.next() {
      None => return Err(ElabError::new_e(try_get_span(&span, &LispVal::from(u)), "func/proc: syntax error")),
      Some(e) => e,
    };
    let mut outmap: Vec<OutVal> = vec![];
    let mut args = vec![];
    let mut outs = vec![];
    let mut rets = vec![];
    let (name, header) = match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => (spanned(&span, &e, self.as_symbol(a)), None),
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e);
        let e = u.next().ok_or_else(||
          ElabError::new_e(&span, "func/proc syntax error: expecting function name"))?;
        let name = self.as_symbol_or(&span, &e, || "func/proc syntax error: expecting an atom")?;
        (spanned(&span, &e, name), Some(u))
      }
      _ => return Err(ElabError::new_e(&span, "func/proc: syntax error"))
    };
    let kind = kind(name.k)?;
    let intrinsic = if intrinsic {
      Some(get_intrinsic(&name.span, name.k, IntrinsicProc::from_symbol)?)
    } else { None };
    self.compiler.forward_declare_proc(&name.span, name.k)?;
    if let Some(u) = header {
      let mut u = u.peekable();
      while let Some((e, a)) =
        u.peek().and_then(|e| e.as_atom().filter(|&a| a != AtomId::COLON).map(|a| (e, a)))
      {
        let name = self.as_symbol(a);
        self.ba.push_tyvar(&spanned(&span, e, name));
        u.next();
      }
      for e in &mut u {
        if e.as_atom() == Some(AtomId::COLON) { break }
        self.push_args_core(&span, Default::default(), e, &mut |span, attr, pat| {
          if attr.out.is_some() {
            return Err(ElabError::new_e(&span, "'out' not permitted on function arguments"))
          }
          if attr.mut_ {
            if let Some((_, name, _)) = pat.var().as_single_name() {
              if outmap.iter().any(|p| p.name == name) {
                return Err(ElabError::new_e(&span, "'mut' variables cannot shadow"))
              }
              outmap.push(OutVal {
                name, used: false,
                index: args.len().try_into().expect("too many arguments"),
              });
            } else { return Err(ElabError::new_e(&span, "cannot use tuple pattern with 'mut'")) }
          }
          args.push(Spanned {span, k: (attr.into(), pat)});
          Ok(())
        })?
      }
      self.with_ctx(|this| {
        let mut rets1 = vec![];
        for e in u {
          this.push_args_core(&span, Default::default(), e, &mut |span, mut attr, pat| {
            if let Some(name) = &mut attr.out {
              if *name == Symbol::UNDER {
                if let Some(v) = pat.var().as_single_name() {*name = v.1}
              }
              if let Some(OutVal {used, ..}) = outmap.iter_mut().find(|p| p.name == *name) {
                if std::mem::replace(used, true) {
                  return Err(ElabError::new_e(&span, "two 'out' arguments to one 'mut'"))
                }
              } else {
                return Err(ElabError::new_e(&span,
                  "'out' does not reference a 'mut' in the function arguments"))
              }
            }
            rets1.push((span, attr, pat));
            Ok(())
          })?
        }
        outs.extend(outmap.iter().filter(|val| !val.used)
          .map(|&OutVal {index, name, ..}| (index, name, this.ba.push_fresh(name), None)));
        for (span, attr, pat) in rets1 {
          if attr.mut_ {
            return Err(ElabError::new_e(&span, "'mut' not permitted on function returns"))
          }
          match pat {
            ArgKind::Let(..) =>
              return Err(ElabError::new_e(&span, "assignment not permitted here")),
            ArgKind::Lam(mut pat) => if let Some(name) = attr.out {
              if !rets.is_empty() {
                return Err(ElabError::new_e(&span,
                  "out parameters must precede regular function returns"))
              }
              let mut oty = None;
              let mut sp = span.clone();
              outs.push(loop {
                match pat {
                  TuplePatternKind::Name(_, name2, v) => {
                    let &OutVal {index, ..} =
                      outmap.iter().find(|p| p.name == name).expect("checked");
                    break (index, name2, v, oty)
                  }
                  TuplePatternKind::Typed(pat2, ty) => {
                    if oty.replace(ty).is_some() {
                      return Err(ElabError::new_e(&span,
                        "double type ascription not permitted here"))
                    }
                    sp = pat2.span.clone();
                    pat = pat2.k;
                  }
                  TuplePatternKind::Tuple(_) => return Err(ElabError::new_e(&sp,
                    "tuple pattern not permitted in 'out' returns"))
                }
              })
            } else {
              rets.push(Spanned {span, k: pat})
            }
          }
        }
        Ok(())
      })?;
    }
    let tyargs = self.ba.num_tyvars();
    let args = args.into();
    let outs = outs.into();
    let rets = rets.into();
    let variant = if let Some(e) = u.head() {
      if intrinsic.is_some() {
        return Err(ElabError::new_e(&span, "intrinsic: unexpected body"))
      }
      self.parse_variant(&span, &e)?
    } else {None};
    let body = self.parse_block(&span, u)?;
    Ok(Spanned {span, k: ItemKind::Proc {
      intrinsic, kind, name, tyargs, args, outs, rets, variant, body
    }})
  }

  #[allow(clippy::type_complexity)]
  fn parse_name_and_tyargs(&mut self, base: &FileSpan, e: &LispVal) -> Result<(Spanned<Symbol>, u32, Box<[Arg]>)> {
    let mut args = vec![];
    let name = match &*e.unwrapped_arc() {
      &LispKind::Atom(a) => spanned(base, e, self.as_symbol(a)),
      LispKind::List(_) | LispKind::DottedList(_, _) => {
        let mut u = Uncons::from(e.clone()).peekable();
        let e = u.next().ok_or_else(|| ElabError::new_e(try_get_span(base, e), "typedef: syntax error"))?;
        let a = spanned(base, &e, self.as_symbol_or(base, &e, || "typedef: expected an atom")?);
        while let Some((e, a)) = u.peek().and_then(|e| e.as_atom().map(|a| (e, a))) {
          let name = self.as_symbol(a);
          self.ba.push_tyvar(&spanned(base, e, name));
          u.next();
        }
        for e in u { self.push_args(base, false, e, &mut args)? }
        a
      },
      _ => return Err(ElabError::new_e(try_get_span(base, e), "typedef: syntax error"))
    };
    Ok((name, self.ba.num_tyvars(), args.into()))
  }

  /// Parses the input lisp literal `e` into a list of top level items and appends them to `ast`.
  fn push_item_group(&mut self,
    base: &FileSpan, e: &LispVal, intrinsic: bool,
  ) -> Result<ItemGroup> {
    let span = try_get_fspan(base, e);
    Ok(match self.head_keyword(e) {
      Some((Keyword::Proc, u)) => {
        let f = |a| Ok(if a == Keyword::Main.as_symbol() {ProcKind::Main} else {ProcKind::Proc});
        ItemGroup::Item(self.parse_proc(span, &f, u, intrinsic)?)
      }
      Some((Keyword::Func, u)) => {
        let f = |_| Ok(ProcKind::Func);
        ItemGroup::Item(self.parse_proc(span, &f, u, intrinsic)?)
      }
      Some((Keyword::Intrinsic, u)) => ItemGroup::Intrinsic(u),
      Some((Keyword::Global, u)) => ItemGroup::Global(u),
      Some((Keyword::Const, u)) => ItemGroup::Const(u),
      Some((Keyword::Typedef, mut u)) =>
        if let (Some(e1), Some(val), true) = (u.next(), u.next(), u.is_empty()) {
          let (name, tyargs, args) = self.parse_name_and_tyargs(base, &e1)?;
          let intrinsic = if intrinsic {
            Some(get_intrinsic(&name.span, name.k, IntrinsicType::from_symbol)?)
          } else { None };
          let val = self.parse_ty(&span, &val)?;
          ItemGroup::Item(spanned(base, e, ItemKind::Typedef {intrinsic, name, tyargs, args, val}))
        } else {
          return Err(ElabError::new_e(try_get_span(base, e), "typedef: syntax error"))
        },
      Some((Keyword::Struct, mut u)) => {
        let e1 = u.next().ok_or_else(||
          ElabError::new_e(try_get_span(base, e), "struct: expecting name"))?;
        let (name, tyargs, args) = self.parse_name_and_tyargs(base, &e1)?;
        let intrinsic = if intrinsic {
          Some(get_intrinsic(&name.span, name.k, IntrinsicType::from_symbol)?)
        } else { None };
        let mut fields = vec![];
        for e in u { self.push_args(base, false, e, &mut fields)? }
        let val = Spanned {span, k: TypeKind::Struct(fields.into())};
        ItemGroup::Item(spanned(base, e, ItemKind::Typedef {intrinsic, name, tyargs, args, val}))
      }
      _ => return Err(ElabError::new_e(try_get_span(base, e),
        format!("MMC: unknown top level item: {}", self.fe.to(e))))
    })
  }

  /// Extract the next item from the provided item iterator.
  pub(crate) fn parse_next_item(&mut self,
    base: &FileSpan, ItemIter {group, u, intrinsic}: &mut ItemIter
  ) -> Result<Option<Item>> {
    self.with_ctx(|this| Ok(loop {
      match group {
        ItemIterInner::New => if let Some(e) = u.next() {
          match this.push_item_group(base, &e, *intrinsic)? {
            ItemGroup::Item(it) => break Some(it),
            ItemGroup::Global(u2) => *group = ItemIterInner::Global(u2),
            ItemGroup::Const(u2) => *group = ItemIterInner::Const(u2),
            ItemGroup::Intrinsic(u) => *group = ItemIterInner::Intrinsic(
              Box::new(ItemIter {group: ItemIterInner::New, u, intrinsic: true})),
          }
        } else {
          break None
        },
        ItemIterInner::Global(u2) => if let Some(e) = u2.next() {
          break Some(this.push_decl(base, &e, false, *intrinsic)?)
        } else {
          *group = ItemIterInner::New
        },
        ItemIterInner::Const(u2) => if let Some(e) = u2.next() {
          break Some(this.push_decl(base, &e, true, *intrinsic)?)
        } else {
          *group = ItemIterInner::New
        }
        ItemIterInner::Intrinsic(iter) => if let Some(item) = this.parse_next_item(base, iter)? {
          break Some(item)
        } else {
          *group = ItemIterInner::New
        }
      }
    }))
  }

  /// Parse a pattern expression.
  fn parse_pattern<T: BuildMatch>(&mut self,
    base: &FileSpan, pb: &mut PatternBuilder<T>, e: &LispVal
  ) -> Result<Pattern> {
    let span = try_get_fspan(base, e);
    Ok(match &*e.unwrapped_arc() {
      LispKind::Atom(AtomId::UNDER) => pb.ignore(),
      &LispKind::Atom(a) => {
        let name = self.as_symbol(a);
        if matches!(self.compiler.names.get(&name), Some(Entity::Const(_))) {
          pb.const_(&span, Spanned {span: span.clone(), k: ExprKind::Const(name)})
        } else {
          pb.var(name, &mut self.ba).map_err(|BadBinding|
            ElabError::new_e(&span, "can't bind variables in this context"))?
        }
      }
      LispKind::List(_) | LispKind::DottedList(_, _) => match self.head_keyword(e) {
        Some((Keyword::Colon, mut u)) =>
          if let (Some(h), Some(p), true) = (u.next(), u.next(), u.is_empty()) {
            let h = self.as_symbol_or(base, &h, || "expecting hypothesis name")?;
            pb.hyped(&span, h, &mut self.ba).map_err(|BadBinding|
              ElabError::new_e(&span, "can't bind variables in this context"))?;
            self.parse_pattern(&span, pb, &p)?.hyped(&span)
          } else {
            return Err(ElabError::new_e(try_get_span(base, e), "':' syntax error"))
          },
        Some((Keyword::Or, u)) => {
          let mut orb = pb.or(&span);
          for pat in u {
            orb.send(pb);
            orb.recv(self.parse_pattern(&span, pb, &pat)?);
          }
          orb.finish()
        }
        Some((Keyword::With, mut u)) =>
          if let (Some(p), Some(g), true) = (u.next(), u.next(), u.is_empty()) {
            pb.with(&span);
            let pat = self.parse_pattern(&span, pb, &p)?;
            let e = self.parse_expr(&span, g)?;
            pat.with(&span, e)
          } else {
            return Err(ElabError::new_e(try_get_span(base, e), "'with' syntax error"))
          },
        _ => return Err(ElabError::new_e(try_get_span(base, e), "pattern syntax error"))
      }
      LispKind::Number(n) =>
        pb.const_(&span, Spanned {span: span.clone(), k: ExprKind::Int(n.clone())}),
      _ => return Err(ElabError::new_e(try_get_span(base, e), "pattern syntax error"))
    })
  }

  #[allow(clippy::type_complexity)]
  fn parse_match<T: BuildMatch>(&mut self, base: &FileSpan,
    mut u: impl Iterator<Item=LispVal>,
    mut f: impl FnMut(&mut Self, LispVal) -> Result<Spanned<T>>
  ) -> Result<Spanned<T>> {
    let c = self.parse_expr(base,
      u.next().ok_or_else(|| ElabError::new_e(base, "match: syntax error"))?)?;
    let mut mb = self.ba.build_match(base.clone(), c);
    self.with_ctx(|this| {
      for e in u {
        if let Some((Keyword::Arrow, mut u)) = this.head_keyword(&e) {
          if let (Some(lhs), Some(rhs), true) = (u.next(), u.next(), u.is_empty()) {
            let span = try_get_fspan(base, &lhs);
            let mut pb = mb.branch(&mut this.ba).map_err(|UnreachablePattern|
              ElabError::new_e(&span, "unreachable pattern"))?;
            let pat = this.parse_pattern(base, &mut pb, &lhs)?;
            let rhs = this.with_ctx(|this| {
              pb.prepare_rhs(&mut this.ba);
              f(this, rhs)
            })?;
            pb.finish(&span, pat, rhs, &mut mb)
          } else {
            return Err(ElabError::new_e(base, "match: syntax error"))
          }
        } else {
          return Err(ElabError::new_e(base, "match: syntax error"))
        }
      }
      mb.finish().map_err(|Incomplete(c)|
        ElabError::new_e(&c.span, "unreachable pattern"))
    })
  }

  /// Parse a type.
  fn parse_ty(&mut self, base: &FileSpan, e: &LispVal) -> Result<Type> {
    let span = try_get_fspan(base, e);
    let mut u = Uncons::New(e.clone());
    let (head, mut args) = match u.next() {
      None if u.is_empty() => return Ok(Spanned {span, k: TypeKind::Unit}),
      None => (u.into(), vec![]),
      Some(head) => (head, u.collect()),
    };

    macro_rules! ty {($ty:expr) => {Box::new(self.parse_ty(&span, $ty)?)}}
    macro_rules! tys {($args:expr) => {
      $args.iter().map(|ty| self.parse_ty(&span, ty)).collect::<Result<_>>()?}}
    macro_rules! expr {($e:expr) => {Box::new(self.parse_expr(&span, $e.clone())?)}}
    macro_rules! exprs {($args:expr) => {
      $args.iter().map(|e| self.parse_expr(&span, e.clone())).collect::<Result<_>>()?}}
    let k = if let Some(name) = head.as_atom() {
      if name == AtomId::UNDER {
        return Ok(spanned(base, e, TypeKind::Infer))
      }
      let name = self.as_symbol(name);
      match self.compiler.names.get(&name) {
        Some(&Entity::Prim(Prim {ty: Some(prim), ..})) => match (prim, &*args) {
          (PrimType::Array, [ty, n]) => TypeKind::Array(ty!(ty), expr!(n)),
          (PrimType::Bool, []) => TypeKind::Bool,
          (PrimType::I8, []) => TypeKind::Int(Size::S8),
          (PrimType::I16, []) => TypeKind::Int(Size::S16),
          (PrimType::I32, []) => TypeKind::Int(Size::S32),
          (PrimType::I64, []) => TypeKind::Int(Size::S64),
          (PrimType::Int, []) => TypeKind::Int(Size::Inf),
          (PrimType::U8, []) => TypeKind::UInt(Size::S8),
          (PrimType::U16, []) => TypeKind::UInt(Size::S16),
          (PrimType::U32, []) => TypeKind::UInt(Size::S32),
          (PrimType::U64, []) => TypeKind::UInt(Size::S64),
          (PrimType::Nat, []) => TypeKind::UInt(Size::Inf),
          (PrimType::Input, []) => TypeKind::Input,
          (PrimType::Output, []) => TypeKind::Output,
          (PrimType::Own, [ty]) => TypeKind::Own(ty!(ty)),
          (PrimType::Ref, [ty]) => TypeKind::Ref(None, ty!(ty)),
          (PrimType::RefSn, [e]) => TypeKind::RefSn(expr!(e.clone())),
          (PrimType::Shr, [ty]) => TypeKind::shr(span.clone(), None, ty!(ty)),
          (PrimType::Sn, [e]) => TypeKind::Sn(expr!(e.clone())),
          (PrimType::List | PrimType::Star, _) => TypeKind::List(tys!(args)),
          (PrimType::Struct, _) => {
            let mut out = vec![];
            for e in args { self.push_args(base, false, e, &mut out)? }
            TypeKind::Struct(out.into())
          },
          (PrimType::And, _) => TypeKind::And(tys!(args)),
          (PrimType::Or, _) => TypeKind::Or(tys!(args)),
          (PrimType::Moved, [ty]) => TypeKind::Moved(ty!(ty)),
          (PrimType::Ghost, [ty]) => TypeKind::Ghost(ty!(ty)),
          (PrimType::Uninit, [ty]) => TypeKind::Uninit(ty!(ty)),
          (PrimType::All, args1) if !args1.is_empty() => self.with_ctx(|this| -> Result<_> {
            let last = args.pop().expect("nonempty");
            let args = args.into_iter().map(|e| {
              this.push_tuple_pattern(base, false, e)
            }).collect::<Result<_>>()?;
            Ok(TypeKind::All(args, Box::new(this.parse_ty(&span, &last)?)))
          })?,
          (PrimType::Ex, args1) if !args1.is_empty() => self.with_ctx(|this| -> Result<_> {
            let last = args.pop().expect("nonempty");
            let args = args.into_iter().map(|e| {
              this.push_tuple_pattern(base, false, e)
            }).collect::<Result<_>>()?;
            let v = this.ba.fresh_var(Symbol::UNDER);
            Ok(TypeKind::ex(span.clone(), args, v, Box::new(this.parse_ty(&span, &last)?)))
          })?,
          (PrimType::Imp, [e1, e2]) => TypeKind::Imp(ty!(e1), ty!(e2)),
          (PrimType::Wand, [e1, e2]) => TypeKind::Wand(ty!(e1), ty!(e2)),
          (PrimType::HasTy, [e, ty]) => TypeKind::HasTy(expr!(e), ty!(ty)),
          _ => return Err(ElabError::new_e(&span, "unexpected number of arguments"))
        },
        Some(&Entity::Prim(p)) if p.op.is_some() => TypeKind::Pure(expr!(e)),
        Some(Entity::Type(ty)) => if let Some(&TypeTy {tyargs, args: ref tgt, ..}) = ty.k.ty() {
          let n = tyargs as usize;
          let nargs = tgt.iter().filter(|&a| matches!(a.1, global::ArgKind::Lam(_))).count();
          if args.len() != n + nargs {
            return Err(ElabError::new_e(try_get_span(base, &head), "unexpected number of arguments"))
          }
          TypeKind::User(name, tys!(args[..n]), exprs!(args[n..]))
        } else {
          TypeKind::Error
        },
        Some(_) => return Err(ElabError::new_e(try_get_span(base, &head), "expected a type")),
        None if args.is_empty() => TypeKind::Var(self.ba.get_tyvar(name).ok_or_else(||
          ElabError::new_e(&span, format!("unknown type variable '{}'", name)))?),
        None => return Err(ElabError::new_e(try_get_span(base, &head),
          format!("unknown type constructor '{}'", name))),
      }
    } else {
      match self.as_keyword(&head) {
        Some(Keyword::If) => {
          let [c, t, e]: &[_; 3] = (&*args).try_into().map_err(|_|
            ElabError::new_e(try_get_span(base, &head), "unexpected number of arguments"))?;
          TypeKind::If(expr!(c), ty!(t), ty!(e))
        }
        Some(Keyword::Match) => return self.parse_match(&span,
          args.into_iter(), |this, ty| this.parse_ty(&span, &ty)),
        _ => TypeKind::Pure(expr!(e)),
      }
    };
    Ok(Spanned {span, k})
  }

  /// Parse an expression that looks like a function call.
  fn parse_call(&mut self,
    span: FileSpan,
    fsp: FileSpan, f: Symbol,
    args: Vec<LispVal>,
    variant: Option<LispVal>,
  ) -> Result<Expr> {
    macro_rules! err {($($e:expr),*) => {
      return Err(ElabError::new_e(&span, format!($($e),*)))
    }}
    macro_rules! ty {($ty:expr) => {Box::new(self.parse_ty(&span, $ty)?)}}
    macro_rules! tys {($args:expr) => {
      $args.iter().map(|ty| self.parse_ty(&span, ty)).collect::<Result<_>>()?}}
    macro_rules! expr {($e:expr) => {Box::new(self.parse_expr(&span, $e.clone())?)}}
    macro_rules! exprs {($args:expr) => {
      $args.iter().map(|e| self.parse_expr(&span, e.clone())).collect::<Result<_>>()?}}
    macro_rules! variant {() => {if let Some(e) = variant {Some(expr!(e))} else {None}}}
    if let Some(lab) = self.ba.get_label(f) {
      let k = ExprKind::Jump(lab, exprs!(args), variant!());
      return Ok(Spanned {span, k})
    }
    let k = match self.compiler.names.get(&f) {
      None => err!("unknown function '{}'", f),
      Some(Entity::Const(_)) => ExprKind::Const(f),
      Some(Entity::Global(_)) => return Err(ElabError::new_e(&span, format!(
        "variable '{}' not found. \
        A global with this name exists but must be imported into scope with\n  (global {0})\
        \nin the function signature.", f))),
      Some(Entity::Prim(Prim {op: Some(prim), ..})) => match (prim, &*args) {
        (PrimOp::Add, _) => {let args = exprs!(args); return Ok(self.ba.mk_add(&span, args))}
        (PrimOp::And, _) => {let args = exprs!(args); return Ok(self.ba.mk_and(&span, args))}
        (PrimOp::Or, _) => {let args = exprs!(args); return Ok(self.ba.mk_or(&span, args))}
        (PrimOp::BitAnd, _) => {let args = exprs!(args); return Ok(self.ba.mk_bit_and(&span, args))}
        (PrimOp::BitNot, _) => {let args = exprs!(args); return Ok(self.ba.mk_bit_nor(&span, args))}
        (PrimOp::BitOr, _) => {let args = exprs!(args); return Ok(self.ba.mk_bit_or(&span, args))}
        (PrimOp::BitXor, _) => {let args = exprs!(args); return Ok(self.ba.mk_bit_xor(&span, args))}
        (PrimOp::Max | PrimOp::Min | PrimOp::Le | PrimOp::Lt | PrimOp::Eq | PrimOp::Ne, _)
        if args.is_empty() => err!("expected 2 arguments"),
        (PrimOp::Max, _) => {let args = exprs!(args); return Ok(self.ba.mk_max(&span, args))}
        (PrimOp::Min, _) => {let args = exprs!(args); return Ok(self.ba.mk_min(&span, args))}
        (PrimOp::MulDeref, [e]) => ExprKind::Deref(expr!(e)),
        (PrimOp::MulDeref, _) => {let args = exprs!(args); return Ok(self.ba.mk_mul(&span, args))}
        (PrimOp::Not, _) => {let args = exprs!(args); return Ok(self.ba.mk_nor(&span, args))}
        (PrimOp::Le | PrimOp::Lt | PrimOp::Eq | PrimOp::Ne, _) if args.is_empty() =>
          err!("expected 2 arguments"),
        (PrimOp::Le, _) => {let args = exprs!(args); return Ok(self.ba.mk_le(&span, args))}
        (PrimOp::Lt, _) => {let args = exprs!(args); return Ok(self.ba.mk_lt(&span, args))}
        (PrimOp::Eq, _) => {let args = exprs!(args); return Ok(self.ba.mk_eq(&span, args))}
        (PrimOp::Ne, _) => {let args = exprs!(args); return Ok(self.ba.mk_ne(&span, args))}
        (PrimOp::List, _) => ExprKind::List(exprs!(args)),
        (PrimOp::Assert, _) =>
          {let args = exprs!(args); ExprKind::Assert(Box::new(self.ba.mk_and(&span, args)))}
        (PrimOp::Index, args) => match args {
          [arr, idx] => ExprKind::Index(expr!(arr), expr!(idx), None),
          [arr, idx, pf] => ExprKind::Index(expr!(arr), expr!(idx), Some(expr!(pf))),
          _ => err!("expected 2 or 3 arguments"),
        },
        (PrimOp::Ghost, _) => ExprKind::Ghost(Box::new(Expr::list(&span, exprs!(args)))),
        (PrimOp::Return, _) => ExprKind::Return(exprs!(args)),
        (PrimOp::Sub, []) => err!("expected 1 or more arguments"),
        (PrimOp::Sub, [e]) => ExprKind::Unop(Unop::Neg, expr!(e)),
        (PrimOp::Sub, _) => {let args = exprs!(args); return Ok(self.ba.mk_sub(&span, args))}
        (PrimOp::Shl, [a, b]) => ExprKind::Binop(Binop::Shl, expr!(a), expr!(b)),
        (PrimOp::Shr, [a, b]) => ExprKind::Binop(Binop::Shr, expr!(a), expr!(b)),
        (PrimOp::Typed, [e, ty]) => ExprKind::Typed(expr!(e), ty!(ty)),
        (PrimOp::As, [e, ty]) => ExprKind::As(expr!(e), ty!(ty)),
        (PrimOp::Shl | PrimOp::Shr | PrimOp::Typed | PrimOp::As, _) =>
          err!("expected 2 arguments"),
        (PrimOp::Cast, args) => match args {
          [e] => ExprKind::Cast(expr!(e), None),
          [e, pf] => ExprKind::Cast(expr!(e), Some(expr!(pf))),
          _ => err!("expected 1 or 2 arguments"),
        },
        (PrimOp::Pun, args) => match args {
          [e] => ExprKind::Pun(expr!(e), None),
          [e, pf] => ExprKind::Pun(expr!(e), Some(expr!(pf))),
          _ => err!("expected 1 or 2 arguments"),
        },
        (PrimOp::Sn, args) => match args {
          [e] => ExprKind::Sn(expr!(e), None),
          [e, pf] => ExprKind::Sn(expr!(e), Some(expr!(pf))),
          _ => err!("expected 1 or 2 arguments"),
        },
        (PrimOp::Slice, args) => match args {
          [arr, idx, len] =>
            ExprKind::Slice(Box::new((*expr!(arr), *expr!(idx), *expr!(len))), None),
          [arr, idx, len, pf] =>
            ExprKind::Slice(Box::new((*expr!(arr), *expr!(idx), *expr!(len))), Some(expr!(pf))),
          _ => err!("expected 3 or 4 arguments"),
        },
        (PrimOp::Uninit, []) => ExprKind::Uninit,
        (PrimOp::Uninit, _) => err!("expected 0 arguments"),
        (PrimOp::Pure, _) => ExprKind::Mm0(self.parse_mm0_expr(&span, args)?),
        (PrimOp::Ref, [e]) => ExprKind::Ref(expr!(e)),
        (PrimOp::Borrow, [e]) => ExprKind::Borrow(expr!(e)),
        (PrimOp::TypeofBang, [e]) => ExprKind::Typeof(expr!(e)),
        (PrimOp::Typeof, [e]) =>
          ExprKind::Typeof(Box::new(Spanned {span: span.clone(), k: ExprKind::Ref(expr!(e))})),
        (PrimOp::Sizeof, [ty]) => ExprKind::Sizeof(ty!(ty)),
        (PrimOp::Ref | PrimOp::Borrow | PrimOp::TypeofBang |
         PrimOp::Typeof | PrimOp::Sizeof, _) => err!("expected 1 argument"),
        (PrimOp::Unreachable, args) => ExprKind::Unreachable(match args {
          [] => Box::new(Spanned {span: span.clone(), k: ExprKind::Infer(false)}),
          [e] => expr!(e),
          _ => err!("expected 1 argument"),
        }),
        (PrimOp::Break, args1) => {
          let (lab, args) = match args1.first().and_then(|e| {
            let a = self.as_symbol(e.as_atom()?); self.ba.get_label(a)
          }) {
            Some(lab) => (lab, &args[1..]),
            None => (self.ba.get_loop_label().ok_or_else(||
              ElabError::new_e(&span, "can't break, not in a loop"))?, &*args)
          };
          ExprKind::Break(lab.0, Box::new(Expr::list(&span, exprs!(args))))
        }
        (PrimOp::Continue, args1) => {
          let (lab, args) = match args1.first().and_then(|e| {
            let a = self.as_symbol(e.as_atom()?); self.ba.get_label(a)
          }) {
            Some(lab) => (lab, &args[1..]),
            None => (self.ba.get_loop_label().ok_or_else(||
              ElabError::new_e(&span, "can't break, not in a loop"))?, &*args)
          };
          ExprKind::Jump(lab, exprs!(args), variant!())
        }
      }
      Some(Entity::Proc(Spanned {k, ..})) => match k.ty() {
        Some(proc) => {
          let ntys = u32_as_usize(proc.tyargs);
          if args.len() != ntys + proc.args.len() {
            err!("{}: expected {} arguments", f, ntys + proc.args.len())
          }
          ExprKind::Call {
            f: Spanned {span: fsp, k: f},
            tys: tys!(args[..ntys]),
            args: exprs!(args[ntys..]),
            variant: variant!()
          }
        }
        None => ExprKind::Error,
      }
      Some(_) => err!("parse_expr unimplemented entity type"),
    };
    Ok(Spanned {span, k})
  }

  fn parse_pure_args(&mut self, base: &FileSpan, mut args: Vec<LispVal>
  ) -> Result<(Vec<(AtomId, Expr)>, LispVal)> {
    if let Some(last) = args.pop() {
      Ok((args.into_iter().map(|e| {
        let span = try_get_fspan(base, &e);
        if let Some((Keyword::ColonEq, mut u)) = self.head_keyword(&e) {
          if let (Some(lhs), Some(rhs), true) = (u.next(), u.next(), u.is_empty()) {
            return Ok((
              lhs.as_atom().ok_or_else(||
                ElabError::new_e(&try_get_fspan(&span, &lhs), "pure: expected an atom"))?,
              self.parse_expr(&span, rhs)?))
          }
        }
        Err(ElabError::new_e(&span, "'pure' syntax error"))
      }).collect::<Result<_>>()?, last))
    } else { Err(ElabError::new_e(base, "expected 1 argument")) }
  }

  /// Parse an MM0 expression. This is a sort of hybrid of MMC and MM0 syntax because it is MM0 syntax
  /// in the term constructors with variables drawn from the MMC context. For example,
  /// `(begin {x := 1} {y := 2} (pure $ x + x = y $))` will work, where `+` and `=` are the MM0 term constructors
  /// `add` and `eq`, while `x` and `y` are program variables in the MMC context. (TODO: MMC antiquotation?)
  fn parse_mm0_expr(&mut self, base: &FileSpan, args: Vec<LispVal>,
  ) -> Result<Mm0Expr<Expr>> {
    struct Mm0<'a, C> {
      subst: Vec<Expr>,
      base: &'a FileSpan,
      vars: HashMap<AtomId, u32>,
      dummies: Vec<AtomId>,
      p: &'a Parser<'a, C>
    }
    impl<C> Mm0<'_, C> {
      fn list_opt(&mut self, e: &LispVal, head: AtomId, args: Option<Uncons>) -> Result<Option<Mm0ExprNode>> {
        let tid = self.p.fe.env.term(head).ok_or_else(|| ElabError::new_e(try_get_span(self.base, e),
          format!("term '{}' not declared", self.p.fe.to(&head))))?;
        let term = &self.p.fe.env.terms[tid];
        if args.as_ref().map_or(0, Uncons::len) != term.args.len() {
          return Err(ElabError::new_e(try_get_span(self.base, e),
            format!("expected {} arguments", term.args.len())));
        }
        Ok(if let Some(u) = args {
          let mut cnst = true;
          let mut vec = Vec::with_capacity(u.len());
          let len = self.dummies.len();
          for (e, (_, arg)) in u.zip(&*term.args) {
            match *arg {
              EType::Bound(_) => {
                let a = e.as_atom().ok_or_else(||
                  ElabError::new_e(try_get_span(self.base, &e), "expected an atom"))?;
                self.dummies.push(a);
                vec.push(Mm0ExprNode::Const(e))
              }
              EType::Reg(_, _) => {
                let n = self.node(e)?;
                cnst &= matches!(n, Mm0ExprNode::Const(_));
                vec.push(n)
              }
            }
          }
          self.dummies.truncate(len);
          if cnst {None} else {Some(Mm0ExprNode::Expr(tid, vec))}
        } else {None})
      }

      fn node_opt(&mut self, e: &LispVal) -> Result<Option<Mm0ExprNode>> {
        e.unwrapped(|r| Ok(if let LispKind::Atom(a) = *r {
          if self.dummies.contains(&a) {return Ok(None)}
          match self.vars.entry(a) {
            Entry::Occupied(entry) => Some(Mm0ExprNode::Var(*entry.get())),
            Entry::Vacant(entry) => {
              let name = self.p.as_symbol_ref(a);
              if let Some(v) = self.p.ba.get_var(name) {
                let n = self.subst.len().try_into().expect("overflow");
                entry.insert(n);
                self.subst.push(Spanned {span: try_get_fspan(self.base, e), k: ExprKind::Var(v)});
                Some(Mm0ExprNode::Var(n))
              } else {
                self.list_opt(e, a, None)?
              }
            }
          }
        } else {
          let mut u = Uncons::from(e.clone());
          let head = u.next().ok_or_else(|| ElabError::new_e(try_get_span(self.base, e),
            format!("bad expression {}", self.p.fe.to(e))))?;
          let a = head.as_atom().ok_or_else(|| ElabError::new_e(try_get_span(self.base, &head),
            "expected an atom"))?;
          self.list_opt(&head, a, Some(u))?
        }))
      }

      #[allow(clippy::unnecessary_lazy_evaluations)]
      fn node(&mut self, e: LispVal) -> Result<Mm0ExprNode> {
        Ok(self.node_opt(&e)?.unwrap_or_else(|| Mm0ExprNode::Const(e)))
      }
    }

    let (subst, e) = self.parse_pure_args(base, args)?;
    let mut vars = HashMap::new();
    let subst = subst.into_iter().enumerate().map(|(i, (a, e))| {
      vars.insert(a, i.try_into().expect("overflow"));
      e
    }).collect();
    let mut mm0 = Mm0 {
      subst,
      base,
      vars,
      dummies: vec![],
      p: self,
    };
    let expr = mm0.node(e)?;
    Ok(Mm0Expr {subst: mm0.subst, expr: self.lambdas.push(expr)})
  }
}
