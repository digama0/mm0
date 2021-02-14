//! Types used in the stages of the compiler.

pub mod parse;
pub mod ast;
pub mod entity;
pub mod ty;
pub mod hir;
pub mod pir;

use std::{rc::Rc, collections::HashMap};
use crate::elab::{environment::{AtomId, Environment, Remap, Remapper, TermId}, lisp::{LispVal, Syntax, print::{EnvDisplay, FormatEnv}}};
use crate::util::FileSpan;

/// A variable ID. These are local to a given declaration (function, constant, global),
/// but are not de Bruijn variables - they are unique identifiers within the declaration.
#[derive(Clone, Copy, Debug, Default, DeepSizeOf, PartialEq, Eq, Hash)]
pub struct VarId(pub u32);

impl std::fmt::Display for VarId {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "_{}", self.0)
  }
}

impl Remap for VarId {
  type Target = Self;
  fn remap(&self, _: &mut Remapper) -> Self { *self }
}

/// A spanned expression.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct Spanned<T> {
  /// The span of the expression
  pub span: FileSpan,
  /// The data (the `k` stands for `kind` because it's often a `*Kind` enum
  /// but it can be anything).
  pub k: T,
}

impl<T: Remap> Remap for Spanned<T> {
  type Target = Spanned<T::Target>;
  fn remap(&self, r: &mut Remapper) -> Spanned<T::Target> {
    Spanned {span: self.span.clone(), k: self.k.remap(r)}
  }
}

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
    }

    impl Keyword {
      #[must_use] fn from_str(s: &str) -> Option<Self> {
        match s {
          $($e => Some(Self::$x),)*
          _ => None
        }
      }

      /// Get the MMC keyword corresponding to a lisp [`Syntax`].
      #[must_use] pub fn from_syntax(s: Syntax) -> Option<Self> {
        SYNTAX_MAP[s as usize]
      }
    }

    impl Environment {
      /// Make the initial MMC keyword map in the given environment.
      #[allow(clippy::string_lit_as_bytes)]
      pub fn make_keywords(&mut self) -> HashMap<AtomId, Keyword> {
        let mut atoms = HashMap::new();
        $(if Syntax::from_str($e).is_none() {
          atoms.insert(self.get_atom($e.as_bytes()), Keyword::$x);
        })*
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

/// Possible sizes for integer operations and types.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Size {
  /// Unbounded size. Used for `nat` and `int`. (These types are only legal for
  /// ghost variables, but they are also used to indicate "correct to an unbounded model"
  /// for operations like [`Unop::BitNot`] when it makes sense. We do not actually support
  /// bignum compilation.)
  Inf,
  /// 8 bits, or 1 byte. Used for `u8` and `i8`.
  S8,
  /// 16 bits, or 2 bytes. Used for `u16` and `i16`.
  S16,
  /// 32 bits, or 4 bytes. Used for `u32` and `i32`.
  S32,
  /// 64 bits, or 8 bytes. Used for `u64` and `i64`.
  S64,
}
crate::deep_size_0!(Size);

impl Default for Size {
  fn default() -> Self { Self::Inf }
}

/// (Elaborated) unary operations.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Unop {
  /// Integer negation
  Neg,
  /// Logical (boolean) NOT
  Not,
  /// Bitwise NOT. For fixed size this is the operation `2^n - x - 1`, and
  /// for infinite size this is `-x - 1`. Note that signed NOT always uses
  /// [`Size::Inf`].
  ///
  /// Infinite size is also the default value before type checking.
  BitNot(Size),
}
crate::deep_size_0!(Unop);

impl Unop {
  /// Return a string representation of the [`Unop`].
  #[must_use] pub fn to_str(self) -> &'static str {
    match self {
      Unop::Neg => "-",
      Unop::Not => "not",
      Unop::BitNot(_) => "bnot",
    }
  }
}

impl std::fmt::Display for Unop {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.to_str().fmt(f)
  }
}

/// (Elaborated) binary operations.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Binop {
  /// Integer addition
  Add,
  /// Integer multiplication
  Mul,
  /// Integer subtraction
  Sub,
  /// Logical (boolean) AND
  And,
  /// Logical (boolean) OR
  Or,
  /// Bitwise AND, for signed or unsigned integers of any size
  BitAnd,
  /// Bitwise OR, for signed or unsigned integers of any size
  BitOr,
  /// Bitwise XOR, for signed or unsigned integers of any size
  BitXor,
  /// Shift left
  Shl,
  /// Shift right (arithmetic)
  Shr,
  /// Less than, for signed or unsigned integers of any size
  Lt,
  /// Less than or equal, for signed or unsigned integers of any size
  Le,
  /// Equal, for signed or unsigned integers of any size
  Eq,
  /// Not equal, for signed or unsigned integers of any size
  Ne,
}
crate::deep_size_0!(Binop);

impl Binop {
  /// Return a string representation of the [`Binop`].
  #[must_use] pub fn to_str(self) -> &'static str {
    match self {
      Binop::Add => "+",
      Binop::Mul => "*",
      Binop::Sub => "-",
      Binop::And => "and",
      Binop::Or => "or",
      Binop::BitAnd => "band",
      Binop::BitOr => "bor",
      Binop::BitXor => "bxor",
      Binop::Shl => "shl",
      Binop::Shr => "shr",
      Binop::Lt => "<",
      Binop::Le => "<=",
      Binop::Eq => "=",
      Binop::Ne => "!=",
    }
  }
}

impl std::fmt::Display for Binop {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.to_str().fmt(f)
  }
}

/// A field accessor.
#[derive(Copy, Clone, Debug)]
pub enum FieldName {
  /// A numbered field access like `x.1`.
  Number(u32),
  /// A named field access like `x.foo`.
  Named(AtomId),
}
crate::deep_size_0!(FieldName);

/// An embedded MM0 expression inside MMC. This representation is designed to make it easy
/// to produce substitutions of the free variables.
#[derive(Debug, DeepSizeOf)]
pub enum Mm0ExprNode {
  /// A constant expression, containing no free variables,
  /// or a dummy variable that will not be substituted.
  Const(LispVal),
  /// A free variable. This is an index into the [`Mm0Expr::subst`] array.
  Var(u32),
  /// A term constructor, where at least one subexpression is non-constant
  /// (else we would use [`Const`](Self::Const)).
  Expr(TermId, Vec<Mm0ExprNode>),
}

impl Remap for Mm0ExprNode {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      Mm0ExprNode::Const(c) => Mm0ExprNode::Const(c.remap(r)),
      &Mm0ExprNode::Var(i) => Mm0ExprNode::Var(i),
      Mm0ExprNode::Expr(t, es) => Mm0ExprNode::Expr(t.remap(r), es.remap(r)),
    }
  }
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

/// An embedded MM0 expression inside MMC. All free variables have been replaced by indexes,
/// with `subst` holding the internal names of these variables.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct Mm0Expr<T> {
  /// The mapping from indexes in the `expr` to internal names.
  /// (The user-facing names have been erased.)
  pub subst: Vec<T>,
  /// The root node of the expression.
  pub expr: Rc<Mm0ExprNode>,
}

impl<T: std::hash::Hash> std::hash::Hash for Mm0Expr<T> {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    self.subst.hash(state);
    Rc::as_ptr(&self.expr).hash(state);
  }
}

impl<T: PartialEq> PartialEq for Mm0Expr<T> {
  fn eq(&self, other: &Self) -> bool {
    self.subst == other.subst && Rc::ptr_eq(&self.expr, &other.expr)
  }
}
impl<T: Eq> Eq for Mm0Expr<T> {}

impl<T: Remap> Remap for Mm0Expr<T> {
  type Target = Mm0Expr<T::Target>;
  fn remap(&self, r: &mut Remapper) -> Mm0Expr<T::Target> {
    Mm0Expr {subst: self.subst.remap(r), expr: self.expr.remap(r)}
  }
}

impl<T: EnvDisplay> EnvDisplay for Mm0Expr<T> {
  fn fmt(&self, fe: FormatEnv<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    Mm0ExprNodePrint(&self.subst, &self.expr).fmt(fe, f)
  }
}
