
//! Implements mm0/mm1 file AST components
//!
//! An [`Ast`] is the result of parsing an mm0/mm1 file. The core of the AST is a
//! `Vec<Stmt>`, where a [`Stmt`] holds both the element's "data" as a [`StmtKind`],
//!  and the element's [`Span`].
//! The actual [`Ast`] type also contains data about the source file, any imports, and
//! any errors encountered during parsing.

use std::sync::Arc;
use std::fmt::{self, Display};
use num::BigUint;
use crate::lined_string::LinedString;
use crate::util::{Span, ArcString};
use crate::elab::environment::DocComment;
use super::ParseError;

bitflags! {
  /// Visibility and sort modifiers for Sort statements and Declarations.
  pub struct Modifiers: u8 {
    // Note: These particular values are important because they are used in the MMB format.

    /// The `pure` sort modifier, used to indicate that
    /// term constructors can not target this sort.
    const PURE = 1;
    /// The `strict` sort modifier, used to indicate that
    /// bound variables (in the sense of [`LocalKind::is_bound`]) of this sort are not allowed.
    const STRICT = 2;
    /// The `provable` sort modifier, used to indicate that this sort
    /// can appear as the sort of hypotheses and conclusions of
    /// `axiom` and `theorem` declarations.
    const PROVABLE = 4;
    /// The `free` sort modifier, used to indicate that
    /// dummy variables of this sort (in `def` and `theorem`) are not allowed.
    const FREE = 8;

    /// The `pub` visibility modifier, used on `theorem` to indicate that a theorem
    /// appears in the specification file (otherwise the theorem is only
    /// usable in the proof file).
    const PUB = 16;
    /// The `abstract` visibility modifier, used on `def` to indicate that
    /// the definition should not be supplied in the specification file.
    const ABSTRACT = 32;
    /// The `local` visibility modifier, the opposite of `pub` and used on
    /// `def`, because `def`s have default public visibility. A `local def`
    /// will not appear in the specification file at all.
    const LOCAL = 64;
  }
}
crate::deep_size_0!(Modifiers);

impl Modifiers {
  /// The null modifier set. Modifiers are represented as bitfields, so this is the same as `0`.
  pub const NONE: Modifiers = Self::empty();

  /// Construct a [`Modifiers`] from a byte.
  #[must_use] pub fn new(bits: u8) -> Self { Self {bits} }

  /// The set of all valid sort modifiers. One can check if a modifier set is valid for a sort
  /// using `sort_data().contains(m)`.
  #[must_use] pub fn sort_data() -> Modifiers {
    Modifiers::PURE | Modifiers::STRICT | Modifiers::PROVABLE | Modifiers::FREE
  }

  /// Returns true if this modifier set is valid for the given [`DeclKind`].
  /// - `term` and `axiom` don't allow any modifiers
  /// - `def` allows `abstract def`, `local def` and `def` (`abstract local` is not valid)
  /// - `theorem` allows `pub theorem` and `theorem`
  #[must_use] pub fn allowed_visibility(self, k: DeclKind) -> bool {
    match k {
      DeclKind::Term |
      DeclKind::Axiom => self.is_empty(),
      DeclKind::Def => self == Modifiers::ABSTRACT || self == Modifiers::LOCAL || self.is_empty(),
      DeclKind::Thm => self == Modifiers::PUB || self.is_empty(),
    }
  }

  /// Parses a string into a singleton [`Modifiers`], or [`NONE`](Self::NONE) if the string is not valid.
  #[must_use] pub fn from_name(s: &[u8]) -> Modifiers {
    match s {
      b"pure" => Modifiers::PURE,
      b"strict" => Modifiers::STRICT,
      b"provable" => Modifiers::PROVABLE,
      b"free" => Modifiers::FREE,
      b"pub" => Modifiers::PUB,
      b"abstract" => Modifiers::ABSTRACT,
      b"local" => Modifiers::LOCAL,
      _ => Modifiers::NONE
    }
  }
}

impl Display for Modifiers {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if self.contains(Modifiers::PURE) {write!(f, "pure ")?}
    if self.contains(Modifiers::STRICT) {write!(f, "strict ")?}
    if self.contains(Modifiers::PROVABLE) {write!(f, "provable ")?}
    if self.contains(Modifiers::FREE) {write!(f, "free ")?}
    if self.contains(Modifiers::PUB) {write!(f, "pub ")?}
    if self.contains(Modifiers::ABSTRACT) {write!(f, "abstract ")?}
    if self.contains(Modifiers::LOCAL) {write!(f, "local ")?}
    Ok(())
  }
}


/// User-supplied delimiter characters.
///
/// A delimiter-stmt with only one math string is parsed
/// as [`Delimiter::Both`]`(..)`, and the contents are put in the environment as both left and right
/// delimiters. delimiter-stmts with two math strings are parsed as [`Delimiter::LeftRight`]`(s1, s2)`.
///
#[derive(Clone, Debug, DeepSizeOf)]
pub enum Delimiter {
  /// A delimiter command `delimiter $ ( , + $;` becomes `Both([b'(', b',', b'+'])`.
  Both(Box<[u8]>),
  /// A delimiter command `delimiter $ ( , $ $ ) , $;` becomes `LeftRight([b'(', b','], [b')', b','])`.
  LeftRight(Box<[u8]>, Box<[u8]>),
}

/// A dollar-delimited formula: $ .. $.
/// `f.0` is the span of the entire formula including the delimiters, and
/// `f.inner()` is the span of the interior (excluding `$` but including any inner whitespace).
#[derive(Copy, Clone, Debug)]
pub struct Formula(pub Span);
crate::deep_size_0!(Formula);

impl Formula {
  /// Get the span of the interior of the formula (excluding `$` but including any inner whitespace).
  #[must_use] pub fn inner(&self) -> Span { (self.0.start + 1 .. self.0.end - 1).into() }
}

/// A constant literal, used in `notation` commands.
/// Information about constants can be found in the [notation grammar].
///
/// [notation grammar]: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#notations
#[derive(Copy, Clone, Debug)]
pub struct Const {
  /// The underlying formula (dollar delimited token)
  pub fmla: Formula,
  /// The span of the constant with whitespace trimmed
  /// (which should itself contain no embedded whitespace)
  pub trim: Span,
}
crate::deep_size_0!(Const);

/// Declarations; term, axiom, theorem, def. Part of a [`Decl`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DeclKind {
  /// A term constructor
  Term,
  /// An axiom declaration (assumed fact)
  Axiom,
  /// A theorem declaration (asserted fact,
  /// proven in the proof file for MM0 and inline for MM1)
  Thm,
  /// A definition (definition optional in MM0, required in MM1)
  Def,
}
crate::deep_size_0!(DeclKind);

/// The "kind" of a binder, denoted using braces vs parentheses on the binder,
/// as well as the prefix dot on dummies.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LocalKind {
  /// A bound variable like `{x: s}` denotes a variable that can be bound under quantifiers,
  /// or a first order variable. Bound variables cannot have dependencies.
  Bound,
  /// A regular variable, or second order variable, like `(ph: s)` or `(ph: s x y)`,
  /// denotes a variable that can be directly substituted for an expression.
  /// Regular variables cannot be bound under quantifiers, but can depend on previous
  /// bound variables (but not dummy variables).
  Reg,
  /// A dummy variable is denoted `(.x: s)` or `{.x: s}` (the enclosing binder type is
  /// ignored), and denotes a bound variable that is used only in the definition/proof ot
  /// the `def`/`theorem`.
  Dummy,
  /// An anonymous variable is denoted `(_: s)` or `{_: s}`, and is a regular variable
  /// (the enclosing binder is ignored). Anonymous variables cannot be referred to in the
  /// statement or proof. Binders declared using arrow syntax like `term foo: nat > nat;`
  /// are equivalent to `term foo (_: nat): nat;` and also declare anonymous variables.
  Anon,
}
crate::deep_size_0!(LocalKind);

impl LocalKind {
  /// Return true iff self is a bound variable, either [`Bound`](LocalKind::Bound)
  /// for inputs to the function, or [`Dummy`](LocalKind::Dummy) for variables local to the
  /// def/proof.
  #[must_use] pub fn is_bound(self) -> bool {
    match self {
      LocalKind::Bound | LocalKind::Dummy => true,
      LocalKind::Reg | LocalKind::Anon => false,
    }
  }
}

/// A type with zero or more dependencies. IE `wff` in `(ph: wff)`, or `wff x y` in `(ph: wff x y)`
#[derive(Clone, Debug, DeepSizeOf)]
pub struct DepType {
  /// The span of the sort part. That is, `"wff"` in `wff x y`.
  pub sort: Span,
  /// The span of the list of dependencies. That is, `["x", "y"]` in `wff x y`.
  pub deps: Box<[Span]>,
}

impl DepType {
  /// The span of the declaraion, from the start of the sort until
  /// the end of the last dependency.
  #[must_use] pub fn span(&self) -> Span {
    (self.sort.start..self.deps.last().unwrap_or(&self.sort).end).into()
  }
}

/// Types can either be a [`DepType`] or a dollar-delimited formula.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum Type {
  /// A bound or regular variable has a type that is a sort name
  /// with possible dependencies like `foo x y`.
  DepType(DepType),
  /// A hypothesis has a type that is a formula like `$ 2 + 2 = x $`.
  Formula(Formula),
}

impl Type {
  /// Get the span of a type.
  #[must_use] pub fn span(&self) -> Span {
    match self {
      Type::DepType(d) => d.span(),
      Type::Formula(f) => f.0
    }
  }
}

/// A list of variables with a type or formula annotation.
/// A binder exists in a binder group such as `(ph ps: wff)` or `{x y .z: set}`,
/// and `bi.span` is the span of the enclosing binder group.
/// Detailed information about binder syntax can be found in the [declaration grammar].
///
/// [declaration grammar]: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#declarations
#[derive(Clone, Debug, DeepSizeOf)]
pub struct Binder {
  /// The span of the enclosing binder group. For example both `ph` and `ps` have
  /// span `"(ph ps: wff)"` for  `(ph ps: wff)`. In an arrow sequence like `wff x > nat`,
  /// the span is `"wff x"` for the implicit `(_: wff x)` binder.
  pub span: Span,
  /// The span of the local avariable, for example `"ph"` in `(ph ps: wff)` and `"x"` in `{.x: nat}`.
  /// It is [`None`] for anonymous binders declared using arrow notation.
  pub local: Option<Span>,
  /// The kind of binder being declared. See [`LocalKind`] for information on the different
  /// binder kinds.
  pub kind: LocalKind,
  /// The type of the binder, a [`DepType`] for variables and a [`Formula`] for hypotheses.
  /// The type is [`None`] for variables that are being type-inferred (not valid in MM0 mode).
  pub ty: Option<Type>,
}

/// A lisp s-expression. See [`SExprKind`] for the different kinds of s-expression.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct SExpr {
  /// The span enclosing the entire expression. For expressions using `@`
  /// like `(f @ g x)` (which is parsed as `(f (g x))`), the `(g x)` expression
  /// is given the sub-span `@ g x)` of the input.
  pub span: Span,
  /// The expression kind and associated data, i.e. string, atom, list, etc.
  pub k: SExprKind,
}

/// Lisp atom kind.
///
/// The [`Ident`](Atom::Ident) atom indicates that the atom text is the span,
/// and the [`Quote`](Atom::Quote), [`Unquote`](Atom::Unquote) and [`Nfx`](Atom::Nfx)
/// atoms have data `quote`, `unquote` and `:nfx` respectively,
/// but the span does not contain this text because
/// these atoms are created implicitly via keywords like `'`.
#[derive(Copy, Clone, Debug)]
pub enum Atom {
  /// This indicates that the atom text is a span from the input, i.e. the user wrote
  /// `foo` and this is interpreted as an atom `"foo"`.
  Ident,
  /// This is an atom with the text `quote` that was generated from a
  /// literal `'` in the input.
  Quote,
  /// This is an atom with the text `unquote` that was generated from a
  /// literal `,` in the input.
  Unquote,
  /// This is an atom with the text `:nfx` that was generated by a malformed curly list
  /// (see [`curly_transform`]).
  Nfx,
}
crate::deep_size_0!(Atom);

/// The data portion of an s-expression.
///
/// Notable additions over normal lisp/scheme are
/// [`Formula`], for MM0 formulas, and the notations `{x op y}` for `(op x y)` and
/// `(f x @ g @ h y)` for `(f x (g (h y)))` (not represented in this data structure
/// because the transformation applies during parsing).
/// See also the [syntax forms] section of `mm1.md` for more information on MM1 lisp syntax.
///
/// [syntax forms]: https://github.com/digama0/mm0/blob/master/mm0-hs/mm1.md#syntax-forms
#[derive(Clone, Debug, DeepSizeOf)]
pub enum SExprKind {
  /// An atom, an unquoted string of identifier characters like `foo`. These are usually
  /// interpreted as variable accesses or variable declarations, unless they appear inside
  /// a quoted context, in which case they evaluate to themselves as a [`LispKind::Atom`].
  ///
  /// [`LispKind::Atom`]: crate::elab::lisp::LispKind::Atom
  Atom(Atom),
  /// A proper list, like `(a b c)`. This is normally interpreted as a function application,
  /// unless the head of the list is a [`Syntax`], in which case it has special semantics.
  /// The empty list `()` evaluates to itself, and when quoted a list evaluates to a
  /// [`LispKind::List`] of its contents.
  ///
  /// [`Syntax`]: crate::elab::lisp::Syntax
  /// [`LispKind::List`]: crate::elab::lisp::LispKind::List
  List(Vec<SExpr>),
  /// A dotted list, like `(a b c . d)`. (The dot must appear at the second to last
  /// position as in the example, but there may be one or more subexpressions before the
  /// dot.) Normally, a dotted list means nothing (it is an error to evaluate), but it
  /// can be quoted to construct improper lists, and it is also used in patterns and function
  /// argument signatures.
  DottedList(Vec<SExpr>, Box<SExpr>),
  /// An unsigned number literal like `12345` or `0xdeadbeef`. These parse into bignums;
  /// there is no fixed size integer type in MM1 lisp.
  Number(BigUint),
  /// A string literal like `"foo"`. Supports `\\`, `\n`, `\r`, and `\"` string escapes.
  String(ArcString),
  /// A boolean literal, `#t` or `#f`.
  Bool(bool),
  /// A documentation comment on another expression.
  DocComment(DocComment, Box<SExpr>),
  /// An undef literal `#undef`. (This is used as the return value of functions that don't
  /// return anything).
  Undef,
  /// An MM0 formula literal like `$ 2 + 2 $`. In both normal and quoted mode, this is parsed
  /// according to the current math parser. Formula literals can contain antiquotations
  /// to splice in lisp expressions.
  Formula(Formula),
}

/// Performs "curly transformation", turning `{x op y op z}` into `(op x y z)`.
///
/// A curly list is valid if
/// - it is a proper list, and
/// - it has at most two elements (in which case it is transformed to itself), or
/// - it has an odd number of elements and the elements at all odd numbered positions compare equal.
///   (in which case the element at position 1 is moved to the front, and the later
///   copies of it are removed).
///
/// Invalid curly lists like `{x op y op2 z}` are converted to `(:nfx x op y op2 z)`.
///
/// # Parameters
///
/// - `es`: The list of elements to transform, such as `[x, op, y, op, z]`
/// - `no_dot`: True if this is a proper list. A dotted list like `{x op y . z}` is not a
///   valid curly list, and is transformed to `(:nfx x op y . z)`.
/// - `eq`: An equality comparator for elements of the list.
/// - `nfx`: A constructor for the `:nfx` atom, in case this is not a valid curly list.
///
/// # Returns
///
/// Returns nothing, but modifies the input `es` to reorder the elements so that the
/// operation at odd positions comes first and the elements at even positions come later,
/// for example `[x, op, y, op, z]` becomes `[op, x, y, z]`.
pub fn curly_transform<T>(es: &mut Vec<T>, no_dot: bool, eq: impl Fn(&T, &T) -> bool, nfx: impl FnOnce() -> T) {
  let n = es.len();
  if n > 2 {
    let valid_curly = no_dot && n % 2 != 0 && {
      let e = &es[1];
      (3..n).step_by(2).all(|i| eq(&es[i], e))
    };
    if valid_curly {
      es.swap(0, 1);
      let mut from = 4;
      let mut to = 3;
      while from < n {
        es.swap(from, to);
        to += 1;
        from += 2;
      }
      es.truncate(to);
    } else {
      es.insert(0, nfx());
    }
  }
}

impl SExpr {
  /// Construct a [`SExprKind::Atom`] from an atom kind and a span.
  pub fn atom(span: impl Into<Span>, a: Atom) -> SExpr {
    SExpr {span: span.into(), k: SExprKind::Atom(a)}
  }

  /// Construct a [`SExprKind::List`] from a list of expressions and a span.
  pub fn list(span: impl Into<Span>, es: Vec<SExpr>) -> SExpr {
    SExpr {span: span.into(), k: SExprKind::List(es)}
  }

  /// Construct a (possibly) dotted list from a list of expressions and a
  /// possible final expression after the dot.
  /// (This is the same as [`list`](SExpr::list) if `dot` is [`None`].)
  /// If `dot` is already a list, it is normalized to a single [`SExprKind::DottedList`] node.
  pub fn dotted_list(span: impl Into<Span>, mut es: Vec<SExpr>, dot: Option<SExpr>) -> SExpr {
    match dot {
      None => Self::list(span, es),
      Some(e) => match e.k {
        SExprKind::DottedList(es2, e2) => {
          es.extend(es2);
          SExpr {span: span.into(), k: SExprKind::DottedList(es, e2)}
        }
        SExprKind::List(es2) => {
          es.extend(es2);
          SExpr::list(span, es)
        }
        _ => SExpr {span: span.into(), k: SExprKind::DottedList(es, Box::new(e))}
      }
    }
  }

  /// Construct a (possibly) curly list `{e1 e2 e3}`. The arguments are the same as [`dotted_list`],
  /// and if `curly` is `false` then this is the same as [`dotted_list`]. If `curly` is true,
  /// meaning that the list is enclosed by curly braces, then we use [`curly_transform`] with the
  /// given comparator to reorder the arguments.
  ///
  /// [`dotted_list`]: Self::dotted_list
  pub fn curly_list(span: Span, curly: bool, mut es: Vec<SExpr>, dot: Option<SExpr>,
    eq: impl Fn(&SExpr, &SExpr) -> bool
  ) -> SExpr {
    if curly {
      curly_transform(&mut es, dot.is_none(), eq,
        || SExpr::atom(span.start..=span.start, Atom::Nfx))
    }
    Self::dotted_list(span, es, dot)
  }
}

/// Holds a Declaration as a [`DeclKind`] with some extra data.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct Decl {
  /// The declaration modifiers: [`abstract`] or [`local`] for `def`,
  /// and [`pub`] for `theorem`.
  ///
  /// [`abstract`]: Modifiers::ABSTRACT
  /// [`local`]: Modifiers::LOCAL
  /// [`pub`]: Modifiers::PUB
  pub mods: Modifiers,
  /// The declaration kind: `axiom`, `term`, `def`, `theorem`.
  pub k: DeclKind,
  /// The span of the identifier being defined (the `foo` in `def foo ...`).
  pub id: Span,
  /// The list of binders
  pub bis: Vec<Binder>,
  /// The return type, or [`None`] for type-inferred (not valid in MM0 mode).
  pub ty: Option<Type>,
  /// The definition of the `def`, or the proof of the `theorem`, as an
  /// s-expression.
  pub val: Option<SExpr>,
}

/// A precedence literal, such as `123` or `max`. These are used in notations like
/// `notation add = ($+$:23)` or `infix add: $+$ prec 23;`.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Prec {
  /// A finite precedence, an unsigned integer like `23`.
  Prec(u32),
  /// The maximum precedence, the precedence class containing atomic literals
  /// and parentheses.
  Max,
}
crate::deep_size_0!(Prec);

impl fmt::Display for Prec {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      &Prec::Prec(p) => p.fmt(f),
      Prec::Max => "max".fmt(f)
    }
  }
}
impl fmt::Debug for Prec {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Display::fmt(self, f) }
}


/// A simple notation, one of `prefix`, `infixl`, and `infixr` (which have the same
/// grammar after the initial keyword).
#[derive(Copy, Clone, Debug, DeepSizeOf)]
pub enum SimpleNotaKind {
  /// The `prefix` keyword
  Prefix,
  /// The `infixl` or `infixr` keyword
  Infix { /** True for `infixr` */ right: bool },
}

/// Represents a notation item declared with the prefix, infixl, or infixr keywords. Notation
/// declared with the 'notation' keyword is represented by [`GenNota`]
#[derive(Copy, Clone, Debug, DeepSizeOf)]
pub struct SimpleNota {
  /// The initial notation keyword, one of `prefix`, `infixl`, or `infixr`.
  pub k: SimpleNotaKind,
  /// The span of the identifier, the `"foo"` in `infix foo: $++$ prec 25;`.
  pub id: Span,
  /// The constant, the `$++$` in `infix foo: $++$ prec 25;`.
  pub c: Const,
  /// The notation precedence level, the `25` in `infix foo: $++$ prec 25;`.
  pub prec: Prec,
}

/// A literal in a notation, either a constant with associated precedence, or a variable.
///
/// For example in `notation ab {x} (ph) = (${$:max) x ($|$:50) ph ($}$:0);` there
/// are 5 notation literals, `(${$:0)`, `x`, `($|$:50)`, `ph`, `($}$:0)`.
#[derive(Copy, Clone, Debug, DeepSizeOf)]
pub enum Literal {
  /// A constant with a precedence, such as `($|$:50)`.
  Const(Const, Prec),
  /// A variable denoting a place for a subexpression, such as `x`.
  Var(Span),
}

/// Represents a notation item declared with the `notation` keyword. Notation declared with
/// the `prefix`, `infixl`, and `infixr` keywords are represented by [`SimpleNota`].
#[derive(Clone, Debug, DeepSizeOf)]
pub struct GenNota {
  /// The span of the identifier, the `foo` in `notation foo ...`.
  pub id: Span,
  /// The binder list. The `notation` command mimics the `def` syntax, so it accepts
  /// binders in the same way, but these are only used in order to name the parameters
  /// for use in [`Literal::Var`].
  pub bis: Vec<Binder>,
  /// The return type. This is included for consistency with `def` but is unused.
  pub ty: Option<Type>,
  /// The list of notation literals.
  pub lits: Vec<Literal>,
  /// The optional notation precedence, needed for generalized infix notations like
  /// `x +[G] y`. This is the `50 lassoc` in `notation ... = ... : 50 lassoc;`.
  /// If provided, it is `Some((prec, right))` where `prec` is the precedence
  /// and `right` is true if it is right associative.
  pub prec: Option<(Prec, bool)>
}

/// A statement in the file. Every statement ends with a `;`, and an MM0/MM1 file
/// is a list of statements.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum StmtKind {
  /// A sort delaration like `pure sort foo;`.
  Sort(Span, Modifiers),
  /// A delaration of an `axiom`, `term`, `def`, or `theorem`.
  Decl(Decl),
  /// A `delimiter` delaration.
  Delimiter(Delimiter),
  /// A `prefix`, `infixl` or `infixr` delaration.
  SimpleNota(SimpleNota),
  /// A `coercion` declaration.
  Coercion {
    /// The name of the declaration, the `foo` in `coercion foo: s > t;`.
    id: Span,
    /// The source sort of the coercion, the `s` in `coercion foo: s > t;`.
    from: Span,
    /// The target sort of the coercion, the `t` in `coercion foo: s > t;`.
    to: Span
  },
  /// A `notation` declaration.
  Notation(GenNota),
  /// An `input` or `output` declaration, such as `output string: foo bar $ baz $;`.
  /// (These are parsed but not otherwise currently supported in MM1.)
  Inout {
    /// True if this is an `output` declaration.
    out: bool,
    /// The span for the output kind, `"string"` in `output string: ...`
    k: Span,
    /// The list of expressions to output
    hs: Vec<SExpr>
  },
  /// An annotation on another statement, like `@(foo) sort bar;`. The
  /// annotation is a lisp s-expression.
  Annot(SExpr, Box<Stmt>),
  /// A documentation comment on another statement.
  DocComment(DocComment, Box<Stmt>),
  /// A `do` block like `do { (print 1) };`. This allows the evaluation of lisp
  /// code, and definitions made in a `do` block populate the global context.
  Do(Vec<SExpr>),
  /// An `import` statement like `import "file.mm1";`. The span gives
  /// the string literal `"file.mm1"`, and the string is the result of parsing
  /// (after interpreting string escapes).
  Import(Span, Vec<u8>),
}

/// The elements of a parsed AST. [`StmtKind`] is the "data", with span providing
/// information about the item's location in the source file.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct Stmt {
  /// The span of the statement, from the beginning of the first keyword to
  /// the semicolon terminator (inclusive).
  pub span: Span,
  /// The statement kind and associated data
  pub k: StmtKind,
}

impl Stmt {
  /// Make a new [`Stmt`] from a [`Span`] and [`StmtKind`].
  #[must_use] pub fn new(span: Span, k: StmtKind) -> Self {
    Stmt { span, k }
  }
}


/// Contains the actual AST as a sequence of [`Stmt`]s, as well as import, source, and parse info.
#[derive(Debug, DeepSizeOf)]
pub struct Ast {
  /// The source [`LinedString`] for the file. This is needed in order to interpret all the
  /// [`Span`]s in the AST.
  pub source: Arc<LinedString>,
  /// The list of `import` statements in the file, giving the span of the string literal,
  /// and the parsed string
  pub imports: Vec<(Span, Vec<u8>)>,
  /// The list of statements.
  pub stmts: Vec<Stmt>,
  /// The list of parse errors resulting from the parse of the file.
  pub errors: Vec<ParseError>,
}

impl LinedString {
  /// Given an [`Atom`] and associated [`Span`], such as those associated with
  /// [`SExprKind::Atom`], construct a string slice with the string contents
  /// of the atom.
  #[must_use] pub fn span_atom(&self, sp: Span, a: Atom) -> &[u8] {
    match a {
      Atom::Ident => &self[sp],
      Atom::Quote => b"quote",
      Atom::Unquote => b"unquote",
      Atom::Nfx => b":nfx",
    }
  }
}

impl Ast {
  /// Return the string corresponding to a span in this AST's source.
  #[must_use] pub fn span(&self, s: Span) -> &[u8] { &self.source[s] }
  /// Return the string corresponding to an atom.
  #[must_use] pub fn span_atom(&self, sp: Span, a: Atom) -> &[u8] { self.source.span_atom(sp, a) }
  /// Given a character index in the file, return `(idx, out)` where
  /// `idx` is the smallest index of a statement which does not end before the
  /// target position, and `out` is the character index of the end of `stmt[idx-1]`.
  ///
  /// (In other words, `out <= pos` is maximal such that `out` is the end of
  /// statement `idx-1`. This is a lower bound on the statements that are unaffected
  /// by a change at position `pos`.)
  #[must_use] pub fn last_checkpoint(&self, pos: usize) -> (usize, usize) {
    match self.stmts.binary_search_by_key(&pos, |stmt| stmt.span.end) {
      Ok(i) => (i+1, pos),
      Err(0) => (0, 0),
      Err(i) => (i, self.stmts[i-1].span.end)
    }
  }
}
