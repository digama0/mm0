//! The [`Environment`] contains all elaborated proof data, as well as the lisp global context.
//!
//! [`Environment`]: struct.Environment.html

use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::{concat, stringify};
use std::fmt;
use std::convert::TryInto;
use std::iter::FromIterator;
use std::rc::Rc;
use std::sync::Arc;
use std::fmt::Write;
use std::hash::Hash;
use std::collections::HashMap;
use super::{ElabError, BoxError, spans::Spans};
use crate::util::*;
use super::lisp::{LispVal, LispRemapper};
pub use crate::parser::ast::{Modifiers, Prec};

macro_rules! id_wrapper {
  ($id:ident: $ty:ty, $vec:ident) => {
    id_wrapper!($id: $ty, $vec,
      concat!("An index into a [`", stringify!($vec), "`](struct.", stringify!($vec), ".html)"));
  };
  ($id:ident: $ty:ty, $vec:ident, $svec:expr) => {
    #[doc=$svec]
    #[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Default)]
    pub struct $id(pub $ty);

    impl fmt::Debug for $id {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
    }

    /// A vector wrapper with a strongly typed index interface.
    #[derive(Clone)]
    pub struct $vec<T>(pub Vec<T>);

    #[allow(dead_code)]
    impl<T> $vec<T> {
      pub fn get(&self, i: $id) -> Option<&T> { self.0.get(i.0 as usize) }
      pub fn get_mut(&mut self, i: $id) -> Option<&mut T> { self.0.get_mut(i.0 as usize) }
    }
    impl<T> Default for $vec<T> {
      fn default() -> $vec<T> { $vec(Vec::new()) }
    }
    impl<T> Index<$id> for $vec<T> {
      type Output = T;
      fn index(&self, i: $id) -> &T { &self.0[i.0 as usize] }
    }
    impl<T> IndexMut<$id> for $vec<T> {
      fn index_mut(&mut self, i: $id) -> &mut T { &mut self.0[i.0 as usize] }
    }
    impl<T> Deref for $vec<T> {
      type Target = Vec<T>;
      fn deref(&self) -> &Vec<T> { &self.0 }
    }
    impl<T> DerefMut for $vec<T> {
      fn deref_mut(&mut self) -> &mut Vec<T> { &mut self.0 }
    }
    impl<T> FromIterator<T> for $vec<T> {
      fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self { $vec(Vec::from_iter(iter)) }
    }
  };
}

id_wrapper!(SortID: u8, SortVec);
id_wrapper!(TermID: u32, TermVec);
id_wrapper!(ThmID: u32, ThmVec);
id_wrapper!(AtomID: u32, AtomVec);

/// The information associated to a defined `Sort`.
#[derive(Clone)]
pub struct Sort {
  /// The sort's name, as an atom.
  pub atom: AtomID,
  /// The sort's name, as a string. (This is a shortcut; you can also look up the atom in
  /// [Environment.data](struct.Environment.html#structfield.data) and get the name from there.)
  pub name: ArcString,
  /// The span for the name of the sort. This is `"foo"` in the statement `sort foo;`.
  pub span: FileSpan,
  /// The span for the entire declaration creating the sort. This is `"sort foo;"`
  /// in the statement `sort foo;` (not including any characters after the semicolon). The file
  /// is the same as `span`.
  pub full: Span,
  /// The sort modifiers. Any subset of [`PURE`], [`STRICT`], [`PROVABLE`], [`FREE`]. The other
  /// modifiers are not valid.
  ///
  /// [`PURE`]: ../../parser/ast/struct.Modifiers.html#associatedconstant.PURE
  /// [`STRICT`]: ../../parser/ast/struct.Modifiers.html#associatedconstant.STRICT
  /// [`PROVABLE`]: ../../parser/ast/struct.Modifiers.html#associatedconstant.PROVABLE
  /// [`FREE`]: ../../parser/ast/struct.Modifiers.html#associatedconstant.FREE
  pub mods: Modifiers,
}

/// The type of a variable in the binder list of an `axiom`/`term`/`def`/`theorem`.
/// The variables themselves are not named because their names are derived from their
/// positions in the binder list (i.e. `{v0 : s} (v1 : t v0) (v2 : t)`)
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Type {
  /// A bound variable `{x : s}`, where `s` is the provided `SortID`.
  Bound(SortID),
  /// A regular variable `(ph : s x y z)`, where `s` is the provided `SortID`.
  ///
  /// The `deps: u64` field encodes the dependencies of the variable, where the nth bit
  /// set means that this variable depends on the nth bound variable
  /// (**not** variable number `n`!).
  ///
  /// For example, given `{v0 v1: s} (v2: s) {v3 v4: s} (v5: s v0 v1 v4)`,
  /// the `deps` field for `v5` would contain `0b1011` because the bound variables
  /// are `v0, v1, v3, v4` and it has dependencies on the variables at positions 0,1,3
  /// in this list.
  Reg(SortID, u64),
}

impl Type {
  /// The sort of a type.
  pub fn sort(self) -> SortID {
    match self {
      Type::Bound(s) => s,
      Type::Reg(s, _) => s,
    }
  }
  /// True if the type is a bound variable.
  pub fn bound(self) -> bool {
    match self {
      Type::Bound(_) => true,
      _ => false,
    }
  }
}

/// An `ExprNode` is interpreted inside a context containing the `Vec<Type>`
/// args and the `Vec<ExprNode>` heap.
#[derive(Clone, Debug)]
pub enum ExprNode {
  /// `Ref(n)` is a reference to heap element `n` (the first `args.len()` of them are the variables)
  Ref(usize),
  /// `Dummy(s, sort)` is a fresh dummy variable `s` with sort `sort`
  Dummy(AtomID, SortID),
  /// `App(t, nodes)` is an application of term constructor `t` to subterms
  App(TermID, Vec<ExprNode>),
}

/// The `Expr` type stores expression dags using a local context of expression nodes
/// and a final expression. See [`ExprNode`] for explanation of the variants.
///
/// [`ExprNode`]: enum.ExprNode.html
#[derive(Clone, Debug)]
pub struct Expr {
  /// The heap, which is used for subexpressions that appear multiple times.
  /// The first `args.len()` elements of the heap are fixed to the variables.
  pub heap: Vec<ExprNode>,
  /// The target expression.
  pub head: ExprNode,
}

/// The data associated to a `term` or `def` declaration.
#[derive(Clone, Debug)]
pub struct Term {
  /// The name of the term, as an atom.
  pub atom: AtomID,
  /// The span around the name of the term. This is the `"foo"` in `def foo ...;`
  pub span: FileSpan,
  /// The modifiers for the term. For `def`, the allowed modifiers are
  /// [`LOCAL`] and [`ABSTRACT`], and for `term` no modifiers are permitted.
  ///
  /// [`LOCAL`]: ../../parser/ast/struct.Modifiers.html#associatedconstant.LOCAL
  /// [`ABSTRACT`]: ../../parser/ast/struct.Modifiers.html#associatedconstant.ABSTRACT
  pub vis: Modifiers,
  /// The span around the entire declaration for the term, from the first modifier
  /// to the semicolon. The file is the same as in `span`.
  pub full: Span,
  /// The list of argument binders. The names of the variables are not used except for
  /// pretty printing and conversion back to s-exprs. (A `None` variable is represented
  /// as `_` and cannot be referred to.)
  pub args: Vec<(Option<AtomID>, Type)>,
  /// The return sort and dependencies of the term constructor. See [`Type::Reg`] for
  /// the interpretation of the dependencies.
  ///
  /// [`Type::Reg`]: enum.Type.html#variant.Reg
  pub ret: (SortID, u64),
  /// The definition of the expression:
  ///
  /// - `None`: This is a `term`, which has no definition
  /// - `Some(None)`: This is an abstract `def` or a `def` missing a definition
  /// - `Some(Some(e))`: This is a `def` which is defined to equal `e`
  pub val: Option<Option<Expr>>,
}

/// A `ProofNode` is a stored proof term. This is an extension of [`ExprNode`] with
/// more constructors, so a `ProofNode` can represent an expr, a proof, or a conversion,
/// and the typing determines which. A `ProofNode` is interpreted in a context of
/// variables `Vec<Type>`, and a heap `Vec<ProofNode>`.
#[derive(Clone, Debug)]
pub enum ProofNode {
  /// `Ref(n)` is a reference to heap element `n` (the first `args.len()` of them are the variables).
  /// This could be an expr, proof, or conv depending on what is referenced.
  Ref(usize),
  /// `Dummy(s, sort)` is a fresh dummy variable `s` with sort `sort`
  Dummy(AtomID, SortID),
  /// `Term {term, args}` is an application of term constructor `term` to subterms
  Term { term: TermID, args: Box<[ProofNode]> },
  /// `Hyp(i, e)` is hypothesis `i` (`hyps[i]` will be a reference to element),
  /// which is a proof of `|- e`.
  Hyp(usize, Box<ProofNode>),
  /// `Thm {thm, args, res}` is a proof of `|- res` by applying theorem `thm` to arguments
  /// `args`. `args` is a list of length `thm.args.len() + thm.hyps.len()` containing the
  /// substitution, followed by the hypothesis subproofs, and it is required that `res`
  /// and the subproofs be the result of substitution of the theorem conclusion and hypotheses
  /// under the substitution.
  Thm { thm: ThmID, args: Box<[ProofNode]>, res: Box<ProofNode> },
  /// `Conv(tgt, conv, proof)` is a proof of `|- tgt` if `proof: src` and `conv: tgt = src`.
  Conv(Box<(ProofNode, ProofNode, ProofNode)>),
  /// `Refl(e): e = e`
  Refl(Box<ProofNode>),
  /// `Refl(p): e2 = e1` if `p: e1 = e2`
  Sym(Box<ProofNode>),
  /// `Cong {term, args}: term a1 ... an = term b1 ... bn` if `args[i]: ai = bi`
  Cong { term: TermID, args: Box<[ProofNode]> },
  /// `Unfold {term, args, res: (lhs, sub_lhs, p)}` is a proof of `lhs = rhs` if
  /// `lhs` is `term args` and `term` is a definition and `sub_lhs` is the result of
  /// substituting `args` into the definition of `term`, and `p: sub_lhs = rhs`
  Unfold { term: TermID, args: Box<[ProofNode]>, res: Box<(ProofNode, ProofNode, ProofNode)> },
}

impl From<&ExprNode> for ProofNode {
  fn from(e: &ExprNode) -> ProofNode {
    match e {
      &ExprNode::Ref(n) => ProofNode::Ref(n),
      &ExprNode::Dummy(a, s) => ProofNode::Dummy(a, s),
      &ExprNode::App(term, ref es) => ProofNode::Term {
        term, args: es.iter().map(|e| e.into()).collect()
      }
    }
  }
}
/// The `Proof` type stores proof term dags using a local context of proof nodes
/// and a final proof. See [`ProofNode`] for explanation of the variants.
///
/// [`ProofNode`]: enum.ProofNode.html
#[derive(Clone, Debug)]
pub struct Proof {
  /// The heap, which is used for subexpressions that appear multiple times.
  /// The first `args.len()` elements of the heap are fixed to the variables.
  pub heap: Vec<ProofNode>,
  /// The hypotheses, where `hyps[i]` points to `Hyp(i, e)`. Because these terms
  /// are deduplicated with everything else, the `Hyp` itself will probably be
  /// on the heap (unless it is never used), and then a `Ref` will be stored
  /// in the `hyps` array.
  pub hyps: Vec<ProofNode>,
  /// The target proof term.
  pub head: ProofNode,
}

/// The data associated to an `axiom` or `theorem` declaration.
#[derive(Clone, Debug)]
pub struct Thm {
  /// The name of the theorem, as an atom.
  pub atom: AtomID,
  /// The span around the name of the theorem. This is the `"foo"` in `theorem foo ...;`
  pub span: FileSpan,
  /// The modifiers for the term. For `theorem`, the only allowed modifier is
  /// [`PUB`], and for `term` no modifiers are permitted.
  ///
  /// [`PUB`]: ../../parser/ast/struct.Modifiers.html#associatedconstant.PUB
  pub vis: Modifiers,
  /// The span around the entire declaration for the theorem, from the first modifier
  /// to the semicolon. The file is the same as in `span`.
  pub full: Span,
  /// The list of argument binders. The names of the variables are not used except for
  /// pretty printing and conversion back to s-exprs. (A `None` variable is represented
  /// as `_` and cannot be referred to.)
  pub args: Vec<(Option<AtomID>, Type)>,
  /// The heap used as the context for the `hyps` and `ret`.
  pub heap: Vec<ExprNode>,
  /// The expressions for the hypotheses (and their names, which are not used except
  /// in pretty printing and conversion back to s-exprs).
  pub hyps: Vec<(Option<AtomID>, ExprNode)>,
  /// The expression for the conclusion of the theorem.
  pub ret: ExprNode,
  /// The proof of the theorem:
  ///
  /// - `None`: This is an `axiom`, which has no proof
  /// - `Some(None)`: This is a `theorem` with a missing or malformed proof
  /// - `Some(Some(p))`: This is a `theorem` which has proof `p`
  ///
  /// **Note**: The [`Proof`] has its own `heap` and `hyps`, separate from the
  /// `heap` and `hyps` in this structure. They are required to be equivalent, but the
  /// indexing can be different between them, and the indexes in the proof are only
  /// valid with the `heap` in the proof.
  ///
  /// [`Proof`]: struct.Proof.html
  pub proof: Option<Option<Proof>>,
}

/// A global order on sorts, declarations ([`Term`] and [`Thm`]), and lisp
/// global definitions based on declaration order.
///
/// [`Term`]: struct.Term.html
/// [`Thm`]: struct.Thm.html
#[derive(Copy, Clone)]
pub enum StmtTrace {
  Sort(AtomID),
  Decl(AtomID),
  Global(AtomID),
}

impl StmtTrace {
  /// The name of a sort, term, or lisp def in the global list.
  pub fn atom(&self) -> AtomID {
    match self {
      &StmtTrace::Sort(a) => a,
      &StmtTrace::Decl(a) => a,
      &StmtTrace::Global(a) => a,
    }
  }
}

/// A declaration is either a [`Term`] or a [`Thm`]. This is done because in MM1
/// Terms and Thms share a namespace (although they are put in separate number-spaces
/// for compilation to MM0).
///
/// [`Term`]: struct.Term.html
/// [`Thm`]: struct.Thm.html
#[derive(Copy, Clone, Debug)]
pub enum DeclKey {
  Term(TermID),
  Thm(ThmID),
}

/// A `Literal` is an element in a processed `notation` declaration. It is either a
/// constant symbol, or a variable with associated parse precedence.
#[derive(Clone, Debug)]
pub enum Literal {
  /// `Var(i, p)` means that we should parse at precedence `p` at this position,
  /// and the resulting expression should be inserted as the `i`th subexpression of
  /// the term being constructed.
  Var(usize, Prec),
  /// `Const(s)` means that we should parse a token and match it against `s`.
  Const(ArcString),
}

/// The data associated to a `notation`, `infixl`, `infixr`, or `prefix` declaration.
#[derive(Clone, Debug)]
pub struct NotaInfo {
  /// The span around the name of the term. This is the `"foo"` in `notation foo ...;`
  pub span: FileSpan,
  /// The name of the term, as an atom.
  pub term: TermID,
  /// The number of arguments in the term. (This is a shortcut; you can also look up the term in
  /// [Environment.terms](struct.Environment.html#structfield.terms) and get the
  /// number of arguments as `args.len()`.)
  pub nargs: usize,
  /// The associativity of this term. This is always set, unless the notation begins and
  /// ends with a constant.
  pub rassoc: Option<bool>,
  /// The literals of the notation declaration. For a `notation` these are declared directly,
  /// but for a `prefix` or `infix`, the equivalent notation literals are generated.
  pub lits: Vec<Literal>,
}

/// A coercion between two sorts. These are interpreted in a context `c: s1 -> s2` where `s1` and
/// `s2` are known.
#[derive(Clone)]
pub enum Coe {
  /// This asserts `t` is a unary term constructor from `s1` to `s2`.
  One(FileSpan, TermID),
  /// `Trans(c1, m, c2)` asserts that `c1: s1 -> m` and `c2: m -> s2` (so we get a transitive
  /// coercion from `s1` to `s2`).
  Trans(Arc<Coe>, SortID, Arc<Coe>),
}

impl Coe {
  fn write_arrows_r(&self, sorts: &SortVec<Sort>, s: &mut String, related: &mut Vec<(FileSpan, BoxError)>,
      sl: SortID, sr: SortID) -> Result<(), std::fmt::Error> {
    match self {
      Coe::One(fsp, _) => {
        related.push((fsp.clone(), format!("{} -> {}", sorts[sl].name, sorts[sr].name).into()));
        write!(s, " -> {}", sorts[sr].name)
      }
      &Coe::Trans(ref c1, sm, ref c2) => {
        c1.write_arrows_r(sorts, s, related, sl, sm)?;
        c2.write_arrows_r(sorts, s, related, sm, sr)
      }
    }
  }

  fn write_arrows(&self, sorts: &SortVec<Sort>, s: &mut String, related: &mut Vec<(FileSpan, BoxError)>,
      s1: SortID, s2: SortID) -> Result<(), std::fmt::Error> {
    write!(s, "{}", sorts[s1].name)?;
    self.write_arrows_r(sorts, s, related, s1, s2)
  }
}

/// The (non-logical) data used by the dynamic parser to interpret formulas.
#[derive(Default, Clone)]
pub struct ParserEnv {
  /// A bitset of all left delimiters.
  pub delims_l: Delims,
  /// A bitset of all right delimiters.
  pub delims_r: Delims,
  /// A map of constants to their precedence, and the location of the first occurrence.
  /// (This way we can report an error with both locations on a precedence mismatch.)
  pub consts: HashMap<ArcString, (FileSpan, Prec)>,
  /// A map of precedences to their associativity, and the location of the first rule
  /// that forced this precedence to have this associativity.
  /// (This way we can report an error with both locations when the same precedence gets both associativities.)
  pub prec_assoc: HashMap<u32, (FileSpan, bool)>,
  /// A map of constants to their notation info, for prefixes (notations that start with a constant).
  pub prefixes: HashMap<ArcString, NotaInfo>,
  /// A map of constants to their notation info, for infixes (notations that start with a variable).
  pub infixes: HashMap<ArcString, NotaInfo>,
  /// A map of sort pairs `s1,s2` to the coercion `c: s1 -> s2`.
  pub coes: HashMap<SortID, HashMap<SortID, Arc<Coe>>>,
  /// A map of sorts `s` to some sort `t` such that `t` is provable and `c: s -> t` is in `coes`,
  /// if one exists.
  pub coe_prov: HashMap<SortID, SortID>,
  /// `decl_nota` maps `t` to `(has_coe, [(c, infx), ...])`, where `has_coe` is true if
  /// `t` has a coercion (in which case the sorts can be inferred from the type of `t`),
  /// and there is one `(c, infx)` for each constant `c` that maps to `t`, where `infx` is true
  /// if `c` is infix and false if `c` is prefix.
  pub decl_nota: HashMap<TermID, (bool, Vec<(ArcString, bool)>)>,
}

/// The data associated to an atom.
#[derive(Clone)]
pub struct AtomData {
  /// The string form of the atom.
  pub name: ArcString,
  /// The global lisp definition with this name, if one exists. The `Option<(FileSpan, Span)>`
  /// is `Some((span, full))` where `span` is the name of the definition and `full` is the
  /// entire definition body, or `None`.
  pub lisp: Option<(Option<(FileSpan, Span)>, LispVal)>,
  /// For global lisp definitions that have been deleted, we retain the location of the
  /// "undefinition" for go-to-definition queries.
  pub graveyard: Option<Box<(FileSpan, Span)>>,
  /// The sort with this name, if one exists.
  pub sort: Option<SortID>,
  /// The term or theorem with this name, if one exists.
  pub decl: Option<DeclKey>,
}

impl AtomData {
  fn new(name: ArcString) -> AtomData {
    AtomData {name, lisp: None, graveyard: None, sort: None, decl: None}
  }
}

/// The different kind of objects that can appear in a [`Spans`].
///
/// [`Spans`]: ../spans/struct.Spans.html
#[derive(Clone, Debug)]
pub enum ObjectKind {
  /// This is a sort; hovering yields `sort foo;` and go-to-definition works.
  /// This sort must actually exist in the `Environment` if is constructed
  Sort(SortID),
  /// This is a term/def; hovering yields `term foo ...;` and go-to-definition works.
  /// This term must actually exist in the `Environment` if is constructed
  Term(TermID, Span),
  /// This is a theorem/axiom; hovering yields `theorem foo ...;` and go-to-definition works
  /// This theorem must actually exist in the `Environment` if is constructed
  Thm(ThmID),
  /// This is a local variable; hovering yields `{x : s}` and go-to-definition takes you to the binder
  /// This should be a variable in the statement.
  Var(AtomID),
  /// This is a global lisp definition; hovering yields the lisp definition line and go-to-definition works.
  /// Either `lisp` or `graveyard` for the atom must be non-`None` if this is constructed
  Global(AtomID),
  /// This is an expression; hovering shows the type and go-to-definition goes to the head term definition
  Expr(LispVal),
  /// This is a proof; hovering shows the intermediate statement
  /// and go-to-definition goes to the head theorem definition
  Proof(LispVal),
  /// This is an import; hovering does nothing and go-to-definition goes to the file
  Import(FileRef),
}

/// The main environment struct, containing all permanent data to be exported from an MM1 file.
pub struct Environment {
  /// The sort map, which is a vector because sort names are allocated in order.
  pub sorts: SortVec<Sort>,
  /// The dynamic parser environment, used for parsing math expressions
  pub pe: ParserEnv,
  /// The term/def map, which is a vector because term names are allocated in order.
  pub terms: TermVec<Term>,
  /// The theorem/axiom map, which is a vector because theorem names are allocated in order.
  pub thms: ThmVec<Thm>,
  /// The map from strings to allocated atoms. This is used to ensure atom injectivity
  pub atoms: HashMap<ArcString, AtomID>,
  /// The atom map, which is a vector because atoms are allocated in order.
  pub data: AtomVec<AtomData>,
  /// The global statement order.
  pub stmts: Vec<StmtTrace>,
  /// The list of spans that have been collected in the current statement.
  pub spans: Vec<Spans<ObjectKind>>,
}

macro_rules! make_atoms {
  {consts $n:expr;} => {};
  {consts $n:expr; $x:ident $($xs:ident)*} => {
    pub const $x: AtomID = AtomID($n);
    make_atoms! {consts AtomID::$x.0+1; $($xs)*}
  };
  {$($x:ident: $e:expr,)*} => {
    impl AtomID {
      make_atoms! {consts 0; $($x)*}
    }

    impl Environment {
      pub fn new() -> Environment {
        let mut atoms = HashMap::new();
        let mut data = AtomVec::default();
        $({
          let s: ArcString = $e.into();
          atoms.insert(s.clone(), AtomID::$x);
          data.push(AtomData::new(s))
        })*
        Environment {
          atoms, data,
          sorts: Default::default(),
          pe: Default::default(),
          terms: Default::default(),
          thms: Default::default(),
          stmts: Default::default(),
          spans: Default::default(),
        }
      }
    }
  }
}

make_atoms! {
  UNDER: "_",
  BANG: "!",
  BANG2: "!!",
  VERB: ":verb",
  CONV: ":conv",
  SYM: ":sym",
  UNFOLD: ":unfold",
  LET: ":let",
  COLON: ":",
  QMARK: "?",
  REFINE_EXTRA_ARGS: "refine-extra-args",
  TERM: "term",
  DEF: "def",
  AXIOM: "axiom",
  THM: "theorem",
  PUB: "pub",
  ABSTRACT: "abstract",
  LOCAL: "local",
  SORRY: ":sorry",
  ERROR: "error",
  WARN: "warn",
  INFO: "info",
}

/// An implementation of a map `u8 -> bool` using a 32 byte array as a bitset.
#[derive(Default, Clone)]
pub struct Delims([u8; 32]);

impl Delims {
  /// Returns `self[i]`
  pub fn get(&self, c: u8) -> bool { self.0[(c >> 3) as usize] & (1 << (c & 7)) != 0 }
  /// Sets `self[i] = true`.
  pub fn set(&mut self, c: u8) { self.0[(c >> 3) as usize] |= 1 << (c & 7) }
  /// Sets `self[i] |= other[i]` for all `i`, that is, sets this bitset to the
  /// union of itself and `other`.
  pub fn merge(&mut self, other: &Self) {
    for i in 0..32 { self.0[i] |= other.0[i] }
  }
}

/// An auxiliary structure for performing [`Environment`] deep copies. This is needed
/// because `AtomID`s from other, previously elaborated files may not be consistent with
/// the current file, so we have to remap them to the current file's namespace
/// during import.
///
/// [`Environment`]: struct.Environment.html
#[derive(Default)]
struct Remapper {
  sort: HashMap<SortID, SortID>,
  term: HashMap<TermID, TermID>,
  thm: HashMap<ThmID, ThmID>,
  atom: HashMap<AtomID, AtomID>,
}

/// A trait for types that can be remapped. This is like `Clone` except it uses a `&mut R` as
/// auxiliary state.
pub trait Remap<R> {
  /// Create a copy of `self`, using `r` as auxiliary state.
  fn remap(&self, r: &mut R) -> Self;
}
impl Remap<Remapper> for SortID {
  fn remap(&self, r: &mut Remapper) -> Self { *r.sort.get(self).unwrap_or(self) }
}
impl Remap<Remapper> for TermID {
  fn remap(&self, r: &mut Remapper) -> Self { *r.term.get(self).unwrap_or(self) }
}
impl Remap<Remapper> for ThmID {
  fn remap(&self, r: &mut Remapper) -> Self { *r.thm.get(self).unwrap_or(self) }
}
impl Remap<Remapper> for AtomID {
  fn remap(&self, r: &mut Remapper) -> Self { *r.atom.get(self).unwrap_or(self) }
}
impl<R> Remap<R> for String {
  fn remap(&self, _: &mut R) -> Self { self.clone() }
}
impl<R, A: Remap<R>, B: Remap<R>> Remap<R> for (A, B) {
  fn remap(&self, r: &mut R) -> Self { (self.0.remap(r), self.1.remap(r)) }
}
impl<R, A: Remap<R>, B: Remap<R>, C: Remap<R>> Remap<R> for (A, B, C) {
  fn remap(&self, r: &mut R) -> Self { (self.0.remap(r), self.1.remap(r), self.2.remap(r)) }
}
impl<R, A: Remap<R>> Remap<R> for Option<A> {
  fn remap(&self, r: &mut R) -> Self { self.as_ref().map(|x| x.remap(r)) }
}
impl<R, A: Remap<R>> Remap<R> for Vec<A> {
  fn remap(&self, r: &mut R) -> Self { self.iter().map(|x| x.remap(r)).collect() }
}
impl<R, A: Remap<R>> Remap<R> for Box<A> {
  fn remap(&self, r: &mut R) -> Self { Box::new(self.deref().remap(r)) }
}
impl<R, A: Remap<R>> Remap<R> for Rc<A> {
  fn remap(&self, r: &mut R) -> Self { Rc::new(self.deref().remap(r)) }
}
impl<R, A: Remap<R>> Remap<R> for Arc<A> {
  fn remap(&self, r: &mut R) -> Self { Arc::new(self.deref().remap(r)) }
}
impl<R, A: Remap<R>> Remap<R> for Box<[A]> {
  fn remap(&self, r: &mut R) -> Self { self.iter().map(|v| v.remap(r)).collect() }
}
impl<R, A: Remap<R>> Remap<R> for Arc<[A]> {
  fn remap(&self, r: &mut R) -> Self { self.iter().map(|v| v.remap(r)).collect() }
}
impl Remap<Remapper> for Type {
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      Type::Bound(s) => Type::Bound(s.remap(r)),
      &Type::Reg(s, deps) => Type::Reg(s.remap(r), deps),
    }
  }
}
impl Remap<Remapper> for ExprNode {
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      &ExprNode::Ref(i) => ExprNode::Ref(i),
      ExprNode::Dummy(a, s) => ExprNode::Dummy(a.remap(r), s.remap(r)),
      ExprNode::App(t, es) => ExprNode::App(t.remap(r), es.remap(r)),
    }
  }
}
impl Remap<Remapper> for Expr {
  fn remap(&self, r: &mut Remapper) -> Self {
    Expr {
      heap: self.heap.remap(r),
      head: self.head.remap(r),
    }
  }
}
impl Remap<Remapper> for Term {
  fn remap(&self, r: &mut Remapper) -> Self {
    Term {
      atom: self.atom.remap(r),
      span: self.span.clone(),
      vis: self.vis,
      full: self.full,
      args: self.args.remap(r),
      ret: (self.ret.0.remap(r), self.ret.1),
      val: self.val.remap(r),
    }
  }
}
impl Remap<Remapper> for ProofNode {
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      &ProofNode::Ref(i) => ProofNode::Ref(i),
      ProofNode::Dummy(a, s) => ProofNode::Dummy(a.remap(r), s.remap(r)),
      ProofNode::Term {term, args} => ProofNode::Term { term: term.remap(r), args: args.remap(r) },
      &ProofNode::Hyp(i, ref e) => ProofNode::Hyp(i, e.remap(r)),
      ProofNode::Thm {thm, args, res} => ProofNode::Thm {
        thm: thm.remap(r), args: args.remap(r), res: res.remap(r) },
      ProofNode::Conv(p) => ProofNode::Conv(Box::new((p.0.remap(r), p.1.remap(r), p.2.remap(r)))),
      ProofNode::Refl(p) => ProofNode::Refl(p.remap(r)),
      ProofNode::Sym(p) => ProofNode::Sym(p.remap(r)),
      ProofNode::Cong {term, args} => ProofNode::Cong { term: term.remap(r), args: args.remap(r) },
      ProofNode::Unfold {term, args, res} => ProofNode::Unfold {
        term: term.remap(r), args: args.remap(r), res: res.remap(r) },
    }
  }
}
impl Remap<Remapper> for Proof {
  fn remap(&self, r: &mut Remapper) -> Self {
    Proof {
      heap: self.heap.remap(r),
      hyps: self.hyps.remap(r),
      head: self.head.remap(r),
    }
  }
}
impl Remap<Remapper> for Thm {
  fn remap(&self, r: &mut Remapper) -> Self {
    Thm {
      atom: self.atom.remap(r),
      span: self.span.clone(),
      vis: self.vis,
      full: self.full,
      args: self.args.remap(r),
      heap: self.heap.remap(r),
      hyps: self.hyps.remap(r),
      ret: self.ret.remap(r),
      proof: self.proof.remap(r),
    }
  }
}
impl Remap<Remapper> for NotaInfo {
  fn remap(&self, r: &mut Remapper) -> Self {
    NotaInfo {
      span: self.span.clone(),
      term: self.term.remap(r),
      nargs: self.nargs,
      rassoc: self.rassoc,
      lits: self.lits.clone(),
    }
  }
}
impl Remap<Remapper> for Coe {
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      Coe::One(sp, t) => Coe::One(sp.clone(), t.remap(r)),
      Coe::Trans(c1, s, c2) => Coe::Trans(c1.remap(r), s.remap(r), c2.remap(r)),
    }
  }
}

/// Several operations have an "incompatibility error" result, involving a conflict between
/// two definitions. This keeps just the locations of those definitions.
pub struct IncompatibleError {
  /// The first declaration in the conflict.
  pub decl1: FileSpan,
  /// The second declaration in the conflict.
  pub decl2: FileSpan,
}

impl ParserEnv {
  pub fn add_delimiters(&mut self, ls: &[u8], rs: &[u8]) {
    for &c in ls { self.delims_l.set(c) }
    for &c in rs { self.delims_r.set(c) }
  }

  pub fn add_const(&mut self, tk: ArcString, sp: FileSpan, p: Prec) -> Result<(), IncompatibleError> {
    if let Some((_, e)) = self.consts.try_insert(tk, (sp.clone(), p)) {
      if e.get().1 == p { return Ok(()) }
      Err(IncompatibleError { decl1: e.get().0.clone(), decl2: sp })
    } else { Ok(()) }
  }

  pub fn add_prec_assoc(&mut self, p: u32, sp: FileSpan, r: bool) -> Result<(), IncompatibleError> {
    if let Some((_, e)) = self.prec_assoc.try_insert(p, (sp.clone(), r)) {
      if e.get().1 == r { return Ok(()) }
      let (decl1, decl2) = if r { (e.get().0.clone(), sp) } else { (sp, e.get().0.clone()) };
      Err(IncompatibleError {decl1, decl2})
    } else { Ok(()) }
  }

  fn add_nota_info(m: &mut HashMap<ArcString, NotaInfo>, tk: ArcString, n: NotaInfo) -> Result<(), IncompatibleError> {
    if let Some((n, e)) = m.try_insert(tk.clone(), n) {
      if e.get().span == n.span { return Ok(()) }
      Err(IncompatibleError { decl1: e.get().span.clone(), decl2: n.span })
    } else { Ok(()) }
  }

  pub fn add_prefix(&mut self, tk: ArcString, n: NotaInfo) -> Result<(), IncompatibleError> {
    self.decl_nota.entry(n.term).or_default().1.push((tk.clone(), false));
    Self::add_nota_info(&mut self.prefixes, tk, n)
  }
  pub fn add_infix(&mut self, tk: ArcString, n: NotaInfo) -> Result<(), IncompatibleError> {
    self.decl_nota.entry(n.term).or_default().1.push((tk.clone(), true));
    Self::add_nota_info(&mut self.infixes, tk, n)
  }

  fn update_provs(&mut self, sp: Span, sorts: &SortVec<Sort>) -> Result<(), ElabError> {
    let mut provs = HashMap::new();
    for (&s1, m) in &self.coes {
      for (&s2, _) in m {
        if sorts[s2].mods.contains(Modifiers::PROVABLE) {
          if let Some(s2_) = provs.insert(s1, s2) {
            let mut err = "coercion diamond to provable detected:\n".to_owned();
            let mut related = Vec::new();
            self.coes[&s1][&s2].write_arrows(sorts, &mut err, &mut related, s1, s2).unwrap();
            err.push_str(" provable\n");
            self.coes[&s1][&s2_].write_arrows(sorts, &mut err, &mut related, s1, s2_).unwrap();
            err.push_str(" provable");
            return Err(ElabError::with_info(sp, err.into(), related))
          }
        }
      }
    }
    self.coe_prov = provs;
    Ok(())
  }

  fn add_coe_raw(&mut self, sp: Span, sorts: &SortVec<Sort>,
      s1: SortID, s2: SortID, fsp: FileSpan, t: TermID) -> Result<(), ElabError> {
    match self.coes.get(&s1).and_then(|m| m.get(&s2).map(|c| &**c)) {
      Some(&Coe::One(ref fsp2, t2)) if fsp2 == &fsp && t == t2 => return Ok(()),
      _ => {}
    }
    let c1 = Arc::new(Coe::One(fsp, t));
    let mut todo = Vec::new();
    for (&sl, m) in &self.coes {
      if let Some(c) = m.get(&s1) {
        todo.push((sl, s2, Arc::new(Coe::Trans(c.clone(), s1, c1.clone()))));
      }
    }
    todo.push((s1, s2, c1.clone()));
    if let Some(m) = self.coes.get(&s2) {
      for (&sr, c) in m {
        todo.push((s1, sr, Arc::new(Coe::Trans(c1.clone(), s2, c.clone()))));
      }
    }
    for (sl, sr, c) in todo {
      if sl == sr {
        let mut err = "coercion cycle detected: ".to_owned();
        let mut related = Vec::new();
        c.write_arrows(sorts, &mut err, &mut related, sl, sr).unwrap();
        return Err(ElabError::with_info(sp, err.into(), related))
      }
      if let Some((c, e)) = self.coes.entry(sl).or_default().try_insert(sr, c) {
        let mut err = "coercion diamond detected: ".to_owned();
        let mut related = Vec::new();
        e.get().write_arrows(sorts, &mut err, &mut related, sl, sr).unwrap();
        err.push_str(";   ");
        c.write_arrows(sorts, &mut err, &mut related, sl, sr).unwrap();
        return Err(ElabError::with_info(sp, err.into(), related))
      }
    }
    Ok(())
  }

  pub fn add_coe(&mut self, sp: Span, sorts: &SortVec<Sort>,
      s1: SortID, s2: SortID, fsp: FileSpan, t: TermID) -> Result<(), ElabError> {
    self.add_coe_raw(sp, sorts, s1, s2, fsp, t)?;
    self.update_provs(sp, sorts)?;
    self.decl_nota.entry(t).or_default().0 = true;
    Ok(())
  }

  fn merge(&mut self, other: &Self, r: &mut Remapper, sp: Span, sorts: &SortVec<Sort>, errors: &mut Vec<ElabError>) {
    self.delims_l.merge(&other.delims_l);
    self.delims_r.merge(&other.delims_r);
    for (tk, &(ref fsp, p)) in &other.consts {
      self.add_const(tk.clone(), fsp.clone(), p).unwrap_or_else(|r|
        errors.push(ElabError::with_info(sp,
          format!("constant '{}' declared with two precedences", tk).into(),
          vec![(r.decl1, "declared here".into()), (r.decl2, "declared here".into())])))
    }
    for (&p, &(ref fsp, r)) in &other.prec_assoc {
      self.add_prec_assoc(p, fsp.clone(), r).unwrap_or_else(|r|
        errors.push(ElabError::with_info(sp,
          format!("precedence level {} has incompatible associativity", p).into(),
          vec![(r.decl1, "left assoc here".into()), (r.decl2, "right assoc here".into())])))
    }
    for (tk, i) in &other.prefixes {
      self.add_prefix(tk.clone(), i.remap(r)).unwrap_or_else(|r|
        errors.push(ElabError::with_info(sp,
          format!("constant '{}' declared twice", tk).into(),
          vec![(r.decl1, "declared here".into()), (r.decl2, "declared here".into())])))
    }
    for (tk, i) in &other.infixes {
      self.add_infix(tk.clone(), i.remap(r)).unwrap_or_else(|r|
        errors.push(ElabError::with_info(sp,
          format!("constant '{}' declared twice", tk).into(),
          vec![(r.decl1, "declared here".into()), (r.decl2, "declared here".into())])))
    }
    for (&s1, m) in &other.coes {
      for (&s2, coe) in m {
        if let &Coe::One(ref fsp, t) = coe.deref() {
          self.add_coe_raw(sp, sorts, s1, s2, fsp.clone(), t.remap(r))
            .unwrap_or_else(|r| errors.push(r))
        }
      }
    }
    self.update_provs(sp, sorts).unwrap_or_else(|r| errors.push(r))
  }
}

/// A specialized version of [`IncompatibleError`] for name reuse errors.
///
/// [`IncompatibleError`]: struct.IncompatibleError.html
pub struct RedeclarationError {
  /// The error message
  pub msg: String,
  /// The message to associate with the earlier definition
  pub othermsg: String,
  /// The location of the earlier definition
  pub other: FileSpan
}

impl Environment {
  pub fn term(&self, a: AtomID) -> Option<TermID> {
    if let Some(DeclKey::Term(i)) = self.data[a].decl { Some(i) } else { None }
  }

  pub fn thm(&self, a: AtomID) -> Option<ThmID> {
    if let Some(DeclKey::Thm(i)) = self.data[a].decl { Some(i) } else { None }
  }
}

/// Adding an item (sort, term, theorem, atom) can result in a redeclaration error,
/// or an overflow error (especially for sorts, which can only have 128 due to the
/// MMB format). The redeclaration case allows returning a value `A`.
pub enum AddItemError<A> {
  /// The declaration overlaps with some previous declaration
  Redeclaration(A, RedeclarationError),
  /// Need more numbers
  Overflow
}

/// Most add item functions return `AddItemError<Option<A>>`, meaning that in the
/// redeclaration case they can still return an `A`, namely the ID of the old declaration
type AddItemResult<A> = Result<A, AddItemError<Option<A>>>;

impl<A> AddItemError<A> {
  pub fn to_elab_error(self, sp: Span) -> ElabError {
    match self {
      AddItemError::Redeclaration(_, r) =>
        ElabError::with_info(sp, r.msg.into(), vec![(r.other, r.othermsg.into())]),
      AddItemError::Overflow =>
        ElabError::new_e(sp, "too many sorts"),
    }
  }
}

impl Environment {
  pub fn add_sort(&mut self, a: AtomID, fsp: FileSpan, full: Span, sd: Modifiers) -> Result<SortID, AddItemError<SortID>> {
    let new_id = SortID(self.sorts.len().try_into().map_err(|_| AddItemError::Overflow)?);
    let data = &mut self.data[a];
    if let Some(old_id) = data.sort {
      let ref sort = self.sorts[old_id];
      if sd == sort.mods { Ok(old_id) }
      else {
        Err(AddItemError::Redeclaration(old_id, RedeclarationError {
          msg: format!("sort '{}' redeclared", data.name),
          othermsg: "previously declared here".to_owned(),
          other: sort.span.clone()
        }))
      }
    } else {
      data.sort = Some(new_id);
      self.sorts.push(Sort { atom: a, name: data.name.clone(), span: fsp, full, mods: sd });
      self.stmts.push(StmtTrace::Sort(a));
      Ok(new_id)
    }
  }

  pub fn add_term(&mut self, a: AtomID, new: FileSpan, t: impl FnOnce() -> Term) -> AddItemResult<TermID> {
    let new_id = TermID(self.terms.len().try_into().map_err(|_| AddItemError::Overflow)?);
    let data = &mut self.data[a];
    if let Some(key) = data.decl {
      let (res, sp) = match key {
        DeclKey::Term(old_id) => {
          let ref sp = self.terms[old_id].span;
          if *sp == new { return Ok(old_id) }
          (Some(old_id), sp)
        }
        DeclKey::Thm(old_id) => (None, &self.thms[old_id].span)
      };
      Err(AddItemError::Redeclaration(res, RedeclarationError {
        msg: format!("term '{}' redeclared", data.name),
        othermsg: "previously declared here".to_owned(),
        other: sp.clone()
      }))
    } else {
      data.decl = Some(DeclKey::Term(new_id));
      self.terms.push(t());
      self.stmts.push(StmtTrace::Decl(a));
      Ok(new_id)
    }
  }

  pub fn add_thm(&mut self, a: AtomID, new: FileSpan, t: impl FnOnce() -> Thm) -> AddItemResult<ThmID> {
    let new_id = ThmID(self.thms.len().try_into().map_err(|_| AddItemError::Overflow)?);
    let data = &mut self.data[a];
    if let Some(key) = data.decl {
      let (res, sp) = match key {
        DeclKey::Thm(old_id) => {
          let ref sp = self.thms[old_id].span;
          if *sp == new { return Ok(old_id) }
          (Some(old_id), sp)
        }
        DeclKey::Term(old_id) => (None, &self.terms[old_id].span)
      };
      Err(AddItemError::Redeclaration(res, RedeclarationError {
        msg: format!("theorem '{}' redeclared", data.name),
        othermsg: "previously declared here".to_owned(),
        other: sp.clone()
      }))
    } else {
      data.decl = Some(DeclKey::Thm(new_id));
      self.thms.push(t());
      self.stmts.push(StmtTrace::Decl(a));
      Ok(new_id)
    }
  }

  pub fn add_coe(&mut self, s1: SortID, s2: SortID, fsp: FileSpan, t: TermID) -> Result<(), ElabError> {
    self.pe.add_coe(fsp.span, &self.sorts, s1, s2, fsp, t)
  }

  pub fn get_atom(&mut self, s: &str) -> AtomID {
    match self.atoms.get(s) {
      Some(&a) => a,
      None => {
        let id = AtomID(self.data.len().try_into().expect("too many atoms"));
        let s: ArcString = s.into();
        self.atoms.insert(s.clone(), id);
        self.data.push(AtomData::new(s));
        id
      }
    }
  }
  pub fn get_atom_arc(&mut self, s: ArcString) -> AtomID {
    let ctx = &mut self.data;
    *self.atoms.entry(s.clone()).or_insert_with(move ||
      (AtomID(ctx.len().try_into().expect("too many atoms")), ctx.push(AtomData::new(s))).0)
  }

  pub fn merge(&mut self, other: &Self, sp: Span, errors: &mut Vec<ElabError>) -> Result<(), ElabError> {
    let lisp_remap = &mut LispRemapper {
      atom: other.data.iter().map(|d| self.get_atom_arc(d.name.clone())).collect(),
      lisp: Default::default(),
      refs: Default::default(),
    };
    for (i, d) in other.data.iter().enumerate() {
      let data = &self.data[lisp_remap.atom[AtomID(i as u32)]];
      data.lisp = d.lisp.as_ref().map(|(fs, v)| (fs.clone(), v.remap(lisp_remap)));
      if data.lisp.is_none() {
        data.graveyard = d.graveyard.clone();
      }
    }
    let remap = &mut Remapper::default();
    for &s in &other.stmts {
      match s {
        StmtTrace::Sort(a) => {
          let i = other.data[a].sort.unwrap();
          let ref sort = other.sorts[i];
          let id = match self.add_sort(a.remap(lisp_remap), sort.span.clone(), sort.full, sort.mods) {
            Ok(id) => id,
            Err(AddItemError::Redeclaration(id, r)) => {
              errors.push(ElabError::with_info(sp, r.msg.into(), vec![
                (sort.span.clone(), r.othermsg.clone().into()),
                (r.other, r.othermsg.into())
              ]));
              id
            }
            Err(AddItemError::Overflow) => Err(ElabError::new_e(sp, "too many sorts"))?
          };
          if i != id { remap.sort.insert(i, id); }
        }
        StmtTrace::Decl(a) => match other.data[a].decl.unwrap() {
          DeclKey::Term(i) => {
            let ref o = other.terms[i];
            let id = match self.add_term(a.remap(lisp_remap), o.span.clone(), || o.remap(remap)) {
              Ok(id) => id,
              Err(AddItemError::Redeclaration(id, r)) => {
                let e = ElabError::with_info(sp, r.msg.into(), vec![
                  (o.span.clone(), r.othermsg.clone().into()),
                  (r.other, r.othermsg.into())
                ]);
                match id { None => Err(e)?, Some(id) => {errors.push(e); id} }
              }
              Err(AddItemError::Overflow) => Err(ElabError::new_e(sp, "too many terms"))?
            };
            if i != id { remap.term.insert(i, id); }
          }
          DeclKey::Thm(i) => {
            let ref o = other.thms[i];
            let id = match self.add_thm(a.remap(lisp_remap), o.span.clone(), || o.remap(remap)) {
              Ok(id) => id,
              Err(AddItemError::Redeclaration(id, r)) => {
                let e = ElabError::with_info(sp, r.msg.into(), vec![
                  (o.span.clone(), r.othermsg.clone().into()),
                  (r.other, r.othermsg.into())
                ]);
                match id { None => Err(e)?, Some(id) => {errors.push(e); id} }
              }
              Err(AddItemError::Overflow) => Err(ElabError::new_e(sp, "too many theorems"))?
            };
            if i != id { remap.thm.insert(i, id); }
          }
        },
        StmtTrace::Global(_) => {}
      }
    }
    self.pe.merge(&other.pe, remap, sp, &self.sorts, errors);
    Ok(())
  }

  pub fn check_term_nargs(&self, sp: Span, term: TermID, nargs: usize) -> Result<(), ElabError> {
    let ref t = self.terms[term];
    if t.args.len() == nargs { return Ok(()) }
    Err(ElabError::with_info(sp, "incorrect number of arguments".into(),
      vec![(t.span.clone(), "declared here".into())]))
  }

  pub fn find(&self, pos: usize) -> Option<&Spans<ObjectKind>> {
    match self.spans.binary_search_by_key(&pos, |s| s.stmt().start) {
      Ok(i) => Some(&self.spans[i]),
      Err(i) => i.checked_sub(1).map(|j| &self.spans[j]),
    }
  }
}
