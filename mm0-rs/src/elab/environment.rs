//! The [`Environment`] contains all elaborated proof data, as well as the lisp global context.

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
use super::{ElabError, BoxError, spans::Spans, FrozenEnv, FrozenLispVal};
use crate::util::{ArcString, FileRef, FileSpan, HashMapExt, Span};
use super::lisp::{LispVal, RefineSyntax, Syntax};
use super::frozen::{FrozenLispKind, FrozenLispRef};
pub use crate::parser::ast::{Modifiers, Prec};

macro_rules! id_wrapper {
  ($id:ident: $ty:ty, $vec:ident) => {
    id_wrapper!($id: $ty, $vec,
      concat!("An index into a [`", stringify!($vec), "`]"));
  };
  ($id:ident: $ty:ty, $vec:ident, $svec:expr) => {
    #[doc=$svec]
    #[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Default)]
    pub struct $id(pub $ty);
    $crate::deep_size_0!($id);

    impl fmt::Debug for $id {
      fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
    }

    /// A vector wrapper with a strongly typed index interface.
    #[derive(Clone, Debug, DeepSizeOf)]
    pub struct $vec<T>(pub Vec<T>);

    #[allow(dead_code)]
    impl<T> $vec<T> {
      /// Get a reference to the element at the given index.
      #[must_use] pub fn get(&self, i: $id) -> Option<&T> { self.0.get(i.0 as usize) }
      /// Get a mutable reference to the element at the given index.
      #[must_use] pub fn get_mut(&mut self, i: $id) -> Option<&mut T> { self.0.get_mut(i.0 as usize) }
      /// Returns the equivalent of `iter().enumerate()` but with the right indexing type.
      pub fn enum_iter(&self) -> impl Iterator<Item=($id, &T)> {
        self.0.iter().enumerate().map(|(i, t)| ($id(i as $ty), t))
      }
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

/// A documentation comment on an item.
pub type DocComment = Arc<str>;

/// The information associated to a defined [`Sort`].
#[derive(Clone, Debug, DeepSizeOf)]
pub struct Sort {
  /// The sort's name, as an atom.
  pub atom: AtomID,
  /// The sort's name, as a string. (This is a shortcut; you can also look up the atom in
  /// [`Environment.data`] and get the name from there.)
  pub name: ArcString,
  /// The span for the name of the sort. This is `"foo"` in the statement `sort foo;`.
  pub span: FileSpan,
  /// The span for the entire declaration creating the sort. This is `"sort foo;"`
  /// in the statement `sort foo;` (not including any characters after the semicolon). The file
  /// is the same as `span`.
  pub full: Span,
  /// The documentation comment on the sort.
  pub doc: Option<DocComment>,
  /// The sort modifiers. Any subset of [`PURE`](Modifiers::PURE), [`STRICT`](Modifiers::STRICT),
  /// [`PROVABLE`](Modifiers::PROVABLE), [`FREE`](Modifiers::FREE).
  /// The other modifiers are not valid.
  pub mods: Modifiers,
}

/// The type of a variable in the binder list of an `axiom`/`term`/`def`/`theorem`.
/// The variables themselves are not named because their names are derived from their
/// positions in the binder list (i.e. `{v0 : s} (v1 : t v0) (v2 : t)`)
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[allow(variant_size_differences)]
pub enum Type {
  /// A bound variable `{x : s}`, where `s` is the provided [`SortID`].
  Bound(SortID),
  /// A regular variable `(ph : s x y z)`, where `s` is the provided [`SortID`].
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
crate::deep_size_0!(Type);

impl Type {
  /// The sort of a type.
  #[must_use] pub fn sort(self) -> SortID {
    match self { Type::Bound(s) | Type::Reg(s, _) => s }
  }
  /// True if the type is a bound variable.
  #[must_use] pub fn bound(self) -> bool { matches!(self, Type::Bound(_)) }
}

/// An [`ExprNode`] is interpreted inside a context containing the `Vec<`[`Type`]`>`
/// args and the `Vec<ExprNode>` heap.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum ExprNode {
  /// `Ref(n)` is a reference to heap element `n` (the first `args.len()` of them are the variables)
  Ref(usize),
  /// `Dummy(s, sort)` is a fresh dummy variable `s` with sort `sort`
  Dummy(AtomID, SortID),
  /// `App(t, nodes)` is an application of term constructor `t` to subterms
  App(TermID, Box<[ExprNode]>),
}

/// The `Expr` type stores expression dags using a local context of expression nodes
/// and a final expression. See [`ExprNode`] for explanation of the variants.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct Expr {
  /// The heap, which is used for subexpressions that appear multiple times.
  /// The first `args.len()` elements of the heap are fixed to the variables.
  pub heap: Box<[ExprNode]>,
  /// The target expression.
  pub head: ExprNode,
}

/// The value of a term or def.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum TermKind {
  /// This is a `term`, which has no definition
  Term,
  /// This is a `def`:
  /// - `None`: This is an abstract `def` or a `def` missing a definition
  /// - `Some(e)`: This is a `def` which is defined to equal `e`
  Def(Option<Expr>)
}

/// The data associated to a `term` or `def` declaration.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct Term {
  /// The name of the term, as an atom.
  pub atom: AtomID,
  /// The span around the name of the term. This is the `"foo"` in `def foo ...;`
  pub span: FileSpan,
  /// The modifiers for the term. For `def`, the allowed modifiers are
  /// [`LOCAL`](Modifiers::LOCAL) and [`ABSTRACT`](Modifiers::ABSTRACT), and for
  /// `term` no modifiers are permitted.
  pub vis: Modifiers,
  /// The span around the entire declaration for the term, from the first modifier
  /// to the semicolon. The file is the same as in `span`.
  pub full: Span,
  /// The documentation comment on the sort.
  pub doc: Option<DocComment>,
  /// The list of argument binders. The names of the variables are not used except for
  /// pretty printing and conversion back to s-exprs. (A `None` variable is represented
  /// as `_` and cannot be referred to.)
  pub args: Box<[(Option<AtomID>, Type)]>,
  /// The return sort and dependencies of the term constructor. See [`Type::Reg`] for
  /// the interpretation of the dependencies.
  pub ret: (SortID, u64),
  /// The term/def classification, and the value of the def.
  pub kind: TermKind,
}

/// A [`ProofNode`] is a stored proof term. This is an extension of [`ExprNode`] with
/// more constructors, so a [`ProofNode`] can represent an expr, a proof, or a conversion,
/// and the typing determines which. A [`ProofNode`] is interpreted in a context of
/// variables `Vec<Type>`, and a heap `Vec<ProofNode>`.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum ProofNode {
  /// `Ref(n)` is a reference to heap element `n` (the first `args.len()` of them are the variables).
  /// This could be an expr, proof, or conv depending on what is referenced.
  Ref(usize),
  /// `Dummy(s, sort)` is a fresh dummy variable `s` with sort `sort`
  Dummy(AtomID, SortID),
  /// `Term {term, args}` is an application of term constructor `term` to subterms
  Term {
    /** the term constructor */ term: TermID,
    /** the subterms */ args: Box<[ProofNode]>,
  },
  /// `Hyp(i, e)` is hypothesis `i` (`hyps[i]` will be a reference to element),
  /// which is a proof of `|- e`.
  Hyp(usize, Box<ProofNode>),
  /// `Thm {thm, args, res}` is a proof of `|- res` by applying theorem `thm` to arguments
  /// `args`. `args` is a list of length `thm.args.len() + thm.hyps.len()` containing the
  /// substitution, followed by the hypothesis subproofs, and it is required that `res`
  /// and the subproofs be the result of substitution of the theorem conclusion and hypotheses
  /// under the substitution.
  Thm {
    /** the theorem to apply */ thm: ThmID,
    /** the substitution, and the subproofs */ args: Box<[ProofNode]>,
    /** the substituted conclusion */ res: Box<ProofNode>,
  },
  /// `Conv(tgt, conv, proof)` is a proof of `|- tgt` if `proof: src` and `conv: tgt = src`.
  Conv(Box<(ProofNode, ProofNode, ProofNode)>),
  /// `Refl(e): e = e`
  Refl(Box<ProofNode>),
  /// `Refl(p): e2 = e1` if `p: e1 = e2`
  Sym(Box<ProofNode>),
  /// `Cong {term, args}: term a1 ... an = term b1 ... bn` if `args[i]: ai = bi`
  Cong {
    /** the term constructor */ term: TermID,
    /** the conversion proofs for the arguments */ args: Box<[ProofNode]>,
  },
  /// `Unfold {term, args, res: (lhs, sub_lhs, p)}` is a proof of `lhs = rhs` if
  /// `lhs` is `term args` and `term` is a definition and `sub_lhs` is the result of
  /// substituting `args` into the definition of `term`, and `p: sub_lhs = rhs`
  Unfold {
    /// the definition to unfold
    term: TermID,
    /// the (non-dummy) parameters to the term
    args: Box<[ProofNode]>,
    /// - `lhs`: the term applied to the arguments, the same as `Term(term, args)`
    /// - `sub_lhs`: the result of unfolding the definition (for some choice of dummy names)
    /// - `p`: the proof that `sub_lhs = rhs`
    res: Box<(ProofNode, ProofNode, ProofNode)>,
  },
}

impl ProofNode {
  /// Strip excess [`Ref`](ProofNode::Ref) nodes from a [`ProofNode`].
  #[must_use] pub fn deref<'a>(&'a self, heap: &'a [ProofNode]) -> &'a Self {
    let mut e = self;
    loop {
      match *e {
        ProofNode::Ref(i) if i < heap.len() => e = &heap[i],
        _ => return e
      }
    }
  }
}

impl From<&ExprNode> for ProofNode {
  fn from(e: &ExprNode) -> ProofNode {
    match *e {
      ExprNode::Ref(n) => ProofNode::Ref(n),
      ExprNode::Dummy(a, s) => ProofNode::Dummy(a, s),
      ExprNode::App(term, ref es) => ProofNode::Term {
        term, args: es.iter().map(|e| e.into()).collect()
      }
    }
  }
}

/// The [`Proof`] type stores proof term dags using a local context of proof nodes
/// and a final proof. See [`ProofNode`] for explanation of the variants.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct Proof {
  /// The heap, which is used for subexpressions that appear multiple times.
  /// The first `args.len()` elements of the heap are fixed to the variables.
  pub heap: Box<[ProofNode]>,
  /// The hypotheses, where `hyps[i]` points to [`Hyp`]`(i, e)`. Because these terms
  /// are deduplicated with everything else, the [`Hyp`] itself will probably be
  /// on the heap (unless it is never used), and then a [`Ref`] will be stored
  /// in the `hyps` array.
  ///
  /// [`Hyp`]: ProofNode::Hyp
  /// [`Ref`]: ProofNode::Ref
  pub hyps: Box<[ProofNode]>,
  /// The target proof term.
  pub head: ProofNode,
}

/// The proof of the axiom or theorem.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum ThmKind {
  /// This is an `axiom`, which has no proof.
  Axiom,
  /// This is a `theorem`:
  /// - `None`: This is a `theorem` with a missing or malformed proof
  /// - `Some(p)`: This is a `theorem` which has proof `p`
  Thm(Option<Proof>)
}

/// The data associated to an `axiom` or `theorem` declaration.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct Thm {
  /// The name of the theorem, as an atom.
  pub atom: AtomID,
  /// The span around the name of the theorem. This is the `"foo"` in `theorem foo ...;`
  pub span: FileSpan,
  /// The modifiers for the term. For `theorem`, the only allowed modifier is
  /// [`PUB`](Modifiers::PUB), and for `term` no modifiers are permitted.
  pub vis: Modifiers,
  /// The span around the entire declaration for the theorem, from the first modifier
  /// to the semicolon. The file is the same as in `span`.
  pub full: Span,
  /// The documentation comment on the sort.
  pub doc: Option<DocComment>,
  /// The list of argument binders. The names of the variables are not used except for
  /// pretty printing and conversion back to s-exprs. (A `None` variable is represented
  /// as `_` and cannot be referred to.)
  pub args: Box<[(Option<AtomID>, Type)]>,
  /// The heap used as the context for the `hyps` and `ret`.
  pub heap: Box<[ExprNode]>,
  /// The expressions for the hypotheses (and their names, which are not used except
  /// in pretty printing and conversion back to s-exprs).
  pub hyps: Box<[(Option<AtomID>, ExprNode)]>,
  /// The expression for the conclusion of the theorem.
  pub ret: ExprNode,
  /// The axiom/theorem classification, and the proof.
  ///
  /// **Note**: The [`Proof`] has its own `heap` and `hyps`, separate from the
  /// `heap` and `hyps` in this structure. They are required to be equivalent, but the
  /// indexing can be different between them, and the indexes in the proof are only
  /// valid with the `heap` in the proof.
  pub kind: ThmKind,
}

/// An `output string` directive, which is anonymous and hence stored directly
/// in the [`StmtTrace`] list.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct OutputString {
  /// The span of the full statement.
  pub span: FileSpan,
  /// The heap of expressions used in the `exprs`.
  pub heap: Box<[ExprNode]>,
  /// The expressions to output.
  pub exprs: Box<[ExprNode]>,
}

/// A global order on sorts, declarations ([`Term`] and [`Thm`]), and lisp
/// global definitions based on declaration order.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum StmtTrace {
  /// A `sort foo;` declaration
  Sort(AtomID),
  /// A declaration of a [`Term`] or [`Thm`] (i.e. `term`, `def`, `axiom`, `theorem`)
  Decl(AtomID),
  /// A global lisp declaration in a `do` block, i.e. `do { (def foo 1) };`
  Global(AtomID),
  /// An `output string` directive.
  OutputString(Box<OutputString>)
}

/// A declaration is either a [`Term`] or a [`Thm`]. This is done because in MM1
/// Terms and Thms share a namespace (although they are put in separate number-spaces
/// for compilation to MM0).
#[derive(Copy, Clone, Debug)]
pub enum DeclKey {
  /// A term or def, with its ID
  Term(TermID),
  /// An axiom or theorem, with its ID
  Thm(ThmID),
}
crate::deep_size_0!(DeclKey);

/// A [`Literal`] is an element in a processed `notation` declaration. It is either a
/// constant symbol, or a variable with associated parse precedence.
#[derive(Clone, Debug, DeepSizeOf)]
pub enum Literal {
  /// `Var(i, p)` means that we should parse at precedence `p` at this position,
  /// and the resulting expression should be inserted as the `i`th subexpression of
  /// the term being constructed.
  Var(usize, Prec),
  /// `Const(s)` means that we should parse a token and match it against `s`.
  Const(ArcString),
}

/// The data associated to a `notation`, `infixl`, `infixr`, or `prefix` declaration.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct NotaInfo {
  /// The span around the name of the term. This is the `"foo"` in `notation foo ...;`
  pub span: FileSpan,
  /// The name of the term, as an atom.
  pub term: TermID,
  /// The number of arguments in the term. (This is a shortcut; you can also look up the term in
  /// [Environment.terms] and get the number of arguments as `args.len()`.)
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
#[derive(Clone, Debug, DeepSizeOf)]
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
#[derive(Default, Clone, Debug, DeepSizeOf)]
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

/// A global lisp definition entry.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct LispData {
  /// A `(span, full)` pair where `span` is the name of the definition and `full` is the
  /// entire definition body, or `None`.
  pub src: Option<(FileSpan, Span)>,
  /// The documentation on the declaration of the item.
  pub doc: Option<DocComment>,
  /// The value associated to the name.
  pub val: LispVal
}

impl Deref for LispData {
  type Target = LispVal;
  fn deref(&self) -> &LispVal { &self.val }
}

/// The data associated to an atom.
#[derive(Clone, Debug, DeepSizeOf)]
pub struct AtomData {
  /// The string form of the atom.
  pub name: ArcString,
  /// The global lisp definition with this name, if one exists. The `Option<(FileSpan, Span)>`
  /// is `Some((span, full))` where `span` is the name of the definition and `full` is the
  /// entire definition body, or `None`.
  /// The [`DocComment`] is the documentation on the declaration of the item.
  pub lisp: Option<LispData>,
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
#[derive(Debug, DeepSizeOf)]
pub enum ObjectKind {
  /// This is a sort; hovering yields `sort foo;` and go-to-definition works.
  /// This sort must actually exist in the [`Environment`] if is constructed
  Sort(SortID),
  /// This is a term/def; hovering yields `term foo ...;` and go-to-definition works.
  /// This term must actually exist in the [`Environment`] if is constructed
  Term(TermID, Span),
  /// This is a theorem/axiom; hovering yields `theorem foo ...;` and go-to-definition works.
  /// This theorem must actually exist in the [`Environment`] if is constructed
  Thm(ThmID),
  /// This is a local variable; hovering yields `{x : s}` and go-to-definition takes you to the binder.
  /// This should be a variable in the statement.
  Var(AtomID),
  /// This is a global lisp definition; hovering yields the lisp definition line and go-to-definition works.
  /// Either `lisp` or `graveyard` for the atom must be non-`None` if this is constructed
  Global(AtomID),
  /// This is an expression; hovering shows the type and go-to-definition goes to the head term definition
  Expr(FrozenLispVal),
  /// This is a proof; hovering shows the intermediate statement
  /// and go-to-definition goes to the head theorem definition
  Proof(FrozenLispVal),
  /// This is a lisp syntax item; hovering shows the doc comment
  Syntax(Syntax),
  /// This is a refine tactic syntax item; hovering shows the doc comment
  RefineSyntax(RefineSyntax),
  /// This is an import; hovering does nothing and go-to-definition goes to the file
  Import(FileRef),
}

impl ObjectKind {
  /// Create an [`ObjectKind`] for an [`Expr`].
  /// # Safety
  /// Because this function calls [`FrozenLispVal::new`],
  /// the resulting object must not be examined before the elaborator is frozen.
  #[must_use] pub fn expr(e: LispVal) -> ObjectKind {
    ObjectKind::Expr(unsafe {FrozenLispVal::new(e)})
  }
  /// Create an [`ObjectKind`] for a [`Proof`].
  /// # Safety
  /// Because this function calls [`FrozenLispVal::new`],
  /// the resulting object must not be examined before the elaborator is frozen.
  #[must_use] pub fn proof(e: LispVal) -> ObjectKind {
    ObjectKind::Proof(unsafe {FrozenLispVal::new(e)})
  }
}

/// The main environment struct, containing all permanent data to be exported from an MM1 file.
#[derive(Debug, DeepSizeOf)]
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
  {consts $n:expr; $(#[$attr:meta])* $x:ident $doc0:expr, $($xs:tt)*} => {
    #[doc=$doc0]
    $(#[$attr])*
    pub const $x: AtomID = AtomID($n);
    make_atoms! {consts AtomID::$x.0+1; $($xs)*}
  };
  {$($(#[$attr:meta])* $x:ident: $e:expr,)*} => {
    impl AtomID {
      make_atoms! {consts 0; $($(#[$attr])* $x concat!("The atom `", $e, "`.\n"),)*}
    }

    impl Environment {
      /// Creates a new environment. The list of atoms is pre-populated with [`AtomID`]
      /// atoms that are used by builtins.
      #[allow(clippy::string_lit_as_bytes)]
      #[must_use] pub fn new() -> Environment {
        let mut atoms = HashMap::new();
        let mut data = AtomVec::default();
        $({
          let s: ArcString = $e.as_bytes().into();
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
  /// The blank, used to represent wildcards in `match`
  UNDER: "_",
  /// In refine, `(! thm x y e1 e2 p1 p2)` allows passing bound and regular variables,
  /// in addition to subproofs
  BANG: "!",
  /// In refine, `(!! thm x y p1 p2)` allows passing bound variables and subproofs but not
  /// regular variables, in addition to subproofs
  BANG2: "!!",
  /// In refine, `(:verb p)` allows passing an elaborated proof term `p` in a refine script
  /// (without this, the applications in `p` would be interpreted incorrectly)
  VERB: ":verb",
  /// In elaborated proofs, `(:conv e c p)` is a conversion proof.
  /// (The initial colon avoids name collision with MM0 theorems, which don't allow `:` in identifiers.)
  CONV: ":conv",
  /// In elaborated proofs, `(:sym c)` is a proof of symmetry.
  /// (The initial colon avoids name collision with MM0 theorems, which don't allow `:` in identifiers.)
  SYM: ":sym",
  /// In elaborated proofs, `(:unfold t es c)` is a proof of definitional unfolding.
  /// (The initial colon avoids name collision with MM0 theorems, which don't allow `:` in identifiers.)
  UNFOLD: ":unfold",
  /// In MMU proofs, `(:let h p1 p2)` is a let-binding for supporting deduplication.
  LET: ":let",
  /// In refine, `{p : t}` is a type ascription for proofs.
  COLON: ":",
  /// In refine, `?` is a proof by "sorry" (stubbing the proof without immediate error)
  QMARK: "?",
  /// `term` is an atom used by `add-decl` to add a term/def declaration
  TERM: "term",
  /// `def` is an atom used by `add-decl` to add a term/def declaration
  DEF: "def",
  /// `axiom` is an atom used by `add-decl` to add an axiom/theorem declaration
  AXIOM: "axiom",
  /// `theorem` is an atom used by `add-decl` to add an axiom/theorem declaration
  THM: "theorem",
  /// `pub` is an atom used to specify the visibility modifier in `add-decl`
  PUB: "pub",
  /// `abstract` is an atom used to specify the visibility modifier in `add-decl`
  ABSTRACT: "abstract",
  /// `local` is an atom used to specify the visibility modifier in `add-decl`
  LOCAL: "local",
  /// `:sorry` is an atom used by `get-decl` to print missing proofs
  SORRY: ":sorry",
  /// `error` is an error level recognized by `set-reporting`
  ERROR: "error",
  /// `warn` is an error level recognized by `set-reporting`
  WARN: "warn",
  /// `info` is an error level recognized by `set-reporting`
  INFO: "info",
  /// The `annotate` function is a callback used to define what happens when an annotation like
  /// `@foo def bar = ...` is used.
  ANNOTATE: "annotate",
  /// The `refine-extra-args` function is a callback used when an application in refine
  /// uses too many arguments.
  REFINE_EXTRA_ARGS: "refine-extra-args",
  /// `to-expr-fallback` is called when elaborating a term that is not otherwise recognized
  TO_EXPR_FALLBACK: "to-expr-fallback",
}

/// An implementation of a map `u8 -> bool` using a 32 byte array as a bitset.
#[derive(Default, Copy, Clone, Debug)]
pub struct Delims([u8; 32]);
crate::deep_size_0!(Delims);

impl Delims {
  /// Returns `self[i]`
  #[must_use] pub fn get(&self, c: u8) -> bool { self.0[(c >> 3) as usize] & (1 << (c & 7)) != 0 }
  /// Sets `self[i] = true`.
  pub fn set(&mut self, c: u8) { self.0[(c >> 3) as usize] |= 1 << (c & 7) }
  /// Sets `self[i] |= other[i]` for all `i`, that is, sets this bitset to the
  /// union of itself and `other`.
  pub fn merge(&mut self, other: &Self) {
    for i in 0..32 { self.0[i] |= other.0[i] }
  }
}

/// An auxiliary structure for performing [`Environment`] deep copies. This is needed
/// because [`AtomID`]s from other, previously elaborated files may not be consistent with
/// the current file, so we have to remap them to the current file's namespace
/// during import.
#[derive(Default, Debug)]
pub struct Remapper {
  /// A mapping of foreign sorts into local sort IDs
  sort: SortVec<SortID>,
  /// A mapping of foreign terms into local term IDs
  term: TermVec<TermID>,
  /// A mapping of foreign theorems into local theorem IDs
  thm: ThmVec<ThmID>,
  /// A mapping of foreign atoms into local atom IDs
  pub(crate) atom: AtomVec<AtomID>,
  /// A mapping of foreign [`FrozenLispVal`]s into local [`LispVal`]s.
  /// It uses a pointer to the underlying allocation as an identifier so that
  /// we don't remap the same lisp values many times.
  pub(crate) lisp: HashMap<*const FrozenLispKind, LispVal>,
  /// A stack of references that are currently being constructed. It is stored
  /// as a hashmap, indexed on the source lisp ref-cell, for fast lookup.
  ///
  /// When a [`Ref`](super::lisp::LispKind::Ref) is remapped, we initially create a
  /// `(ref! #undef)` and put it in `refs` (if it is not already present),
  /// then we remap the contents of the ref, and finally we assign the result
  /// to the ref we created and remove the newly assigned ref-cell from `refs`.
  /// That way, a mutable cell is remapped to another mutable cell, but we can
  /// detect cycles and correctly remap them into cycles.
  pub(crate) refs: HashMap<*const FrozenLispRef, LispVal>,
}

/// A trait for types that can be remapped.
/// This is like [`Clone`] except it uses a `&mut R` as auxiliary state.
pub trait Remap: Sized {
  /// The type that is constructed as a result of the remap, usually `Self`.
  type Target;
  /// Create a copy of `self`, using `r` as auxiliary state.
  fn remap(&self, r: &mut Remapper) -> Self::Target;
}
impl Remap for SortID {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self { r.sort[*self] }
}
impl Remap for TermID {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self { r.term[*self] }
}
impl Remap for ThmID {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self { r.thm[*self] }
}
impl Remap for AtomID {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self { r.atom[*self] }
}
impl<A: Remap, B: Remap> Remap for (A, B) {
  type Target = (A::Target, B::Target);
  fn remap(&self, r: &mut Remapper) -> Self::Target { (self.0.remap(r), self.1.remap(r)) }
}
impl<A: Remap, B: Remap, C: Remap> Remap for (A, B, C) {
  type Target = (A::Target, B::Target, C::Target);
  fn remap(&self, r: &mut Remapper) -> Self::Target { (self.0.remap(r), self.1.remap(r), self.2.remap(r)) }
}
impl<A: Remap> Remap for Option<A> {
  type Target = Option<A::Target>;
  fn remap(&self, r: &mut Remapper) -> Self::Target { self.as_ref().map(|x| x.remap(r)) }
}
impl<A: Remap> Remap for Vec<A> {
  type Target = Vec<A::Target>;
  fn remap(&self, r: &mut Remapper) -> Self::Target { self.iter().map(|x| x.remap(r)).collect() }
}
impl<A: Remap> Remap for Box<A> {
  type Target = Box<A::Target>;
  fn remap(&self, r: &mut Remapper) -> Self::Target { Box::new(self.deref().remap(r)) }
}
impl<A: Remap> Remap for Rc<A> {
  type Target = Rc<A::Target>;
  fn remap(&self, r: &mut Remapper) -> Self::Target { Rc::new(self.deref().remap(r)) }
}
impl<A: Remap> Remap for Arc<A> {
  type Target = Arc<A::Target>;
  fn remap(&self, r: &mut Remapper) -> Self::Target { Arc::new(self.deref().remap(r)) }
}
impl<A: Remap> Remap for Box<[A]> {
  type Target = Box<[A::Target]>;
  fn remap(&self, r: &mut Remapper) -> Self::Target { self.iter().map(|v| v.remap(r)).collect() }
}
impl<A: Remap> Remap for Arc<[A]> {
  type Target = Arc<[A::Target]>;
  fn remap(&self, r: &mut Remapper) -> Self::Target { self.iter().map(|v| v.remap(r)).collect() }
}
impl Remap for Type {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      Type::Bound(s) => Type::Bound(s.remap(r)),
      &Type::Reg(s, deps) => Type::Reg(s.remap(r), deps),
    }
  }
}
impl Remap for ExprNode {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      &ExprNode::Ref(i) => ExprNode::Ref(i),
      ExprNode::Dummy(a, s) => ExprNode::Dummy(a.remap(r), s.remap(r)),
      ExprNode::App(t, es) => ExprNode::App(t.remap(r), es.remap(r)),
    }
  }
}
impl Remap for Expr {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Expr {
      heap: self.heap.remap(r),
      head: self.head.remap(r),
    }
  }
}
impl Remap for TermKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      TermKind::Term => TermKind::Term,
      TermKind::Def(e) => TermKind::Def(e.remap(r)),
    }
  }
}
impl Remap for Term {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Term {
      atom: self.atom.remap(r),
      span: self.span.clone(),
      vis: self.vis,
      full: self.full,
      doc: self.doc.clone(),
      args: self.args.remap(r),
      ret: (self.ret.0.remap(r), self.ret.1),
      kind: self.kind.remap(r),
    }
  }
}
impl Remap for OutputString {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    OutputString {
      span: self.span.clone(),
      heap: self.heap.remap(r),
      exprs: self.exprs.remap(r),
    }
  }
}
impl Remap for ProofNode {
  type Target = Self;
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
impl Remap for Proof {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Proof {
      heap: self.heap.remap(r),
      hyps: self.hyps.remap(r),
      head: self.head.remap(r),
    }
  }
}
impl Remap for ThmKind {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      ThmKind::Axiom => ThmKind::Axiom,
      ThmKind::Thm(e) => ThmKind::Thm(e.remap(r)),
    }
  }
}
impl Remap for Thm {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    Thm {
      atom: self.atom.remap(r),
      span: self.span.clone(),
      vis: self.vis,
      full: self.full,
      doc: self.doc.clone(),
      args: self.args.remap(r),
      heap: self.heap.remap(r),
      hyps: self.hyps.remap(r),
      ret: self.ret.remap(r),
      kind: self.kind.remap(r),
    }
  }
}
impl Remap for NotaInfo {
  type Target = Self;
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
impl Remap for Coe {
  type Target = Self;
  fn remap(&self, r: &mut Remapper) -> Self {
    match self {
      Coe::One(sp, t) => Coe::One(sp.clone(), t.remap(r)),
      Coe::Trans(c1, s, c2) => Coe::Trans(c1.remap(r), s.remap(r), c2.remap(r)),
    }
  }
}

/// Several operations have an "incompatibility error" result, involving a conflict between
/// two definitions. This keeps just the locations of those definitions.
#[derive(Debug)]
pub struct IncompatibleError {
  /// The first declaration in the conflict.
  pub decl1: FileSpan,
  /// The second declaration in the conflict.
  pub decl2: FileSpan,
}

impl ParserEnv {
  /// Add the characters in `ls` to the left delimiter set,
  /// and the characters in `rs` to the right delimiter set.
  pub fn add_delimiters(&mut self, ls: &[u8], rs: &[u8]) {
    for &c in ls { self.delims_l.set(c) }
    for &c in rs { self.delims_r.set(c) }
  }

  /// Add a constant to the parser, at the given precedence. This function will fail
  /// if the constant has already been previously added at a different precedence.
  pub fn add_const(&mut self, tk: ArcString, sp: FileSpan, p: Prec) -> Result<(), IncompatibleError> {
    if let Some((_, e)) = self.consts.try_insert(tk, (sp.clone(), p)) {
      if e.get().1 == p { return Ok(()) }
      Err(IncompatibleError { decl1: e.get().0.clone(), decl2: sp })
    } else { Ok(()) }
  }

  /// Set the associativity of precedence level `p` to `r`.
  ///
  /// In order to prevent ambiguity, all operators at a single precedence level must have
  /// the same associativity. Most precedence levels have no associativity, but when we
  /// add an `infixl` operator at precedence `p`, we call `add_prec_assoc(p, _, false)`
  /// to record that no `infixr` operators can be added to precedence `p` in the future.
  ///
  /// This function will fail if `p` has previously been associated with the opposite
  /// associativity.
  pub fn add_prec_assoc(&mut self, p: u32, sp: FileSpan, r: bool) -> Result<(), IncompatibleError> {
    if let Some((_, e)) = self.prec_assoc.try_insert(p, (sp.clone(), r)) {
      if e.get().1 == r { return Ok(()) }
      let (decl1, decl2) = if r { (e.get().0.clone(), sp) } else { (sp, e.get().0.clone()) };
      Err(IncompatibleError {decl1, decl2})
    } else { Ok(()) }
  }

  fn add_nota_info(m: &mut HashMap<ArcString, NotaInfo>, tk: ArcString, n: NotaInfo) -> Result<(), IncompatibleError> {
    if let Some((n, e)) = m.try_insert(tk, n) {
      if e.get().span == n.span { return Ok(()) }
      Err(IncompatibleError { decl1: e.get().span.clone(), decl2: n.span })
    } else { Ok(()) }
  }

  /// Add a `prefix` declaration to the dynamic parser.
  pub fn add_prefix(&mut self, tk: ArcString, n: NotaInfo) -> Result<(), IncompatibleError> {
    self.decl_nota.entry(n.term).or_default().1.push((tk.clone(), false));
    Self::add_nota_info(&mut self.prefixes, tk, n)
  }

  /// Add an `infixl/r` declaration to the dynamic parser.
  pub fn add_infix(&mut self, tk: ArcString, n: NotaInfo) -> Result<(), IncompatibleError> {
    self.decl_nota.entry(n.term).or_default().1.push((tk.clone(), true));
    Self::add_nota_info(&mut self.infixes, tk, n)
  }

  fn update_provs(&mut self, sp: Span, sorts: &SortVec<Sort>) -> Result<(), ElabError> {
    let mut provs = HashMap::new();
    for (&s1, m) in &self.coes {
      for &s2 in m.keys() {
        if sorts[s2].mods.contains(Modifiers::PROVABLE) {
          if let Some(s2_) = provs.insert(s1, s2) {
            let mut err = "coercion diamond to provable detected:\n".to_owned();
            let mut related = Vec::new();
            self.coes[&s1][&s2].write_arrows(sorts, &mut err, &mut related, s1, s2).expect("write to str");
            err.push_str(" provable\n");
            self.coes[&s1][&s2_].write_arrows(sorts, &mut err, &mut related, s1, s2_).expect("write to str");
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
        c.write_arrows(sorts, &mut err, &mut related, sl, sr).expect("write to str");
        return Err(ElabError::with_info(sp, err.into(), related))
      }
      if let Some((c, e)) = self.coes.entry(sl).or_default().try_insert(sr, c) {
        let mut err = "coercion diamond detected: ".to_owned();
        let mut related = Vec::new();
        e.get().write_arrows(sorts, &mut err, &mut related, sl, sr).expect("write to str");
        err.push_str(";   ");
        c.write_arrows(sorts, &mut err, &mut related, sl, sr).expect("write to str");
        return Err(ElabError::with_info(sp, err.into(), related))
      }
    }
    Ok(())
  }

  /// Add a `coercion t: s1 > s2;` declaration to the parser.
  ///
  /// This function can fail if the updated coercion graph contains a diamond or cycle.
  pub fn add_coe(&mut self, sp: Span, sorts: &SortVec<Sort>,
      s1: SortID, s2: SortID, fsp: FileSpan, t: TermID) -> Result<(), ElabError> {
    self.add_coe_raw(sp, sorts, s1, s2, fsp, t)?;
    self.update_provs(sp, sorts)?;
    self.decl_nota.entry(t).or_default().0 = true;
    Ok(())
  }

  /// Merge environment `other` into this environment.
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
        if let Coe::One(ref fsp, t) = **coe {
          self.add_coe(sp, sorts, s1, s2, fsp.clone(), t.remap(r))
            .unwrap_or_else(|r| errors.push(r))
        }
      }
    }
    self.update_provs(sp, sorts).unwrap_or_else(|r| errors.push(r))
  }
}

/// A specialized version of [`IncompatibleError`] for name reuse errors.
#[derive(Debug)]
pub struct RedeclarationError {
  /// The error message
  pub msg: String,
  /// The message to associate with the earlier definition
  pub othermsg: String,
  /// The location of the earlier definition
  pub other: FileSpan
}

impl Default for Environment {
  fn default() -> Self { Self::new() }
}

impl Environment {
  /// Convert an [`AtomID`] into the corresponding [`TermID`],
  /// if this atom denotes a declared term or def.
  #[must_use] pub fn term(&self, a: AtomID) -> Option<TermID> {
    if let Some(DeclKey::Term(i)) = self.data[a].decl { Some(i) } else { None }
  }

  /// Convert an [`AtomID`] into the corresponding [`ThmID`],
  /// if this atom denotes a declared axiom or theorem.
  #[must_use] pub fn thm(&self, a: AtomID) -> Option<ThmID> {
    if let Some(DeclKey::Thm(i)) = self.data[a].decl { Some(i) } else { None }
  }
}

/// Adding an item (sort, term, theorem, atom) can result in a redeclaration error,
/// or an overflow error (especially for sorts, which can only have 128 due to the
/// MMB format). The redeclaration case allows returning a value `A`.
#[derive(Debug)]
pub enum AddItemError<A> {
  /// The declaration overlaps with some previous declaration
  Redeclaration(A, RedeclarationError),
  /// Need more numbers
  Overflow
}

/// Most add item functions return [`AddItemError`]`<Option<A>>`, meaning that in the
/// redeclaration case they can still return an `A`, namely the ID of the old declaration
type AddItemResult<A> = Result<A, AddItemError<Option<A>>>;

impl<A> AddItemError<A> {
  /// Convert this error into an [`ElabError`] at the provided location.
  pub fn into_elab_error(self, sp: Span) -> ElabError {
    match self {
      AddItemError::Redeclaration(_, r) =>
        ElabError::with_info(sp, r.msg.into(), vec![(r.other, r.othermsg.into())]),
      AddItemError::Overflow =>
        ElabError::new_e(sp, "too many sorts"),
    }
  }
}

impl Environment {
  /// Add a sort declaration to the environment. Returns an error if the sort is redeclared,
  /// or if we hit the maximum number of sorts.
  pub fn add_sort(&mut self, a: AtomID, fsp: FileSpan, full: Span, sd: Modifiers, doc: Option<DocComment>) ->
      Result<SortID, AddItemError<SortID>> {
    let new_id = SortID(self.sorts.len().try_into().map_err(|_| AddItemError::Overflow)?);
    let data = &mut self.data[a];
    if let Some(old_id) = data.sort {
      let sort = &self.sorts[old_id];
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
      self.sorts.push(Sort { atom: a, name: data.name.clone(), span: fsp, full, doc, mods: sd });
      self.stmts.push(StmtTrace::Sort(a));
      Ok(new_id)
    }
  }

  /// Add a term declaration to the environment. The [`Term`] is behind a thunk because
  /// we check for redeclaration before inspecting the term data itself.
  pub fn try_add_term(&mut self, a: AtomID, new: &FileSpan, t: impl FnOnce() -> Term) -> AddItemResult<TermID> {
    let new_id = TermID(self.terms.len().try_into().map_err(|_| AddItemError::Overflow)?);
    let data = &mut self.data[a];
    if let Some(key) = data.decl {
      let (res, sp) = match key {
        DeclKey::Term(old_id) => {
          let sp = &self.terms[old_id].span;
          if *sp == *new { return Ok(old_id) }
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

  /// Specialization of [`try_add_term`](Self::try_add_term) when the term is constructed already.
  pub fn add_term(&mut self, t: Term) -> AddItemResult<TermID> {
    let fsp = t.span.clone();
    self.try_add_term(t.atom, &fsp, || t)
  }

  /// Add a theorem declaration to the environment. The [`Thm`] is behind a thunk because
  /// we check for redeclaration before inspecting the theorem data itself.
  pub fn try_add_thm(&mut self, a: AtomID, new: &FileSpan, t: impl FnOnce() -> Thm) -> AddItemResult<ThmID> {
    let new_id = ThmID(self.thms.len().try_into().map_err(|_| AddItemError::Overflow)?);
    let data = &mut self.data[a];
    if let Some(key) = data.decl {
      let (res, sp) = match key {
        DeclKey::Thm(old_id) => {
          let sp = &self.thms[old_id].span;
          if *sp == *new { return Ok(old_id) }
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

  /// Specialization of [`try_add_thm`](Self::try_add_thm) when the term is constructed already.
  pub fn add_thm(&mut self, t: Thm) -> AddItemResult<ThmID> {
    let fsp = t.span.clone();
    self.try_add_thm(t.atom, &fsp, || t)
  }

  /// Add a coercion declaration to the environment.
  pub fn add_coe(&mut self, s1: SortID, s2: SortID, fsp: FileSpan, t: TermID) -> Result<(), ElabError> {
    self.pe.add_coe(fsp.span, &self.sorts, s1, s2, fsp, t)
  }

  /// Convert a string to an [`AtomID`]. This mutates the environment because we maintain
  /// the list of all allocated atoms, and two calls with the same `&str` input
  /// will yield the same [`AtomID`].
  pub fn get_atom(&mut self, s: &[u8]) -> AtomID {
    self.atoms.get(s).copied().unwrap_or_else(|| {
      let id = AtomID(self.data.len().try_into().expect("too many atoms"));
      let s: ArcString = s.into();
      self.atoms.insert(s.clone(), id);
      self.data.push(AtomData::new(s));
      id
    })
  }

  /// Convert an [`ArcString`] to an [`AtomID`]. This version of [`get_atom`](Self::get_atom)
  /// avoids the string clone in the case that the atom is new.
  pub fn get_atom_arc(&mut self, s: ArcString) -> AtomID {
    let ctx = &mut self.data;
    *self.atoms.entry(s.clone()).or_insert_with(move ||
      (AtomID(ctx.len().try_into().expect("too many atoms")), ctx.push(AtomData::new(s))).0)
  }

  /// Merge `other` into this environment. This merges definitions with the same name and type,
  /// and relabels lisp objects with the new [`AtomID`] mapping.
  pub fn merge(&mut self, other: &FrozenEnv, sp: Span, errors: &mut Vec<ElabError>) -> Result<(), ElabError> {
    let remap = &mut Remapper {
      atom: other.data().iter().map(|d| self.get_atom_arc(d.name().clone())).collect(),
      ..Default::default()
    };
    #[allow(clippy::cast_possible_truncation)]
    for (i, d) in other.data().iter().enumerate() {
      let data = &mut self.data[remap.atom[AtomID(i as u32)]];
      data.lisp = d.lisp().as_ref().map(|v| v.remap(remap));
      if data.lisp.is_none() {
        data.graveyard = d.graveyard().clone();
      }
    }
    for s in other.stmts() {
      match *s {
        StmtTrace::Sort(a) => {
          let i = other.data()[a].sort().expect("wf env");
          let sort = other.sort(i);
          let id = match self.add_sort(a.remap(remap), sort.span.clone(), sort.full, sort.mods, sort.doc.clone()) {
            Ok(id) => id,
            Err(AddItemError::Redeclaration(id, r)) => {
              errors.push(ElabError::with_info(sp, r.msg.into(), vec![
                (sort.span.clone(), r.othermsg.clone().into()),
                (r.other, r.othermsg.into())
              ]));
              id
            }
            Err(AddItemError::Overflow) => return Err(ElabError::new_e(sp, "too many sorts"))
          };
          assert_eq!(remap.sort.len(), i.0 as usize);
          remap.sort.push(id);
        }
        StmtTrace::Decl(a) => match other.data()[a].decl().expect("wf env") {
          DeclKey::Term(tid) => {
            let otd: &Term = other.term(tid);
            let id = match self.try_add_term(a.remap(remap), &otd.span, || otd.remap(remap)) {
              Ok(id) => id,
              Err(AddItemError::Redeclaration(id, r)) => {
                let e = ElabError::with_info(sp, r.msg.into(), vec![
                  (otd.span.clone(), r.othermsg.clone().into()),
                  (r.other, r.othermsg.into())
                ]);
                match id { None => return Err(e), Some(id) => {errors.push(e); id} }
              }
              Err(AddItemError::Overflow) => return Err(ElabError::new_e(sp, "too many terms"))
            };
            assert_eq!(remap.term.len(), tid.0 as usize);
            remap.term.push(id);
          }
          DeclKey::Thm(tid) => {
            let otd: &Thm = other.thm(tid);
            let id = match self.try_add_thm(a.remap(remap), &otd.span, || otd.remap(remap)) {
              Ok(id) => id,
              Err(AddItemError::Redeclaration(id, r)) => {
                let e = ElabError::with_info(sp, r.msg.into(), vec![
                  (otd.span.clone(), r.othermsg.clone().into()),
                  (r.other, r.othermsg.into())
                ]);
                match id { None => return Err(e), Some(id) => {errors.push(e); id} }
              }
              Err(AddItemError::Overflow) => return Err(ElabError::new_e(sp, "too many theorems"))
            };
            assert_eq!(remap.thm.len(), tid.0 as usize);
            remap.thm.push(id);
          }
        },
        StmtTrace::Global(_) => {}
        StmtTrace::OutputString(ref e) => self.stmts.push(StmtTrace::OutputString(e.remap(remap))),
      }
    }
    self.pe.merge(other.pe(), remap, sp, &self.sorts, errors);
    Ok(())
  }

  /// Return an error if the term has the wrong number of arguments, based on its declaration.
  pub(crate) fn check_term_nargs(&self, sp: Span, term: TermID, nargs: usize) -> Result<(), ElabError> {
    let td = &self.terms[term];
    if td.args.len() == nargs { return Ok(()) }
    Err(ElabError::with_info(sp, "incorrect number of arguments".into(),
      vec![(td.span.clone(), "declared here".into())]))
  }
}
