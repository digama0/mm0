//! Definitions of the atoms used in the MM1 language.
use super::AtomId;

macro_rules! make_atoms {
  {consts $n:expr;} => {};
  {consts $n:expr; $(#[$attr:meta])* $x:ident $doc0:expr, $($xs:tt)*} => {
    #[doc=$doc0]
    $(#[$attr])*
    pub const $x: AtomId = AtomId($n);
    make_atoms! {consts AtomId::$x.0+1; $($xs)*}
  };
  {$($(#[$attr:meta])* $x:ident: $e:expr,)*} => {
    impl AtomId {
      make_atoms! {consts 0; $($(#[$attr])* $x concat!("The atom `", $e, "`.\n"),)*}

      /// Map a function over the list of atom constants (in increasing order).
      pub fn on_atoms(mut f: impl FnMut(&str, AtomId)) { $(f($e, AtomId::$x);)* }
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
