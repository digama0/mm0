Metamath Zero
===

This is a language for writing specifications and proofs. Its emphasis is on balancing simplicity of verification and human readability, with the intent that a skeptical auditor can be convinced of the following:

1. The verifier is implemented correctly to this specification (by reading the code)
2. This specification ensures that a conforming verifier checks that programs meet their specifications (by a paper proof or formalization, forthcoming)
3. The input specification to the verifier correctly describes an axiom system `A`, and the stated theorems are correct transcriptions of theorems `T1,...,Tn` (by reading the specification file)

From the conjunction of these properties, the auditor finds that `A |- T1,...,Tn`, and if they believe `A` is true or representative of the world then they may conclude that `T1,...,Tn` are as well.

Input to a Metamath Zero verifier consists of two parts: a "specification" or "header file", with extension `.mm0`, and a "proof" file with extension `.mp0`. The specification file contains axioms, definitions, and theorem statements, while the proof file contains proofs of the theorems and auxiliary data.

The major distinction between the two files is that in the hypothetical auditing  process above, *the `.mp0` file plays no role*. All information relevant to correctness of the final result is put in the `.mm0` file, and the `.mp0` file is nothing more than an extended "hint" to the verifier to show why the theorems in the `.mm0` file are true. As such, the format of the `.mp0` file is not officially specified, although there is a recommended format (see [?]).

See [set.mm0](set.mm0) for an example of a `.mm0` file.

Unlike many specifications of a similar kind, this specification should be read as an *upper bound* on allowable specification files. That is, a conforming implementation need not support all of the specification, and may fail for implementation-defined reasons. The important property verifiers must have is that a specification that is accepted by the verifier should be correct to the specification.

Lexical structure
===

    file ::= (lexeme | whitespace)*

The file is separated out into a list of lexemes, or tokens, according to the "maximum munch" principle: the longest matching token is used when ambiguity is possible.

    whitespace ::= whitestuff+
    whitestuff ::= whitechar | line-comment
    whitechar ::= ' ' | '\r' | '\n' | '\t'
    line-comment ::= '--' [^\n]* '\n'

Whitespace is a sequence of spaces, newlines, carriage returns and tabs. Comments are line comments, begining with `#` and continuing to the end of the line.

Implementations are encouraged to support "special comments" via comments beginning `--|`, but they have no semantic value in this specification.

    lexeme ::= symbol | identifier | number | math-string
    symbol ::= '*' | '.' | ':' | ';' | '(' | ')' | '>' | '{' | '}' | '=' | '_'
    identifier ::= [a-zA-Z_][a-zA-Z0-9_-]*
    number ::= 0 | [1-9][0-9]*
    math-string ::= '$' [^\$]* '$'

A lexeme is either one of the symbols, an identifier, a number (nonnegative integer), or a math string. An identifier is a sequence of alphanumeric symbols, together with the punctuation characters `_`, and `-`, except that it cannot begin with a digit or `-`, and the single character `_` is not an identifier.

A math string is a sequence of characters quoted by `$`. Inside a math string `$` cannot appear.

These strings will go through a secondary lexing phase, using a dynamic lexer defined by the notations in the file.

Pseudo-keywords
---

The following words appear in the syntax with special meanings:

    axiom coercion def infixl infixr max nonempty notation output
    prec prefix provable pure sort strict term theorem var

However, they are not really "keywords" because the grammar never permits these words to appear where an identifier can also appear. So they are lexed simply as identifiers, and it is permissible to declare a variable, sort, or theorem with one of these keywords as its name.

Grammar for the `.mm0` file format
===

An `.mm0` file is a list of directives. Directives are used to declare sorts, define axioms, definitions, and theorems, as well as notation to be used in the inline math blocks. Directives are block structured, with `{` `}` enclosing scopes.

    mm0-file ::= (directive)*
    directive ::= statement | '{' (directive)* '}'
    statement ::= sort-stmt
               |  var-stmt
               |  term-stmt
               |  assert-stmt
               |  def-stmt
               |  notation-stmt
               |  output-stmt

Sorts
---
    sort-stmt ::= ('pure')? ('strict')? ('provable')? ('nonempty')? 'sort' identifier ';'

The underlying semantics of metamath zero is based on multi-sorted first order logic. The `sort` keyword declares a new sort. There are several properties that a sort may or may not have, indicated by modifiers on the sort declaration.

* `pure` means that this sort does not have any term formers. It is an uninterpreted domain which may have variables but has no constant symbols, binary operators, or anything else targeting this sort. If a sort has this modifier, it is illegal to declare a `term` with this sort as the target.
* `strict` is the "opposite" of `pure`: it says that the sort does not have any variable binding operators. It is illegal to have a variable of this sort appear as a dependency in another variable. For example, if `x: set` and `ph: wff x` then `set` must not be declared `strict`. (`pure` and `strict` are not mutually exclusive, although a sort with both properties is not very useful.)
* `provable` means that the sort is a thing that can be "proven". All formulas appearing in axioms and definitions (between `$`) must have a provable sort.
* `nonempty` means that theorems and definitions are permitted to introduce dummy variables of this sort.

Variables and types
---

    var-stmt ::= 'var' (identifier)* ':' open-type ';'
    type ::= identifier (identifier)*
    open-type ::= type | identifier '*'

A variable statement does not represent any actual statement or theorem, it just sets up variable names with their types so that they may be inferred in later `term`s, `axiom`s, `def`s and `theorem`s. See "Variable Inference" for details on how the inference process works. In the statement itself, we can declare a list of variables with type dependencies.

A type is the name of a sort followed by 0 or more variable names, which represent the values this variable is allowed to depend on. An open type is either a type, or a sort followed by a `*`, representing all variable dependencies.

Term constructors
---
The `term` directive constructs a new piece of syntax, a function symbol on the sorts. The syntax permits two ways to list the arguments of the function, via binders or as a simple function. The names are not used except in dependencies of the types, so `term imp (ph ps: wff): wff;` and `term imp: wff -> wff -> wff` mean the same thing. The symbol `_` in place of an identifier indicates an anonymous variable.

    term-stmt ::= 'term' identifier (type-binder)* ':' arrow-type ';'
    identifier_ ::= identifier | '_'
    type-binder ::= '(' (identifier_)* ':' type ')'
    arrow-type ::= type | type '>' arrow-type

Axioms and theorems
---
An `axiom` and a `theorem` appear exactly the same in the specification file, although only one will require a proof. The syntax is similar to term constructors but now rather than just types, a binder may have a formula as its type. A formula is any sequence of tokens other than `$`, fenced by `$`. The `$` may be escaped by reduplication `$$`.

    assert-stmt ::= ('axiom' | 'theorem') identifier
       (formula-type-binder)* ':' formula-arrow-type ';'
    formula-type-binder ::= '(' (identifier_)* ':' (type | formula) ')'
    formula-arrow-type ::= formula | (type | formula) '>' arrow-type
    formula ::= math-string

Definitions
---
A `def` is similar to an `axiom` except that it may also have dot-quantifiers, representing dummy variables in the definition that are not exposed in the syntax. It also ends with a block rather than a semicolon, because the definition itself has a limited lifetime. Inside the block, the definition is unfolded for the purpose of the proof, and it is made opaque once the block is exited.

    def-stmt ::= 'def' identifier (dummy-binder)* ':'
      type '=' formula '{' (directive)* '}'
    dummy-binder ::= '(' (dummy-identifier)* ':' type ')'
    dummy-identifier ::= '.' identifier | identifier_

Notations
---
The notation system is intended to be a minimal operator precedence parser. There is support for `prefix` and `infix` notations, `coercion` (nameless notation), and `notation` for everything else. The precedence levels are nonnegative integers, or `max`, representing infinity.

* A `prefix` constructor parses its argument with the given precedence. It should be a unary syntax operator.

* An `infixl` or `infixr` constructor uses the given precedence for the level of the operator, which should be unique. `infixl` means that the operator is left-associative, and `infixr` means it is right-associative.

* A `coercion` between distinct sorts means that the given syntax axiom will be silently inserted to convert from one sort to another.

* `notation` allows an arbitrary sequence of constants and variables (annotated with precedence) to act as a notation. To ensure unambiguity, we require that the first token be a constant unique to this notation.

As an additional check, `notation` requires its variables be annotated with types.

    notation-stmt ::= simple-notation-stmt | coercion-stmt | gen-notation-stmt
    simple-notation-stmt ::= ('infixl' | 'infixr' | 'prefix') identifier ':'
      constant 'prec' precedence-lvl ';'
    constant ::= math-string
    precedence-lvl ::= number | 'max'
    coercion-stmt ::= 'coercion' identifier ':' identifier '>' identifier ';'
    gen-notation-stmt ::= 'notation' identifier (type-binder)* ':'
      type '=' (notation-literal)+ ';'
    notation-literal ::= constant | prec-variable
    prec-variable ::= '(' identifier ':' precedence-lvl ')'

Output
---

*Note*: This command is optional, even more so than the rest of this specification.

    output-stmt ::= 'output' output-kind identifier (formula-dummy-binder)* ';'
    formula-dummy-binder ::= '(' (dummy-identifier)* ':' (type | formula) ')'
    output-kind ::= identifier

The `output` command allows the verifier to produce an output of some kind, in an implementation-defined manner. The manner in which output is produced is controlled by the `output-kind`, which specifies the target format, for example `s-expr`, or a program language such as `g` or `x86_asm`. The details vary depending on the target, but this can be read as an *existential* statement, by contrast to `theorem`, which proves universal statements. A statement such as

    output c halting (e: c-expr) (.x: set) (_: $ A. x e. Input halts(e, x) $);

might assert that the verifier produces a C source file described by `e`, which always halts when executed on any input. Or more simply:

    output s-expr halting (ph: wff) (h: $ ph $);

would print the s-expression corresponding to some provable wff. The proof file is responsible for demonstrating the existential witness - the program that halts, or the provable wff - and the verifier is responsible for interpreting the term from the logic as a string to output or a file to produce.

Interpretation
===

There are two notions of correctness for a specification file. First, it can be *well-formed*, meaning that the file meets the above grammar, all the formulas are syntactically correct, and in this case we have a well defined notion of what the assertions in the file are. Second, it can be *proven*, meaning that the assertions in the file in fact hold - all theorems follow from the axioms. This distinction is not essential, and the choice of what counts as well-formedness is somewhat arbitrary, but roughly speaking a verifier doesn't need to consult the proof file to determine that the specification file is well formed, but it will need more help to check that it is correct, unless it is really good at guessing proofs.

When `output` is involved, the specification describes a relation that should hold on the output of the verifier on success.

TODO

Variable inference
---

A theorem may reference variables inside types and formulas that are not explicitly bound in the declaration. Variable inference is the process by which these variables, declared in the local scope, are automatically inserted into the theorem statement.

Additionally, at this stage variables are organized into two types, bound variables and regular variables. Dummy variables (in dot binders) are always bound. A variable is considered regular unless it is required to be bound.

* Bound variables may not have a dependent type.
* Bound variables may not have a `strict` type.
* All variables appearing as dependencies of a type must be bound.
* If a term constructor has an bound argument, then the substitution to this argument must be a variable, and that variable must be bound.

For example:

    var x y z: set;
    var ph ps: wff*;
    theorem foo (x: set) (ph: wff y): $ A. x A. z (ph /\ ps) $ -> $ ps $;

Here the binder `(ph: wff y)` refers to `y` which is not among the previous binders, and the first hypothesis `$ A. x A. z (ph /\ ps) $` refers to `z`, and `ps`, neither of which are declared.

Note that `x` and `ph` are both declared in the local scope; these declarations are ignored because their names are *shadowed* by the theorem binders.

Inference processing proceeds from left to right on the variable bindings, including the arrow bindings. The above theorem has three bindings: `(x: set)`, `(ph: wff y)` and the anonymous binding `(_: $ A. x A. z (ph /\ ps) $)`. Bindings come in three groups: the nondependent bindings, the dependent variable bindings, and the formulas. It is an error for the explicit bindings to come out of order, and the inferred bindings are added at the boundaries between these groups.

For variables with simple types, like `(x: set)`, no variables are inferred. For `(ph: wff y)`, this variable depends on `y` and so `(y: set)` is inserted at the end of the nondependent bindings (after `x`). Bindings are inserted in the order they appear in the type.

For formulas, binders are inserted in the order they appear in the syntax tree. The syntax tree of the example is `wal x (wal z (wa ph ps))`, and so we check for `x,z,ph,ps` in turn that they appear in the binder list, and insert the ones that don't. So this would add `(z: set)` as a nondependent bound variable binder and `(ps: wff*)` as a dependent binder. (This is not a proper type yet, but we defer resolution of the open type.) Finally, we look at the target formula `ps` and we don't need to do anything because the variable is already present.

Once all the bindings are accumulated, all the variables with open types are given types that depend on all bound variables. So `(ps: wff*)` becomes `(ps: wff x y z)`. The end result is:

    theorem foo (x y z: set) (ph: wff y) (ps: wff x y z)
      (_: $ A. x A. z (ph /\ ps) $): $ ps $;

and this is the version of the theorem that is proven in the proof file.

For definitions, the process is the same except that inferred bound variables are marked as dummy variables if possible (if they do not appear as a type dependency). It is illegal for a bound variable in a definition to not appear as a type dependency to some other variable.

Definition substitution
---

Inside a definition block, theorems are permitted to reference the definition, and even between theorems in the same definition block the definition appears "unexpanded", but the actual proof obligations use expanded forms of the definition. For example:

    def wb (ph ps: wff): wff = $ ~((ph -> ps) -> ~(ps -> ph)) $ {
      infixl wb: $<->$ prec 20;

      theorem bi1: $ (ph <-> ps) -> ph -> ps $;
      theorem bi2: $ (ph <-> ps) -> ps -> ph $;
      theorem bi3: $ (ph -> ps) -> (ps -> ph) -> (ph <-> ps) $;
    }

From the point of view of any other theorem, including `bi2` and `bi3`, `bi1` has the statement `$ (ph <-> ps) -> ph -> ps $`, but the proof obligation corresponding to `bi1` is actually:

      theorem bi1 (ph ps: wff): $ ~((ph -> ps) -> ~(ps -> ph)) -> ph -> ps $ = ...;

These modified theorem statements are calculated as follows:

* Starting from the original syntax tree `wi (wb ph ps) (wi ph ps)`, find all occurrences of `wb e1 e2` where `e1` and `e2` are the subtrees.
* Let `e` be the syntax tree for the definition, `wn (wi (wi ph ps) (wn (wi ps ph)))`.
* Rename each dummy variable in the definition with a fresh name, to form `e'`. (In this case `e' = e`.)
* Substitute `e1` and `e2` for the variables in the definition bindings `ph` and `ps`. In this case `e1 = ph` and `e2 = ps` so the result is `e'' = e` again.
* Replace the original subtree `wb e1 e2` with this expression `e''`.
* Repeat for all instances of `wb` in the expression.

As an example of nontrivial modifications:

    def weu (x .y: set) (ph: wff x): wff = $ E. y A. x (ph <-> x =s y) $ {
      prefix wex: $E!$ prec 30;

      theorem df-eu: $ E! x ph <-> E. y A. x (ph <-> x = y) $;
      theorem example (x y: set) (ph: wff x): $ E! x E! y ph $;
    }

translates to:

    theorem df-eu (x y y': set) (ph: wff x):
      $ E. y' A. x (ph <-> x = y') <-> E. y A. x (ph <-> x = y) $ = ...;
    theorem example (x y y' y'': set) (ph: wff x):
      $ E. y'' A. x ((E. y' A. y (ph <-> y =s y')) <-> x =s y'') $ = ...;

Proof files
===

The syntax of a proof file is implementation dependent, but we will give one possible format, used by the reference implementation. It is designed to be read and used by the verifier in an efficient and convenient way. Usually, such a file will be compiled from another language to prepare it for use by the verifier. The contents of the proof file do not affect the correctness of any of the theorems in the specification file. At worst, the verifier will fail on a provable theorem, because it was not able to find the proof with the assistance of the proof file.

The reference implementation uses a binary proof format, but we will show it with a similar syntax to the `.mm0` format for convenience.

For the [set.mm0](set.mm0) running example, which begins as:

    strict provable nonempty sort wff;
    var ph ps ch: wff*;
    term wi (ph ps: wff): wff; infixr wi: $->$ prec 25;
    term wn (ph: wff): wff; prefix wn: $~$ prec 40;

    axiom ax-1: $ ph -> ps -> ph $;
    axiom ax-2: $ (ph -> ps -> ch) -> (ph -> ps) -> ph -> ch $;
    axiom ax-3: $ (~ph -> ~ps) -> ps -> ph $;
    axiom ax-mp: $ ph $ -> $ ph -> ps $ -> $ ps $;

    theorem a1i: $ ph $ -> $ ps -> ph $;

    def wb (ph ps: wff): wff = $ ~((ph -> ps) -> ~(ps -> ph)) $ {
      infixl wb: $<->$ prec 20;

      theorem bi1: $ (ph <-> ps) -> ph -> ps $;
      theorem bi2: $ (ph <-> ps) -> ps -> ph $;
      theorem bi3: $ (ph -> ps) -> (ps -> ph) -> (ph <-> ps) $;
    }

the corresponding section of the proof file might look like:

    sort wff;
    term wi;
    term wn;

    axiom ax-1;
    axiom ax-2;
    axiom ax-3;
    axiom ax-mp;

    new theorem mp2 (ph ps ch: wff) (h1: $ ph $) (h2: $ ps $)
      (h3: $ ph -> ps -> ch $): $ ch $ =
      ax-mp ps ch h2 (ax-mp ph $ps -> ch$ h1 h3);

    theorem a1i (ph ps: wff) (h1: $ ph $): $ ps -> ph $ =
      ax-mp ph $ps -> ph$ h1 (ax-1 ph ps);

    theorem bi1 (ph ps: wff): $ ~((ph -> ps) -> ~(ps -> ph)) -> ph -> ps $ = ...;
    theorem bi2 (ph ps: wff): $ ~((ph -> ps) -> ~(ps -> ph)) -> ps -> ph $ = ...;
    theorem bi3 (ph ps: wff): $ (ph -> ps) -> (ps -> ph) -> ~((ph -> ps) -> ~(ps -> ph)) $ = ...;

    new theorem biid (ph: wff): $ ph <-> ph $ = ...;

    new def wo (ph ps: wff): wff = $ ~ph -> ps $ {
      -- infixl wo: $\/$ prec 20;
      new theorem df-or (ph ps: wff): $ (ph \/ ps) <-> (~ph -> ps) $ =
        proof (ph ps: wff): $ (~ph -> ps) <-> (~ph -> ps) $ =
          biid $ ~ph -> ps $;
    }


The declarations must come in the same order as they appear in the specification file. The `term` and `axiom` declarations serve only to move the "pointer" through the file, acknowledging that these axioms are now available for use in proofs. The theorem `mp2` in this example does not exist in the specification file; this is permitted. Similarly definitions may be added beyond those present in the specification file, and they may be referenced in proofs as well. These follow the same rules as declarations in the specification file itself, with the following modifications:

* `sort`, `term` and `axiom` only refer to the corresponding directive by name and provide no definition. These must be declared in the same order as in the specification file.
* There are no notation commands. (The math strings appearing above are only there for readability; the actual proof file format uses s-expressions in RPN.)
* There are no `var` statements and no variable inference. All variables are declared in the theorems.
* In the concrete syntax above, `new theorem` means the statement was not declared in the specification file, while `theorem`s have corresponding statements. The statements must be given in the same order as in the specification file.
* Similarly `new def` allows the declaration of definitions that do not appear in the specification.
  * Theorems in a new definition block have two theorem statements, indicated with the ad hoc notation `new theorem foo: ... = proof ... = ...` above. The first is the "global" version, which is how this theorem appears to users of the theorem; the second is the version that is proved. The verifier should check that the second statement is obtained from the first by substitution of the definition, as in regular definition blocks.
