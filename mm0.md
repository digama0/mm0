Metamath Zero
===

> *Warning:* This spec has not yet stabilized. If you are interested in writing a verifier for this spec you should stay appraised for changes to the spec.

This is a language for writing specifications and proofs. Its emphasis is on balancing simplicity of verification and human readability, with the intent that a skeptical auditor can be convinced of the following:

1. The verifier is implemented correctly to this specification (by reading the code)
2. This specification ensures that a conforming verifier checks that programs meet their specifications (by a paper proof or formalization, forthcoming)
3. The input specification to the verifier correctly describes an axiom system `A`, and the stated theorems are correct transcriptions of theorems `T1,...,Tn` (by reading the specification file)

From the conjunction of these properties, the auditor finds that `A |- T1,...,Tn`, and if they believe `A` is true or representative of the world then they may conclude that `T1,...,Tn` are as well.

Input to a Metamath Zero verifier consists of two parts: a "specification" or "header file", with extension `.mm0`, and a "proof" file with extension `.mp0`. The specification file contains axioms, definitions, and theorem statements, while the proof file contains proofs of the theorems and auxiliary data.

The major distinction between the two files is that in the hypothetical auditing  process above, *the `.mp0` file plays no role*. All information relevant to correctness of the final result is put in the `.mm0` file, and the `.mp0` file is nothing more than an extended "hint" to the verifier to show why the theorems in the `.mm0` file are true. As such, the format of the `.mp0` file is not officially specified, although there is a recommended format (see [?]).

See [examples/set.mm0](examples/set.mm0) for an example of a `.mm0` file.

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
    identifier ::= [a-zA-Z_][a-zA-Z0-9_]*
    number ::= 0 | [1-9][0-9]*
    math-string ::= '$' [^\$]* '$'

A lexeme is either one of the symbols, an identifier, a number (nonnegative integer), or a math string. An identifier is a sequence of alphanumeric symbols, together with `_`, except that it cannot begin with a digit, and the single character `_` is not an identifier.

A math string is a sequence of characters quoted by `$`. Inside a math string `$` cannot appear.

These strings will go through a secondary lexing phase, using a dynamic lexer defined by the notations in the file.

Pseudo-keywords
---

The following words appear in the syntax with special meanings:

    axiom coercion def delimiter free infixl infixr max notation output
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
    sort-stmt ::= ('pure')? ('strict')? ('provable')? ('free')? 'sort' identifier ';'

The underlying semantics of metamath zero is based on multi-sorted first order logic. The `sort` keyword declares a new sort. There are several properties that a sort may or may not have, indicated by modifiers on the sort declaration.

* `pure` means that this sort does not have any term formers. It is an uninterpreted domain which may have variables but has no constant symbols, binary operators, or anything else targeting this sort. If a sort has this modifier, it is illegal to declare a `term` with this sort as the target.
* `strict` is the "opposite" of `pure`: it says that the sort does not have any variable binding operators. It is illegal to have a variable of this sort appear as a dependency in another variable. For example, if `x: set` and `ph: wff x` then `set` must not be declared `strict`. (`pure` and `strict` are not mutually exclusive, although a sort with both properties is not very useful.)
* `provable` means that the sort is a thing that can be "proven". All formulas appearing in axioms and definitions (between `$`) must have a provable sort.
* `free` means that theorems and definitions are not permitted to introduce dummy variables of this sort.

Variables and types
---

    var-stmt ::= 'var' (identifier)* ':' var-type ';'
    var-type ::= identifier '*'?

A variable statement does not represent any actual statement or theorem, it just sets up variable names with their types so that they may be inferred in later `term`s, `axiom`s, `def`s and `theorem`s. See "Variable Inference" for details on how the inference process works. In the statement itself, we can declare a list of variables with type dependencies.

A type is the name of a sort followed by 0 or more variable names, which represent the values this variable is allowed to depend on. In variable declarations, dependent sorts are not permitted, but a type may be declared with a trailing `*`, representing that this variable depends on all bound variables in statements.

Term constructors
---
The `term` directive constructs a new piece of syntax, a function symbol on the sorts. The syntax permits two ways to list the arguments of the function, via binders or as a simple function. The names are not used except in dependencies of the types, so `term imp (ph ps: wff): wff;` and `term imp: wff -> wff -> wff` mean the same thing. The symbol `_` in place of an identifier indicates an anonymous variable. A binder enclosed in curly braces as in `{x: set}` denotes a bound variable, which may appear in dependencies of other types (see "Variable Inference").

    term-stmt ::= 'term' identifier (type-binder)* ':' arrow-type ';'
    identifier_ ::= identifier | '_'
    type ::= identifier (identifier)*
    type-binder ::= '{' (identifier)* ':' type '}'
                 |  '(' (identifier_)* ':' type ')'
    arrow-type ::= type | type '>' arrow-type

Axioms and theorems
---
An `axiom` and a `theorem` appear exactly the same in the specification file, although only one will require a proof. The syntax is similar to term constructors but now rather than just types, a binder may have a formula as its type. A formula is any sequence of tokens other than `$`, fenced by `$`. The `$` may be escaped by reduplication `$$`.

    assert-stmt ::= ('axiom' | 'theorem') identifier
       (formula-type-binder)* ':' formula-arrow-type ';'
    formula-type-binder ::= '{' (identifier)* ':' type '}'
                         |  '(' (identifier_)* ':' (type | formula) ')'
    formula-arrow-type ::= formula | (type | formula) '>' arrow-type
    formula ::= math-string

Definitions
---
A `def` is similar to an `axiom` except that it may also have dot-quantifiers, representing dummy variables in the definition that are not exposed in the syntax.

If the definition part is omitted, then the existence of a definition satisfying the theorems is asserted.

    def-stmt ::= 'def' identifier (dummy-binder)* ':'
      type ('=' formula)? ';'
    dummy-binder ::= '{' (dummy-identifier)* ':' type '}'
                  |  '(' (dummy-identifier)* ':' type ')'
    dummy-identifier ::= '.' identifier | identifier_

Notations
---
The notation system is intended to be a minimal operator precedence parser. There is support for `prefix` and `infix` notations, `coercion` (nameless notation), and `notation` for everything else. The precedence levels are nonnegative integers, or `max`, representing infinity.

* A `delimiter` is an instruction for the secondary lexer. The secondary lexer is very simple, splitting on whitespace only, except that a token marked as a delimiter is treated as a standalone token even if it appears in a larger string. A declared token (from another notation commmand) must not contain a delimiter token as a substring, and a delimiter must not consist entirely of identifier characters. A verifier may reject this command entirely (in which case all tokens must be separated by spaces), or only allow single-character delimiters.

* A `prefix` constructor parses its argument with the given precedence.

* An `infixl` or `infixr` constructor uses the given precedence for the level of the operator, which should be unique. `infixl` means that the operator is left-associative, and `infixr` means it is right-associative.

* A `coercion` between distinct sorts means that the given syntax axiom will be silently inserted to convert from one sort to another.

* `notation` allows an arbitrary sequence of constants and variables (annotated with precedence) to act as a notation. To ensure unambiguity, we require that the first token be a constant unique to this notation.

As an additional check, `notation` requires its variables be annotated with types.

    notation-stmt ::= delimiter-stmt
                   |  simple-notation-stmt
                   |  coercion-stmt
                   |  gen-notation-stmt
    delimiter-stmt ::= 'delimiter' math-string ';'
    simple-notation-stmt ::= ('infixl' | 'infixr' | 'prefix') identifier ':'
      constant 'prec' precedence-lvl ';'
    constant ::= math-string
    precedence-lvl ::= number | 'max'
    coercion-stmt ::= 'coercion' identifier ':' identifier '>' identifier ';'
    gen-notation-stmt ::= 'notation' identifier (type-binder)* ':'
      type '=' prec-constant (notation-literal)* ';'
    notation-literal ::= prec-constant | identifier
    prec-constant ::= '(' constant ':' precedence-lvl ')'

Output
---

*Note*: This command is optional, even more so than the rest of this specification.

    output-stmt ::= 'output' output-kind identifier (formula-dummy-binder)* ';'
    formula-dummy-binder ::= '{' (dummy-identifier)* ':' type '}'
                          |  '(' (dummy-identifier)* ':' (type | formula) ')'
    output-kind ::= identifier

The `output` command allows the verifier to produce an output of some kind, in an implementation-defined manner. The manner in which output is produced is controlled by the `output-kind`, which specifies the target format, for example `s-expr`, or a program language such as `g` or `x86_asm`. The details vary depending on the target, but this can be read as an *existential* statement, by contrast to `theorem`, which proves universal statements. A statement such as

    output c halting (e: c-expr) (.x: set) (_: $ A. x e. Input halts(e, x) $);

might assert that the verifier produces a C source file described by `e`, which always halts when executed on any input. Or more simply:

    output s-expr halting (ph: wff) (h: $ ph $);

would print the s-expression corresponding to some provable wff. The proof file is responsible for demonstrating the existential witness - the program that halts, or the provable wff - and the verifier is responsible for interpreting the term from the logic as a string to output or a file to produce.

Secondary parsing
===

In the grammar above, math strings are simply treated as strings, deferring interpretation of the strings until after main parsing. Verifiers may choose to interpret math strings on the spot (in a single pass), or collect all notations and build a parser to run on all strings (two pass). A consequence of the two pass approach is that notations may be used before they are defined in the file, for example:

    term wi (ph ps: wff): wff;
    axiom ax-1 (ph ps: wff): $ ph -> ps -> ph $;
    infix wi: $->$ prec 25;

Verifiers are allowed but not required to support out of order notation declarations. However, out of order term definitions are not permitted:

    axiom ax-1 (ph ps: wff): $ ph -> ps -> ph $; -- error: wi not defined
    term wi (ph ps: wff): wff;
    infix wi: $->$ prec 25;

Tokenization is somewhat simpler than primary lexical analysis. We can partition the string into substrings such that the beginning and end of every delimiter substring or whitespace sequence is a split point, and interpret each substring in the partition as a token, discarding the whitespace. For example, if the delimiters are `(`, `)` and `**`, then `a**b(***{}) c` tokenizes as `'a', '**', 'b', '(', '**', '*{}', ')', 'c'`. It is illegal to write a string with an ambiguous tokenization. (Verifiers may choose to check this on a per-string basis, or use single-character delimiters or other restrictions to ensure that this property holds.)

    math-string ::= (math-lexeme | math-whitespace)*
    math-whitespace ::= whitechar+
    math-lexeme ::= math-symbol | identifier | '(' | ')'
    math-symbol ::= OP  (if OP appears in a infix/prefix/notation declaration)
    constant-tk ::= any string of non-whitespace non-$ characters

Notations are intended to be parsed by an operator precedence parser [[1]](https://en.wikipedia.org/wiki/Operator-precedence_parser). The expressions are given by a context free grammar with nonterminals for each precedence level. Precedences are taken from the set of nonnegative integers with infinity adjoined (called `max` in the syntax). Verifiers should support precedences up to at least `2^11 - 2 = 2046`.

    math-string ::= '$' expression(0) '$'
    constant ::= '$' whitechar* constant-tk whitechar* '$'

The nonterminals `expression(prec)` are defined by the following productions:

    expression(p1) <- expression(p2)                   (if p1 < p2)
    expression(max) <- '(' expression(0) ')'
    expression(max) <- VAR                             (if VAR is a variable in scope)
    expression(1024) <- FUNC expression(max){n}        (if FUNC is an n-ary term constructor)
    expression(p) <- OP expression(max){n} expression(p)
                                                       (if OP is is n+1-ary prefix prec p)
    expression(p) <- expression(p) OP expression(p+1)  (if OP is infixl prec p)
    expression(p) <- expression(p+1) OP expression(p)  (if OP is infixr prec p)
    expression(p) <- c X(lits, p)  where               (if notation := (c: p) lits)
      X((c: p) lits, q) = c X(lits, q)
      X(v (c: p) lits, q) = expression(p+1) X((c: p) lits, q)
      X(v1 v2 lits, q) = expression(max) X(v2 lits, q)
      X(v, q) = expression(q)

The term constructors appear in the syntax as s-expressions at precedence level `1024`. `notation` commands have precedences on the constants, such that the precedence on the immediately preceding variable is one higher. There are rules on notations to prevent an ambiguous parse:

* A constant is infixy if it is used in an `infix` command (with the given precedence), or if it appears immediately after a variable in a `notation` command (and it acquires the precedence of this variable). The precedence of an infixy constant must be unique.
* An `infix` command must have a precedence less than `max`.
* The first token of a `notation` must be a constant, and must not be shared with any other `prefix` constant or infixy constant.
* If two variables are adjacent in a `notation`, the first one must have precedence `max`.

If a math string is parsed successfully, the result is a syntax tree whose nodes are given by the term constructors referenced by the notations. Type checking is performed during or after this process, from inside out. If an expression with one sort is used in an argument with a different sort, `coercion` functions are inserted. The rules on `coercions`:

* The collection of sorts and coercions should form a directed graph, whose undirected counterpart is acyclic.

There is thus at most one path from one sort to another, and these coercion functions are inserted. If no path exists this is a type error.

Interpretation
===

There are two notions of correctness for a specification file. First, it can be *well-formed*, meaning that the file meets the above grammar, all the formulas are syntactically correct, and in this case we have a well defined notion of what the assertions in the file are. Second, it can be *proven*, meaning that the assertions in the file in fact hold - all theorems follow from the axioms. This distinction is not essential, and the choice of what counts as well-formedness is somewhat arbitrary, but roughly speaking a verifier doesn't need to consult the proof file to determine that the specification file is well formed, but it will need more help to check that it is correct, unless it is really good at guessing proofs.

When `output` is involved, the specification describes a relation that should hold on the output of the verifier on success.

TODO

Variable inference
---

A theorem may reference variables inside types and formulas that are not explicitly bound in the declaration. Variable inference is the process by which these variables, declared in the local scope, are automatically inserted into the theorem statement. To prevent ambiguity of inferred variable order, `term`s and `def`s are not permitted to use inferred variables, although `def`s may infer dummy variables used in the definition.

Additionally, variables are organized into two types, bound variables and regular variables. For variables in the given binder list, this is denoted by curly braces for bound variables and parentheses for regular variables. Dummy variables (in dot binders) are always bound. An inferred variable is considered regular unless it is required to be bound.

* Bound variables may not have a dependent type.
* Bound variables may not have a `strict` type.
* All variables appearing as dependencies of a type must be bound.
* If a term constructor has an bound argument, then the substitution to this argument must be a variable, and that variable must be bound.

For example:

    var x y z: set;
    var ph ps: wff*;
    theorem foo {x: set} (ph: wff y): $ A. x A. z (ph /\ ps) $ > $ ps $;

Here the binder `(ph: wff y)` refers to `y` which is not among the previous binders, and the first hypothesis `$ A. x A. z (ph /\ ps) $` refers to `z`, and `ps`, neither of which are declared.

Note that `x` and `ph` are both declared in the local scope; these declarations are ignored because their names are *shadowed* by the theorem binders.

Inferred variables are unordered in the specification file. Verifiers are permitted to enforce any standard ordering in the proof file (for example, alphabetical order). The above theorem has three bindings: `{x: set}`, `(ph: wff y)` and the anonymous binding `(_: $ A. x A. z (ph /\ ps) $)`. Bindings come in three groups: the (nondependent) bound variables, the regular variable bindings, and the formulas. It is an error for the explicit bindings to come out of order.

For bound variables and variables with simple types, like `{x: set}`, no variables are inferred. For `(ph: wff y)`, this variable depends on `y` and so `{y: set}` is inferred.

For formulas, any variables that are referenced in the syntax tree are inferred. The syntax tree of the example is `wal x (wal z (wa ph ps))`, and so we check for `x,z,ph,ps` that they appear in the binder list, and insert the ones that don't. So this would add `{z: set}` as a bound variable binder and `(ps: wff*)` as a dependent binder. (This is not a proper type yet, but we defer resolution of the open type.) Finally, we look at the target formula `ps` and we don't need to do anything because the variable is already present.

Once all the bindings are accumulated, all the variables with open types are given types that depend on all bound variables. So `(ps: wff*)` becomes `(ps: wff x y z)`. The end result is:

    theorem foo {x y: set} (ph: wff y) {z: set} (ps: wff x y z)
      (_: $ A. x A. z (ph /\ ps) $): $ ps $;

and this is the version of the theorem that is proven in the proof file.

For definitions, the process is the same except that inferred bound variables are marked as dummy variables. It is illegal for a bound variable in a definition to not appear as a type dependency to some other variable.

Definition substitution
---

In the proof file, definitions may be unfolded in the statement of a theorem. This has the effect that the statement being proven is obtained by definition substitution from the given statement. For example:

    def wb (ph ps: wff): wff = $ ~((ph -> ps) -> ~(ps -> ph)) $;
    infixl wb: $<->$ prec 20;

    theorem bi1: $ (ph <-> ps) -> ph -> ps $;
    theorem bi2: $ (ph <-> ps) -> ps -> ph $;
    theorem bi3: $ (ph -> ps) -> (ps -> ph) -> (ph <-> ps) $;

From the point of view of any other theorem, `bi1` has the statement `$ (ph <-> ps) -> ph -> ps $`, but the proof obligation corresponding to `bi1` is actually:

    theorem bi1 (ph ps: wff): $ ~((ph -> ps) -> ~(ps -> ph)) -> ph -> ps $ = ...;

These modified theorem statements are calculated as follows:

* Starting from the original syntax tree `wi (wb ph ps) (wi ph ps)`, find all occurrences of `wb e1 e2` where `e1` and `e2` are the subtrees.
* Let `e` be the syntax tree for the definition, `wn (wi (wi ph ps) (wn (wi ps ph)))`.
* Rename each dummy variable in the definition with a fresh name, to form `e'`. (In this case `e' = e`.)
* Substitute `e1` and `e2` for the variables in the definition bindings `ph` and `ps`. In this case `e1 = ph` and `e2 = ps` so the result is `e'' = e` again.
* Replace the original subtree `wb e1 e2` with this expression `e''`.
* Repeat for all instances of `wb` in the expression.

As an example of nontrivial modifications:

    def weu {x .y: set} (ph: wff x): wff = $ E. y A. x (ph <-> x =s y) $;
    prefix wex: $E!$ prec 30;

    theorem df-eu: $ E! x ph <-> E. y A. x (ph <-> x = y) $;
    theorem example {x y: set} (ph: wff x): $ E! x E! y ph $;

translates to:

    theorem df-eu {x y y': set} (ph: wff x):
      $ E. y' A. x (ph <-> x = y') <-> E. y A. x (ph <-> x = y) $ = ...;
    theorem example {x y y' y'': set} (ph: wff x):
      $ E. y'' A. x ((E. y' A. y (ph <-> y =s y')) <-> x =s y'') $ = ...;

Proof files
===

The syntax of a proof file is implementation dependent, but we will give one possible format, used by the reference implementation. It is designed to be read and used by the verifier in an efficient and convenient way. Usually, such a file will be compiled from another language to prepare it for use by the verifier. The contents of the proof file do not affect the correctness of any of the theorems in the specification file. At worst, the verifier will fail on a provable theorem, because it was not able to find the proof with the assistance of the proof file.

The reference implementation uses a binary proof format, but we will show it with a similar syntax to the `.mm0` format for convenience.

For the [set.mm0](set.mm0) running example, which begins as:

    strict provable sort wff;
    var ph ps ch: wff*;
    term wi (ph ps: wff): wff; infixr wi: $->$ prec 25;
    term wn (ph: wff): wff; prefix wn: $~$ prec 40;

    axiom ax-1: $ ph -> ps -> ph $;
    axiom ax-2: $ (ph -> ps -> ch) -> (ph -> ps) -> ph -> ch $;
    axiom ax-3: $ (~ph -> ~ps) -> ps -> ph $;
    axiom ax-mp: $ ph $ > $ ph -> ps $ > $ ps $;

    theorem a1i: $ ph $ > $ ps -> ph $;

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
