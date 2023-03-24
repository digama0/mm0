Metamath Zero
===

> *Warning:* This spec has not yet stabilized. If you are interested in writing a verifier for this spec you should stay appraised for changes to the spec.

This is a language for writing specifications and proofs. Its emphasis is on balancing simplicity of verification and human readability, with the intent that a skeptical auditor can be convinced of the following:

1. The verifier is implemented correctly to this specification (by reading the code)
2. This specification ensures that a conforming verifier checks that programs meet their specifications (by a paper proof or formalization, forthcoming)
3. The input specification to the verifier correctly describes an axiom system `A`, and the stated theorems are correct transcriptions of theorems `T1,...,Tn` (by reading the specification file)

From the conjunction of these properties, the auditor finds that `A |- T1,...,Tn`, and if they believe `A` is true or representative of the world then they may conclude that `T1,...,Tn` are as well.

Input to a Metamath Zero verifier consists of two parts: a "specification" or "header file", with extension `.mm0`, and a "proof" file with implementation-defined extension. The specification file contains axioms, definitions, and theorem statements, while the proof file contains proofs of the theorems and auxiliary data.

The major distinction between the two files is that in the hypothetical auditing  process above, *the proof file plays no role*. All information relevant to correctness of the final result is put in the `.mm0` file, and the proof file is nothing more than an extended "hint" to the verifier to show why the theorems in the `.mm0` file are true. As such, the format of the proof file is not officially specified, although there is a recommended format (see [the MMB file format](mm0-c/mmb.md)).

See [examples/set.mm0](examples/set.mm0) for an example of a `.mm0` file.

Unlike many specifications of a similar kind, this specification should be read as an *upper bound* on allowable specification files. That is, a conforming implementation need not support all of the specification, and may fail for implementation-defined reasons. The important property verifiers must have is that a specification that is accepted by the verifier should be correct to the specification.

Lexical structure
===

    file ::= (lexeme | whitespace)*

The file is separated out into a list of lexemes, or tokens, according to the "maximum munch" principle: the longest matching token is used when ambiguity is possible.

    whitespace ::= whitestuff+
    whitestuff ::= whitechar | line-comment
    whitechar ::= ' ' | '\n'
    line-comment ::= '--' [^\n]* '\n'

Whitespace is a sequence of spaces and newlines. Comments are line comments, begining with `--` and continuing to the end of the line.

> *Note for Windows users*: For portability reasons, carriage returns are **not** legal characters in a .mm0 file. Make sure your text editor is set to LF line endings.

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

    axiom coercion def delimiter free infixl infixr input max notation
    output prec prefix provable pure sort strict term theorem

However, they are not really "keywords" because due to the structure of the grammar, whenever these words are used with their special meanings, an identifier would not be valid at that position. So they are lexed simply as identifiers, and it is permissible to declare a variable, sort, or theorem with one of these keywords as its name.

Grammar for the `.mm0` file format
===

An `.mm0` file is a list of statements. Statements are used to declare sorts, define axioms, definitions, and theorems, as well as notation to be used in the inline math blocks.

    mm0-file ::= (statement)*
    statement ::= sort-stmt
               |  term-stmt
               |  assert-stmt
               |  def-stmt
               |  notation-stmt
               |  inout-stmt

Sorts
---
    sort-stmt ::= ('pure')? ('strict')? ('provable')? ('free')? 'sort' identifier ';'

The underlying semantics of metamath zero is based on multi-sorted first order logic. The `sort` keyword declares a new sort. There are several properties that a sort may or may not have, indicated by modifiers on the sort declaration.

* `pure` means that this sort does not have any term formers. It is an uninterpreted domain which may have variables but has no constant symbols, binary operators, or anything else targeting this sort. If a sort has this modifier, it is illegal to declare a `term` with this sort as the target.
* `strict` is the "opposite" of `pure`: it says that the sort does not have any variable binding operators. It is illegal to have a bound variable or dummy variable of this sort, and it cannot appear as a dependency in another variable. For example, if `x: set` and `ph: wff x` then `set` must not be declared `strict`. (`pure` and `strict` are not mutually exclusive, although a sort with both properties is not very useful.)
* `provable` means that the sort is a thing that can be "proven". All formulas appearing in axioms and theorems (between `$`) must have a provable sort.
* `free` means that definitions and theorems are not allowed to use dummy variables with this sort.

Term constructors
---
The `term` directive constructs a new piece of syntax, a function symbol on the sorts. The syntax permits two ways to list the arguments of the function, via binders or as a simple function. The names are not used except in dependencies of the types, so `term imp (ph ps: wff): wff;` and `term imp: wff > wff > wff` mean the same thing. The symbol `_` in place of an identifier indicates an anonymous variable. A binder enclosed in curly braces as in `{x: set}` denotes a bound variable, which may appear in dependencies of other types (see "Variable Inference").

    term-stmt ::= 'term' identifier (type-binder)* ':' arrow-type ';'
    identifier_ ::= identifier | '_'
    type ::= identifier (identifier)*
    type-binder ::= '{' (identifier)* ':' type '}'
                 |  '(' (identifier_)* ':' type ')'
    arrow-type ::= type | type '>' arrow-type

Axioms and theorems
---
An `axiom` and a `theorem` appear exactly the same in the specification file, although only one will require a proof. The syntax is similar to term constructors but now rather than just types, a binder may have a formula as its type. A formula is any sequence of tokens other than `$`, fenced by `$`.

    assert-stmt ::= ('axiom' | 'theorem') identifier
       (formula-type-binder)* ':' formula-arrow-type ';'
    formula-type-binder ::= '{' (identifier)* ':' type '}'
                         |  '(' (identifier_)* ':' (type | formula) ')'
    formula-arrow-type ::= formula | (type | formula) '>' formula-arrow-type
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

* A `delimiter` is an instruction for the secondary lexer. The secondary lexer is very simple, splitting on whitespace only, except that a token marked as a delimiter is treated as a standalone token even if it appears in a larger string. A declared token (from another notation command) must not contain a delimiter token as a substring, and a delimiter must not consist entirely of identifier characters. A verifier may reject this command entirely (in which case all tokens must be separated by spaces), or only allow single-character delimiters.

* A `prefix` constructor parses its argument with the given precedence.

* An `infixl` or `infixr` constructor uses the given precedence for the level of the operator, which should be unique. `infixl` means that the operator is left-associative, and `infixr` means it is right-associative.

* A `coercion` between distinct sorts means that the given syntax axiom will be silently inserted to convert from one sort to another.

* `notation` allows an arbitrary sequence of constants and variables (annotated with precedence) to act as a notation. To ensure unambiguity, we require that the first token be a constant unique to this notation.

As an additional check, `notation` requires its variables be annotated with types.

    notation-stmt ::= delimiter-stmt
                   |  simple-notation-stmt
                   |  coercion-stmt
                   |  gen-notation-stmt
    delimiter-stmt ::= 'delimiter' math-string math-string? ';'
    simple-notation-stmt ::= ('infixl' | 'infixr' | 'prefix') identifier ':'
      constant 'prec' precedence-lvl ';'
    constant ::= math-string
    precedence-lvl ::= number | 'max'
    coercion-stmt ::= 'coercion' identifier ':' identifier '>' identifier ';'
    gen-notation-stmt ::= 'notation' identifier (type-binder)* ':'
      type '=' prec-constant (notation-literal)* ';'
    notation-literal ::= prec-constant | identifier
    prec-constant ::= '(' constant ':' precedence-lvl ')'

Input and Output
---

*Note*: This command is optional, even more so than the rest of this specification.

    inout-stmt ::= input-stmt | output-stmt
    input-stmt ::= 'input' input-kind ':' (identifier | math-string)* ';'
    output-stmt ::= 'output' output-kind ':' (identifier | math-string)* ';'
    input-kind ::= identifier
    output-kind ::= identifier

The `output` command allows the verifier to produce an output of some kind, in an implementation-defined manner. The manner in which output is produced is controlled by the `output-kind`, which specifies the target format, for example `s_expr`, or a program language such as `g` or `x86_asm`. The math string should be an expression or definition which encodes the output. A statement such as

    output c: $ my_program $;

might cause the verifier to produce a C source file described by `my_program`, which we may additionally prove theorems about (because it is a definition in the logic), such as always-halting. Note that `my_program` may be given an implicit `def`, in which case the production of such a program would be the responsibility of the proof file, and the specification is only asserting the existence of such a program. A (cheating) "hello world" program in this language might be:

    sort foo;
    term hello: foo > foo;
    term world: foo;
    output s_expr: $ hello world $;

which would print `hello world` to the console if the verifier supports s-expression printing. (Printing arbitrary strings would require significantly more encoding, because the language does not support string literals.) All definitions may be unfolded by the output command.

Complementary to this is the `input` command, which does something like the opposite. Given an implementation defined `input-kind`, the verifier will check that the `math-string` matches the encoding of some aspect of the current verifier state. For example,

    input ast: $ this_file_ast $;

will check that `this_file_ast` is an encoding of the AST of the specification file itself. Yes, this AST will even include a node for `input ast: $ this_file_ast $;` and the definition of `this_file_ast`, so for this to work the file AST would have to be encoded in the proof file.

Specific input and output commands are expected to depend on the existence of terms and definitions defined in the specification file (but not the proof file).

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

Tokenization is somewhat simpler than primary lexical analysis, and is primarily influenced by the `delimiter` command. A `delimiter` command has the form

    delimiter $ both $;
    delimiter $ left $ $ right $;

where `both`, `left`, `right` are space separated lists of non-whitespace characters to be declared as left delimiters, right delimiters, or both. Delimiters can only be one character long (although this restriction may be lifted in the future).

Given a math string, we first split the string on whitespace characters, and then further split the string *after* every left delimiter and *before* every right delimiter. All unsplit nonempty non-whitespace substrings in the result become the tokens. For example, if `(` is a left delimiter, `)` is a right delimiter, and `*` is both, then `a*b(**{}) c` tokenizes as `'a', '*', 'b(', '*', '*', '{}', ')', 'c'`.

    math-string ::= (math-lexeme | math-whitespace)*
    math-whitespace ::= whitechar+
    math-lexeme ::= math-symbol | identifier | '(' | ')'
    math-symbol ::= OP  (if OP appears in a infix/prefix/notation declaration)
    constant-tk ::= any string of non-whitespace non-$ characters

Notations are intended to be parsed by an operator precedence parser [[1]](https://en.wikipedia.org/wiki/Operator-precedence_parser). The expressions are given by a context free grammar with nonterminals for each precedence level. Precedences are taken from the set of nonnegative integers with infinity adjoined (called `max` in the syntax). Verifiers should support precedences up to at least `2^11 - 2 = 2046`.

    math-string ::= '$' expression(0) '$'
    constant ::= '$' whitechar* constant-tk whitechar* '$'

The nonterminals `expression(prec)` are defined by the following productions:

    expression(p1) -> expression(p2)                   (if p1 < p2)
    expression(max) -> '(' expression(0) ')'
    expression(max) -> VAR                             (if VAR is a variable in scope)
    expression(1024) -> FUNC expression(max){n}        (if FUNC is an n-ary term constructor)
    expression(p) -> OP expression(max){n} expression(p)
                                                       (if OP is is n+1-ary prefix prec p)
    expression(p) -> expression(p) OP expression(p+1)  (if OP is infixl prec p)
    expression(p) -> expression(p+1) OP expression(p)  (if OP is infixr prec p)
    expression(p) -> c X(lits, p)  where               (if notation foo: ... = (c: p) lits)
      X([], q) = []
      X((c: p) lits, q) = c X(lits, q)
      X(v lits, q) = expression(P(lits, q)) X(lits, q)
      P([], q) = q
      P((c: p) lits, q) = p+1
      P(v lits, q) = max

The term constructors appear in the syntax as s-expressions at precedence level `1024`. `notation` commands have precedences on the constants, such that the precedence on the immediately preceding variable is one higher. There are rules on notations to prevent an ambiguous parse:

* A constant is infixy if it is used in an `infix` command (with the given precedence), or if it appears immediately after a variable in a `notation` command (and it acquires the precedence of this variable). The precedence of an infixy constant must be unique.
* An `infix` command must have a precedence less than `max`.
* The first token of a `notation` must be a constant, and must not be shared with any other `prefix` constant or infixy constant.
* If a variable precedes a constant in a `notation`, the constant must have precedence less than `max`.
* The tokens `(` and `)` are not permitted to be declared in any notation command; they are reserved for grouping. (However the `(` and `)` characters can be used in multi-character tokens like `foo(`.)

As an example of the rule for `notation`-based productions, the notation `notation foo (a b c: T): T = ($[$:20) a b ($]$:40) c` yields the production:

    expression(20) -> '[' expression(max) expression(41) ']' expression(20)

If a math string is parsed successfully, the result is a syntax tree whose nodes are given by the term constructors referenced by the notations. Type checking is performed during or after this process, from inside out. If an expression with one sort is used in an argument with a different sort, `coercion` functions are inserted. The rules on `coercions`:

* The collection of sorts and coercions should form a directed graph, whose undirected counterpart is acyclic.

There is thus at most one path from one sort to another, and these coercion functions are inserted. If no path exists this is a type error.

Interpretation
===

There are two notions of correctness for a specification file. First, it can be *well-formed*, meaning that the file meets the above grammar, all the formulas are syntactically correct, and in this case we have a well defined notion of what the assertions in the file are. Second, it can be *proven*, meaning that the assertions in the file in fact hold - all theorems follow from the axioms. This distinction is not essential, and the choice of what counts as well-formedness is somewhat arbitrary, but roughly speaking a verifier doesn't need to consult the proof file to determine that the specification file is well formed, but it will need more help to check that it is correct, unless it is really good at guessing proofs.

When `output` is involved, the specification describes a relation that should hold on the output of the verifier on success.

The [examples/mm0.mm0](examples/mm0.mm0) file contains a complete formal specification of the interpretation function, from string input through lexing, parsing and elaboration, to well formedness checking and validation.

MM0 should be viewed as a logical foundation, based on many-sorted first order logic without equality. In order to simplify the core validation step, however, we use a simplified underapproximation of bound variables. Unlike HOL, this language does not have higher order sorts or variables. Instead, the built in notion is of an "open term", a variable which only depends on an explicitly designated list of bound variables (as well as other variables in an outer context).

* A `sort` directive declares a new sort. None of the sort modifiers affect the semantics of the sort, although they can be used to restrict uses of the sort.
* A `term` directive creates a new function symbol in the first order logic. These are combined to produce expressions.
* An `axiom` directive declares a new axiom or inference rule. This asserts that a term in a provable sort (i.e. a formula) is derivable if all the hypotheses are derivable.
* A `def` directive allows the creation of a new function symbol, defined to equal some expression in terms of the input variables, as well as some additional "dummy variables", which do not appear as arguments to the definition and are instantiated "arbitrarily" when unfolded. (See Definition Substitution.)
* A `theorem` directive asserts that a formula is derivable assuming that the hypotheses are derivable.

Type checking
---

The math expressions in `theorem`, `axiom`, and `def` commands must be elaborated into type correct expressions during parsing. This process is called type checking. Given `term foo: A > B > C`, any expression `foo a b` requires that `a` be of sort `A` and `b` have sort `B`, and the result has sort `C`. Notations allow additional ways to write such terms, but the type checking process is the same. If coercions are declared, then coercion functions may be inserted into the term in order to prevent a type error; for example, if `a` has type `X` instead, but a coercion `coercion xa: X > A` is declared, then the elaborated s-expression is `foo (xa a) b` instead. The restrictions on coercions prevent the possibility of multiple valid parses.

Some terms accept bound variables, such as `term all {x: set} (ph: wff x): wff`. Here a term `all a P` requires that `a` have sort `set` and `P` have sort `wff` (the `x` in `wff x` does not matter for type checking), but because `x` is a bound variable, `a` must also be a bound variable (not a more complicated expression of sort `set`).

Definition checking
---

A definition may depend on declared bound and regular variables, as well as dummy variables. The definition itself must be type-correct, but we additionally track that every free variable in the definiens is among the dependencies in the result type. So for example:

    def weu {x .y: set} (ph: wff x): wff = $ E. y A. x (ph <-> x =s y) $;

We can calculate the free variables of the expression recursively.

    FV(ph) = {x}
    FV(x) = {x}
    FV(y) = {y}
    FV(x =s y) = FV(x) u. FV(y) = {x, y}
    FV(ph <-> x =s y) = FV(ph) u. FV(x =s y) = {x, y}
    FV(A. x (ph <-> x =s y)) = FV(ph <-> x =s y) \ {x} = {y}
    FV(E. y A. x (ph <-> x =s y)) = FV(A. x (ph <-> x =s y)) \ {y} = {}

We only care about bound variables (variables with curly binders) for the calculation. Here the fact that `A.` has the declaration `term all {x: set} (ph: wff x): wff` means that any occurrences of `x` in `ph` are bound by the term. If it had type `{x: set}: wff x > wff x` then it would depend on `x` regardless of whether an `x` appears in the subterms, and if it had type `{x: set} (ph: wff): wff` then `x` would not be free in `all x ph` unless it appears in `ph`. More generally, `v` is free in a term `foo x1 ... xn`:

* If `v` is substituted for bound variable `xi`, and `foo` has return type depending on `xi`, or
* If `v` is free in the substitution for regular variable `xi`,
  * unless `v` is also substituted for bound variable `xj` and `xi` depends on `xj`

For example, if

    term foo {x y: set} (ph: wff x): wff y;

then for the term `foo a b P`, we have `FV(foo a b P) = (FV(P) \ {a}) u. {b}`, so that if `P := (a = b /\ a = c)` then `FV(P) = {a,b,c}` and `FV(foo a b P) = {b,c}`.

We require for a definition, that every free variable in the definiens with a  `free` sort is among the declared dependencies of the definition (i.e. the return type is `wff x` if `x` is free in the definiens and the sort of `x` is declared as `free`).

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

The syntax of a proof file is implementation dependent. It is designed to be read and used by the verifier in an efficient and convenient way. Usually, such a file will be compiled from another language to prepare it for use by the verifier. The contents of the proof file do not affect the correctness of any of the theorems in the specification file. At worst, the verifier will fail on a provable theorem, because it was not able to find the proof with the assistance of the proof file.

See [mm0-hs/README.md](mm0-hs/README.md) for the proof file format of the reference implementation.

Verification
---

The verification of a specification file proceeds in linear order through the file, providing definitions for any `def` directives without a given definition, and providing proofs for all the `theorem` statements.

Inside a theorem context, we have all the variables in the theorem statement (after definition unfolding), plus all the hypotheses, plus any number of additional dummy variables of any desired sorts (these are usually declared up-front as with `def` statements, but they don't appear in the specification file). From this (fixed) context, we can derive two types of statements:

* Expression `e` is well formed of sort `T` (optionally: and `Vars(e) = S`)
* Expression `ph` is derivable.

We must show that the conclusion of the theorem is derivable. The inference rules are:

* If `v` is a variable in the context of sort `T`, then `v` is well formed of sort `T`, and `Vars(v) = {v}`.
* If `foo` is a term or definition, and `e1 ... en` are given such that
  * `ei` is well formed of sort `Ti` and `Vars(ei) = Si`,
  * the type of foo is `T1 > ... > Tn > U` (ignoring dependencies), and
  * all bound variables are substituted for bound variables,
  then `foo e1 ... en` is well formed of type `U`, and `Vars(foo e1 ... en) = U i, Si`.
* If `h: T` is a hypothesis in the context, then `T` is derivable.
* If `foo (v1 ... vn): A1 > ... > Ak > B` is a theorem or axiom, and `e1 ... en` is a substitution for `v1 ... vn`, such that
  * `ei` is well formed of sort `Ti` and `Vars(ei) = Si`,
  * `vi` is a variable of sort `Ti`,
  * if `vi` is a bound variable then `ei` is also a bound variable,
  * if `vi` is a bound variable and `vj` comes after `vi` and `vj` does not depend on `vi`, then `ei` is not in `Sj`.
  In this case:
  * Let `Ai' = Ai[e/v]` be the simultaneous direct substitution of the `ei`'s for the `vi`'s in `Ai`, and let `B' = B[e/v]`.
  * If `Ai'` is derivable for all `i`, then `B'` is derivable.
