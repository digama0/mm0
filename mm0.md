Metamath Zero
===

This is a language for writing specifications and proofs. Its emphasis is on balancing simplicity of verification and human readability, with the intent that a skeptical auditor can be convinced of the following:

1. The verifier is implemented correctly to this specification (by reading the code)
2. This specification ensures that a conforming verifier checks that programs meet their specifications (by a paper proof or formalization, forthcoming)
3. The input specification to the verifier correctly describes an axiom system `A`, and the stated theorems are correct transcriptions of theorems `T1,...,Tn` (by reading the specification file)

From the conjunction of these properties, the auditor finds that `A |- T1,...,Tn`, and if they believe `A` is true or representative of the world then they may conclude that `T1,...,Tn` are as well.

Input to a Metamath Zero verifier consists of two parts: a "specification" or "header file", with extension `.mm0`, and a "proof" file with extension `.mp0`. The specification file contains axioms, definitions, and theorem statements, while the proof file contains proofs of the theorems and auxiliary data.

The major distinction between the two files is that in the hypothetical auditing  process above, *the `.mp0` file plays no role*. All information relevant to correctness of the final result is put in the `.mm0` file, and the `.mp0` file is nothing more than an extended "hint" to the verifier to show why the theorems in the `.mm0` file are true. As such, the format of the `.mp0` file is not officially specified, although there is a recommended format (see [?]).

Example `.mm0` file
---

    strict provable nonempty sort wff;
    var ph ps ch: wff*;
    term wi (ph ps: wff): wff; infixr wi: $->$ prec 25;
    term wn (ph: wff): wff; prefix wn: $~$ prec 40;

    axiom ax-1: $ ph -> ps -> ph $;
    axiom ax-2: $ (ph -> ps -> ch) -> (ph -> ps) -> ph -> ch $;
    axiom ax-3: $ (~ph -> ~ps) -> ps -> ph $;
    axiom ax-mp: $ ph $ -> $ ph -> ps $ -> $ ps $;

    theorem a1i: $ ph $ -> $ ps -> ph $;

    def wb (ph ps: wff): wff := $ ~((ph -> ps) -> ~(ps -> ph)) $ {
      infixl wb: $<->$ prec 20;

      theorem bi1: $ (ph <-> ps) -> ph -> ps $;
      theorem bi2: $ (ph <-> ps) -> ps -> ph $;
      theorem bi3: $ (ph -> ps) -> (ps -> ph) -> (ph <-> ps) $;
    }

    def wa (ph ps: wff): wff := $ ~(ph -> ~ps) $ {
      infixl wa: $/\$ prec 20;
      theorem df-an: $ (ph /\ ps) <-> ~(ph -> ~ps) $;
    }

    def wtru (bound p: wff): wff := $ p <-> p $ {
      notation wtru := $ T. $;
      theorem df-tru: $ T. <-> (ph <-> ph) $;
    }

    pure nonempty sort set;
    bound x y z w: set;

    term wal (x: set) (ph: wff x): wff; prefix wal: $A.$ prec 30;

    def wex (x: set) (ph: wff x): wff := $ ~A. x ~ph $ {
      prefix wex: $E.$ prec 30;

      theorem df-ex: $ E. x ph <-> ~A. x ~ph $;
    }

    axiom ax-gen: $ ph $ -> $ A. x ph $;
    axiom ax-4: $ A. x (ph -> ps) -> A. x ph -> A. x ps $;
    axiom ax-5 (ph: wff): $ ph -> A. x ph $;

    var a b c: set;
    term weq (a b: set): wff; infixl weq: $=s$ prec 50;
    term wel (a b: set): wff; infixl wel: $es.$ prec 40;

    def weu (x: set) (ph: wff x): wff :=
      $ E. y A. x (ph <-> x =s y) $ {
      prefix wex: $E!$ prec 30;

      theorem df-ex: $ E! x ph <-> E. y A. x (ph <-> x = y) $;
    }

    axiom ax-6: $ E. x x =s a $;
    axiom ax-7: $ a =s b -> a =s c -> b =s c $;

    axiom ax-8: $ a =s b -> a es. c -> b es. c $;
    axiom ax-9: $ a =s b -> c es. a -> c es. b $;

    axiom ax-10: $ ~A. x ph -> A. x ~ A. x ph $;
    axiom ax-11: $ A. x A. y ph -> A. y A. x ph $;
    axiom ax-12 (ph: wff y): $ A. y ph -> A. x (x = y -> ph) $;

    axiom ax-ext: $ A. x (x e. a <-> x e. b) -> a = b $;
    axiom ax-rep (ph: wff y z):
      $ A. y E. x A. z (ph -> z = x) ->
        E. x A. z (z e. x <-> E. y (y e. a /\ ph)) $;
    axiom ax-pow: $ E. x A. y (A. z (z e. y -> z e. a) -> y e. x) $;
    axiom ax-un: $ E. x A. y (E. z (y e. z /\ z e. a) -> y e. x) $;
    axiom ax-reg: $ E. x x e. a -> E. x (x e. a /\ A. y (y e. x -> ~ y e. a)) $;
    axiom ax-inf:  $ E. x (a e. x /\ A. y (y e. x -> E. z (y e. z /\ z e. x))) $;
    axiom ax-ac:
      $ E. x A. y (y e. a -> E. z z e. y ->
        E! z (z e. y /\ E. w (w e. x /\ y e. w /\ z e. w))) $;

    strict nonempty sort class;
    var A B C: class*;
    term cab (x: set) (ph: wff x): class;
    term welc (a: set) (A: class): wff; infixl welc: $ec.$ prec 50;
    notation cab (x: set) (ph: wff x): class := ${$ (x: max) $|$ (ph: 0) $}$;

    axiom ax-8b: $ a = b -> a ec. A -> b ec. A $;

    axiom ax-clab: $ x ec. {x | ph} <-> ph $;

    def wceq (A B: class): wff := $ A. x (x ec. A <-> x ec. B) $ {
      infixl wceq: $=$ prec 50;

      theorem df-ceq: $ A = B <-> A. x (x ec. A <-> x ec. B) $;
    }

    def cv (a: set): class := $ {x | x es. a} $ {
      coercion cv: set -> class;

      theorem df-cv: $ a ec. b <-> a es. b $;
    }

    def wcel (A B: class): wff := $ E. x (x = A /\ welc x B) $ {
      infixl wcel: $e.$ prec 50;

      theorem df-cel: $ A e. B <-> E. x (x = A /\ welc x B) $;
    }

Lexical structure
===

    file ::= (lexeme | whitespace)*

The file is separated out into a list of lexemes, or tokens, according to the "maximum munch" principle: the longest matching token is used when ambiguity is possible.

    whitespace ::= whitestuff+
    whitestuff ::= whitechar | line-comment | multiline-comment
    whitechar ::= ' ' | '\r' | '\n' | '\t'
    line-comment ::= ('--' | '---') [^\n]* '\n'
    multiline-comment ::= ('/-' | '/--') .* '-/'

Whitespace is a sequence of spaces, newlines, carriage returns and tabs. Comments come in two kinds - the line comment begins with `--` and continues to the end of the line, and the multiline comment is bracketed between `/-` and `-/`. Inside a multiline comment `/-` is not permitted (no nested comments), and `-/` ends the comment.


    lexeme ::= symbol | identifier | number | math-string
    symbol ::= '*' | ':' | ';' | '(' | ')' | '->' | '{' | '}' | ':='
    identifier ::= [a-zA-Z_.-][a-zA-Z0-9_.-]*
    number ::= 0 | [1-9][0-9]*
    math-string ::= '$' ('$$' | dollar-comment | [^\$])* '$'
    dollar-comment ::= '$-' .* '-$'

A lexeme is either one of the symbols, an identifier, a number (nonnegative integer), or a math string. An identifier is a sequence of alphanumeric symbols, together with the punctuation characters `_`, `.` and `-`, except that it cannot begin with a digit.

A math string is a sequence of characters quoted by `$`. Inside a math string `$` cannot appear, except that `$$` is permitted (and is interpreted as a single dollar), and `$- ... -$` is a comment inside the string. Like with multiline comments, nested `$- -$` comments are not allowed, although `$- /- -/ -$` is permitted (the `/- -/` comment syntax is not applicable). There is no analogous line comment inside math strings.

These strings will go through a secondary lexing phase, using a dynamic lexer defined by the notations in the file.

Pseudo-keywords
---

The following words appear in the syntax with special meanings:

    axiom bound coercion def infixl infixr max nonempty notation
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

Sorts
---
    sort-stmt ::= ('pure')? ('strict')? ('provable')? ('nonempty')? 'sort' identifier ';'

The underlying semantics of metamath zero is based on multi-sorted first order logic. The `sort` keyword declares a new sort. There are several properties that a sort may or may not have, indicated by modifiers on the sort declaration.

* `pure` means that this sort does not have any term formers. It is an uninterpreted domain which may have variables but has no constant symbols, binary operators, or anything else targeting this sort. If a sort has this modifier, it is illegal to declare a `term` with this sort as the target.
* `strict` is the "opposite" of `pure`: it says that the sort does not have any variable binding operators. It is illegal to have a variable of this sort appear as a dependency in another variable. For example, if `x: set` and `ph: wff x` then `set` must not be declared `strict`. (`pure` and `strict` are not mutually exclusive, although a sort with both properties is not very useful.)
* `provable` means that the sort is a thing that can be "proven". All formulas appearing in axioms and definitions (between `$`) must have a provable sort.
* `nonempty` means that theorems and definitions are permitted to introduce `bound` variables of this sort.

Variables and types
---

    var-stmt ::= 'var' (identifier)* ':' open-type ';'
              |  'bound' (identifier)* ':' identifier ';'
    type ::= identifier (identifier)*
    open-type ::= type | identifier '*'

A variable statement does not represent any actual statement or theorem, it just sets up variable names with their types so that they may be inferred in later `term`s, `axiom`s, `def`s and `theorem`s. See "Variable Inference" for details on how the inference process works. In the statement itself, we can declare a list of variables with type dependencies.

A type is the name of a sort followed by 0 or more variable names, which represent the values this variable is allowed to depend on. An open type is either a type, or a sort followed by a `*`, representing all variable dependencies.

A variable may be declared as either `var` or `bound`. A `bound` variable is permitted to appear in type dependencies, and will be inferred as `bound` if possible. (See "Variable Inference".) A `bound` variable cannot have a dependent type.

Term constructors
---
The `term` directive constructs a new piece of syntax, a function symbol on the sorts. The syntax permits two ways to list the arguments of the function, via binders or as a simple function. The names are not used except in dependencies of the types, so `term imp (ph ps: wff): wff;` and `term imp: wff -> wff -> wff` mean the same thing.

    term-stmt ::= 'term' identifier (type-binder)* ':' arrow-type ';'
    type-binder ::= '(' (identifier)* ':' type ')'
    arrow-type ::= type | type '->' arrow-type

Axioms and theorems
---
An `axiom` and a `theorem` appear exactly the same in the specification file, although only one will require a proof. The syntax is similar to term constructors but now rather than just types, a binder may have a formula as its type. A formula is any sequence of tokens other than `$`, fenced by `$`. The `$` may be escaped by reduplication `$$`.

    assert-stmt ::= ('axiom' | 'theorem') identifier
       (formula-type-binder)* ':' formula-arrow-type ';'
    formula-type-binder ::= '(' (identifier)* ':' (type | formula) ')'
    formula-arrow-type ::= formula | (type | formula) '->' arrow-type
    formula ::= math-string

Definitions
---
A `def` is similar to an `axiom` except that it may also have `bound` quantifiers, representing dummy variables in the definition that are not exposed in the syntax. It also ends with a block rather than a semicolon, because the definition itself has a limited lifetime. Inside the block, the definition is unfolded for the purpose of the proof, and it is made opaque once the block is exited.

    def-stmt ::= 'def' identifier (type-binder | bound-binder)* ':'
      type ':=' formula '{' (directive)* '}'
    bound-binder ::= '(' 'bound' (identifier)* ':' identifier ')'

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
    coercion-stmt ::= 'coercion' identifier ':' identifier '->' identifier ';'
    gen-notation-stmt ::= 'notation' identifier (type-binder)* ':'
      type ':=' (notation-literal)+ ';'
    notation-literal ::= constant | prec-variable
    prec-variable ::= '(' identifier ':' precedence-lvl ')'

Interpretation
===

There are two notions of correctness for a specification file. First, it can be *well-formed*, meaning that the file meets the above grammar, all the formulas are syntactically correct, and in this case we have a well defined notion of what the assertions in the file are. Second, it can be *proven*, meaning that the assertions in the file in fact hold - all theorems follow from the axioms. This distinction is not essential, and the choice of what counts as well-formedness is somewhat arbitrary, but roughly speaking a verifier doesn't need to consult the proof file to determine that the specification file is well formed, but it will need more help to check that it is correct, unless it is really good at guessing proofs.
