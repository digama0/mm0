# mm0-hs

This is a Haskell reference implementation of the Metamath Zero specification. See [mm0.md](/mm0.md) for the main specification.

To compile, install [Haskell `stack`](https://haskellstack.org/), then go to the `mm0-hs` directory and run `stack setup`, then use `stack build` to build the program and `stack exec -- mm0-hs [args..]` to run it, or `stack install` to move it to a global location in your PATH, so that `mm0-hs [args..]` works from any directory (which in particular is what the `vscode-mm0` extension expects, if you don't tell it otherwise).

To run the program you can use the following:

* `mm0-hs verify MM0-file [MMU-FILE]`:

  This verifies the given `.mm0` specification file, and checks the proof file if given. It prints `spec checked` if the `.mm0` file is well formed and typechecks, and if the `.mmu` file is also provided then it prints `verified` if the specification is proven, followed by all the result of all `output` statements.

The MM0 spec leaves many parts of the language implementation-defined, and most of the specification is optional. This implementation has the following behavior:

* All the primary commands are supported: `sort, term, axiom, def, theorem, delimiter, notation, infixl/r, prefix, coercion, input, output`.
* All sort modifiers are supported.
* Delimiters must be single characters. Other tokens may not contain delimiter characters.
* The following IO kinds are supported:
  * `input string, output string` (see "`string` IO" below)
* See below for the specification of the `.mmu` proof file format.

`string` IO
---
Both the `input` and `output` commands use the same grammar for reading strings from the logic, given by the following specification:

    strict free sort hex;
    term x0: hex; term x1: hex; term x2: hex; term x3: hex;
    term x4: hex; term x5: hex; term x6: hex; term x7: hex;
    term x8: hex; term x9: hex; term xa: hex; term xb: hex;
    term xc: hex; term xd: hex; term xe: hex; term xf: hex;

    strict free sort char;
    term ch: hex > hex > char;

    strict free sort string;
    term s0: string;
    term s1: char > string;
    term sadd: string > string > string;

That is, for a specification to use the `input string` and `output string` directives, it must contain these sorts and terms with these exact names (and these sorts should not have any additional term constructors, although it is permissible to define term constructors taking these sorts as input). Both commands take exactly one definition identifier or expression, of type `string`.

* The `hex` sort contains the numbers 0-15 with hexadecimal names.
* The `char` sort forms an 8-bit character from two `hex` digits. So for example `ch x3 x0` is the character `0x30` which represents ASCII character '0'.
* The `string` sort contains lists of characters, formed by appending (using `sadd`) strings of length 0 and 1 (using `s0` and `s1`). The associativity of the `sadd`'s in a string does not matter.

With these terms and sorts, we can encode strings inside the logic, prove theorems about them and so on.
* The `output` command accepts a definition or expression of type `string` and completely unfolds the definition until only the above terms remain, and then interprets the result as a string and outputs it to standard out.
* The `input` command "passes the contents of the `.mm0` file to the logic" into the given definition or expression. More precisely, the proof file needs to already know what the input is, and the verifier will check that the proof file has provided a witness that matches the actual contents of the `.mm0` file.

See [hello.mm0](/examples/hello.mm0) for an example of a specification file that can print `Hello World!` on standard out (and also asserts that it does so in the specification) using `output string`.

A (necessarily more complicated) example is [string.mm0](/examples/string.mm0), which uses both `input string` and `output string` to read the specification file `string.mm0`, assert that it equals a particular `string` value defined in the logic, and then output it back to the console. (So it is similar in spirit to a quine, a program that prints its own source code, although the self reference is enabled explicitly by the `input` command. A real quine would also need to print the contents of the `.mmu` file.) It then also outputs `hello world` for good measure. (Note for windows users: Make sure that git does not replace `LF` with `CRLF` in the specification file, or else the verification will fail.)

The `.mmu` file format
---
For demonstration purposes, this verifier accepts a text format for the proof file. (A production quality verifier should probably use a binary file format, but the information contained in the file should be about the same.) To simplify parsing, the whole file is written using lisp s-expression syntax:

* Whitespace is ignored except to separate tokens
* Line comments are written `--comment` and extend until the next `\n`;
  line comments act like whitespace
* An identifier token matches `[0-9a-zA-Z_:]+`
* Characters `( )` are single character symbol tokens
* Anything else is forbidden

The syntax is as follows:

    mmu-file ::= (directive)*
    directive ::= sort-stmt | term-stmt | def-stmt | axiom-stmt | thm-stmt | io-stmt
    sort-stmt ::= '(' 'sort' sort-name ('pure')? ('strict')? ('provable')? ('free')? ')'
    term-stmt ::= '(' 'term' term-name binders ret-type ')'
    def-stmt ::= '(' ('local')? 'def' term-name binders ret-type dummies expr ')'
    axiom-stmt ::= '(' 'axiom' assert-name binders axiom-hyps expr ')'
    thm-stmt ::= '(' ('local')? 'theorem' assert-name binders thm-hyps expr dummies proof-expr ')'
    io-stmt ::= '(' 'input' input-kind ')'
             |  '(' 'output' output-kind ')'
    identifier ::= [0-9a-zA-Z_]+
    sort-name ::= identifier
    term-name ::= identifier
    assert-name ::= identifier
    var-name ::= identifier
    hyp-name ::= identifier
    input-kind ::= 'string'
    output-kind ::= 'string'
    binders ::= '(' (binder)* ')'
    binder ::= '(' var-name sort-name ')'
            |  '(' var-name sort-name '(' (var-name)* ')' ')'
    dummies ::= '(' (dummy-binder)* ')'
    dummy-binder ::= '(' var-name sort-name ')'
    ret-type ::= '(' sort-name '(' (var-name)* ')' ')'
    axiom-hyps := '(' (expr)* ')'
    thm-hyps ::= '(' (hyp-binder)* ')'
    hyp-binder ::= '(' hyp-name expr ')'
    expr ::= var-name | '(' term-name (expr)* ')'
    proof-expr ::= hyp-name
                |  '(' assert-name '(' (expr)* ')' (proof-expr)* ')'
                |  '(' ':let' hyp-name proof-expr proof-expr ')'
                |  '(' ':conv' expr conv-expr proof-expr ')'
    conv-expr ::= var-name
               |  '(' term-name (conv-expr)* ')'
               |  '(' ':sym' conv-expr ')'
               |  '(' ':unfold' term-name '(' (expr)* ')' '(' (var-name)* ')' conv-expr ')'

A proof file is a list of declarations, mirroring the declarations in the specification file. The verification of the proof proceeds in lock step with the declarations in the spec, but the proof file will potentially add additional definitions and theorems that are not present in the specification.

* A `sort-stmt` declares a new sort. The syntax is the same as in `.mm0` files except that the sort modifiers come after the word `sort`.

* A `term-stmt` declares a new term, and `def-stmt` declares a new definition. These are also the same as `.mm0` files, except that bodies are required for definitions.

* An `axiom-stmt` declares a new axiom, and `thm-stmt` declares a new theorem. The list of hypotheses is slightly different between axioms and theorems because axiom hypotheses don't need (or accept) names. Unlike the `.mm0` format, theorems have proofs, and we also must pre-declare the list of dummy variables used in the proof.

* An `io-stmt` is an input or output statement, which for `mm0-hs` can only be `(input string)` or `(output string)`.

Binders have a simplified syntax:
* A bound variable binder like `{x: set}` is rendered `(x set)`
* A regular variable binder like `(ph: wff x)` is rendered `(ph wff (x))`. Even if there are no dependencies, a regular variable will have the third argument: `(ph: wff)` becomes `(ph wff ())`.

Proof expressions are composed of theorem applications on hypotheses, but special rules have keywords starting with `:` for them.

* `H` is the application of hypothesis `H`, or a saved local proof `H`.
* `(thm (e1 e2) p1 p2)` is the application of theorem `thm`, substituting `e1` and `e2` for the variables in the theorem and `p1` and `p2` are subproofs proving the hypotheses to the theorem.
* `(:let H p1 p2)` constructs a subproof `p1` and binds it to a name `H`, which can be used in the proof of `p2` as if it were an additional hypothesis.
* `(:conv rhs c p)` is a proof of `|- rhs` if `c` is a conversion proof of `lhs = rhs` and `p` is a proof of `|- lhs`.

Conversion expressions are "proofs of definitional equality":
* `x` is a proof that `x = x`
* `(t c1 .. cn)` is a proof that `(t l1 .. ln) = (t r1 .. rn)` if `ci: li = ri`. Note that because of this rule and the previous one, any expr `t` is a proof of `t = t` when interpreted as a conversion.
* `(:sym c)` is a proof of `r = l` if `c: l = r`.
* `(:unfold t (e1 .. en) (d1 .. dm) c)` is a proof of `(t e1 .. en) = rhs` if `t` is a definition, and substituting `e1 .. en` for the arguments and `d1 .. dm` for the dummy variables in `t`'s definition expression yields `sub_lhs`, and `c: sub_lhs = rhs`.
