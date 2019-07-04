# mm0-hs

This is a Haskell reference implementation of the Metamath Zero specification. See [mm0.md](/mm0.md) for the main specification.

To run the program you can use the following:

* `mm0-hs verify MM0-file [MMU-FILE]`:

  This verifies the given `.mm0` specification file, and checks the proof file if given. It prints `spec checked` if the `.mm0` file is well formed and typechecks, and if the `.mmu` file is also provided then it prints `verified` if the specification is proven, followed by all the result of all `output` statements.

The MM0 spec leaves many parts of the language implementation defined, and most of the specification is optional. This implementation has the following behavior:

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

See [hello.mm0](examples/hello.mm0) for an example of a specification file that can print `Hello World!` on standard out (and also asserts that it does so in the specification) using `output string`.

A (necessarily more complicated) example is [string.mm0](examples/string.mm0), which uses both `input string` and `output string` to read the specification file `string.mm0`, assert that it equals a particular `string` value defined in the logic, and then output it back to the console. (So it is similar in spirit to a quine, a program that prints its own source code, although the self reference is enabled explicitly by the `input` command. A real quine would also need to print the contents of the `.mmu` file.) It then also outputs `hello world` for good measure. (Note for windows users: Make sure that git does not replace `LF` with `CRLF` in the specification file, or else the verification will fail.)

The `.mmu` file format
---
For demonstration purposes, this verifier accepts a text format for the proof file. (A production quality verifier should probably use a binary file format, but the information contained in the file should be about the same.) Lexing is very simple:

* Whitespace is ignored except to separate tokens
* An identifier token matches `[0-9a-zA-Z_]+`
* Characters `( ) { } [ ] , : =` are single character symbol tokens
* Anything else is forbidden

The declarations are visually similar to the `.mm0` format, except that there is no terminating semicolon after each definition.

    mmu-file ::= (directive)*
    directive ::= step-stmt | def-stmt | thm-stmt
    step-stmt ::= 'sort' sort-name
               |  'term' term-name
               |  'axiom' assert-name
               |  'input' input-kind
               |  'output' output-kind
    def-stmt ::= ('local')? 'def' term-name (binder)* ':' type '='
                   (dummy-binder)* expr
    thm-stmt ::= ('local')? 'theorem' assert-name (binder)* ',' (unfolding-stmt)?
                   (hyp-binder)* ':' expr '=' (dummy-binder)* proof-expr
    unfolding-stmt ::= 'unfolding' (term-name)+ '(' var-name ')'
    identifier ::= [0-9a-zA-Z_]+
    sort-name ::= identifier
    term-name ::= identifier
    assert-name ::= identifier
    var-name ::= identifier
    input-kind ::= 'string'
    output-kind ::= 'string'
    dummy-binder ::= '{' var-name ':' sort-name '}'
    binder ::= '{' var-name ':' sort-name '}'
            |  '(' var-name ':' sort-name ')'
    hyp-binder ::= '(' var-name ':' expr ')'
    type ::= sort-name (var-name)*
    expr ::= var-name | term-name | '(' term-name (expr)* ')'
    proof-expr ::= '?' | expr
                |  '(' assert-name (expr)* (proof-expr)* ')'
                |  '[' proof-expr '=' var-name ']'

A proof file is a list of declarations, mirroring the declarations in the specification file. The verification of the proof proceeds in lock step with the declarations in the spec, but the proof file will potentially add additional definitions and theorems that are not present in the specification.

* A `step-stmt` has very little content because it is just a directive to "step" the specification; that is, it instructs the verifier to proceed to the next declaration in the specification file. As a sanity check, we require step statements to say the type and name of the declaration, although there is exactly one correct choice. So for example the `sort nat` step statement says "the next declaration in the spec is `sort nat;`, please move past this point so that now we can use the declaration in theorems and defs". But we do not recapitulate the types of `term`s or the statement of `axiom`s, we just say the name.

* A `def-stmt` makes a new declaration, and here we must provide the full type and value of the declaration. Like in the spec, curly binders like `{x: set}` denote bound variables and parentheses denote regular variables. Unlike the `.mm0` format, dummy variables here come after the `=` sign, before the expression itself. (This requires no lookahead because the dummy binders use curly braces and expressions don't.) For example:

      local def df_eu {x: set} (ph: wff x): wff =
      {y: set} (ex y (all x (iff (eq x y) ph)))

  If a definition is marked `local`, then it does not step the specification and the definition is only checked for correctness. If it is not marked `local` then it steps the specification, and checks that the next statement in the spec is a `def` with the same name and type, and if the specification gives a value to the `def` then that must also match.

* A `thm-stmt` proves a theorem.
  * Like the `def` statement, if it is not marked `local` then it will also step the specification and check that the next declaration is a `theorem` with the same name and statement.
  * Unlike the `.mm0` format, there is a mandatory `','` to separate the bound/regular variables from the dummy/hypothesis variables.
  * A theorem can declare that it wants to unfold some definitions in the statement using `unfolding foo bar (v1 v2)` just after the comma. This will unfold all occurrences of `foo` and `bar` in the hypotheses and conclusion of the theorem, and if these definitions have dummy variables then the list `(v1 v2)` gives them names. (There will be `n` new dummy variables for each occurrence of an unfolded definition `T` with `n` dummy variables.) Then the dummy variables and hypotheses are given names, and finally the proof expression.
* Expressions are given as pure s-expressions, with mandatory brackets for all term constructors with 1 or more arguments.
* Proof expressions are also formatted as s-expressions, where a theorem application accepts the variable substitutions followed by the hypothesis subproofs.
  * The `[foo=x]` backreference syntax can be used to name an expression or proof expression inside a proof expression. It is equivalent to a notation like `let x = foo in bar[x]`, where occurrences of `x` in `bar` refer to `foo` (which could be a commonly occurring expression or a local lemma), but it is not lexically scoped - it is valid everywhere to the right of the `x` until the end of the proof. For example, if we have the axiom

        axiom mulpos (a b: nat): $ pos a $ > $ pos b $ > $ pos (a * b) $;

    then we can prove a highly redundant theorem using backreferences:

        theorem eightpos (a: nat), (h: pos a):
          pos (mul (mul (mul a a) (mul a a)) (mul (mul a a) (mul a a))) =
        (mulpos [(mul [(mul a a)=a2] a2)=a4] a4
                [(mulpos a2 a2 [(mulpos a a h h)=h2] h2)=h4] h4)

    Without deduplication the theorem would look like this:

        theorem eightpos (a: nat), (h: pos a):
          pos (mul (mul (mul a a) (mul a a)) (mul (mul a a) (mul a a))) =
        (mulpos (mul (mul a a) (mul a a)) (mul (mul a a) (mul a a))
          (mulpos (mul a a) (mul a a) (mulpos a a h h) (mulpos a a h h))
          (mulpos (mul a a) (mul a a) (mulpos a a h h) (mulpos a a h h)))

    In the worst case the redundantly stated version can be exponentially larger than its deduplicated version. Currently deduplication inside expressions is not supported, but you can use definitions to achieve a similar asymptotic gain.
