Metamath One (The MM0 Compiler)
===

The `mm0-hs` program comes with a compiler for assembling `.mm0` specs and their associated `.mmu` proof files. The source files for the compiler have `.mm1` extension, and the syntax extends the [`.mm0` file format](../mm0.md).

The key new capability of MM1 over MM0 is the inclusion of a Turing-complete programming language over MM0, a lisp dialect similar to [Scheme](https://schemers.org/). Proofs of theorems are given as s-expressions, which may be constructed by lisp programs, also known as "tactics" in this context.

Unlike MM0, MM1 is deliberately unverified. MM1 files are compiled to proofs in MM0, which may then pass through an efficient and correct bare-bones verifier that knows nothing about the MM1 extensions. This means that we can "hack without fear" in MM1, because any bugs will be caught by the MM0 "kernel". (Of course we still want to avoid bugs, but we don't need to be fanatic about it because as long as the proofs we care about are produced correctly it has done its job.)


Syntax
===
As mentioned above, the syntax of MM1 is based on MM0, and the grammar below makes reference to the [MM0 grammar](../mm0.md). New productions and differences are noted in comments on the right.

    mm1-file ::= (statement)*
    statement ::= sort-stmt
               |  decl-stmt                ; This includes MM0's term-stmt,
                                           ; assert-stmt and def-stmt
               |  notation-stmt
               |  inout-stmt
               |  do-stmt                  ; NEW
               |  annot-stmt               ; NEW

Sorts
---

    sort-stmt ::= ('pure')? ('strict')? ('provable')? ('free')?
      'sort' identifier ';'

Sort declarations are unchanged from [MM0](../mm0.md#sorts).

Declarations
---

    decl-stmt ::= visibility? decl-kind identifier (binder)*
      (':' arrow-type)? ('=' sexpr)? ';'
    visibility ::= 'pub' | 'abstract' | 'local'
    decl-kind ::= 'term' | 'axiom' | 'def' | 'theorem'
    identifier_ ::= identifier | '_'
    type ::= identifier (identifier)*
    type-or-fmla ::= type | formula
    binder ::= '{' (var-decl)* (':' type-or-fmla)? '}'
            |  '(' (var-decl)* (':' type-or-fmla)? ')'
    var-decl ::= '.'? identifier_
    arrow-type ::= type-or-fmla | type-or-fmla '>' arrow-type

This grammar is more permissive than MM0, but many of the same restrictions as in MM0 still exist but are enforced later for better error reporting.

* `term` and `def` declarations do not permit formulas in the types of binders or in the return type.

* All hypotheses (formula binders) must come after regular types in `axiom` and `theorem`.

* An arrow type `A > B` is exactly identical to `(_: A): B`, that is, an anonymous binder added to the end of the list of binders. However, `theorem` and `def` do not permit a value (the `'=' sexpr` clause) when an arrow type is used.

* `term` and `axiom` do not allow a definition; `def` and `theorem` require a definition but will give a warning and interpret the declaration as `term` and `axiom` respectively if a definition is not supplied.

* Declarations allow a visibility modifier, which determines whether the statement will appear in the compiled MM0 file.

  * `term` and `axiom` do not accept visibility modifiers - they are always public.
  * `def` accepts `pub`, `abstract`, `local` modifiers, and `pub` is the default.
    * `pub def` means the definition and the value will be put in the MM0 file.
    * `abstract def` means the definition will be put in the MM0 file, but the value will be omitted. For example, `abstract def foo: nat = $ 1 $;` would result in `def foo: nat;` in the MM0 file.
    * `local def` means the definition will not appear in the MM0 file, but it will appear in the proof file. Public theorems and definitions cannot refer to local theorems and definitions.
  * `theorem` accepts only `pub` and `local` modifiers, and `local` is the default.
    * `pub theorem` means that the theorem statement (but not the proof) will appear in the MM0 file. (MM0 does not ever have proofs for theorems, so this is conceptually the same as `abstract`.)
    * `local theorem` means that the theorem statement will not appear in the file. (Public theorems are allowed to refer to local theorems in the proof.)

* Binders come in several kinds, as in MM0:

  * A `{x: foo}` binder states that this is a bound variable, a name that will appear as a binding variable in a binder for the statement. For example, the forall quantifier `A. x ph` would be declared as

        term all {x: nat} (ph: wff x): wff;

    and an axiom or theorem using it would also have to declare the `x` binder:

        axiom all_imp {x: nat} (ph ps: wff x):
          $ A. x (ph -> ps) -> A. x ph -> A. x ps $;

  * A `(a: foo)` binder says that this is a regular variable, which may be substituted for a term of type `foo`. As in MM0, `(a: foo x)` means that the term may depend on `x`, and `(a: foo)` means that it may not depend on `x`, if `{x: bar}` is another binder in the statement.

  * A `{.x: foo}` binder (note that `(.x: foo)` is treated as if it were `{.x: foo}`) declares a dummy variable, a variable that appears in the value of a `def` or the proof of a `theorem` but not in the statement. These are permitted for compatibility with MM0 but MM1 does not require these to be declared in advance and will infer them.

  * A `{_: foo}` or `(_: foo)` binder declares a variable that will not be used. When an expression is expected, `_` means a hole, which will be inferred if possible.

  * A hypothesis binder such as `(h: $ foo $)` or `(_: $ foo $)` names a hypothesis for use in a `theorem`. These are not permitted in `def` or `term`, and in `axiom` they are usually unnecessary since the names are unnecessary so they can be written as `$ foo $ > $ bar $` instead. `{h: $ foo $}` and `(.h: $ foo $)` are not permitted.

* The value of a `def` is a lisp expression that evaluates to a term, and the value of a `theorem` is a lisp expression that is elaborated with the statement of the theorem as a goal. See the [Evaluation](#evaluation) and [Elaboration](#elaboration) sections for details.

Notations
---

    notation-stmt ::= delimiter-stmt
                   |  simple-notation-stmt
                   |  coercion-stmt
                   |  gen-notation-stmt
    delimiter-stmt ::= 'delimiter' math-string (math-string)? ';'
    simple-notation-stmt ::= ('infixl' | 'infixr' | 'prefix') identifier ':'
      constant 'prec' precedence-lvl ';'
    constant ::= math-string
    precedence-lvl ::= number | 'max'
    coercion-stmt ::= 'coercion' identifier ':' identifier '>' identifier ';'
    gen-notation-stmt ::= 'notation' identifier (type-binder)* ':'
      type '=' prec-constant (notation-literal)* ';'
    notation-literal ::= prec-constant | identifier
    prec-constant ::= '(' constant ':' precedence-lvl ')'

Notations in MM1 are unchanged from [MM0](../mm0.md#notations).

The `input` and `output` commands
---

    inout-stmt ::= input-stmt | output-stmt
    input-stmt ::= 'input' input-kind ':' (sexpr)* ';'
    output-stmt ::= 'output' output-kind ':' (sexpr)* ';'
    input-kind ::= identifier
    output-kind ::= identifier

Input and output commands in MM1 are similar to [MM0](../mm0.md#notations) IO commands, but the input values are lisp expressions instead of formulas, and the "input" that is being referred to is the result of compilation to MM0, rather than the MM1 file itself. So this statement is very sensitive to the output process, and it is recommended that one uses the tactic language to produce `input` statements rather than writing one directly.

Annotations
---

    annot-stmt ::= '@' sexpr statement

Annotations are uninterpreted markers that may be applied to statements. They can be used to mark definitions, or derive statements based on other statements. When an annotation is placed, the annotation is evaluated to `e`, the statement is executed, and then the global lisp function `(annotate s e)` is called. This function does not exist by default, but lisp code can define it to provide a custom behavior here.

Do blocks
---

    do-stmt ::= 'do' '{' (sexpr)* '}' ';'

This command executes some lisp code at the top level, meaning that any definitions `(def x foo)` will not go out of scope at the end of the block but will instead define a global variable which will be visible in later theorem proofs and `do` blocks. See [Evaluation](#evaluation) for more on lisp code.

S-expressions
---

    sexpr ::= atom | list | number | string | bool | formula
            | ['] sexpr | ',' sexpr
    atom ::= initial (subsequent)* | '+' | '-' | '...' | '->' (subsequent)*
    initial ::=    [a-z] | [A-Z] |         [!%&*/:<=>?^_~]
    subsequent ::= [a-z] | [A-Z] | [0-9] | [!%&*/:<=>?^_~+-.@]
    list ::= '(' list-inner ')' | '[' list-inner ']'
    list-inner ::= (sexpr)* | (sexpr)+ '.' sexpr
    number ::= [0-9]+
    string ::= '"' (char)* '"'
    char ::= <any character other than " and \ > | '\"' | '\\' | '\n' | '\r'
    bool ::= '#t' | '#f'

The syntax of s-expressions here is very similar to that of [R6RS Scheme](http://www.r6rs.org/), without the unicode support and with dollar delimited formulas added.

* Atoms are simple unquoted strings like `foo`, and are used for the names of scheme functions and variables.
* The `'expr` notation is shorthand for `(quote expr)`, and causes `expr` to be treated literally as data rather than as a function call or variable reference.
  * MM0 theorems and terms are represented using quoted atoms like `'ax_mp`.
  * Inside a quotation, `,expr` or `(unquote expr)` is unquotation and causes the result to be treated as lisp again.
  * Unquotation works also inside math strings; for example `$ foo 1 ,(bar) $` is the expression `(foo 1 v)` where `v` is the result of evaluating `bar`.
* `[]` brackets are mere synonyms for `()` can can be used to make deeply nested brackets more readable.

Evaluation
===

Inside a `do` block, the language looks very similar to scheme. For example:

    do {
      (display "hello world")      -- hello world
      (print (null? ()))           -- #t
      (if (null? '(1)) 0 1)        -- 1
      (if (null? ()) 0 1)          -- 0
      (+ 2 2)                      -- 4
      '(+ 2 2)                     -- (+ 2 2)
      (< 1 2 3 4)                  -- #t
      (< 1 2 3 3)                  -- #f
      (* 1 2 3 4)                  -- 24
      (max 1 2 3 4)                -- 4
      (min 1 2 3 4)                -- 1
      (hd '(* 1 2 3 4))            -- *
      (tl '(* 1 2 3 4))            -- (1 2 3 4)
      (list 1 2 3 4)               -- (1 2 3 4)
      (def x 5)
      (+ x x)                      -- 10
      (def (x) 5)
      x                            -- #<closure>
      (x)                          -- 5
      (def (fact x) (if (= x 0) 1 (* x (fact (- x 1)))))
      (fact 5)                     -- 120
    };

The primary syntactic difference is that `define` is spelt `def`, `lambda` is spelt `fn`, and `car` and `cdr` are written as `hd` and `tl`. Like scheme, the language is lexically scoped, so the valid identifiers at a particular place in the program are determinable statically. (MM1 currently uses an interpreter for evaluating lisp expressions, but a compiler may be implemented in the future.)

When an s-expression is evaluated:

* Numbers like `0` or `42` evaluate to themselves, as do strings, booleans (`#t` and `#f`), the empty list `()`, and the atom `_`.
* A quoted expression `'expr` evaluates to the literal expression `expr`, except that unquotations `,expr` are evaluated. (In other words, MM1 quotation is the same as scheme quasiquotation.)
* A formula `$ foo $` is parsed using the math parser in the current environment, producing an unelaborated term s-expression. Prefix comma is also used to denote unquotation here. For example:

      sort wff;
      term imp: wff > wff > wff;
      infixr imp: $->$ prec 25;
      do {
        $ foo -> bar $       -- (imp (foo) (bar))
        $ foo -> ,(+ 2 2) $  -- (imp (foo) 4)
      };

* It is an error to evaluate a improper list `(a b . c)`.
* A list `(f a b c)` first evaluates `f`. If `f` is a syntax form, then the form handles the arguments `a b c` according to its own rules. If `f` is a procedure (or a reference to a procedure) then it evaluates `a b c` as an argument list and calls `f` with the result.
* An atom such as `x` evaluates to the stored value associated to `x` in the local context if it exists, or in the global context otherwise. There is a default global context which contains all the bindings for `+`, `min`, `def` and so on from the examples.

There are a few ways that lists can be evaluated, so we name them here:

* An argument list such as `a b c` above evaluates each in turn (from left to right) and passes on the resulting list of values to the function, except that a `(def)` in the list creates a local definition (for the rest of the argument list) and does not contribute to the list itself. For example:

      (list 1 (def x 5) x)     -- (1 5)

  At the location of the `1` and after the body of the `(list)` expression `x` is no longer valid.

* A `begin`-list is a sequence of expressions that are all evaluated, but only the last expression in the list is returned. As with argument lists, `(def)` creates a local definition that scopes over the remainder of the block. An empty sequence is also valid and produces the special value `#<undef>`.

In addition to the expressions that have s-expression counterparts, there are some other runtime values that have no explicit representation:

* `#<undef>` is a special value that is produced by many expressions that "return nothing", such as `set!`. In a `do` block, the default behavior is to evaluate each expression and print the result, unless the result is `#<undef>` in which case nothing is printed.
* A syntax form is bound to a syntax value; for example `def` itself evaluates to a syntax value "def". This is what triggers macro-like treatment of the other arguments rather than eager evaluation.
* A `#<closure>` or procedure is a value that can be applied to arguments to produce a result. `fn` can be used to produce closures.
* A `ref` is a mutable wrapper around a value. Unlike Scheme, not all s-expressions are mutable; `set!` only works on refs and they must be created explicitly.
* `mvar` and `goal` are special types used in elaboration; see [Elaboration](#elaboration).

Syntax forms
---

Some expressions have special behavior when evaluated; these roughly correspond to "keywords" in a standard programming language, but the list can be extended by macro forms.

* `def` defines a new local or global binding. `(def x exprs)` will evaluate `exprs` as a `begin`-list, and bind the result to `x`. If the `(def)` appears at the top level of a `do` block, it produces a global definition `x`, otherwise it is locally scoped (until the end of the enclosing expression).
  * `(def (x a b c) exprs)` is equivalent to `(def x (fn (a b c) exprs))`.
  * `(def (x a b . c) exprs)` is equivalent to `(def x (fn (a b . c) exprs))`.
  * `(def (x . a) exprs)` is equivalent to `(def x (fn a exprs))`.

  A definition `(def x foo)` at the top level is equivalent to an assignment `(set! x foo)`, if `x` is already assigned. That is, the global environment acts as if it consists of mutable references, so global variables are not lexically scoped. For example, this is valid even though `bar` is a forward reference:

      (def (foo) bar)
      (def bar 5)
      (foo)          -- 5

* `fn` declares a closure, a value that can be applied to a list of values to obtain a result. The first argument determines how the incoming argument list is bound to values:
  * `(fn (a b c) exprs)` requires that the list has length exactly 3, and the values are bound to `a`, `b` and `c` respectively.
  * `(fn (a b . c) exprs)` requires that the list has length at least 2. The first two values are bound to `a` and `b`, and `c` is bound to a list with the remainder of the arguments.
  * `(fn a exprs)` binds `a` to the list of all the arguments.
  The list `exprs` is then evaluated as a `begin`-list where the local context is extended with the bindings determined by the first argument.
* `let` assigns a list of variables to values inside its scope. For example, `(let ([x 1] [y 2] [z 3]) exprs)` evaluates `exprs` as a `begin`-list with the local context extended with `x := 1`, `y := 2`, and `z := 3`.
  * The use of brackets for individual initializers is conventional but not required.
  * The bindings are evaluated in order, so `(let ([x1 e1] [x2 e2] [x3 e3]) exprs)` is equivalent to
    `(let ([x1 e1]) (let ([x2 e2]) (let ([x3 e3]) exprs)))`. This means that when expression `e2` is evaluated, `x1` is in the local context but `x2` and `x3` are not. In Scheme, this is called `let*`.
  * Like `def`, the LHS variable can also be a list or improper list, and it will define a function.\
    `(let ([(f a b) e]) exprs)` is equivalent `(let ([f (fn (a b) e)]) exprs)`.
  * Because of lexical scoping and the fact that `x` is not bound while the expression for `x` is being evaluated, this means that `let` cannot be used to define local recursive functions.
* `letrec` has the same syntax as `let`, but it can be used to define local recursive and mutually recursive functions. `(letrec ([x e1] [y e2]) exprs)` is equivalent to:

      (let ([x (ref!)] [y (ref!)])
        (set! x e1)
        (set! y e2)
        exprs)

  Notice in particular that `x` does not actually refer to the result of `e1` this way, but rather to a ref-cell that contains the result of `e1`. For the case of mutually recursive functions, this is mostly transparent, because references to functions can be applied without explicit dereferencing.

  As an example, we can reuse the factorial example as a local function:

      (letrec ([(fact x) (if (= x 0) 1 (* x (fact (- x 1))))])
        (fact 5))       -- 120

* `quote` evaluates its argument in "quotation mode", in which syntax expressions evaluate to the corresponding s-expression values. It has the special syntax `'expr` which is the same as `(quote expr)`. So while `x` evaluates to the value that `x` refers to in the local or global context, `'x` evaluates to the atom `x`.
  * The only expression that does not evaluate to itself in quotation mode is `(unquote e)`, with syntax `,e`, which evaluates `e` in the usual way and returns the result.
* `if` evaluates a conditional expression. `(if cond e1 e2)` evaluates `cond`, and if `cond` is truthy then it evaluates and returns `e1`, otherwise it returns `e2`. An expression is truthy if it is not `#f` - all other values, including `#<undef>`, `()`, `""`, and `0` are considered as "true".

* `match` performs pattern matching on an expression. It is based on the [Chicken Scheme implementation](https://wiki.call-cc.org/man/3/Pattern%20matching). For example, `(match '(1 (2) 3) [(x (y) z) expr])` will bind `x` to `1`, `y` to `2`, and `z` to `3` in the body of `expr`.
  * The syntax is `(match e clauses)` where `clauses` is a list of clauses. Each clause is tried in order, and the result of the body of the match is the first successful clause.
  * A clause has the form `[pat expr]` or `[pat (=> k) expr]`. This matches the pattern `pat` against the input, evaluating `expr` with the bindings resulting from the pattern match if it is successful, and otherwise passing to the next clause. If the `(=> k)` form is used, the variable `k` is bound to a zero-argument continuation which can be called in the body of `expr` to pass to the next clause even though the current clause was successful.
  * When a pattern is "matched" against a value, it will either succeed and bind a set of variables to values (the set of variables is determined statically), or fail and bind nothing. The patterns are:

    * `x` (an atom) matches anything, and binds the value to `x`.
    * `_` matches anything, and binds nothing.
    * A string, `#t` or `#f`, or `()` all match against themselves (they ensure the input is equal to them) and bind nothing.
    * A quoted pattern `'pat` will match in "quote mode", which is the same as a regular pattern match except that atoms match against themselves instead of binding. An unquotation `,pat` will return to regular pattern matching mode.
    * A formula `$ foo $` acts like a quotation; the formula is parsed and the resulting expression is treated as a quoted pattern. As with regular quotation, `,x` can be used for unquotation. For example, if there is a notation `<` for the definition `lt`, then `$ ,x < ,y $` will check that the input is a less-than expression and the arguments will be bound to `x` and `y`.
    * `(p1 ... pn)` ensures the input is a list of length `n`, and matches the `n` patterns with the `n` input values.
    * `(p1 ... pn "...")` (with a literal `...` at the end) ensures the input is a proper list of length at least `n`, and matches the first `n` patterns with the `n` input values. You can also use `___` in place of `...`.
    * `(p1 ... pn __ k)`, where `k` is a number, ensures the input is a proper list of length at least `n + k`, and matches the first `n` patterns with the `n` input values.
    * `(p1 ... pn . p)`, ensures the input is a proper or improper list of length at least `n`, and matches the first `n` patterns with the `n` input values and matches the tail against the pattern `p`.
    * `(and p1 ... pn)` will match the input against all the patterns `p1` through `pn`, and using all the resulting bindings. It succeeds if all the patterns match.
    * `(or p1 ... pn)` succeeds if any of the patterns match, and it uses all bindings from the successes. Results are unspecified if the patterns do not all bind the same variables.
    * `(not p1 ... pn)` succeeds if none of the patterns match, and binds nothing.
    * `(? pred p1 ... pn)` succeeds if all of the patterns `p1`, ..., `pn` match, and `(pred v)` evaluates to a truthy value where `v` is the value being matched. `pred` should evaluate to a unary predicate *in the context of the match expression*; bindings from the match are not available when the predicate is evaluated.

* The `match-fn` and `match-fn*` keywords are similar to `match`, but define functions instead of matching an input argument immediately. `(match-fn clauses)` is equivalent to `(fn (x) (match x clauses))`, and `(match-fn* clauses)` is equivalent to `(fn x (match x clauses))`.
* `focus` is a tactic that is a syntax form because it does some preprocessing before evaluating its arguments (which is not something a regular function can do). See [Elaboration](#elaboration) for more details.

Builtin functions
---

At the beginning of execution, the global context contains a number of primitive functions useful for constructing and manipulating values.

* `display` takes a string and prints it. In the interactive editor mode, this appears as an info diagnostic over the word "`display`". In this documentation the results are displayed in comments on the right.

      (display "hello world")         -- hello world
      (display 42)                    -- error, expected string
* `print` takes an arbitrary expression and pretty-prints it.

      (print "hello world")   -- "hello world"
      (print 42)              -- 42
      (print ())              -- ()
      (print #t)              -- #t
      (print '(1 2 . 3))      -- (1 2 . 3)
      (print '$ foo $)        -- $ foo $
      (print print)           -- #<closure>
      (print (begin))         -- #<undef>
      (print (ref! 5))        -- 5

* `begin` returns its last argument, or `#<undef>` if it is given no arguments. In Scheme this is a syntax form, but in MM1 all functions have the same evaluation semantics as `begin`, so the only interesting thing this function does is ignore its other arguments.

* `(apply f a b '(c d))` evaluates to the result of `(f a b c d)`. That is, the first argument should be a closure and the last argument should be a list, and it applies the closure to the list, with any in between arguments added to the head of the list. `(apply)` is an error, and if `f` is a syntax form then this is also an error, i.e. `(apply def (x 5))` does not work.

* `(+ a b c)` computes the sum of the (integer) arguments. `(+)` is zero and `(+ a)` is `a`.
* `(* a b c)` computes the product of the (integer) arguments. `(*)` is one and `(* a)` is `a`.
* `(max a b c)` computes the maximum of the (integer) arguments. `(max)` is an error.
* `(min a b c)` computes the minimum of the (integer) arguments. `(min)` is an error.
* `(- a b)` computes the subtraction `a - b`. `(- a b c)` is `a - b - c`, `(- a)` is `-a`, and `(-)` is an error.
* `(< a b)` is true if `a` is less than `b`. `(< a b c)` is true if `a < b` and `b < c`. `(< a)` is true and `(<)` is an error.
* Similarly, `<=`, `>=`, `>` and `=` perform analogous iterated comparisons. There is no not-equal operator.
* `(->string e)` converts an expression to a string. Numbers are converted in the usual way, strings, atoms and formulas (which are all containers for strings) get the underlying string, and other expressions are pretty printed using the same method as `print`.

      (->string 42)     -- "42"
      (->string (- 42)) -- "-42"
      (->string "foo")  -- "foo"
      (->string 'foo)   -- "foo"
      (->string $foo$)  -- "foo"
      (->string '(1 . 2))  -- "(1 . 2)"

* `(string->atom s)` converts a string to an atom. This can be used to create atoms that violate the concrete syntax, for example if they have embedded spaces.

      (string->atom "foo")         -- foo
      (string->atom "foo$bar baz") -- foo$bar baz

* `(not e1 e2 e3)` returns `#f` if any argument is truthy, and `#t` otherwise. It is not short-circuiting.
* `(and e1 e2 e3)` returns `#t` if every argument is truthy, and `#f` otherwise. It is not short-circuiting.
* `(or e1 e2 e3)` returns `#t` if any argument is truthy, and `#f` otherwise. It is not short-circuiting.
* `(list e1 e2 e3)` returns the list `(e1 e2 e3)`. It differs from `quote` in that it evaluates its arguments.
* `(cons e1 e2)` returns `(e1 . e2)`. With more or less arguments:
  * `(cons)` returns the empty list.
  * `(cons e1)` returns `e1`.
  * `(cons e1 e2 e3)` returns `(e1 e2 . e3)`.
* `(pair? e)` is true if its argument is a cons of something, that is, a nonempty list or improper list.
* `(null? e)` is true if its argument is `()`.
* `(string? e)` is true if its argument is a string (not a formula or atom).
* `(def? e)` is true if the argument is not `#<undef>`.
* `(hd e)` returns the head of the list, or left element of the cons expression. It is known as `car` in most lisps.
* `(tl e)` returns the tail of the list, or right element of the cons expression. It is known as `cdr` in most lisps.
* `(ref? e)` is true if the argument is a ref-cell.
* `(ref! e)` constructs a new ref-cell containing the value `e`.\
  `(ref!)` constructs a new ref-cell containing `#<undef>`.
* `(get! r)` dereferences the ref-cell `r` to get the value.
* `(set! r v)` sets the value of the ref-cell `r` to `v`.
* `(async f args)` evaluates `(f args)` on another thread, and returns a procedure that will join on the thread to wait for the result.
* `(atom-map! [k1 v1] [k2 v2] ...)` creates a new mutable atom map, a key-value store.
* `(lookup m k)` gets the value stored in the atom map `m` at `k`, or `#<undef>` if not present.
* `(insert! m k v)` inserts the value `v` at key `k` in the mutable map `m`, and returns `#<undef>`.
* `(insert m k v)` returns an immutable map based on the immutable map `m`, with the value `v` inserted at key `k`.

See [MM0-specific builtin functions](#MM0-specific-builtin-functions) for more functions that have to do with interaction between the lisp and MM0 environments.

Elaboration
===

After parsing, the MM1 file goes through elaboration, which performs most of the actual work described in the file. There is a global context that contains all the definitions and theorems encountered so far, the parser environment (that determines how to parse formulas), as well as the lisp global context.

Each statement effects some change to the global environment:

* `delimiter` and the other notation commands add themselves to the math parser.
* `do` evaluates the contained lisp expressions.
* A declaration goes through the following steps:
  * Type inference is used to infer any missing binders or binder types. This uses only the information available from the statement of the theorem.
  * Definitions have their values evaluated right away.
  * For theorems, the proof is evaluated asynchronously.
* The annotation expression itself is evaluated before the enclosed statement, but the function `(annotate s e)` is called after `s` has been added to the environment. (Any statement can be annotated, but declarations that do not have names pass `#<undef>` to the `annotate` function.)

The fact that `theorem` proofs are evaluated asynchronously has some consequences. In particular the theorem is elaborated in a copy of the global environment, so its ability to affect the environment is limited, for example it cannot add new theorems to the environment. However, mutable ref-cells still allow for communication between threads. For example, this program will return a number nondeterministically:

    provable sort wff;

    do { (def mutex (ref! #f)) };

    theorem foo (h: $ ph $): $ ph $ =
    (begin
      (set! mutex #t)
      'h);

    do {
      (def (spinlock n) (if (get! mutex) n (spinlock (+ n 1))))
      (spinlock 0)
    };

The effect of the `theorem` can also be done more directly using `(async (fn () (set! mutex #t)))`.

Metavariables and goals
---

Once the statement of a theorem has been determined, the local context is set up with the declared variables and hypotheses, and the initial state is set to have no metavariables and one goal, the theorem statement. A goal is a hole awaiting a proof, and a metavariable is a hole awaiting a term. The syntax of MM0 statements maps to expressions like so:

* A variable `x` from the context is represented as the atom `'x`.
* A term constructor such as `ph -> ps` is represented as the list `'(imp ph ps)` containing three atoms. (`imp` is not a lisp function, so this must be written as `'(imp ph ps)` to obtain this literal expression).
* A metavariable is represented as `#<ref #<mvar s bd>>`, that is, a mutable reference to an `mvar` value, which stores the target sort (an atom like `'wff`) and boundedness (`#t` if the target is a bound variable).
* Metavariables are assigned using `set!`, so it is also possible to find a reference to an expression in a lisp term that denotes an expression; these ref cells should be ignored. For example `(imp #<ref ph> ps)` is also a representation of the expression `ph -> ps`. These indirections are cleaned up lazily.

The syntax of proofs is parallel to that of expressions:

* A hypothesis `h` from the context is represented as the atom `'h`.
* A theorem application `(foo x1 t2 p1 p2)`, written as a list with theorem `'foo` at the head, contains arguments for all the binders, including expressions for the bound variables like `x1` and regular variables `t2`, and proof expressions for the subproofs `p1` and `p2`.
* The expression `(:conv t c p)` represents a proof of `t` given a proof `p` of `t2` and a conversion proof `c: t = t2`.
* A goal is represented as `#<ref #<goal t>>` where `t` is the expression to be proved.
* After a goal has been assigned, it takes the form `#<ref p>` where `p` is a proof.

Conversions are proofs of definitional unfolding:

* A variable `x` represents a proof of `x = x`, and
* `(t c1 c2 c3)` represents a proof of `(t a1 a2 a3) = (t b1 b2 b3)` where `c1: a1 = b1`, `c2: a2 = b2`, and `c3: a3 = b3`. Together these imply that a term `t` represents its own proof of reflexivity.
* `(:sym c)` is a proof of `e2 = e1` if `c` proves `e1 = e2`.
* `(:unfold d es xs c)` represents a proof of `d es = e2` where `c` is a proof of `e1 = e2` and `e1` is the result of substituting `es` for the bound/regular variables and `xs` for the dummy variables in the value of the definition `d`.

The list of unresolved metavariables is maintained by MM1. These are displayed as variables like `?a`, `?b`, `?c` (suppressing the type information). The names are consistent at a given time but new metavariables are created and old metavariables get assigned frequently, so the list is culled periodically and the variables renamed to prevent the display names from getting too long.

The list of goals is more explicitly accessible to tactics via the `(get-goals)` and `(set-goals gs)` functions. Many tactics work on the first goal or first few goals, and the `(focus)` tactic suppresses the other goals temporarily. Tactics are responsible for ensuring that they do not "drop" a goal, i.e. they do not forget to assign all goals they remove from the list.

In the initial state there are no metavariables and one goal corresponding to the theorem statement. New metavariables can be created via the `(mvar! s bd)` function, which makes a new metavariable with the specified type and boundedness and adds it to the list of metavariables.

New goals are created via `(ref! (goal t))`, but they are not added to the list of goals automatically.

Pre-expressions
---

The main workhorse tactic is `(refine)`, which gets some helpful syntax sugar to assist with short proofs. `(refine es)` will accept a list of `n` proof pre-expressions, and will unify them against the first `n` goals. (Additional arguments are ignored.) A proof pre-expression is similar to a proof expression, but it is generally less explicit and contains placeholders that indicate that a metavariable should be constructed. Pre-expressions are always elaborated with a target type, propagated from the outside in.

* The atom `_` indicates that a new proof goal or metavariable should be created with the target type.
* An atom `h` applies a hypothesis, or a nullary theorem. In general `(h)` and `h` are not distinguished as pre-expressions, with the correct interpretation being inferred from context.
* A theorem application is written as `(foo p1 p2)`. With this application, only proof subterms should be given; bound and regular variables should not be specified and are treated as `_`.
  * `(foo p1)` is equivalent to `(foo p1 _)` if `foo` takes two arguments.
  * `(foo p1 p2 p3 p4)` will call the function `(refine-extra-args callback e e3 e4)` when elaborated, where `e` is the result of elaboration of `(foo p1 p2)`, and `e3` and `e4` are the results of elaborating `p3` and `p4` respectively. `callback` is a function that can be called such that `(callback p)` will elaborate a proof pre-expression. (This allows for new goals to be sequenced properly, because `set-goals` is not called until `refine` finishes elaborating the pre-expression.)

    The default implementation of `refine-extra-args` simply gives an error, but it can be overridden to provide a more useful behavior.
* The expression `(! foo x1 t2 p1 p2)` also applies theorem `foo` to subproofs `p1` and `p2`, but it provides a place to supply the bound and regular variables in the substitution rather than letting them be inferred by unification.
* The expression `(!! foo x1 p1 p2)` is similar, except it only accepts values for the bound variables, not the regular variables. (This variant is useful because all dummy variables must be named but unification will not invent names for dummy variables unless they are written somewhere.)
* The expression `(:verb e)` accepts an expression `e`, and elaborates to `e` "verbatim". That is, no additional analysis is performed on `e`, and it follows the syntax of complete expressions, not pre-expressions. This is helpful for "unquotation" in tactic programming.
* A *quoted* formula `$ foo $` evaluates the formula `$ foo $` in the current formula context, in an empty lisp local context (if unquotation is used). This is needed because refine pre-expressions are usually written inside `quote`, so formulas end up quoted as well unless you use `,$ foo $`. Since evaluating a formula yields a pre-expression, these can be passed straight to `refine`.

In order to make it easy to specify proofs from pre-expressions, if the lisp expression `e` given as the value of a theorem evaluates to something other than `#<undef>`, then it is silently replaced with `(refine e)`, which will elaborate the pre-expression and apply it to the single open goal.

MM0-specific builtin functions
---

* `(set-timeout n)` sets the timeout for running individual theorems and `do` blocks to `n` milliseconds. The default is 5 seconds.

* `(mvar? e)` returns `#t` if `e` is an unsolved metavariable value. *Note:* Holes in expressions are *not* represented as raw metavariables, they are ref-cells to metavariables. So to test if a metavariable has not been assigned you can use `(mvar? (get! e))`.

* Similarly, `(goal? e)` returns `#t` if `e` is an unsolved goal expression, and `(goal? (get! e))` checks if a goal reference has not been solved.

* `(mvar! s bd)` creates a new metavariable ref-cell with sort `s` and boundedness `bd` and adds it to the list of open metavariables. To emphasize:

      (mvar? (mvar! "foo" #t))            -- #f
      (ref? (mvar! "foo" #t))             -- #t
      (mvar? (get! (mvar! "foo" #t)))     -- #t

* `(pp e)` pretty-prints a (fully elaborated) term expression using declared math notations. It relies on the theorem context to typecheck the formulas and provide context, and will use `???` or `?foo?` for things it doesn't understand.

      provable sort wff;
      term imp: wff > wff > wff;
      infixr imp: $->$ prec 25;

      do { (display (pp '(imp x y))) };   -- ?x? -> ?y?
      theorem foo (x y: wff): $ x $ =
      (display (pp '(imp x y)));          -- x -> y

* `(goal e)` creates a new goal value given a statement expression. It will need to be wrapped with a `ref!` to be used with `set-goals`.

      (goal? (goal $foo$))                -- #t

* `(goal-type g)` gets the statement of a goal (wrapped by any number of refs).

      (goal? (goal $foo$))                -- (foo)
      (goal? (goal $foo$))                -- (foo)

* `(infer-type p)` gets the statement proven by the proof `p`. This does not perform full typechecking on `p`.

* `(get-goals)` returns the current goal list, a list of references to goals. Some goals may already have been assigned.

* `(set-goals g1 g2 g3)` sets the goal list to `(g1 g2 g3)`, replacing the current goal list. If any of the provided goals are already assigned they are removed from the list.

* `(to-expr e)` elaborates a term pre-expression into an expression, producing metavariables for `_` placeholders in the expression.

* `(refine p)` elaborates a proof pre-expression into a proof, and unifies its type against the first goal.\
  `(refine p1 p2 p3)` applies three proof pre-expressions to the first three goals. If there are fewer than three goals the remaining proofs are ignored.

* `(have h p)` elaborates the proof pre-expression `p` to a proof, infers the type `e` of the proof, and adds `e` to the list of proven subproofs, after which `h` may be referred to like any other theorem hypothesis.\
  `(have h e p)` is the same except that `p` is elaborated with `e` as the expected type.

* `(stat)` prints the current proof state, which consists of a list of subproofs, a list of goals, and a list of metavariables accompanied by their sorts.

Compilation
===

Once a MM1 file is elaborated successfully, the resulting definitions are compiled down to an MM0 file containing all the public theorem statements, and an MMU file containing the proofs. TODO
