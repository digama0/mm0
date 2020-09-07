# Metamath C: A programming language for verified programs

The requirements of verified programs are somewhat unique and not well addressed by either conventional programming languages such as C, Python, Rust, Haskell etc.,  or proof assistants like Isabelle, Coq, Lean, etc. On the one hand, for a low level language we need ways to talk about imperative procedures, pointer manipulation, while loops and the like, where every construct has a well defined lowering to machine instructions, and on the other hand we need the expressiveness to reason about the program inside an ambient logic, where infinite sets and undecidable predicates are common. These can sometimes be approximated by assertions, which have the advantage of being executable, but these can only be used for dynamic analysis, and in the context of a formal proof of correctness, executability of intermediate assertions is irrelevant and limiting (although it is nice to have when available).

Metamath C (abbreviated MMC) is a language that uses total functions (provably terminating mathematical functions as one would find in HOL or a dependent type theory) for its semantics, combined with inline separation logic through erased "hypothesis variables" for reasoning about heap structures and non-functional components, on top of a C-like structure that is used to provide well defined and predictable lowering to machine code.

MMC is currently written in arguments to the MMC compiler, which has an interface through MM1. As a result it inherits the same Scheme-like syntax used in MM1 tactics. (This may change in the future.) MMC has an extensible type system, and it produces MM0 proofs in the back-end. Because types are implemented as "type guards", they have an independent existence as well, and there are primitives for "casting" a variable to a type `T` given a proof that it has type `T`.

## Types

A *type* is a function that maps values to separating propositions over machine states. That is, it is a true-or-false statement that applies to portions of the machine state (registers and memory). This is a very low level view, but it has the advantage that because it is so general, users can define types of arbitrary complexity, containing invariants and ownership semantics. Types also contain a size and an alignment, although for the x86 instantiation of MMC all types have alignment 1. Here are some basic types:

    () | bool | u8 | u16 | u32 | u64 | i8 | i16 | i32 | i64 | (own T) | (array T n)

The first few represent signed and unsigned integers of various widths. The `(own T)` type is an owned pointer to a type. The `(array T n)` type is a contiguous sequence of `n` elements of type `T`. (The value `n` is not stored anywhere in memory, it is a parameter of the type.) Types can depend on values, which is often known as dependent typing, however unlike most dependent type theories very little "computation" is done inside types, and instead a `(pun)` must be used to re-type a term given a proof that it has a type. (This is not like a C cast that can be used to reinterpret a type - the value must satisfy all invariants of the target type to be eligible for `pun`.)

There are two other pointer types, inspired by Rust semantics:

    (& T) | (&mut T)

The `(& T)` type of shared references is not a real type, but desugars to `(& p T)` where `p` is the "provenance" of the allocation from which `T` derives. The compiler inserts an assertion that all pointer provenances are alive to the function's frame condition. (The proper way to handle this is with ghost state as in Iris, but that is future work.) The upshot is that these types can be manipulated and copied like regular shared references.

The `(&mut T)` type of mutable references is also not a real type, but desugars to `(mut {x : (own T)})`, which corresponds to an inout parameter of type `(own T)`. That is, this is an argument that is passed into the function, and must be preserved and passed out at the end (but the output part is only a ghost parameter). The compiler ensures that the value is not dropped. `(mut _)` is an attribute that does this inout translation generally.

With any of the pointer types `(own T)`, `(& T)`, `(&mut T)`, the notation `(* x)` can be used in assertions to refer to the value of type `T` that `x` dereferences to. This is desugared to `x |-> y` in the frame and `y` at the point of use.

There are also some additional types used only in ghost variables and propositions. `nat` is the type of nonnegative integers, and `int` is the type of integers. These types are unbounded and so cannot be concretized. (As a reminder, even bignums cannot get arbitrarily large. This set includes numbers that provably cannot exist on an x86 machine.) All numeric operations like `x + y` operate on `nat` or `int`, even when the arguments are fixed length integers like `u32`. That is, if `x y: u32` then `x + y: nat`. (If subtraction or signed numbers are involved then the result has type `int` instead.) This means that in the expression language overflow is impossible.

Instead, overflow occurs when assigning this expression to a variable (which as mentioned cannot have type `nat` unless it is a ghost variable). This is done using the `cast` function, which requires a proof that the computed value lies within the bounds for the target type. The compiler will sometimes be able to prove these goals automatically, and in particular some specific patterns like `x + y < 2^64` can be synthesized by the compiler without necessarily first computing `x + y` and then comparing with `2^64` (which wouldn't work if `x` and `y` are fixed size types like `u64`). For larger expressions that go well beyond the range of a fixed size expression before coming back in range like `b := (2 ^ 2 ^ x < 2 ^ 2 ^ 64)`, the compiler may need assistance to find a valid execution plan.

## Names and scoping

Identifiers can refer to:

* MMC keywords and builtin functions, like `proc` or `cast`,
* Local variables, introduced by variable declarations and function parameters,
* Bound variables in assertions with quantifiers,
* Global variables and constants,
* MMC functions and procedures,
* Types, and
* Imported MM1 definitions.

As a DSL embedded in MM1, antiquotation can also be used to perform the equivalent of C preprocessor macros by constructing an MMC program expression programmatically.

Global variables, functions and procedures have global scope, and can be forward-referenced as long as the declaration comes in the same MMC invocation. Otherwise the usual C technique of declaring and then defining a function can be used. Bound variables extend until the end of the binding structure (for example `A. x (ph /\ ps)` permits the use of `x` in `ph` and `ps` but not past the end parenthesis) and local variables extend until the end of the block. Note that `:=` variable declarations can be used to destructure functions with multiple return values as in `(x y z) := (foo)` and this declares variables `x,y,z`.

## Expressions

Expressions in MMC have roughly two "kinds", terms and hypotheses. Terms are as one would expect in an imperative programming language: arithmetic, function application, and some special syntax forms for operators like `cast`. Hypotheses are assertions about variables in the program, and these variables get passed around like regular variables but they are ghosts: they leave no trace in the generated code and only serve to tie the proof together. The type of a hypothesis is a separating proposition. For example, a function that only returns prime numbers might look like `proc (mk-me-a-prime : {val : u32} {h : $ Prime val $})`, where `val` is the actual returned value and `h` is a proof that `val` is prime. This might be received by the caller as `(val h) := (mk-me-a-prime 2)`, using multiple return values to pass both arguments.

(As a side note: the `{}` are used as in MM1 to write infix functions. You will see them used here for functions like `:`, `:=` and `+` so that we don't have to write `(: val u32)`. This is the price of being an MM1 embedded DSL, at least until MM1 supports custom parsing.)

### Arithmetic operations

Most functions on natural numbers work in MMC, but all of them return unbounded integers, and must be explicitly `cast` back to the desired storage type.

* If `x,y: nat` then `{x + y}: nat`. Similarly if `x` and `y` have types `u8-64` then `{x + y}: nat`. If `x` and `y` have types `i8-64` or `int` then `{x + y}: int`.
* If `x,y` have any integral types then `{x - y}: int`
* The promotion rules for `{x * y}: nat/int` are the same as `{x + y}`
* The promotion rules for `{x // y}: nat/int` and `{x % y}: nat/int` are also the same as `{x + y}`. Division by zero is defined and returns 0, and `{x % 0} = x`, but one can also use `{x // (y h)}` and `{x % (y h)}` where `h: $ y != 0 $` to skip the check.
* If `x,y: nat` then `{x ^ y}: nat`. Prefer `{x * {2 ^ n}}` and `{x // {2 ^ n}}` to left and right shift if the intent is to do numeric operations. The actual bitshift operators truncate, as mentioned below.

Bitwise operations and logical shifts on fixed width unsigned integers do nothing to the types.

* If `x,y: uN` then `{x band y}, {x bor y}, {x bxor y}, (bnot x): uN`
* If `x,y: nat` then `{x band y}, {x bor y}, {x bxor y}: nat`
* If `x,y: int` then `{x band y}, {x bor y}, {x bxor y}, (bnot x): int`
* Signed values are promoted to `int` for bitwise ops

In most cases where unintended `nat` promotion has occurred a `cast` will bring the value back in range, although if the proof cannot be performed automatically the user must provide it. Alternatively `as` can be used to turn a `nat`/`int` into a `uN` or `sN` by reducing modulo `2^N`.

### Comparison operations

* If `x,y` have any numeric type (including `nat`/`int`) then the operators `<` `<=` `>` `>=` `=` `!=` compare them to produce a value of type `bool`. The compiler may fail to find a way to compile comparisons on type `nat` or `int`, but if it succeeds then the meaning is that of the abstract mathematical reading.
* If `x,y` have type `bool` then `{x or y}, {x and y}, (not y): bool`.

## Assignment

The `:=` operator in MMC has several functions. In its simplest use it binds the result of the right hand side of the equation to the place on the left, for example

    {{x : u64} := {1 + 2}}
    -- now x: u64

Here `{x : u64}` is a type ascription, and indicates that the storage for `x` will be 64 bits large. In subsequent lines the type checker will know that `x` is in the context and has type `u64`, but not that it has value `3`. The assignment statement is itself an expression, and it returns a proof that the value is equal to the expression (if the RHS is a pure expression).

    {h := {{x : u64} := {1 + 2}}}
    -- now x: u64 and h: $ x = 1 + 2 $

This is just one example of expressions that return proofs. Another example is the `assert` function, which returns a proof of any expression:

    {h := (assert {{2 + 2} = 4})}
    -- here h: $ 2 + 2 = 4 $

This also works if the statement is false:

    {h := (assert {{2 + 2} = 5})}
    -- here h: $ 2 + 2 = 5 $

because `assert` terminates the program if the assertion fails to hold, so we can safely assume that on the branch where we are still executing the program, the assertion is true.

The semantics of assignments here is like that in functional programming languages, i.e. they are let bindings. However, shadowed bindings can be used as a hint to the compiler that a variable can be overwritten:

    {{x : u8} := 2}
    {{x : u8} := 3} -- this shadows/overwrites the other x

However, this causes a problem with hypotheses:

    {h1 := {{x : u8} := 2}} -- x: u8, h1: $ x = 2 $
    {h2 := {{x : u8} := 3}} -- x: u8, (x*: ghost u8), h1: $ x* = 2 $, h2: $ x = 3 $

The variable `x*` shown for the type of `h1` is used in printing to refer to a shadowed variable named `x`. The variable `x*: ghost u8` is in the state but hidden by default. It cannot be typed directly in the program. (We will discuss `ghost` variables in the next section.) Instead, we can add a `with` clause to the assignment to rename the old version of the variable:

    {h1 := {{x : u8} := 2}}
    {h2 := ({{x : u8} := {3 + x}} with {x -> old_x})}
    -- old_x: u8, x: u8, h1: $ old_x = 2 $, h2: $ x = 3 + old_x $

    {h1 := {{x : u8} := 2}} -- x: u8, h1: $ x = 2 $
    {h2 := ({{x : u8} := {3 + x}} with {new_x <- x})}
    -- x: u8, new_x: u8, h1: $ x = 2 $, h2: $ new_x = 3 + x $

The `with` modifier on an assignment allows it to simultaneously rename some variables in the state, which is especially useful for self-assignments like `{x := {x + 1}}`. Note that neither the old or new value of `x` is considered ghost in this situation because they can both be referred to later as a result of the rename. It is also possible to use `x -> (ghost old_x)` to ensure that the old value of `x` is marked ghost, so that it can be compiled to a reassignment instead of a copy.

### Ghost variables

An assignment

    {(ghost x) := 2}
    -- here x: ghost nat

is like a regular assignment except that the introduced variable does not exist at run time. The compiler tracks usage of ghost variables to ensure that they do not enter the data flow, but they can be used to perform computations that are needed for the proof but not for the program. They can be used in types (like the `n` in `array T n`) as well as in loop variants and invariants. They can also have infinite types like `nat`, unlike regular variables. We can use them to store old values of variables:


    {h := {{x : u8} := 1}}
    -- x: u8, h: $ x = 1 $
    {h2 := {(ghost old_x) := x}}
    -- x: u8, h: $ x = 1 $, old_x: ghost u8, h2: $ old_x = x $
    {h3 := (entail h2 h eqtr)}
    -- x: u8, old_x: ghost u8, h2: $ old_x = x $, h3: $ old_x = 1 $
    {h4 := {{x : u8} := {(reflect x (eqcom h2)) + 2}}}
    -- x: u8, old_x: ghost u8, h3: $ old_x = 1 $, h4: $ x = old_x + 2 $

We will discuss the `entail` function later, and the `eqtr` and `eqcom` functions are proofs in the ambient logic of PA. The `reflect` function allows us to have an expression whose computational realization is `x` and whose proof realization is `old_x`, so that `h4` is not discarded before it can be used. A simpler version of the above would be

    {h := {{x : u8} := 1}}
    -- x: u8, h: $ x = 1 $
    {h2 := {{x : u8} := {(reflect x h) + 2}}}
    -- x: u8, h2: $ x = 1 + 2 $

where we have skipped the definition of `old_x` by threading the known previous value of `x`, and as seen in the previous section we can also use a `with` clause to perform the renaming directly:

    {h := {{x : u8} := 1}}
    -- x: u8, h: $ x = 1 $
    {h2 := ({{x : u8} := {x + 2}} with {x -> old_x})}
    -- x: u8, old_x: u8, h2: $ x = old_x + 2 $

### Tuples

Some functions return a list of values, which are destructured at the call site:

    (proc (foo {x : u8} {y : u8} : {a : u8} {b : u8} {h : $ a = b $}))

    {(x y h) := (foo 1 2)}
    -- x: u8, y: u8, h: $ x = y $

Tuples can be constructed using the `list` function, and `list` is also the name of the tuple type:

    {{(a b c) : (list u8 u8 u64)} := (list 1 2 3)}
    -- a: u8, b: u8, c: u64

### Strong updates and soft typing

Because we can view a re-assignment as a mere shadowing let binder, assignments to variables can change their type:

    {{x : u64} := 1}
    {{x : i64} := (- 1)}

The old type of a variable can be used as a hint for the new type but the type of the RHS of the expression takes precedence (unless the RHS is an expression that takes its type from the calling context, e.g. `cast`).

But more unusually, a variable is "separable" from its type using the `typeof!` operator:

    {{x : (own (array u8 4))} := (malloc u8 4)}
    {({x : u64} {h : $ x :> (own (array u8 4)) $}) := (typeof! x)}

Here we have stripped the variable `x` of its rich type `(own (array u8 4))`, producing the bare type `u64` (representing that the original variable is in a 64 bit storage location) and separately the predicate `x :> (own (array u8 4))` (read `x` has type `(own (array u8 4))`) that this is a valid pointer to an array of `4` `u8`'s. (There is a variation on `typeof!` called `typeof`, which applies in the special case where `x` is already a base type, so that its type is not changed by the operation of `typeof!`. That is, if `x :> T` is a duplicable separating proposition.) The dual operation is `pun`:

    {x := (malloc u8 4)}
    -- x: (own (array u8 4))
    {(x h) := (typeof! x)}
    -- x: u64, h: $ x :> (own (array u8 4)) $
    {x := (pun x h)}
    -- x: (own (array u8 4))

    {(x h) := (typeof! x)}
    -- x: u64, h: $ x :> (own (array u8 4)) $
    {{h2: $ x :> (own (array u8 2)) $} :=
      (entail h
        -- proof of x :> (own (array u8 4)) |- x :> (own (array u8 2))
        _)}
    {x := (pun x h2)}
    -- x: (own (array u8 2))

In the second example we do a proof in separation logic that `x :> (own (array u8 4)) |- x :> (own (array u8 2))`, and use it to reconstitute `x` at a different type than its original one.

It is worth reiterating that all of the above operations are no-ops in the computational semantics. `pun` and `typeof!` are identity functions and `entail` is a proof-only notion, so the only thing that is in the emitted binary is the call to `malloc` on the first line.

### Casting, type punning and truncation

"Casting" in C might mean any of the above notions. We separate them in MMC as follows.

`cast` is used for downcasting or upcasting integers, preserving the logical value of the cell. If `x: X` then `(cast x h): Y` under the following conditions:
  * `X` and `Y` are numeric types and `h` is a proof that `x` is within the bounds of `Y`, for example `h: $ x < 2 ^ 64 $` if `Y = u64`.
  * If `X` is a signed integral type then we must also prove that `x` is nonnegative, that is, `h: $ 0 <=Z x /\ x <Z b0 (2 ^ 64) $`, where all operations are stated over integers this time (encoded in PA).
  * If `X` is `u64` and `Y` is a pointer type, then `h` should be a proof that `$ x :> Y $`.
  * If `X` is a pointer type and `Y` is `u64`, then `h` is not needed.

If the compiler can prove the side goal `h`, it can be omitted using `(cast x)` or just `x` when the context forces type `Y`.

For truncation and generally non-value-preserving type casts, we use the `as` function. If `x: X` then `{x as Y}: Y` under the following conditions:

* If `X` is a numeric type and `Y` is `uN`, then it is upcast to `nat` and then downcast using a modulo function. The resulting formal expression is `x % 2^N` if reified in a proof.
* If `X` is a numeric type and `Y` is `iN`, then it is upcast to `int` and then downcast using a modulo function. The resulting formal expression is `iword N x`, which is defined to equal `(x + 2^(N-1)) % 2^N - 2^(N-1)`.
* If `X` is `bool` and `Y` is a numeric type, it returns `0` or `1`.
* If `X` is a numeric type and `Y` is `bool`, it returns `x != 0`.

For type punning and reconstituting values of complex types that have been stripped by `typeof!`, we use `pun`, which is guaranteed to be an identity function in the computer but may have an effect on the logical value of the expression. If `x: X` then `(pun x h): Y` under the following conditions:

* If `h: $ x :> Y $` and `Y` has the same `sizeof` as `X`. (The evidence that `x :> X` is dropped.)
* It has the same effect as `(trunc x)` if `X` and `Y` are numeric types with the same `sizeof`.
* If `X = (& T)` or `(own T)` and `Y = (& U)`, or `X = (own T)` and `Y = (own U)` and `h` proves `sizeof U <= sizeof T` and `(* x) <: U` if the latter is not trivial.

### Slicing

A related operation to casting is slicing, the extraction of a subsequence of an array. If `x: (& (array T n))`, then `(slice {x + b} h): (& (array T a))` if `h` is a proof that `b + a <= n`. Computationally this corresponds to simply `x + b * sizeof T`, in the manner of C pointer arithmetic. The addition is syntactically part of the operator, but it can also be omitted when `b = 0`, in which case the slice has the same behavior as `(pun x h)`.

The `slice` operator can also be used to perform simultaneous punning: if `x: (& (array T n))`, then `(slice {x + b} h): (& U)` provided that `h` is a proof of ` b * sizeof T + sizeof U <= n * sizeof T` and `(* x) <: U` if the latter is not trivial.

The `slice` operator uses the expected type in order to infer the type of `h`, so a type ascription will usually be necessary.

### Assertions

The `(assert p)` function will assert the truth of any boolean predicate `p`, by terminating the program with an error code if the predicate fails to hold. Syntactically `p` can be any separating proposition, including quantifiers and nondecidable expressions; the compiler will attempt to compile these on a best effort basis. Generally it should be expected to work only when `p` is a boolean expression using fixed size temporaries. It cannot be used to manufacture resources, so you can't prove that `x :> (own T)` using assertions, although if `x : (own (array u8 (sizeof T)))` and `T` represents some predicate over simple data then you may be able to `assert` that `(* x) :> T` and then `pun` `x` to type `(own T)`.

    {{x : u64} := 1}
    {{y : u64} := 2}
    {h := (assert {x < y})}
    -- x: u64, y: u64, h: $ x < y $

Note that this example contains runtime overhead for the testing of the predicate `x < y`, but we can obtain a proof that it is true without the test and eliminate the overhead:

    {hx := {{x : u64} := 1}}
    {hy := {{y : u64} := 2}}
    -- x: u64, hx: $ x = 1 $, y: u64, hy: $ y = 2 $
    {{h : $ x < y $} := (entail hx hy (proof...))}
    -- x: u64, y: u64, hx: $ x = 1 $, hy: $ y = 2 $, h: $ x < y $

This demonstrates how we can trade extra proof work for runtime overhead. (The compiler may well eliminate the test in the first case as well because it has a theorem prover of its own in the form of constant propagation.)

## Control structures

Control structures are mechanisms for changing the flow of control in a program: conditional branches, function calls, and loops.

### Blocks

Not really a control structure, but necessary for organizing function bodies, `(begin s1 s2 ... sn)` is a sequential block of statements, similar to the use of `{` `}` in C. It can also be used in an expression context, where it acts as a scoped block of statements followed by a value:

    {h := {{y : u8} := 0}}
    {{x : u8} := (begin
      {h := {{y : u8} := 1}}
      -- y: u8, h: $ y = 1 $
      {y + 1})}
    -- y: u8, h: $ y = 0 $, x: u8

Note that `y` and `h` were shadowed in the block but are visible outside the block with their original values.

Alternatively, the `mut` keyword can be used at the start of a block to indicate that variables from the outer context should be assigned by the block. In functional style, this is equivalent to passing the marked variables as multiple return values of the block and then performing a shadowing binding in the outer context.

    {h := {{y : u8} := 0}}
    {{x : u8} := (begin (mut y)
      {h := {{y : u8} := 1}}
      -- y: u8, h: $ y = 1 $
      {y + 1})}
    -- x: u8, y: u8

We have lost both hypotheses in this example because the first one is obsolete and the second one was dropped at the end of the block. If we export both:

    {h := {{y : u8} := 0}}
    {{x : u8} := (begin (mut y h)
      {h := {{y : u8} := 1}}
      -- y: u8, h: $ y = 1 $
      {y + 1})}
    -- x: u8, y: u8, h: $ y = 1 $

Now we can see that `y` is in fact `1` at the end of the block, and this will be compiled to a re-assignment to the storage location of `y`.

### Conditional statements

The construct `(if p [t...] else [f...])` functions as both the `if` statement and `?` ... `:` operator of C. `[t...]` and `[f...]` are lists of statements, and the `else` keyword is optional. (The use of `[]` here is purely conventional, to remind us that this is a list of statements, not an application. `()` can be used as well.)

    {res := (if {x < 1} [
      {{x : u8} := 1}
      (f x)
    ] else [
      {{x : u8} := 2}
      (g x)
    ])}

The form `(if {h : p} [t...] else [f...])` binds `h` to a proof of `p` in the body of `t` and to `~ p` in the body of `f`. The types of the branches must be the same. (It may be necessary to finish a block with `()` to ensure nothing is returned if the `if` is operating at statement level.) As with `begin`, any let bindings in the body of the branches must be marked with `mut` in order to affect the outer value of the variable.

If statements can be chained with C-like `else if` syntax: `(if p [e1...] else if q [e2...] else [e3...])`.

Like blocks, `if` statements can have a `mut` clause, which goes after the initial condition as in `(if p (muts xs) t else f)`. The effect of this `mut` scopes over all branches of the if-statement.

### Labels and goto

The most general form of control flow is a `goto`, and Metamath C does not run from them. In fact, we will see that labels are actually very similar to mutually recursive functions, and because we pass around correctness witnesses it is easy to locally reason about them. The hardest part is termination checking, which is a global property.

`begin`s can be labeled with a name, at which point they become callable by name using `goto`. Calls to a label are always tail calls, and return any type `T` to the caller (indicating that control flow does not proceed past the call). They can either take parameters like a function call, or implicitly receive arguments using `mut`.

    (begin
      {{x : u8} := 1}

      ((begin f (mut x))
        {x := {x + 1}}
        (g))

      ((begin g (mut x))
        {x := {x + 1}}
        (f)))

This definition would not work as written, because `g` and `f` call each other infinitely. (Also the addition would overflow.) Instead we can terminate when the value overflows:

    (begin
      {{x : u8} := 1}

      ((begin f (mut x))
        (if {h : $ x + 1 < 256 $} (mut x) [
          {x := (cast {x + 1} h)}
          (f)
        ] else [
          (return)
        ]))

This will still not be accepted because we need to provide a *variant*, a value that counts down in recursive calls (or up to some bound). We use the notation `(variant foo)` to denote a downward counting variant and `(variant foo < bound)` or `(variant foo <= bound)` for a variant that counts up to `bound`. We must prove in recursive calls that the variant has indeed increased/decreased, again using the keyword `variant`:


    (begin
      {{x : u8} := 1}

      ((begin f (mut x) (variant x < 256))
        (if {h : $ x + 1 < 256 $} (mut x) [
          (ghost {x_old := x})
          {x := (cast {x + 1} h)}
          (f (variant {... : $ x_old < x $} h))
        ] else [
          (return)
        ])))

For examples such as this it is often convenient to assign `x` in the function call instead, since we need to talk about both old and new values in the variant. So rather than use `(mut x)` we can pass it in:

    ((begin f {{x : u8} := 1} (variant x < 256))
      (if {h : $ x + 1 < 256 $}
        [(f (cast {x + 1} h)
          (variant {... : $ x < x + 1 $} h))]
        [(return)]))

Keep in mind that a labeled begin will always be compiled to a label in a function, so even though it looks like a function it does not have its own stack frame, so only tail recursion is possible. Besides `(f)` which will jump to the label `f`, one can also `(break f)` which will jump to the end of the `((begin f) ...)` block. If control reaches the end of a labeled begin, `(break f)` is automatically called.

A group of labels that mutually call each other must all share the same `variant`. For advanced uses, different `variant`s can be used to perform nested loops, but these must be structured hierarchically: the compiler ensures that variants decrease in lexicographic order and reject cycles in the graph of variant uses.

### While loops

The example in the previous section is actually a while loop in disguise, and because this is a common structuring pattern we provide syntax for this. `(while p t)` evaluates `t` until `p` becomes false. As with labels, `while` requires a variant, which can count up or down. The body `t` ends with a `(continue)` (the equivalent of `(f)` in the labeled begin example) by default, but this may not suffice if a proof of variance needs to be provided (which is almost always the case). So usually an MMC while loop will end with a `(continue)` containing all the data for the next iteration of the loop.

The arguments to a while loop can be provided through the `(invariant)` command, which is otherwise similar to the argument list of a labeled `begin`. So the example at the end of the previous section can be represented as a while loop like so:

    (while {h : $ x + 1 < 256 $}
      (variant x < 256)
      (invariant {{x : u8} := 1})

      (continue (cast {x + 1} h)
        (variant {... : $ x < x + 1 $} h)))
    (return)

As with `if` statements, `h` can be used on the condition to obtain a proof that the condition is true inside the loop and false outside it (although in this case `h` is not available after the loop because `x` is scoped to the while loop itself). If we scope `x` outside the loop, we obtain:

    {{x : u8} := 1}
    (while {h : $ x + 1 < 256 $}
      (variant x < 256)
      (invariant (mut x))

      (continue (cast {x + 1} h)
        (variant {... : $ x < x + 1 $} h)))
    -- x: u8, h: $ ~ x + 1 < 256 $
    (return)

While loops can also be labeled using `((while f) p t)`, in which case you can use `(break f)` and `(continue f)` to target a loop in a deeper scope; the unlabeled `(break)` and `(continue)` break to the nearest enclosing loop.

### Unreachable

The `(unreachable h)` command takes a proof of false and cancels the current code path. This can be used to eliminate unnecessary branches. The following code produces no output:

    (if {h : $ 2 + 2 = 5 $}
      (unreachable (entail h <proof of 2 + 2 != 5>)))

This is especially useful for exhaustiveness checking in switches, see below.

### Switches

The `(switch x {a1 => b1} ... {an => bn})` command executes `bi` for the first `i` for which `x = ai`. The `ai` should be numeric constants (pattern matching on enums and the like are future work). In a pattern, one can use `{a or b}` to pattern match on multiple constants, `{x with p}` to evaluate a predicate, and `{h : x}` to capture the assertion that `x` matches the given pattern in `h` (and the assertion that `x` doesn't match the pattern in `h` in all subsequent branches). For example:

    (switch {2 + 2}
      {{h : 4} =>
        -- h: 2 + 2 = 4 here
        "all is well"}
      {_ => (unreachable (entail h (proof of $ 2+2 != 4 -> F. $)))})

    (switch x
      {{h : {x with (is_groovy x)}} => "x is groovy"}
      {{h2 : {1 or 2}} =>
        -- h: $ ~ is_groovy x $, h2: $ x = 1 \/ x = 2 $
        "x is not groovy but it is 1 or 2"}
      {_ =>
        -- h: $ ~ is_groovy x $, h2: $ ~ (x = 1 \/ x = 2) $
        "what is this???"})

### For loops

The special case of bounded `for` loops is especially helpful for verified programming because it eliminates the need to prove variance, as well as prove that the loop counter does not go out of bounds. The syntax is `(for {x : T} in {a .. b} t)`, where annotating `a` and `b` as in `{h : a}` obtains proofs that `x <= a` and `x < b`, respectively. Like a while loop, the `invariant` command can be used to indicate properties that hold through the loop. For example:

    (for {x : u8} in {0 .. 256} (f x))

This would be difficult to express in C, because a naive attempt to implement this using `for (unsigned char x = 0; x < 256; x++)` would loop forever. MMC knows how to use the overflow flag to implement this loop. A similar loop over `0 .. 257` is impossible to implement because the last iteration of the loop has `256` in a `u8` which is impossible, and the compiler will give an error.

<!--
### Map and reduce

Another special case of interest for verified programming is a special case of the `for` loop involving parallel access to one or more arrays (to read or write). It is convenient to have this built in because the invariant of the underlying for loop is unpleasant.
-->

## Structured types

Structures are declared using the syntax `(struct Foo f1 ... fn)`. This creates a new type `Foo` such that `sizeof Foo` is the sum of the sizes of the `fi`.

    (struct Foo
      {bar : u8} {_ : u8}
      {baz : u16}
      {big_field : u64})

*Structs are packed by default.* The programmer is responsible for adding padding bytes as necessary, but the compiler will prove that the struct is aligned if necessary.

Fields can be dependent (and can reference each other in any order), and can contain ghost variables and hypotheses:

    (struct Foo
      {arr : (array u8 len)}
      {(ghost len) : nat})

Fields can be referred to by `(x . field)`, and struct literals are written using the `mk` keyword, as `((mk Foo) arr len)`, or `(mk arr len)` when `Foo` can be inferred.

Structs can also have parameters:

    (struct (Foo A {n : nat})
      {arr : (array A {2 * n})})

They can also depend on global variables:

    (global {n : u64})
    (struct Foo
      {arr : (array u64 {2 * n})})

This is just the same as a parameterized class but the global parameter is implicit. If the global changes, it may be necessary to refer to old versions of the type. Parameters can be made explicit using `(! Foo n)`, and then `(! Foo n_old)` refers to the old version of the type.

Anonymous or "padding" bits can be represented using fields named `_`. In the mathematical model, a struct is encoded as a (right associated) iterated pair of all non-anonymous fields of the struct. This implies that two structs that differ in padding bits are considered to be equal.

### Tuples

The tuple type is `(list A1 ... An)`. This is the same as a struct except that the elements are referred to by `(p . 0)`, `(p . 1)`, .. `(p . n-1)`, and the constructor is called `(list a b c)`.

Tuples and structs can be destructured in an assignment using `(a b c) := ...`.

### Singleton type

The singleton type is `(sn {a : T})`, and denotes the type of values of type `T` that are equal to `a`. This may appear to be a waste of space because we know in advance what a variable of this type contains, but it can be used as a component in larger type definitions. Additionally, this type can be computationally relevant even if `a` is not, which allows us to compute with ghost data.

### Unions

The typing predicate of a union is the disjunction of all typing predicates of the elements. That is, `x :> (or A B C)` is equivalent to `x :> A \/ x :> B \/ x :> C`. The empty union is the never type or "void" type (but not `C`'s `void`!). The `void` type in MMC has no elements, and one can pass it to `(unreachable)` just like a proof of false.

MMC does not have union declarations like `C`, and you cannot use field access with unions. One might wonder how a union type can be used at all, but the key is to note that the individual types in a union can be dependent on some other piece of data in the program. Many functional programming languages contain a discriminated union type, but here we can build it as a union type:

    (enum A B) = (or (list (sn {0 : u8}) A) (list (sn {1 : u8}) B))

To use a value of a union type, one must prove that the value is one of the disjuncts, and then one can use `pun` to reconstitute the value as the resulting type.

### Arrays

We have already seen the `(array T n)` type in several examples. Unlike C, `(array T n)` is not a pointer and does not decay to one; the type represents the bits of an array directly. Because `array` is a large type, it is usually passed around behind a pointer type.

* The function `(index a i h)` is the equivalent of `C`'s `a[i]`; it has type `(own T)` if `a` has type `(own (array T i))` and type `(& T)` if `a` has type `(& (array T i))`. The hypothesis `h` is a proof that `i` is in the bounds of the array. The variant `(index a i)` supplies `(assert {i < n})` for the proof, making this a bounds-checked access.
* The function `{(slice {a + i} h) : (& (array T n))}` has already been discussed in the [slicing](#slicing) section. It is also possible to write this as `(& {(slice (* {a + i}) h) : (array T n)})`, using `slice` with a non-pointer type to construct the place and then getting its address. This is only a stylistic difference.

### Typedefs

The command `(typedef foo bar)` defines a type in terms of another type. Just like in structs, types can have parameters, as in `(typedef (foo A {n : T}) (union (sn {n : T}) (bar A A)))`.

### Raw types

The low level interface for creating new types is the function `(mmc-new-type '(T args) size_of 'T_def)`. This is not part of the MMC language, it is a tactic that runs in the MM1 language and acts as a plugin for the compiler. It takes a function `size_of` that will compute the `sizeof T` theorem for the new type `T`, and `T_def` which is a separating proposition defining the typehood predicate `x :> T`.

## Proofs

The underlying proof system is a model of separation logic instantiated on the target architecture (x86 for the present). The advantage of this is that it is possible to prove theorems and build programs at any level of abstraction. (Inline assembly syntax is TBD but can certainly be supported in the framework.) Proofs can be written directly inline in the MM1 language, or they can be proven as `theorem` commands at the top level of the enclosing MM1 file and referenced in the MMC program. The main tool that MMC adds to the MM1 proof architecture is the `entail` command: `(entail h1 h2 .. hn p)` produces a proof of a separating proposition `$ Q $` given `hi : $ Pi $` and assuming `p` is a proof of the entailment `P1 * ... * Pn |- Q`. If everything is independent of the heap, then it can be a proof of `P1 /\ ... /\ Pn -> Q` instead.

## Functions and procedures

The `proc` command declares a new top level procedure, and `func` declares a new function. These commands have the same syntax: `(proc/func (foo params : returns) body)` declares a function `foo` which takes a list of arguments `params`, and returns a list of values `returns`. Each element of `returns` can be either `T` or `{val : T}` where `T` is a type; the names of named returns can be used in the types of other returns. Both parameters and returns can be marked as ghost using `(ghost {x : T})`; hypotheses are always treated as ghost.

To call a function or procedures, we write `(foo a b c)`, and we can assign the result(s) to a value using `x := (foo a b c)` or `(x y z) := (foo a b c)`.

Inside a function body, the `(return a b c)` function is used to return a value. As an escape directive, it returns `F.` so that we can prove that any code after a `return` is dead.

Functions and procedures in global scope can be forward referenced, but only within a single call to the MMC compiler. If compilation is done in stages then functions must be declared before use, like in C. This is done by writing `(proc/func (foo params : returns))` with no `body` component.

The difference between `func` and `proc` is that a `func` is a *pure* function, in the mathematical sense. In previous sections we have indicated how language features like mutation are modelled functionally using parameters that are passed in a "local state monad", and the MMC compiler will generate a function in the logic that represents the behavior of the imperative program, without changing the generated code at all. The equality capture operation `h := {x := e}` only works when `e` is a pure expression, which includes function calls but not procedure calls. Almost everything in MMC has a pure functional equivalent; the main source of impurity is IO (and other `proc`s).

Because functions can be forward declared and forward referenced, they can be mutually recursive. If the call graph is not acyclic, then, similarly to labeled blocks, they must be annotated with a `(variant x)` or `(variant x < bound)` directive, which goes at the beginning of the function before any statements. The variables `x` and `bound` must be passed between all functions in the cycle, and `bound` must remain fixed while `x` decreases/increases on each call (depending on the orientation of the variant).

## Input and output

The underlying axiomatization includes not only the x86 architecture but also (a very small POSIX compliant subset of) the linux kernel interface, accessible from user mode programs using the `syscall` instruction. The behavior of these calls are axiomatized, and the result is a compiler intrinsic for each system call. For example:

    (intrinsic sys_mmap {pos : (sn 0)} {len : u64} {prot : Prot}
      {flags : (sn $ MAP_PRIVATE + nat (fd = bitsNeg 32 1) * MAP_ANONYMOUS $)}
      {fd : u64} {off : (sn 0)} :
      (union (sn {MAP_FAILED : u64})
        (list {ret : (own (array u8 len))}
          $ fd = bitsNeg 32 1 -> all (sn 0) ,'(* ret) $)))

In words, this function, an axiomatization of the `mmap` system call, accepts 6 arguments `pos len prot flags fd off`, where `pos` must be 0, `len` can be any `u64`, `prot` must be a `Prot` (which is a type defined by the interface, basically a 3 bit field or a `u8` less than `8`), `flags` must be the value `MAP_PRIVATE + nat (fd = bitsNeg 32 1) * MAP_ANONYMOUS`, which is to say, it must be `MAP_PRIVATE + MAP_ANONYMOUS` if `fd` is `-1` and `MAP_PRIVATE` otherwise, `fd` must be a `u64`, and `off` must be `0`. It returns a union type, either the singleton `MAP_FAILED` (which is the 64 bit constant `-1`) or an owned pointer to an array of `u8`'s of length `len`, with the property that if the value `fd` passed in is `-1` then the array is cleared.

This can be used for either memory allocation (with fd = -1) or for memory mapping a file (when fd is the file descriptor for an open file). This is clearly an underspecification, as many of the parameters are being fixed to certain values; this is done to keep the OS model simple. It is interesting future work to try to extend the model to cover more of the OS, or else cover the hardware interface for a simpler "bare metal" environment.

## Usage

As has been mentioned, MMC exists as a DSL inside the MM1 proof assistant. The compiler itself is implemented as a plugin to the `mm0-rs` executable, which is the proof assistant. For example:

    import "compiler.mm1";
    do {
      (mmc-add '(
        (proc (adder {x : u32} {y : u32} : {ret : (sn {{x + y} : u64})})
          (cast {(cast {x + y} (assert {{x + y} < {2 ^ 64}})) : u64}))
      ))

      (mmc-add '(
        (proc (main : $ 2 + 2 = 4 $)
          {(four h) := (adder 2 2)}
          -- h: $ 2 + 2 = four $
          {h2 := (assert {four = 4})}
          -- h: $ 2 + 2 = four $, h2: $ four = 4 $
          (return (entail h h2 eqtr)))
      ))

      (mmc-finish 'Adder)
      (export-string 'Adder "adder")
    };

Here we are using the incremental compilation feature to typecheck the `adder` procedure separately from `main`. We could end the `do` block between the two parts of the program if we wanted to prove a theorem manually for use in `main`. The `mmc-finish` function takes all functions that have been passed to `mmc-add` (which are already typechecked) and completes the linking and assembly process to produce a complete program. This results in the following MM1 definitions:

    def Adder: string := ...;
    theorem Adder_basicElf: $ basicElf Adder $;
    theorem Adder_terminates (k s: nat):
      $ initialConfig Adder k -> alwaysTerminates k s 0 $;
    theorem Adder_valid (k s: nat):
      $ initialConfig Adder k /\ succeeds k s 0 -> 2 + 2 = 4 $;

The definition, `Adder`, is a large string literal like `ch x7 xf ': ch x4 x5 ': ch x4 xc ': ch x4 x6 ': ...` that encodes a binary string inside the logic. The theorem `Adder_basicElf` asserts that the `Adder` string parses as an ELF file (so it is safe to load). `Adder_terminates` asserts that if the OS has set up the program at an initial state `k` where the ELF is loaded into memory as directed, then the program always terminates on any input `s` (waiting on stdin), and produces no output. (This is because our signature for `main` lacks the `input` and `output` arguments.) The final theorem `Adder_valid` asserts that if the OS sets the program up at initial state `k` and the program terminates successfully with error code 0, then `2 + 2 = 4`. This final statement comes from the return type of `main`.

Finally, we run the `export-string` function giving it the `Adder` logic string, and it will parse the string into an actual binary string and spit it out to a file, here `"adder"`. But we're not done yet! We've proved that if the program terminates successfully then `2 + 2 = 4`, but until we actually *run* the program this is a useless fact. The exact same proof above would have worked with `5` in place of `4`. But if we `chmod +x` it and run it, and observe that it didn't crash (don't forget to check the error code!), then we can celebrate: the computer has been made to prove `2 + 2 = 4` by execution.

The framework does not prove "liveness" properties (e.g. `initialConfig Adder k -> succeeds k s 0`). We have striven for model correctness, and the fact is that a program running on x86 on Linux can be interrupted (and possibly not resumed) at any time due to interrupts. Beyond this, one can always pull the power. While it is possible to state theorems about crash-resistant programs, this requires much more detailed modeling of non-volatile memory, much of which is not even visible to a userland program.

Strictly speaking, even the termination theorem is unnecessary, because an essential part of the proof is running the program and observing success, so if the program is nonterminating then we will not observe success in any case. Future work will add a "partial mode" to the MMC compiler so that it proves partial correctness theorems instead of total correctness (and then we can drop the `variant` annotations).