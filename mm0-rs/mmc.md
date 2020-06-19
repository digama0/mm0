# Metamath C: A programming language for verified programs

The requirements of verified programs are somewhat unique and not well addressed by either conventional programming languages such as C, Python, Rust, Haskell etc.,  or proof assistants like Isabelle, Coq, Lean, etc. On the one hand, for a low level language we need ways to talk about imperative procedures, pointer manipulation, while loops and the like, where every construct has a well defined lowering to machine instructions, and on the other hand we need the expressiveness to reason about the program inside an ambient logic, where infinite sets and undecidable predicates are common. These can sometimes be approximated by assertions, which have the advantage of being executable, but this is irrelevant and limiting when the goal is to write a functionally correct program.

Metamath C (abbreviated MMC) is a language that uses total functions (provably terminating mathematical functions as one would find in HOL or a dependent type theory) for its semantics, combined with inline separation logic through erased "hypothesis variables" for reasoning about heap structures and non-functional components, on top of a C-like structure that is used to provide well defined and predictable lowering to machine code.

MMC is currently written in arguments to the MMC compiler, which has an interface through MM1. As a result it inherits the same Scheme-like syntax used in MM1 tactics. (This may change in the future.) MMC has an extensible type system, and it produces MM0 proofs in the back-end. Because types are implemented as "type guards", they have an independent existence as well, and there are primitives for "casting" a variable to a type `T` given a proof that it has type `T`.

## Types

A *type* is a separating proposition over machine states. That is, it is a true-or-false statement that applies to portions of the machine state (registers and memory). This is a very low level view, but it has the advantage that because it is so general, users can define types of arbitrary complexity, containing invariants and ownership semantics. Types also contain a size and an alignment, although for the x86 instantiation of MMC all types have alignment 1. Here are some basic types:

    bool | u8 | u16 | u32 | u64 | i8 | i16 | i32 | i64 | (own T) | (array T n)

The first few represent signed and unsigned integers of various widths. The `(own T)` type is an owned pointer to a type. The `(array T n)` type is a contiguous sequence of `n` elements of type `T`. (The type is not stored anywhere in memory, it is a parameter of the type.) Types can depend on values, which is often known as dependent typing, however unlike most dependent type theories very little "computation" is done inside types, and instead a `(pun)` must be used to re-type a term given a proof that it has a type. (This is not like a C cast that can be used to reinterpret a type - the value must satisfy all invariants of the target type to be eligible for `pun`.)

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
* The promotion rules for `{x // y}: nat/int` are also the same as `{x + y}`. Division by zero is defined and returns 0, but one can also use `{x // (y h)}` where `h: $ y != 0 $` to skip the check.
* If `x,y: nat` then `{x ^ y}: nat`. Prefer `{x * {2 ^ n}}` and `{x // {2 ^ n}}` to left and right shift if the intent is to do numeric operations. The actual bitshift operators truncate, as mentioned below.

Bitwise operations and logical shifts on fixed width unsigned integers do nothing to the types.

* If `x,y: uN` then `{x band y}, {x bor y}, {x bxor y}, (~ x): uN`
* If `x,y: nat` then `{x band y}, {x bor y}, {x bxor y}: nat`
* If `x,y: int` then `{x band y}, {x bor y}, {x bxor y}, (~ x): int`
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
    {h2 := {{x : u8} := 3}} -- x: u8, h1: $ x = 2 $, h2: $ x = 3 $   (wrong!)

Here the name conflict has caused us to derive an apparent contradiction. To resolve this, `h1` is removed from the context at the point of the re-assignment. (In other words this is a sub-structural type system.)

    {h1 := {{x : u8} := 2}} -- x: u8, h1: $ x = 2 $
    {h2 := {{x : u8} := 3}} -- x: u8, h2: $ x = 3 $

This also means that an assignment like `x := x + 2` cannot be saved as an equation, because the RHS is already out of date after execution of the assignment. To resolve this, we use ghost variables.

### Ghost variables

An assignment

    (ghost {x := 2})
    -- here (ghost) x: nat

is like a regular assignment except that the introduced variable does not exist at run time. The compiler tracks usage of ghost variables to ensure that they do not enter the data flow, but they can be used to perform computations that are needed for the proof but not for the program. They can be used in types (like the `n` in `array T n`) as well as in loop variants and invariants. They can also have infinite types like `nat`, unlike regular variables. We can use them to store old values of variables:


    {h := {{x : u8} := 1}}
    -- x: u8, h: $ x = 1 $
    {h2 := (ghost {old_x := x})}
    -- x: u8, h: $ x = 1 $, old_x: u8, h2: $ old_x = x $
    {h3 := (entail h2 h eqtr)}
    -- x: u8, h: $ x = 1 $, old_x: u8, h2: $ old_x = x $, h3: $ old_x = 1 $
    {h4 := {{x : u8} := {(reflect x (eqcom h2)) + 2}}}
    -- x: u8, h3: $ old_x = 1 $, h4: $ x = old_x + 2 $

We will discuss the `entail` function later, and the `eqtr` and `eqcom` functions are proofs in the ambient logic of PA. The `reflect` function allows us to have an expression whose computational realization is `x` and whose proof realization is `old_x`, so that `h4` is not discarded before it can be used. A simpler version of the above would be

    {h := {{x : u8} := 1}}
    -- x: u8, h: $ x = 1 $
    {h2 := {{x : u8} := {(reflect x h) + 2}}}
    -- x: u8, h2: $ x = 1 + 2 $

where we have skipped the definition of `old_x` by threading the known previous value of `x`.

### Tuples

Some functions return a list of values, which are destructured at the caller:

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

It is worth reiterating that all of the above operations are no-ops in the computational semantics. `pun` and `typeof!` are identify functions and `entail` is a proof-only notion, so the only thing that is in the emitted binary is the call to `malloc` on the first line.

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
* If `X = (& T)` or `(own T)` and `Y = (& U)` and `h` proves `sizeof U <= sizeof T` and `(* x) <: U` if the latter is not trivial.

<!--
## MMC syntax

    program ::= decl*

As MMC is written as a DSL in Lisp, we don't have to worry about lexing here. The BNF grammars given in this file use quoted atoms like `'typedef` to indicate a keyword, and unquoted atoms like `ident` to indicate nonterminals.
## Declarations

    decl ::= typedef-decl | const-decl | global-decl | intrinsic-decl | func-decl | proc-decl

These are top level declaration items, such as one would find at the top level of a C file. The MMC compiler can either be called with a full program, or it can typecheck one function at a time. The latter allows for interspersing MM1 theorems with MMC function definitions. These functions are not compiled separately (in C terminology, they are all in one "translation unit") but typechecking can proceed to completion in such blocks, and the semi-compiled functions are stored internally until the program is complete, at which point they can be compiled down to a block of machine code and a proof of correctness.

### Typedef

    typedef-decl ::= ('typedef ident type) | ('typedef (ident ident*) type)

This defines a new type or type family to be equal to an expression. A type is
-->