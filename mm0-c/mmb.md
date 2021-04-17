# The MMB file format

> *Warning:* This spec has not yet stabilized. If you are interested in writing a verifier for this spec you should stay appraised for changes to the spec.

The `.mmb` file format is a binary format for compactly expressing proofs that can be verified by checkers like `mm0-c`. The details of this format will eventually become part of the formal proof of correctness of a verifier based on `mm0-c`. This verifier reads an `.mm0` file (using the [MM0 file format](../mm0.md)) and a companion `.mmb` file, and checks that the proofs in the `.mmb` file are correct and align with the `.mm0` theorem statements.

Encoding and types
---
All numbers are expressed in little endian fixed width types. Some tables require 4 or 8 byte alignment, but the proof stream is 1 byte aligned.

* `u8`: a 1 byte unsigned integer
* `u16`: a 2 byte unsigned integer
* `u32`: a 4 byte unsigned integer
* `u64`: an 8 byte unsigned integer
* `u1`: a bit, used in bit packing descriptions
* `u7`: sorts are 7 bits, so the high bit is used to encode additional information.
* `[T; n]`: a list of exactly `n` elements of type `T`
* `p32<T>`: a 32 bit pointer to `T`, relative to the start of the file
* `p64<T>`: a 64 bit pointer to `T`, relative to the start of the file
* `str4`: a fixed length 4 byte string
* `cstr`: a UTF-8 null terminated string
* `(cmd, data)`: see below

Command pairs are denoted `(cmd, data)` and use a variable length encoding, from 1 to 5 bytes. The low six bits of the first byte are `cmd`, while the high two bits give the number of `data` bytes:

* `00xxxxxx: cmd = x, data = 0`
* `01xxxxxx yyyyyyyy: cmd = x, data = y` (1 byte `data` field)
* `10xxxxxx yyyyyyyy yyyyyyyy: cmd = x, data = y` (2 byte `data` field)
* `11xxxxxx yyyyyyyy yyyyyyyy yyyyyyyy yyyyyyyy: cmd = x, data = y` (4 byte `data` field)

## Header

The file header contains basic information about the format and pointers to the other tables in the file, and starts at the first byte of the file.

`sizeof(header) = 40; align(header) = 8; header =`
| Field       | Type                         | Description                                         |
| ----------- | ---------------------------- | --------------------------------------------------- |
| `magic`     | `str4 = "MM0B" = 0x42304D4D` | Indicates that this file uses MMB format            |
| `version`   | `u8 = 1`                     | Indicates the version of the MMB format in use;<br/>this document details version `1`. |
| `num_sorts` | `u8`                         | The number of sorts in the file.                    |
| `reserved`  | `u16`                        | Reserved, should be set to `0`.                     |
| `num_terms` | `u32`                        | The number of `term` and `def` in the file.         |
| `num_thms`  | `u32`                        | The number of `axiom` and `theorem` in the file.    |
| `p_terms`   | `p32<[term; num_terms]>`     | The pointer to the [term table](#term-table).       |
| `p_thms`    | `p64<[thm; num_thms]>`       | The pointer to the [theorem table](#theorem-table). |
| `p_proof`   | `p32<proof_stream>`          | The pointer to the [proof stream](#proof-stream).   |
| `reserved2` | `u32`                        | Reserved, should be set to `0`.                     |
| `p_index`   | `p64<index>`                 | The pointer to the [index](#debugging-index).       |
| `sorts`     | `[sort_data; num_sorts]`     | The [sort table](#sort-table).                      |

## Sort Table

The sort table comes directly at the end of the header, and is a list of `sort_data = u8` items that give the sort modifiers for each of the sorts.

| Bit  | Modifier         |
| ---- | ---------------- |
| 0    | `pure`           |
| 1    | `strict`         |
| 2    | `provable`       |
| 3    | `free`           |
| 4-7  | unused, set to 0 |

See [mm0.md](../mm0.md) for a description of the sort modifiers.

## Term Table

The term table is an array `[term; num_terms]` where `term` is as follows:

`sizeof(term) = 8; align(term) = 8; term =`
| Field      | Type             | Description                                           |
| ---------- | ---------------- | ----------------------------------------------------- |
| `num_args` | `u16`            | The number of arguments of the term constructor       |
| `ret_sort` | `u7`             | The sort of the return type.                          |
| `is_def`   | `u1`             | The high bit of `ret_sort` is `1` if this is a `def`. |
| `reserved` | `u8`             | Reserved, should be set to `0`.                       |
| `p_data`   | `p32<term_data>` | Pointer to additional information.                    |

The `p_data` field points to additional data `term_data` for a term that cannot fit in these 8 bytes. Note that this data structure depends on the `num_args` and `is_def` fields of the relevant entry in the term table.

`sizeof(term_data)` varies; `align(term_data) = 8; term_data =`
| Field              | Type                | Description     |
| ------------------ | ------------------- | --------------- |
| `args`             | `[arg; num_args]`   | The arguments   |
| `ret`              | `arg`               | The return type |
| `unify` (optional) | `p32<unify_stream>` | The [unify stream](#unify-stream), only present if `is_def = 1` |

The type `arg = u64` contains a bit array for storing the dependencies of a sort.

`sizeof(arg) = 8; align(arg) = 8; arg =`
| Field      | Type       | Description                                                  |
| ---------- | ---------- | ------------------------------------------------------------ |
| `deps`     | `[u1; 55]` | Bit `i` is 1 if this arg depends on the `i`th bound variable |
| `reserved` | `u1`       | Must be `0`. (reserved for extensions to allow >55 deps)     |
| `sort`     | `u7`       | The sort of the type                                         |
| `bound`    | `u1`       | True if this is a bound variable                             |

Note that bound variables must depend only on themselves in `deps`, i.e. the `i`th bound variable should have `deps = 1 << i`. Also, the indexing of bound variables in `deps` skips non-bound variables, but otherwise matches the ordering of the `args` array. A non-bound variable cannot depend on bound variables that are declared later in the list.

The `ret` field of the `term_data` does not use `bound` and sets it to `0`; also `ret_sort` must agree with `ret.sort`.

## Theorem Table

The theorem table is an array `[thm; num_thms]` where `thm` is as follows:

`sizeof(thm) = 8; align(thm) = 8; thm =`
| Field      | Type            | Description                                         |
| ---------- | --------------- | --------------------------------------------------- |
| `num_args` | `u16`           | The number of (expression) arguments of the theorem |
| `reserved` | `u16`           | Reserved, should be set to `0`.                     |
| `p_data`   | `p32<thm_data>` | Pointer to additional information.                  |

The `p_data` field points to additional data `thm_data` for a theorem that cannot fit in these 8 bytes. Note that this data structure depends on the `num_args` field of the relevant entry in the theorem table.

`sizeof(thm_data)` varies; `align(thm_data) = 8; thm_data =`
| Field   | Type                | Description      |
| ------- | ------------------- | ---------------- |
| `args`  | `[arg; num_args]`   | The arguments    |
| `unify` | `p32<unify_stream>` | The [unify stream](#unify-stream) |

The interpretation of `args` is the same as in the term table.

## Unify Stream

Definitions, axioms, and theorems contain a pointer to `unify_stream`, which is an unaligned list of `(cmd, data)` pairs (see [Encoding and types](#encoding-and-types)) which continues until `cmd = END = 0`. The valid commands in a unify stream (which are 6 bit opcodes) are:

| Name         | Value  | `data`    | Summary (*)                                                |
| ------------ | ------ | --------- | ---------------------------------------------------------- |
| `UTerm`      | `0x30` | `term_id` | Apply term `term_id`                                       |
| `UTermSave`  | `0x31` | `term_id` | Apply term `term_id`, and save this subterm to the heap    |
| `URef`       | `0x32` | `heap_id` | Refer to heap element `heap_id`                            |
| `UDummy`     | `0x33` | `sort_id` | Create a new dummy with sort `sort_id`, apply and save it (only in `def`) |
| `UHyp`       | `0x36` | `0`       | Start reading a new hypothesis (only in `theorem`/`axiom`) |
| `END`        | `0x00` | `0`       | Not a command, signals the end of the stream               |

(*) The summary column is not a complete description of the behavior of the command. See [Unification](#unification) for the full stack machine semantics.

The operations are written in "polish notation", where a term constructor like `UTerm t` comes before the subterms. At the beginning of the unify stream, the heap is initialized with the variables in the order of declaration at indexes `0..num_args`, but the heap grows every time a `UTermSave` or `UDummy` operation is encountered, and is assigned the next available index.

Since a term is "saved" before the contents of the term are read, cyclic terms are representable in this encoding; for example `UTermSave 0, URef 0` is the term `x = (t0 x)`. Cyclic terms are not legal in MMB files.

For definitions, the unify stream encodes the value of the definition. For theorems and axioms, the unify stream has the pattern `UHyp, <h1>, UHyp, <h2>, ..., UHyp, <hn>, <concl>` for a theorem with `n` hypotheses, where each `<hi>` is the encoding of the hypothesis expression and `<concl>` is the encoding of the conclusion expression.

The `CMD_END` terminator is redundant because it is possible to predict the end of the stream, since each `UTerm[Save]` must be followed by `num_args` subexpressions, `URef` and `UDummy` have no subexpressions, and `UHyp` has two subexpressions (the first hypothesis and the remainder of the hypotheses and conclusion). A unify stream that terminates too early or too late is malformed.

## Proof Stream

The proof stream contains the proofs of all the theorems that have been declared in the term and theorem tables. It is an unaligned stream of `(cmd, data)` pairs like the unify stream, but it has a two-level structure to enable fast scanning through the file.

The first command in the stream is a *statement*, and the `data` field is a relative pointer that gives the number of bytes from the start of this statement to the start of the following statement. For statements that need a proof stream,

The valid statements are:

| Name       | Value  | Has proof stream? | Description                                    |
| ---------- | ------ | ----------------- | ---------------------------------------------- |
| `Sort`     | `0x04` | No                | Declares a new `sort`                          |
| `Term`     | `0x05` | No                | Declares a new `term`                          |
| `Def`      | `0x05` | Yes               | Declares a new `pub def` (*)                   |
| `LocalDef` | `0x0D` | Yes               | Declares a new `def`                           |
| `Axiom`    | `0x02` | Yes               | Declares a new `axiom`                         |
| `Thm`      | `0x06` | Yes               | Declares a new `theorem`                       |
| `LocalThm` | `0x0E` | Yes               | Declares a new `local theorem`                 |
| `END`      | `0x00` |                   | Not a statement, signals the end of the stream |

(*) Note that `Term` and `Def` have the same value; this is because the actual indication of whether this is a `term` or `def` is by looking at the `is_def` field in the term table.

The verifier keeps track of how many `sort`, `term`/`def`, and `axiom`/`theorem` items have been encountered, and each occurrence of a statement from each of these classes increments the respective counter, with the new index being the index into the sort, term, or theorem tables, respectively. All references to terms with an ID larger than the running count (i.e. forward references) are considered to be invalid.

For statements that do not have a proof stream, the next command will be the next statement (and the `data` field for the statement will be the byte length of that single command). For statements that do have a proof stream, the next command will be a sequence of proof commands ending at `END`, and the `data` field will point immediately following the `END`.

The valid proof commands are:

| Name        | Value  | `data`    | Summary (*)                                                 |
| ----------- | ------ | --------- | ----------------------------------------------------------- |
| `Term`      | `0x10` | `term_id` | Apply term `term_id`                                        |
| `TermSave`  | `0x11` | `term_id` | Apply term `term_id`, and save this subterm to the heap     |
| `Ref`       | `0x12` | `heap_id` | Put heap element `heap_id` on the stack                     |
| `Dummy`     | `0x13` | `sort_id` | Create a new dummy with sort `sort_id`, apply and save it   |
| `Thm`       | `0x14` | `thm_id`  | Apply theorem `thm_id`                                      |
| `ThmSave`   | `0x15` | `thm_id`  | Apply theorem `thm_id`, and save it to the heap             |
| `Hyp`       | `0x16` | `0`       | Add the expression just constructed as a hypothesis         |
| `Conv`      | `0x17` | `0`       | Apply the conversion rule `e1 = e2 /\ proof e2 -> proof e1` |
| `Refl`      | `0x18` | `0`       | Reflexivity conversion `e = e`                              |
| `Sym`       | `0x19` | `0`       | Symmetry of conversion `e1 = e2 -> e2 = e1`                 |
| `Cong`      | `0x1A` | `0`       | Congruence `e1 = e1' /\ ... /\ en = en' -> t es = t es'`    |
| `Unfold`    | `0x1B` | `0`       | Unfolding: `e = e' -> D es = e'` if `D es` unfolds to `e`   |
| `ConvCut`   | `0x1C` | `0`       | Prove a conversion `e1 = e2`                                |
| `ConvSave`  | `0x1E` | `0`       | Save a conversion `e1 = e2` to the heap                     |
| `Save`      | `0x1F` | `0`       | Save an element on the stack to the heap without popping it |
| `Sorry`     | `0x20` | `0`       | Push a proof of anything, or a conversion (**)              |
| `END`       | `0x00` | `0`       | Not a command, signals the end of the stream                |

(*) The summary column is not a complete description of the behavior of the command. See [Proof checking](#proof-checking) for the full stack machine semantics.

(**) The `Sorry` command is not a valid proof command, but is useful for generating partial proofs. Verifiers are permitted to not recognize its existence.

The proof commands construct a proof in *reverse* polish notation (meaning that constructors follow their arguments) as follows:

* Definitions construct the value of the definition `expr e` on the stack. (This is redundant with the unify stream encoded in the term table, but by checking one against the other we can ensure no cyclic terms.)
* Axioms and theorems first construct each hypothesis and then use `Hyp` to add them to the hypothesis list, and then axioms construct `expr concl` and theorems construct `proof concl`.

There is no difference between local and public theorems/defs in terms of verification, but sorts, terms, axioms, public theorems, and public defs require reading the next statement in the MM0 file and ensuring that it matches the current statement in the MMB file. Local theorems and local defs do not require any corresponding statement in the MM0 file.

## Proof Checking

The proof stream is a sequence of commands that are designed to operate on a stack machine with the following components:

* `S`: The (main) stack, which starts empty and on which most commands operate. The valid stack elements are:
  * `expr e` or `e`: `e` is an expression
  * `proof e` or `|- e`: `e` is a proven expression
  * `e1 = e2`: A conversion proof
  * `e1 =?= e2`: A conversion obligation
* `H`: The heap, which is initialized to the list of all the variables, and can contain all kinds of stack elements except `e1 =?= e2`.
* `HS`: The list of hypotheses to the current theorem, which starts empty and grows on `Hyp` commands.
* `next_bv`: The number of active bound variables, which is initialized to the number of bound variables in the declaration and is incremented on `Dummy` calls

The backing store is not mentioned explicitly in the description but holds the memory for all constructed s-expressions. In particular, operations like `Term` that allocate a new expression are considered distinct from any previously constructed expression, so equality testing, such as is required by the `Refl` command and in unification, is pointer equality, not structural equality. For example, `Term 0, Term 0` constructs `t0, t0'` on the stack, but if these ended up in a reflexivity obligation `t0 =?= t0'` then a proof that applied `Refl` would not be valid. To actually get the same term twice it is required to use `Save` and `Ref`, as in `TermSave(0), Ref(0)` which puts `t0, t0` on the stack.

During operation, we pre-calculate certain metadata about allocated expressions:

* `bound(e)` is true if `e` is a bound variable (a variable with `args[i].bound = true`), or a dummy variable. All composite expressions have `bound(t ...) = false`.
* `sort(e)` is the sort of the expression
* `V(e)` is the set of variables in `e`
  * `V(xi)` is `{xi}` if `xi` is a variable with `bound(x)`
  * `V(xi)` is `args[i].deps` if `xi` is a variable
  * `V(t e1 ... en)` is `V(e1) ∪ ... ∪ V(en)`
* `FV(e)` is the set of free variables in `e`
  * `FV(xi)` is the same as `V(xi)` on variables
  * `FV(t e1 ... en)` is `S1 ∪ ... ∪ Sn ∪ T` where
    * if `term[t].args[i].bound`, `Si = FV(ei)`
    * otherwise `Si` is `FV(ei)` minus the union of `FV(e[bv[j]])` over all `j` such that `term[t].args[i].deps[j]`, and `bv[j]` is the `j`'th bound variable
    * `T` is the union of `FV(e[bv[j]])` over all `j` such that `term[t].ret.deps[j]`

Because `V` is used only in theorem proofs and `BV` only in definitions, `mm0-c` will cache one or the other depending on which kind of statement is being proven.

The proof opcodes have the following operation on the state:

* ```
  Term t: H; S, e1, ..., en --> H; S, (t e1 .. en)
  ```
  `Term t` does the following:
  * Look up `term[t]`, which must be a valid `term` or `def`.
  * Let `n = term[t].num_args`
  * Pop `e1`, ..., `en` in reverse order (so `e1` is deepest on the stack before the operation)
  * For each argument `ei`, check that `sort(ei) = term[t].args[i].sort`, and if `term[t].args[i].bound` then `bound(ei)`.
  * Allocate `(t e1 ... en)` with `sort(t e1 ... en) = term[t].ret_sort`
  * Push `(t e1 ... en)` on the stack

* ```
  TermSave t = Term t, Save
  TermSave t: H; S, e1, ..., en --> H, (t e1 .. en); S, (t e1 .. en)
  ```
  `TermSave t` has exactly the same effect as `Term t, Save`. Specifically, it constructs the expression `(t e1 .. en)`, and puts it on both the stack and on the heap.

* ```
  Ref i: H; S, e1 =?= e2 --> H; S    (if H[i] = (e1 = e2))
  Ref i: H; S --> H; S, H[i]         (otherwise)
  ```
  `Ref i` does the following:
  * Look up `H[i]`, which should be in range of the heap.
  * If `H[i] = e` or `|- e`, push it to the stack.
  * If `H[i] = (e1 = e2)`, pop `e1 =?= e2` and ensure that the expressions match.

* ```
  Dummy s: H; S --> H, x; S, x
  ```
  `Dummy s` does the following:
  * Look up `sort[s]`, which must be a valid `sort` such that `!sort[s].strict`.
  * Let `x = var(next_bv)` be a new bound variable, and increment `next_bv`
  * Allocate `x` with `sort(x) = s`
  * Push `x` on the stack and the heap


* ```
  Thm T: H; S, e1, ..., en, e --> H; S', |- e
  where Unify(T): S; e1, ..., en; e --> S'; H'; .
  ```
  `Thm T` is only valid in proofs of `axiom` and `theorem`. `Thm T` does the following:
  * Look up `thm[T]`, which must be a valid `axiom` or `theorem`.
  * Let `n = thm[T].num_args`
  * Pop expression `e`
  * Pop `e1`, ..., `en` in reverse order (so `e1` is deepest on the stack before the operation)
  * Initialize `uheap := []`
  * For each argument `ei`:
    * check that `sort(ei) = thm[T].args[i].sort`
    * If `thm[T].args[i].bound`:
      * check that `bound(ei)`.
      * check that `FV(e') ∩ FV(ei) = {}` for all `e'` in `uheap`
      * push `FV(ei)` to `deps`
    * Otherwise:
      * For each `j` such that `thm[T].args[i].deps[j]`:
        * check that `deps[j] ∩ FV(ei) = {}`
    * Push `ei` to `uheap`
  * Run [unification](#unification) for `thm[T].unify`, with `uheap` as the original unification heap and with `[e]` on the unification stack. The unifier also has access to the main stack and may pop theorem hypotheses as necessary.
  * Push `|- e` to the stack.

* ```
  ThmSave T = Thm T, Save
  ```
  `ThmSave T` has exactly the same effect as `Thm T, Save`. Specifically, it applies theorem `T` and puts the conclusion `|- e` on both the stack and on the heap.

* ```
  Hyp: HS; H; S, e --> HS, e; H, |- e; S
  ```
  `Hyp` is only valid in proofs of `axiom` and `theorem`. `Hyp` does the following:
  * Pop `e`.
  * Ensure that `sorts[sort(e)].provable`.
  * Push `e` to the hypothesis list.
  * Push `|- e` to the heap.

* ```
  Conv: S, e1, |- e2 --> S, |- e1, e1 =?= e2
  ```
  * Pop `|- e2`, pop `e1`, push `|- e1`, push `e1 =?= e2`.

* ```
  Refl: S, e =?= e --> S
  ```
  * Pop `e1 =?= e2`, ensure that `e1` and `e2` are equal. (Reminder: this is O(1) pointer equality)

* ```
  Symm: S, e1 =?= e2 --> S, e2 =?= e1
  ```
  * Pop `e1 =?= e2`, push `e2 =?= e1`.

* ```
  Cong: S, (t e1 ... en) =?= (t e1' ... en') --> S, en =?= en', ..., e1 =?= e1'
  ```
  * Pop `(t e1 ... en) =?= (t e1' ... en')`.
  * Ensure that both expressions are term constructors for the same `t`.
  * Push `en =?= en`, ..., `e1 =?= e1`. (Note that the obligations are pushed in reverse order.)

* ```
  Unfold: S, (t e1 ... en) =?= e', e --> S, e =?= e'
  where Unify(t): e1, ..., en; e --> H'; .
  ```
  * Pop `e`.
  * Pop `(t e1 ... en) =?= e'`.
  * Ensure that `t` is a term constructor such that `term[t].is_def`.
  * Run [unification](#unification) for `term[t].unify`, with `[e1, ..., en]` as the original unification heap and with `[e]` on the unification stack.
  * Push `e =?= e'`.

* ```
  ConvCut: S, e1 =?= e2 --> S, e1 = e2, e1 =?= e2
  ```
  * Pop `e1 =?= e2`, push `e1 = e2`, push `e1 =?= e2`.

* ```
  ConvSave: H; S, e1 = e2 --> H, e1 = e2; S
  ```
  * Pop `e1 = e2`, push `e1 = e2` to the heap.

* ```
  Save: H; S, s --> H, s; S, s
  ```
  * Pop any stack element `s`.
  * Ensure `s` is not a convertibility obligation `e1 =?= e2`
  * Push `s` to the heap and the stack.

* ```
  Sorry: S, e -> S, |- e
  Sorry: S, e1 =?= e2 -> S
  ```
  Pop a stack element `s`:
  * If `s = e`, push `|- e` to the stack.
  * If `s = (e1 =?= e2)`, do nothing.
  * Record that `Sorry` was used. Verifiers that signal successful verification using exit codes are required to report failure for proofs using `Sorry`, although they can use implementation-defined printing to distinguish proofs-modulo-`Sorry` from malformed proofs.

## Unification

Unification is called during proof checking, in the `Unfold` and `Thm` rules, as well as when verifying `Def` statements. The unifier uses the following state:

* `MS`: The main stack (which was called `S` in the previous section) is consulted to get hypotheses, but is not otherwise used.
* `S`: The unify stack, which contains expressions that have yet to be unified. Unification starts with a single expression on the unify stack, and it should be empty when unification is done.
* `H`: The unify heap, which contains substitutions, and is extended by `UDummy` and `UTermSave` steps. It is initialized to the list of substitutions to the variables in the `theorem` or `def`.

The action of the unify commands is as follows:

* ```
  URef i: H; S, H[i] --> H; S
  ```
  * Pop `e`, ensure that `e = H[i]`. (Reminder: this is O(1) pointer equality)

* ```
  UTerm t: S, (t e1 ... en) --> S, en, ..., e1
  ```
  * Pop `e`.
  * Ensure that `e = (t e1 ... en)` is a term constructor with head `t`.
  * Push `en`, ..., `e1`. (Note that the expressions are pushed in reverse order.)

* ```
  UTermSave t = USave, UTerm t
  UTermSave t: H; S, (t e1 ... en) --> H, (t e1 ... en); S, en, ..., e1
  ```
  `UTermSave t` has exactly the same effect as `USave, UTerm t`. Specifically, it pops the expression `(t e1 .. en)`, puts it on the heap, and puts the subexpressions on the stack.

* ```
  UDummy s: H; S, x --> H, x; S
  ```
  `UDummy` is only allowed in `def` declarations.
  * Pop `x`.
  * Ensure that `x` is a variable and `sort(x) = s`.
  * Ensure that `V(e) ∩ V(x) = {}` for all `e` in `H`.
  * Push `x` to the unify heap.

* ```
  UHyp: MS, |- e; S --> MS; S, e
  ```
  `UHyp` is only allowed in `theorem` declarations.
  * Pop `|- e` from the main stack.
  * Push `e` to the unify stack.

* ```
  USave: H; S, e --> H, e; S, e
  ```
  (`USave` is not an available opcode but is used to describe the operation of `UTermSave`.)
  * Pop `e`, push `e` to the heap and the stack.

## Debugging Index

The `p_index` field in the header points to an `index` which contains a list of index entries.

`sizeof(index)` varies; `align(index) = 8; index =`
| Field         | Type                         | Description                 |
| ------------- | ---------------------------- | --------------------------- |
| `num_entries` | `u64`                        | The number of index entries |
| `entries`     | `[index_entry; num_entries]` | The index entries           |

Each index entry has a `type` which determines the meaning of the fields.

`sizeof(index_entry) = 16; align(index_entry) = 8; index_entry =`
| Field  | Type   | Description       |
| ------ | ------ | ----------------- |
| `type` | `str4` | The type of table |
| `data` | `u32`  | Varies            |
| `ptr`  | `u64`  | Varies            |

The collection of valid `type` settings is open-ended, but extensions should coordinate in order to avoid overlaps. The following table types are defined:

| `type`                | `data` | `ptr`            | Description                                 |
| --------------------- | ------ | ---------------- | ------------------------------------------- |
| `"Name" = 0x656D614E` | `0`    | `p64<names>`     | String names for sorts, terms, and theorems |
| `"VarN" = 0x4E726156` | `0`    | `p64<var_names>` | String names for variables                  |
| `"HypN" = 0x4E726156` | `0`    | `p64<hyp_names>` | String names for hypotheses                 |

## The `Name` table: names for statements

`align(names) = 8; names =`
| Field   | Type                      | Description           |
| ------- | ------------------------- | --------------------- |
| `sorts` | `[name_entry; num_sorts]` | The names of sorts    |
| `terms` | `[name_entry; num_terms]` | The names of terms    |
| `thms`  | `[name_entry; num_thms]`  | The names of theorems |

Each name entry consists of a pointer to the statement in the proof stream where it was introduced, and a UTF-8 C string with the name. (MM0 itself doesn't support non-ASCII names, but the names listed here are allowed to include arbitrary unicode.)

`sizeof(name_entry) = 16; align(name_entry) = 8; name_entry =`
| Field   | Type                | Description                                     |
| ------- | ------------------- | ----------------------------------------------- |
| `proof` | `p64<proof_stream>` | A pointer to this statement in the proof stream |
| `name`  | `p64<cstr>`         | A pointer to the name string                    |

## The `VarN` table: names for variables

`align(var_names) = 8; var_names =`
| Field       | Type                         | Description                                  |
| ----------- | ---------------------------- | -------------------------------------------- |
| `term_vars` | `[p64<str_list>; num_terms]` | The list of variables in a `term`/`def`      |
| `thm_vars`  | `[p64<str_list>; num_thms]`  | The list of variables in a `axiom`/`theorem` |

The `str_list` type is just a list of pointers to UTF-8 null-terminated strings:

`sizeof(str_list)` varies; `align(str_list) = 8; str_list =`
| Field      | Type                    | Description                       |
| ---------- | ----------------------- | --------------------------------- |
| `num_strs` | `u64`                   | The number of strings in the list |
| `strs`     | `[p64<cstr>; num_strs]` | A list of string pointers         |

The list `term_vars[t]` is the list of variable names in `term[t]` in the order of declaration, but the list continues past `num_args` to include the dummies, named by order of appearance of `Dummy` steps in the proof stream, which happens to coincide with the order of `UDummy` steps in the unify stream version. Similarly, the `thm_vars[T]` list gives the variable names in `thm[T]`, including the dummy variables.

## The `HypN` table: names for hypotheses

`align(hyp_names) = 8; hyp_names =`
| Field       | Type                         | Description                                   |
| ----------- | ---------------------------- | --------------------------------------------- |
| `thm_hyps`  | `[p64<str_list>; num_thms]`  | The list of hypotheses in a `axiom`/`theorem` |

The `hyp_names` table is similar to `var_names`, and reuses the `str_list` type. The list gives the names of hypotheses in the order of `Hyp` commands in the statement.
