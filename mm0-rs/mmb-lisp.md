# The `Lisp` table: serialized global lisp definitions

This document specifies the `Lisp` debugging-index table of the [MMB file format](../mm0-c/mmb.md). It is an extension used by `mm0-rs`, not part of what a verifier such as `mm0-c` checks: like the other index tables (`Name`, `VarN`, `Nota`) it lives off the file's `p_index` and a verifier skips it. Unlike those, it is not merely advisory to `mm0-rs`; it is what makes *separate compilation* possible. Compiling an `.mm1` file currently requires re-elaborating every file it depends on, because the global lisp environment those files build up (the `(def ...)`s, tables, and tactics they leave behind) lives only in memory. The `Lisp` table serializes that environment into the `.mmb` so a later file can load it directly.

The table is a single stream, read once to rebuild the environment. A recursive-descent reader walks it: `read_value` reads one value and calls itself for that value's parts, so the encoding is *prefix* — a constructor precedes its children. Sharing is recovered by a heap with `Save`/`Ref`, as in the [proof stream](../mm0-c/mmb.md#proof-stream)'s DAG encoding, so a value is written once however often it is referenced; and because lisp values can hold mutable references, and so form *cycles*, `NewRef` installs a heap cell before reading its contents, letting a child point back at it. The top-level reader loops to `END`, reconstructing the *statement trace* — the source order of the file's sorts, terms, theorems and lisp globals — and supplying for each declaration the metadata the proof stream does not carry: its doc comment, its source span, and whether a `def` was `abstract`.

[`LispData`]: https://github.com/digama0/mm0/blob/master/mm0-rs/src/elab/environment.rs

## Versioning

The table versions independently of the rest of the file. Its [`index_entry`](../mm0-c/mmb.md#debugging-index) uses the `data` field as a format version. This document describes version `0`. A reader must check the version before trusting anything below and ignore a table whose version it does not recognize.

| `type`                | `data`        | `ptr`             | Description
| --------------------- | ------------- | ----------------- | -----------
| `"Lisp" = 0x7073694C` | `version = 0` | `p64<val_stream>` | Serialized global lisp definitions

## Additional encoders

Beyond the `(cmd, data)` pair and the fixed width types of [mmb.md](../mm0-c/mmb.md#encoding-and-types), the table uses two variable length integers, `uleb` and `sleb`. Both are standard LEB128: the value is cut into 7 bit groups from the least significant end, one group per byte in little-endian order, and each byte's high bit is a *continuation flag*, set on every byte but the last. Neither is length-prefixed and neither is bounded by the format — the first byte with its high bit clear ends the integer, and nothing before it says how many bytes to expect.

The bit patterns below keep the [same ordering as `(cmd, data)`](../mm0-c/mmb.md#encoding-and-types): most significant bit first within a byte, so the leftmost bit of each pattern is bit 7, the continuation flag; least significant byte first across bytes, so the leftmost byte holds the low 7 bits of the value.

### `uleb`

An unsigned LEB128. Writing `x`, `y`, `z` for successive bytes' low 7 bits:

* `0xxxxxxx: n = x`
* `1xxxxxxx 0yyyyyyy: n = x | y << 7`
* `1xxxxxxx 1yyyyyyy 0zzzzzzz: n = x | y << 7 | z << 14`
* and so on: byte `i` (from `0`) contributes `(b[i] & 0x7f) << 7 * i`.

There is no sign extension — `n` is exactly the sum of the payloads — so a value of `k` significant bits occupies `ceil(k / 7)` bytes, and `n = 0` is the single byte `0x00`. A writer always emits this minimal form, so the last byte is never `0x00` unless the whole integer is one byte. The encoding nonetheless admits redundant high groups (`0x80` bytes contributing zeros), and a reader that accepts them recovers the same value.

### `sleb`

A signed LEB128, two's complement. The bytes are read exactly as for `uleb`, but the accumulated payload is a two's-complement bit string *sign-extended from bit 6* (`0x40`) of the final byte — marked `s` below, so with `k` bytes the payload is `7k` bits wide and bit `7k - 1` is `s`:

* `0sxxxxxx: n = x - s * 2^6`, so `-2^6 <= n < 2^6`
* `1xxxxxxx 0syyyyyy: n = (x | y << 7) - s * 2^13`, so `-2^13 <= n < 2^13`
* `1xxxxxxx 1yyyyyyy 0szzzzzz: n = (x | y << 7 | z << 14) - s * 2^20`, so `-2^20 <= n < 2^20`
* and so on: with `k` bytes the low `7k - 1` bits are the magnitude and `s` contributes `-s * 2^(7k - 1)`.

As with `uleb` this minimal form is what a writer emits, and longer sign-extended encodings of the same value decode identically.

## The value stream

`val_stream` is an unaligned stream of `(cmd, data)` pairs, in the same [command encoding](../mm0-c/mmb.md#encoding-and-types) as the proof stream. It is read by three mutually recursive functions over the byte cursor: `read_stmts` at the top level, `read_value` for one value, and [`read_ir`](#the-ir-sub-stream) for one lambda-code instruction. The encoding is recursive-descent and *prefix* — a command precedes its children, each read by a recursive call — and a byte's meaning is fixed by which function is reading it, so the three opcode spaces are independent. Sharing is by a heap `H`, initially empty: some reads *save* their result, appending it at the next index (from `0`), and a later `Ref i` returns `H[i]`.

### `read_stmts`

The top level reconstructs the *statement trace*: the order in which an `.mm1` declared its sorts, terms, theorems and global lisp definitions. The proof stream already carries the declarations themselves, but not their source metadata — the doc comment, the source span, and whether a `def` was `abstract` — nor where the `do` blocks that produced the lisp globals sat among them. This table supplies both, one entry per statement, in trace order, until `END` (`0x00`).

A declaration entry says nothing about *which* declaration it describes. It does not need to: the exporter writes the proof stream by walking this same trace, so the two agree on the sequence of declarations, and a reader that walks them together knows each entry's kind and id already. An entry therefore just consumes the next declaration. A table whose declaration count differs from the proof stream's is malformed.

A global has no introducing opcode — it is a fixed record whose first field is the name, a `read_value` yielding an atom, so its first byte is a value opcode, never `0x00`; a `0x00` there is unambiguously `END`. The other commands are distinguished from a name by their opcodes, all of which lie above the value opcodes (`0x1B` is the highest a `value` can begin with):

| Name         | Value  | `data`  | Reads                                | Effect
| ------------ | ------ | ------- | ------------------------------------ | ------
| ~~`END`~~    | `0x00` | `0`     |                                      | not a statement; ends the table
| *(a global)* |        |         | the record below                     | a global lisp definition
| `SetWeak`    | `0x1C` | `i`     | `value`                              | not a statement; fills the `ref!` cell `H[i]` with a weak link
| `Decl`       | `0x1D` | `flags` | `full, span, doc: value`    | the next declaration; `flags` bit `0` marks an `abstract` def
| `Decls`      | `0x1E` | `n`     |                                      | the next `n` declarations, with no span and no doc
| `Spans`      | `0x1F` | `n`     | `full, span: value`, `[uleb; 4n]`    | a run of `n+1` declarations with sequential spans and no doc

`SetWeak`s are emitted after every statement, once every target has been written, to fill the weak-reference cells that [`NewRef` set up](#references-and-cycles).

A global's record is:

| Field      | Type          | Note
| ---------- | ------------- | ----
| `name`     | `value`       | an atom; also what distinguishes a global from `END` and the commands above
| `lo`, `hi` | `u32`, `u32`  | the name's byte range within its file
| `value`    | `value`       | the value bound to the name
| `span`     | `value`       | the source `FileSpan`, or `#undef`
| `merge`    | `value`       | the merge strategy, or `#undef`
| `doc`      | `value`       | the doc string, or `#undef`

A `Decl`'s `span` is the declaration's *name* as a `FileSpan`, and `full` bounds the whole declaration — every modifier through the semicolon — in that same file, which a reader must check. `full` comes first because it is the one that fixes the file; `span` then names it again by `Ref`. Both are needed: the name span is what a jump-to-definition lands on, and the full span is the range an editor highlights and the doc generator renders from source. A `Spans` run opens with this same pair, so the two are read by the same code.

<a id="spans-runs"></a>Most declarations have a span and no doc comment, so `Spans` encodes them by their structure instead of one record each. The four positions of a declaration nest,

    full.lo <= span.lo < span.hi <= full.hi

and consecutive declarations in one file do not overlap, so a run of them is a single ascending sequence of positions. `Spans` writes the first declaration in full — the same `full, span` pair a lone `Decl` carries — and then a `uleb` per position thereafter, each the gap from the position before it, in the order `full.lo`, `span.lo`, `span.hi`, `full.hi`. The `data` field is the number of further declarations `n`, so the run is `4n` deltas long. It cannot instead be closed by an `END`: a delta is a raw `uleb`, and any byte whose low six bits are zero — `0x40` is a delta of 64 — would read as an `END` command. Every delta is a local gap: the two inside a declaration are a keyword and a name, and the two between them are the tail of one declaration and the whitespace before the next.

A run is confined to one file and to ascending positions, since it carries neither. A `.mmb` holds the declarations of the file's imports as well as its own, so a writer starts a new run wherever the source file changes, and wherever a position would go backwards.

Neither `Decls` nor `Spans` can carry a doc comment or the `abstract` flag, so a documented or abstract declaration is written as its own `Decl` and interrupts the run. Both are rare next to the bulk of a library, which is what makes the runs worth having.

### `read_value`

`read_value` reads one value (or `END`): a command, and for a constructor a recursive call per child. Some reads *save*: `Atom`, `String`, and `Span` always do — a symbol, string, or span recurs constantly, so each is written once and reached again by `Ref` — and `Save` saves the one value after it, `ListSave`/`DottedListSave` fusing the save of a freshly read list. There is no string or number pool; the heap is one. Any value may also be saved by prefixing `Save` to it, and that is the only way the rules with no save of their own reach the heap. Small values like `#undef`, `#t` and `#f`, `BuiltinProc` and small numbers are not saved even if shared, since repeating them costs less than referencing them. `List`, `DottedList`, and `Map` read their children until `END` (`0x00`) — a value never begins with `0x00`, so a parent peeks for it, just as `read_stmts` does — rather than counting them. And `Code` reads a lambda's *core* — its arity spec and its body ([`read_code`](#the-ir-sub-stream)) — and saves it, so the core a literal shares with the closures made from it is written once and reached by `Ref`.

The recursion here describes the *grammar*, not the implementation: values may nest arbitrarily deep, so a reader (and a writer) must take care to avoid stack overflow in the below recursive implementations of `read_value` and `read_code`.

Each command's arguments follow it in the order shown under **Reads**, each written as its [type](#argument-types); **Result** is the value produced. `data` is the scalar in the command's varint.

| Name             | Value  | `data` | S | Reads                          | Result
| ---------------- | ------ | ------ |:-:| ------------------------------ | ------
| ~~`END`~~        | `0x00` | `0`    |   |                                | not a value; ends a sequence
| `Undef`          | `0x01` | `0`    |   |                                | `#undef`
| `False`          | `0x02` | `0`    |   |                                | `#f`
| `True`           | `0x03` | `0`    |   |                                | `#t`
| `Atom`           | `0x04` | `0`    | → | `cstr`                         | an atom interned from it
| `AtomZ`          | `0x05` | `len`  | → | `[u8; len]`                    | an atom of them
| `String`         | `0x06` | `0`    | → | `cstr`                         | a string
| `StringZ`        | `0x07` | `len`  | → | `[u8; len]`                    | a string of them
| `Number`         | `0x08` | `0`    |   | `sleb`                         | the bignum
| `Syntax`         | `0x09` | `code` |   |                                | the syntax keyword with this code
| `Builtin`        | `0x0A` | `code` |   |                                | the builtin procedure with this code
| `List`           | `0x0B` | `0`    |   | `[value] END`                  | their proper list
| `ListSave`       | `0x0C` | `0`    | → | `[value] END`                  | their proper list
| `DottedList`     | `0x0D` | `0`    |   | `[value] END`                  | the dotted list (last is the tail)
| `DottedListSave` | `0x0E` | `0`    | → | `[value] END`                  | the dotted list (last is the tail)
| `Map`            | `0x0F` | `0`    |   | `[value] END`                  | the atom map (key/value pairs)
| `Span`           | `0x10` | `0`    | → | `lo, hi: u32`, `file: value`   | the span
| `Annot`          | `0x11` | `0`    |   | `span, value: value`           | the value annotated with the span
| `Save`           | `0x12` | `0`    | → | `value`                        | it
| `Ref`            | `0x13` | `i`    |   |                                | the value `H[i]`
| `NewRef`         | `0x14` | `0`    | ← | `value`                        | a `ref!` cell holding it
| `Lambda`         | `0x16` | flags  |   | [see `Lambda`](#lambda-encoding)  | the closure
| `CustomProc`     | `0x17` | `kind` |   | [see `CustomProc`](#customproc-encoding) | a procedure
| `Code`           | `0x18` | `0`    | → | [see `Ir`](#the-ir-sub-stream) | the `(spec, body)` core
| `MVar`           | `0x19` | `idx`  |   | `tgt:` [`infer_target`](#infer_target) | a metavariable
| `Goal`           | `0x1A` | `0`    |   | `value`                        | a goal
| `DeadWeak`       | `0x1B` | `0`    |   |                                | a weak reference with no target
| ~~`SetWeak`~~    | `0x1C` | `i`    |   | `value`                        | not a value; sets weak ref `H[i]` to `value`
| ~~`Decl`~~       | `0x1D` | flags  |   | `full, span, doc: value`       | not a value; the next declaration; `flags` bit `0` marks an `abstract` def
| ~~`Decls`~~      | `0x1E` | `n`    |   |                                | not a value; the next `n` declarations, with no span and no doc
| ~~`Spans`~~      | `0x1F` | `n`    |   | `full, span: value`, `[uleb; 4n]` | not a value; a run of `n+1` declarations with sequential spans and no doc

The **Save** (**S**) column specifies when a saving command takes its heap index, relative to its arguments: → afterwards, ← beforehand, empty for not at all. Every saving command is → except `NewRef`, which pre-initializes the cell so that it can encode [a cycle](#references-and-cycles). The → on `Atom`, `AtomZ`, `String` and `StringZ` is nominal, since they have no contents to be after.

`MVar` and `Goal` are proof-elaboration state — a metavariable's `idx` is its place in a local context that is gone once elaboration ends, so a reloaded one is inert until a proof rebuilds that context. They are encoded anyway, because a tactic can stash one in a `ref!` and leave it in a global.

A `Span`'s `file` is a string `value` holding the source file's path, stored relative to the `.mmb`'s own directory (the same convention as an `import "a/b.mm1"`, resolved against the importing file's directory) and localized against it on read.

<a id="argument-types"></a>The argument types, beyond the [`(cmd, data)`](../mm0-c/mmb.md#encoding-and-types) pair and the `u8`/`u32`/`cstr` of [mmb.md](../mm0-c/mmb.md#encoding-and-types):

* `value`: a value, read recursively by `read_value`.
* `body`: an `Ir` body — `Ir` instructions up to `END`, read by `read_code`.
* `[value] END`: values up to an `END` (`0x00`), which no value begins with.
* [`uleb`](#uleb) / [`sleb`](#sleb): an unsigned / signed LEB128.
* `[u8; len]`: exactly `len` raw bytes (the `AtomZ`/`StringZ` case, whose string may contain a NUL).

#### `infer_target`

An [`InferTarget`], a metavariable's expected type, is a `u8` tag optionally followed by a `sort` atom:

| Tag | Variant    | Reads         | Summary
| --- | ---------- | ------------- | -------
| `0` | `Unknown`  |               | an unconstrained hole
| `1` | `Provable` |               | a term of some provable sort
| `2` | `Bound`    | `sort: value` | a bound variable of that sort
| `3` | `Reg`      | `sort: value` | an expression of that sort

[`InferTarget`]: https://github.com/digama0/mm0/blob/master/mm0-rs/src/elab/lisp.rs

### References and cycles

A value's children are read before the value is complete, so a child can only refer *backward*, to something already read and saved — the immutable values thus form a DAG, recovered by `Save`/`Ref`. A *cycle* needs a node that exists before its contents, which is what a mutable `ref!` gives, and `NewRef` provides it: it saves an empty `(ref! #undef)` at the next heap index *first*, then reads its contents; a `Ref` back to that index inside the contents closes the loop, and the cell is filled once the contents are read.

    x = (ref (a . x)), where x is a reference cell:
      NewRef            ; save (ref! #undef) at H[0], then read its contents:
        DottedList 1    ;   a dotted list, one element and a tail
          Atom a        ;     the element
          Ref 0         ;     the tail — H[0], the cell itself
                        ; fill H[0] with (a . H[0]);  x = H[0]

Because the cell is installed before its contents are read, this handles every cycle, mutual ones included: a second `NewRef` met while reading the first's contents is itself installed before *its* contents, so a back-reference to either resolves — no separate back-patch command is needed. This is exactly what the in-memory importer does when copying values between environments: install an empty cell, descend into the contents, fill it in.

The weak links `letrec` and `set-weak!` create are handled the way those forms build them: a `ref!` cell, later pointed weakly at its target. A weak reference does *not* keep its target alive, so the writer never follows one to reach new values; it only records the target and, once the whole table is built, checks whether some *strong* path reached it. If so, the reference is written exactly as its in-memory construction — `NewRef #undef` installs an ordinary cell (this is where the cycle the weak link sits in breaks, since the cell as written points at nothing), and a deferred `SetWeak i` — emitted after every global, once the target has its heap slot — fills `H[i]` with a weak link to the target (a `Ref` back to it). The target is marked shared so it is written under a save and the `SetWeak` can name it. If no strong path reached it (it is unreachable but for the weak link, so it is not in the table), or if the target was already dead at serialization time, the reference is written as `DeadWeak` instead: a weak reference with an empty target, reading as `#undef`. `DeadWeak` has no pointer identity and effectively acts like another `#undef`.

Because a cycle can only close through a mutable cell, and every such cell — a strong `ref!` (`NewRef`) or a weak one (the `SetWeak` cell) — installs itself pre-order, the immutable values in between, closures included, are always reached forward exactly once and need no special handling.

### Procedures

A lisp procedure is read by one of three opcodes. `Builtin` is the simple case — a builtin is only a code, and is hash-consed by that code (the elaborator interns one object per code, so merging is faithful). The other two are reference-equality values and need genuine identity: a shared closure or `CustomProc` is observably `==` to itself, so it is written once under `Save` (post-order, like an `atom-map`) and `Ref`d thereafter.

#### `Lambda` encoding

`Lambda` builds a closure `Proc::Lambda { spec, pos, env, code }`. Its `data` is a flag byte: bit 0 set for `Named`. Then, in order:

| Field                 | Type         | When | Summary
| --------------------- | ------------ | ---- | -------
| `env`                 | `[value] END`| always | the captured environment, a list
| `span`                | `value`      | always | the definition's `FileSpan`
| `name_lo`, `name_hi`  | `u32`, `u32` | if `Named` | the name's byte range
| `name`                | `value`      | if `Named` | the name atom
| `code`                | `value`      | always | a [`Code`](#the-ir-sub-stream) or a `Ref`

#### `CustomProc` encoding

`CustomProc` builds any other `Proc` variant, chosen by the `kind` byte in `data`:

| `kind` | variant          | Reads | Summary
| ------ | ---------------- | ----- | -------
| `0`    | `MatchCont`      |       | an unusable match continuation
| `1`    | `RefineCallback` |       | also unusable
| `2`    | `MergeMap`       | `value` | A partial application `(merge-map s)`
| `3`    | `ProofThunk`     | `name: value` | the thunk from `(get-decl name)`, unforced
| `4`    | `Dyn`            | `magic: [u8; 4]`, `len: uleb`, `[u8; len]` | a user-defined object

`Dyn` is an extension point for custom objects, started with a `magic: [u8; 4]` which determines the parsing of the byte blob. The only used magic is `magic = "MMCC"` for `mmcc`'s own [encoding]. It uses an autogenerated serializer/deserializer structurally similar to the main encoding but specialized for the MMCC internal types.

[encoding]: https://github.com/digama0/mm0/blob/master/mm0-rs/components/mmcc/src/encode.rs

## The `Ir` sub-stream

A [`Code`](#read_value)'s payload is a lambda's `(spec, body)` core, read by `read_code`:

| Field   | Type       | Summary
| ------- | ---------- | -------
| `spec`  | `spec`     | The arity specification
| `body`  | `[ir] END` | the instructions

Here `spec = (kind: u8, count: u8)` where `kind` is `0 = Exact` or `1 = AtLeast` and `count` is the arity (procedures can only take up to 255 arguments).

`ir` instructions are a sequence of `(cmd, data)` pairs like the `value` stream. Each instruction is appended to the array and takes the next index from `0`, so the jump instructions (`Jump`, `JumpUnless`, `Branch`, `PatternTry`) name instruction indices.

`Code` saves the finished core to the heap and returns it as a value, so the core is an ordinary heap item, `Ref`d wherever it recurs. Bundling the spec with the body is what lets an `Ir::Lambda` literal and every `Proc::Lambda` stamped from it — spec copied, `Arc` cloned — name one core by index rather than repeat the function.

The `Ir` instructions (`0x00` is `END`):

| Value | Instruction | `data`  | Reads
| ----- | ----------- | ------- | -----
| `0x01` | `Undef` | `0` |
| `0x02` | `Dup` | `0` |
| `0x03` | `FocusFinish` | `0` |
| `0x04` | `TestPatternResume` | `0` |
| `0x05` | `Map` | `0` |
| `0x06` | `Have` | `0` |
| `0x07` | `RefineResume` | `0` |
| `0x08` | `AddThm` | `0` |
| `0x09` | `MergeMap` | `0` |
| `0x0A` | `OnDecls` | `0` |
| `0x0B` | `PatternUndef` | `0` |
| `0x0C` | `PatternGoal` | `0` |
| `0x0D` | `PatternTestPause` | `0` |
| `0x0E` | `Drop` | `n` |
| `0x0F` | `DropAbove` | `n` |
| `0x10` | `AssertScope` | `n` |
| `0x11` | `EndScope` | `n` |
| `0x12` | `Local` | `n` |
| `0x13` | `DottedList` | `n` |
| `0x14` | `JumpUnless` | `n` |
| `0x15` | `Jump` | `n` |
| `0x16` | `LocalDef` | `n` |
| `0x17` | `PatternAtom` | `n` |
| `0x18` | `PatternEqAtom` | `n` |
| `0x19` | `PatternDottedList` | `n` |
| `0x1A` | `RefineGoal` | `b` |
| `0x1B` | `PatternResult` | `b` |
| `0x1C` | `PatternBool` | `b` |
| `0x1D` | `PatternQuoteAtom` | `0` | `atom: value`
| `0x1E` | `PatternQExprAtom` | `0` | `atom: value`
| `0x1F` | `Const` | `0` | `value`
| `0x20` | `PatternString` | `0` | `value`
| `0x21` | `PatternNumber` | `0` | `value`
| `0x22` | `AppHead` | `0` | `span: value`
| `0x23` | `FocusStart` | `0` | `span: value`
| `0x24` | `BranchFail` | `0` | `span: value`
| `0x25` | `Global` | `0` | `span, atom: value`
| `0x26` | `SetMergeStrategy` | `0` | `span, atom: value`
| `0x27` | `List` | `count` | `span: value`
| `0x28` | `GlobalDef` | `0` | `span1, span2, atom: value`
| `0x29` | `SetDoc` | `0` | `doc, atom: value`
| `0x2A` | `App` | `count` | `span1, span2: value`
| `0x2B` | `TailApp` | `count` | `span1, span2: value`
| `0x2C` | `BuiltinApp` | `count` | `builtin`, `span1, span2: value`
| `0x2D` | `BuiltinTailApp` | `count` | `builtin`, `span1, span2: value`
| `0x2E` | `ArityError` | `0` | `span: value`, `spec`
| `0x2F` | `Branch` | `n` | `next, cont: uleb`
| `0x30` | `PatternList` | `n` | `dot: uleb`
| `0x31` | `PatternTry` | `ok` | `err: uleb`
| `0x32` | `PatternMVar` | `tag` |
| `0x33` | `Lambda` | `backref` | `span, core: value`

* `builtin` is a `BuiltinProc` code.
* `Branch`'s `cont` and `PatternList`'s `dot` are optional: a `uleb` that is `0` for `None`, else the value plus one.
* `PatternMVar`'s `tag` is `0` `Unknown`, `1` `Any`, or `2` `Simple`.
* `Lambda`'s `backref` is the enclosing `GlobalDef`'s index, or `0xFF` if unnamed; its spec lives in the `core`, not on the instruction.
