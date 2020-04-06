# `mm0-c`

This is a high-performance MM0 verifier written in "bare bones C". The main part of the code is in `verifier.c`, with the individual instructions described in `types.c`.

## Execution

It is run as:

    mm0-c foo.mmb < foo.mm0

The specification of an MM0 verifier says that it takes an MM0 file on standard input, and returns `0` only if all the theorems described in the MM0 file are provable. The `.mmb` file is not described in the specification, and is viewed as a side-input, but it contains the actual proofs, and the verifier is responsible for checking that they are in fact proofs of the given theorems.

## Compilation

* It compiles with `gcc main.c -o mm0-c`
* You can get better performance by playing with profile-guided optimization; `make.sh` will compile it with `-O2` and profile-guided optimizations using `peano.mmb` as a baseline.
* `bare.sh` will compile it for minimum "cruft"; it removes the C runtime library except for syscall shims, and removes debugging information and other things gcc doesn't need to do. It is intended for "clean assembly" and will be near to the final verified bare-metal verifier.

## Compilation options

The code contains `#ifdef` commands using symbols that are intended to be passed via the `-D` command line option.

* `-D BARE` will remove all references to `printf`, so that only syscalls remain. In the default mode, when an error is encountered it goes into a verbose mode to backtrace the error, but in `BARE` mode it has only one bit of output - the exit code is `0` on successful verification and nonzero otherwise.

* `-D HIGHWATER` will report statistics on how much of the system limits were used in the current verification. This is useful for setting limits (see Limits).

* `-D NO_PARSER` disables the parser, the part of the program that reads the `.mm0` file coming from standard in. Without this, it can still check `.mmb` proofs for internal correctness, but the statements of proven theorems are not reported, so this leaves open the possibility that the `.mmb` file is correctly proving a triviality rather than the target theorem.

## Limits

For simplicity and efficiency, the verifier does not do any dynamic growing of limits. When a limit is exceeded, verification fails, and the verifier must be recompiled with a greater limit (in `verifier_types.c`) in order to verify the input.

* `STACK_SIZE = 2^16`: the size of the main stack in fourbyte units. Can be raised up to `2^64` (C language limits will kick in first).
* `HEAP_SIZE = 2^16`: the size of the main heap in fourbyte units. Can be raised up to `2^32-1`.
* `STORE_SIZE = 2^26`: the size of the store in bytes. This is where most memory is stored, and the most likely limit to be exceeded in large proofs. Can be raised up to `2^32-1`.
* `HYP_STACK_SIZE = 256`: the number of hypotheses in a given theorem (fourbyte units). Can be raised up to `2^64`, but format restrictions prevent it from exceeding `2^32`.
* `UNIFY_STACK_SIZE = 256`: the size of the unification stack (fourbyte units), i.e. the maximum depth of theorem statements. Can be raised up to `2^64`, but format restrictions prevent it from exceeding `2^32`.
* `UNIFY_HEAP_SIZE = 2^16`: the size of the unification heap (fourbyte units), i.e. the number of backreferences in a theorem statement. Can be raised up to `2^32-1`.

The default numbers are calibrated based on values seen in practice, plus one or two orders of magnitude for safety margin.

There are additional restrictions ("format restrictions") that are caused by the design of the `.mmb` file format, rather than limits in the code per se, so these limits require a modification to the format in order to be exceeded.

* The set of bound variables in an expression is at most `55`, because disjoint variable restrictions are tracked with a `64`-bit bitset with the top `8` bits reserved for the sort, and one bit reserved for a possible future extension to relax this limit.

  Note that while this is quite small, it is still larger than the `set.mm` limit of 26 bound variables (because each variable is a lowercase letter), and this has proven to be enough to do large portions of mathematics. Computer-generated proofs may exceed this limit, though.

* All pointers to the theorem table are `32`-bit, as well as the term table. This means that all theorem statements must fit in the first 4GB of the file (and in particular there cannot be more than `2^32` theorems). Also proofs have forward references to the next proof, so each individual proof must be at most 4GB. The index, which is expected to go at the end of the file, is a `64`-bit pointer.
