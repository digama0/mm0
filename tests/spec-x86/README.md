# x86 spec tests

Tests for the machine model in `examples/x86.mm0`. Each test names a byte string
and checks it three ways, which fail for different reasons:

- **in the semantics** — an MM0 theorem that the bytes take some concrete state to
  another one, proved in `x86_tests.mm1` and checked against the contract
  `x86_tests.mm0` by `mm0-c`;
- **as an encoding** — `objdump` decodes the same bytes to the same instruction,
  and consumes exactly as many of them;
- **on hardware** — the bytes actually run, and the registers and flags come back
  as the model says.

The theorems are deliberately of the form `E. k2 (step k k2 /\ ...)`. An
existence claim cannot be satisfied vacuously, which is the point: the audit that
motivated this suite found a definition (`pushAux`) that was unsatisfiable, and
every theorem about it had the form `X -> well-typed`, which holds of nothing at
all.

The corollary is that **only positive facts are testable here**. A bug that makes
the model too *permissive* — accepting an encoding it should reject — cannot be
caught by any test in this directory.

## Running

```sh
./run.sh              # from this directory; needs mm0-rs and mm0-c on PATH
TERSE=1 ./run.sh      # one line per check, the style tests/run-tests.sh uses
STRICT=1 ./run.sh     # a skipped runtime oracle is a failure, not a skip (CI)
```

Also run as part of `tests/run-tests.sh`. Besides `mm0-rs`/`mm0-c` it wants
`python3`, `objdump` and a C compiler; `qemu-x86_64` is optional and adds a
second runtime oracle. Override any of them with `MM0_RS`, `MM0_C`, `OBJDUMP`,
`CC`, `XCC`, `EMULATOR`.

There are two runtime oracles and they are independent signals:

| oracle | needs | a disagreement means |
|---|---|---|
| native | an x86-64 host | the model and a real CPU differ — evidence about x86 |
| emulated | `qemu-x86_64` | the model and *another implementation* differ — either may be wrong |

QEMU is not a reference, it is a second model. Under emulation alone a new
disagreement is a regression signal; confirm it on hardware before believing it
says anything about x86. When both run they cross-check each other through the
model: native passing while emulated fails points at the emulator, or at an
under-specified test.

## Files

| file | |
|---|---|
| `manifest.py` | **the single source of truth.** One `Test` per row: bytes, disassembly, register state in, observables out |
| `gen.py` | generates the three files below from it; `--check` fails if they are stale |
| `x86_tests.mm0` | *(generated)* the contract — one theorem statement per test, nothing else |
| `gen/cases.inc` | *(generated)* the same rows as a C table for the harness |
| `gen/disasm.expected` | *(generated)* the listing `objdump` is held to |
| `x86_tests.mm1` | **hand-written.** The proofs, plus the shared machinery they are built from |
| `check_disasm.py` | runs `objdump` on each test's bytes and diffs against `gen/disasm.expected` |
| `harness.c` | the runtime runner: loads the state, runs the bytes, compares. One `fork` per case, so a fault is a result rather than the end of the run |
| `trampoline.S` | the state load/store around the code buffer. One copy, shared by every test |
| `run.sh` | runs all of the above |

`gen.py` is not trusted. It emits statements only, so if it emits the wrong one
the hand-written proof stops discharging it and `mm0-c` says so.

`harness.c` and `trampoline.S` *are* trusted, and cannot be otherwise: the
teardown stores registers RIP-relative because that is the only addressing form
needing no scratch register, and that encoding is one of the things the suite
exists to test. Modelling the harness would make the test for RIP-relative
addressing depend on RIP-relative addressing. Hence one trampoline, small enough
to read, validated by an identity self-test that runs before any real test.

## Adding a test

**1. Add a row to `manifest.py`.**

```python
Test(
    name="test_add_rax_rcx",
    disasm="add rax,rcx",          # exactly as objdump -M intel prints it
    code=(0x48, 0x03, 0xc1),
    doc="...",                      # becomes the doc comment on the theorem
    pre=(("RAX", ALL_ONES), ("RCX", 1)),
    post=(Reg("RAX", 0), Flag("CF", True),
          Flag("ZF", True), Flag("SF", False), Flag("OF", False)),
),
```

Post-state clauses are `Reg(r, v)`, `RegsSame()` (nothing moved, at a symbolic
register), `FlagsSame()`, `Flag(f, bool)` and `FlagSame(f)`. The RIP advance is
implicit — every test asserts `readRIP k2 = rip +_64 len(code)`, which is the
instruction-length check and is not optional.

**Assert only what the model constrains.** `test_mul_rcx` checks `CF` and `OF`
and says nothing about `ZF`/`SF`, because `mul` goes through `eraseFlags` and the
SDM calls them undefined. Asserting them would be inventing a claim, and would
also be the first thing to break under emulation.

**2. Run `./gen.py`** to regenerate the contract, the C table and the objdump
listing.

**3. Prove it in `x86_tests.mm1`**, in the same order as the manifest. Typically:

- a `decode_*` lemma, built from the `parse*` rules in
  `examples/assembler-new.mm1` — building on those validates them too, and they
  need no bound-variable work, which makes the proofs mechanical;
- an `exec_*` lemma stating how the instruction evaluates, with every existential
  witness supplied as a hypothesis;
- the `pub theorem test_*` itself, via `stepI` and the flag projections.

Look at `test_add_rax_rcx` for the ordinary shape and `test_mul_rcx` for one with
a nondeterministic (`eraseFlags`) step.

## Not done yet: generating the proofs

`x86_tests.mm1` is written by hand, and most of that work should not be
necessary: the decode half of every test is a mechanical fact about an encoding.
There are two ways to stop writing it.

**The new assembler, in MMCC.** `mm0-rs/src/mmc/proof/assembler.rs` builds
`parseOpc`/`parseInst` proofs from MMCC's `PInst`, and covers far more than
anything in MM1 lisp: `Binop`, `Unop`, `Mul`, `DivRem`, `Cdx`, `Shift`, `Cmp`,
`SetCC`, `MovzxRmR`, `MovsxRmR`, `Lea`, `Imm`, `MovRR`, `Load64`, `Store`. That
is most of tier 1 and all of its arithmetic, including the two items next on the
list here. Generating tests through it would also **double as coverage testing
for the assembler** — the same feedback loop that motivated building these tests
on `assembler-new.mm1` rather than around it.

`parse_opc` is already parameterized on `(pinst, bytes, layout, ip, rex)`, so the
missing piece is an entry point driving it for a single instruction, rather than
`assemble(&ElfProof)` over a whole program. Two things to expect: its output is
at the `parseInst` layer, so the `parseInst_decode_*` bridges here stay; and the
vocabulary is `PInst`, the compiler's own instruction type, so anything the
compiler never emits — `nop`, `stc`, `xadd` — stays hand-written.

**The compiler side is not reusable.** Its judgments (`okAssembled`,
`assembled pctx`, the proc context) carry whole-program context, which does not
match a harness that runs one instruction at a fixed position. Making it match
means going the whole way: a standalone program per test, with the harness
written *into* the generated output and proved correct. That is a much larger
design, but it would retire the trusted-harness compromise described above, since
the prologue and epilogue would then be modelled rather than assumed.

**The MM1 lisp assembler** is the other option, enticing because it needs no
support on the compiler side at all. `examples/assembler-old.mm1` has
`(assemble-inst inst)`, which "assembles the instruction `inst`, and returns
`(ast s p)` where `p` proves `decode ast s`" — straight to `decode`, bypassing
`parseInst` and so the `instBinop` side conditions and the `DestSrc` existential
entirely. It is not bit-rotted (`assembler-old.mm1` still compiles), but it
covers two instructions, `mov.32 reg, imm` and `syscall`, because it was written
for `hello_assembler.mm1`. Extending its table is the work; the supporting pieces
are already in `x86.mm1` — `mk-splitBits`, `merge-bits`, `to-iNBytes`, `to-eli`,
alongside `assemble-rex` — and are what the `parseModRM_*` / `parseOpc_*` lemmas
here re-derive once per instruction.

The exec half does not generate the same way — each instruction's semantics
differ, which is the point of testing them — but it is already factored so that
what is left per test is small. The arithmetic is automated (`to-bitop`,
`to-elu`, `to-elBits`, `to-MSB64`), and `stepI`/`exec_unop_rax`/`exec_binop_rr`
plus the flag projections are boilerplate a generator could emit. What genuinely
has to be written is the `writeUnop*`/`writeBinop*` instance at the chosen
operands — roughly one lemma per test rather than the five or so today.
