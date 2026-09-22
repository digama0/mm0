<p align="center">
  <a href="https://digama0.github.io/mm0/">
    <picture>
      <source media="(prefers-color-scheme: dark)" srcset="site/logos/wordmark-dark.svg">
      <img src="site/logos/wordmark.svg" alt="Metamath Zero" width="420">
    </picture>
  </a>
</p>

<p align="center">
  <b>A language for writing specifications and proofs,<br>
  checked by a verifier small enough to read.</b>
</p>

<p align="center">
  <a href="https://digama0.github.io/mm0/">Website</a> &middot;
  <a href="https://digama0.github.io/mm0/m0e/">Try it in your browser</a> &middot;
  <a href="mm0.md">Specification</a> &middot;
  <a href="https://digama0.github.io/mm0/thesis.pdf">Thesis</a> &middot;
  <a href="https://www.youtube.com/watch?v=A7WfrW7-ifw">Video tutorial</a>
</p>

<p align="center">
  <a href="https://github.com/digama0/mm0/actions/workflows/build.yml"><img
    src="https://github.com/digama0/mm0/actions/workflows/build.yml/badge.svg" alt="CI status"></a>
</p>

## What it is

An `.mm0` file is a specification and nothing else: sorts, term constructors,
axioms, and the statements of theorems. It contains no proofs, which is what
keeps it short enough to read, and reading it is the only way to know what a
formalization actually claims.

The proofs live in a separate file (the binary `.mmb`, or the text `.mmu`).
Anything may produce them. Usually that is an `.mm1` file, which is `.mm0`
extended with a proof syntax and a Scheme-like metaprogramming language for
writing tactics; `mm0-rs` elaborates it and emits the specification and the
proof. None of that has to be trusted, because the verifier re-checks every
step against the specification knowing nothing about where the proof came from.

That verifier is the only thing you have to believe, so it is kept small: the
reference implementation, `mm0-c`, is under 3,000 lines of C, and checking a
library costs about what reading the file costs. It also fixes no logic of its
own: you supply the axioms (Peano arithmetic, ZFC, higher-order logic, whatever
the development needs) and it checks proofs in the system you defined.

The project's endpoint is [`verifier.mm0`](examples/verifier.mm0): the statement
that an MM0 verifier is correct, down to the x86 instructions it executes, to be
proved in MM0 and checked by an MM0 verifier. The reason to finish it is what
can be stacked on top: verifiers for more mainstream languages, and verified
programs generally, resting on a base that has been verified rather than
assumed.

## Try it

Nothing is uploaded in any of these; the verifier is compiled to WebAssembly and
every file is checked in the tab you opened it in.

* [**Editor**](https://digama0.github.io/mm0/m0e/): `mm0-rs` in the browser,
  elaborating and reporting errors as you type.
* [**Proof explorer**](https://digama0.github.io/mm0/mmb/): step a compiled
  `.mmb` proof the way the verifier's stack machine runs it.
* [**Documentation**](https://digama0.github.io/mm0/doc/peano/): generated pages
  for a whole library, every statement and proof tree cross-linked.

To work locally, build the compiler and language server (this needs
[Rust](https://rustup.rs/)):

```sh
git clone https://github.com/digama0/mm0
cd mm0/mm0-rs
cargo build --release
```

then add the editor integration, which gives live diagnostics, go-to-definition
and hover:

```sh
code --install-extension digama0.metamath-zero
```

The [video tutorial](https://www.youtube.com/watch?v=A7WfrW7-ifw) walks through
that pair. Vim syntax files are in [`vim/`](vim/) (`cp -r vim/* ~/.vim/`).

Building the reference verifier takes one command, and it is worth doing at
least once to see how little there is to it:

```sh
gcc mm0-c/main.c -O2 -o mm0-c
./mm0-c proof.mmb < spec.mm0
```

## Why another proof language

MM0 was shaped by two systems at opposite ends of a spectrum.

[Metamath](http://us.metamath.org/) has a specification so simple that many
independent verifiers exist for it, and checking all of
[set.mm](https://github.com/metamath/set.mm/) takes seconds. But a reasonable
Metamath axiomatization has soundness gaps that the verifier does not close.
Proof expressions are strings rather than trees, so an ambiguous grammar (which
Metamath does not check for) can be exploited to derive a contradiction, rather
as C undefined behavior is a condition the compiler needs but does not verify.
Definitions are just axioms, and the tools that check them for conservativity
live outside the verifier.

[Lean](http://leanprover.github.io/) has the interactive story: tactics, and a
server that gives live feedback while you write a proof. But its axiomatic
framework is strong and cannot be turned off, so proving something in a weak
logic means a deep embedding, where the tactic machinery no longer applies. It
is also monolithic: one large program reads `.lean` files, and verifying that
program is impractical.

Metamath Zero aims at Metamath without the verification gaps. It is
interpretable as a subset of HOL, checks about as fast as Metamath, and because
no verifier can substitute for a human reading the definitions and the final
theorem statements, the specification format is built to be read (it looks
rather like Lean).

The split between the two is deliberate. A *proof* is a finished artifact that a
trusted verifier checks; a *proof script* is what a front end runs to produce
one. MM0 is concerned only with the first, on the assumption that proofs are
compiled from something friendlier rather than written by hand, so they tend to
be verbose and fully explicit (though not repetitive, which would be a
performance problem).

## What's in this repository

| Path | What it is |
| --- | --- |
| [`mm0.md`](mm0.md) | The specification of the MM0 language. [`examples/mm0.mm0`](examples/mm0.mm0) says the same thing formally. |
| [`mm0-rs/`](mm0-rs/README.md) | Rust: the MM1 compiler, the LSP server, the documentation generator, and the MMC compiler. |
| [`mm0-c/`](mm0-c/README.md) | The reference verifier, in C. [`mmb.md`](mm0-c/mmb.md) defines the MMB proof format it reads. |
| [`examples/`](examples/) | The libraries: Peano arithmetic, x86, the MM0 specification, the compiler. |
| [`m0e/`](m0e/README.md) | The browser editor: `mm0-rs` compiled to WebAssembly behind a Monaco front end. |
| [`mm0-js/`](mm0-js/) | The MMB proof explorer, a verifier in TypeScript that shows its state at every step. |
| [`vscode-mm0/`](vscode-mm0/README.md) | The VS Code extension: syntax highlighting, and the LSP client for `mm0-rs server`. |
| [`mm0-hs/`](mm0-hs/README.md) | Haskell: deprecated as a server, but still where most of the translations live. |
| [`site/`](site/README.md) | The sources for [digama0.github.io/mm0](https://digama0.github.io/mm0/). |
| [`tests/`](tests/README.md) | Test suites for MM0, MM1, MMU and MMB, and the x86 specification tests. |
| [`mm0-lean/`](mm0-lean/README.md), [`mm0-lean4/`](mm0-lean4/README.md) | Lean scratch work, including a Lean formalization of x86 semantics. |
| [`vim/`](vim/README.md) | Vim syntax files. |

The languages each have their own description: [`mm1.md`](mm0-hs/mm1.md) for the
proof language (it lives in the `mm0-hs` directory but is current for `mm0-rs`),
and [`mmc.md`](mm0-rs/mmc.md) for Metamath C, the systems language whose
compiler emits a proof that the program it produced meets its specification.

`mm0-hs` is out of date as a compiler and server, but it is still the way to get
a large corpus in and out of MM0: `from-mm` translates wholesale from Metamath,
and `to-hol`, `to-othy` and `to-lean` translate outward, to HOL syntax, to
[OpenTheory](http://www.gilith.com/opentheory/) (and from there to HOL Light,
HOL4, ProofPower and Isabelle), and to Lean.

<details>
<summary><b>The example libraries in full</b></summary>

| File | What it is |
| --- | --- |
| [`peano.mm0`](examples/peano.mm0) / [`peano.mm1`](examples/peano.mm1) | Peano arithmetic, built for practical use: everything else is stacked on it. |
| [`peano_hex.mm1`](examples/peano_hex.mm1) | Hexadecimal digits and strings on top of `peano`, for talking about concrete input and output. |
| [`mm0.mm0`](examples/mm0.mm0) / [`mm0.mm1`](examples/mm0.mm1) | A formal specification of the `.mm0` format and of verification itself, from input string through parsing to proof checking. For the formally minded this is a better reference than [`mm0.md`](mm0.md). |
| [`x86.mm0`](examples/x86.mm0) / [`x86.mm1`](examples/x86.mm1) | The x86 architecture, the target the MMC compiler proves things about. |
| [`compiler.mm0`](examples/compiler.mm0) / [`compiler.mm1`](examples/compiler.mm1) | The MMC compiler's correctness statement, and the proof in progress (it still admits a `sorry` axiom, so that the partial proof stays checked in CI). |
| [`verifier.mm0`](examples/verifier.mm0) | The goal theorem: an MM0 verifier is correct. [`verifier.mm1`](examples/verifier.mm1) will be the proof. |
| [`hol.mm0`](examples/hol.mm0) / [`hol.mm1`](examples/hol.mm1) | Higher-order logic, as a second axiom system to work in. |
| [`set.mm0`](examples/set.mm0) | The [`set.mm`](https://github.com/metamath/set.mm/) axiom system, hand-translated. The proof file is a work in progress. |
| [`hello.mm0`](examples/hello.mm0) / [`hello.mmu`](examples/hello.mmu) | A test of the `output` command, MM0's way of producing verified output. |
| [`string.mm0`](examples/string.mm0) / [`string.mmu`](examples/string.mmu) | `output` and `input` together: a program that reads its own specification. |
| [`demo.mm1`](examples/demo.mm1), [`miu.mm0`](examples/miu.mm0) | Small self-contained systems, a good place to start reading. |

</details>

## Other verifiers

Because the format is small and precisely specified, more than one program can
play the role of the verifier, which is the point: no single implementation has
to be believed. These are third-party projects, some of them work in progress,
and [@digama0](https://github.com/digama0) is not affiliated with them. See the
linked repositories for status.

| Verifier | | |
| --- | --- | --- |
| [`second_opinion`](https://github.com/ammkrn/second_opinion) | Rust | An MM0 + MMB verifier, like `mm0-c`, by [@ammkrn](https://github.com/ammkrn). |
| [`trivial-rs`](https://github.com/trivial-rs/kernel) | Rust | An MMB verifier, plus [`mmb-objdump`](https://github.com/trivial-rs/mmb-binutils/tree/main/objdump) for inspecting MMB files, by [@IvoWingelaar](https://github.com/IvoWingelaar). |
| [`mm0kt`](https://github.com/Lakedaemon/mm0kt/) | Kotlin | An MM0 + MMU verifier, by [@Lakedaemon](https://github.com/Lakedaemon). |
| [`mm0-zig`](https://github.com/gleachkr/Aufbau) | Zig | An MM0 + MMB verifier; part of a suite including an mmb compiler with integrated lsp and proof search support, by [@gleachkr](https://github.com/gleachkr)]

## License

Released to the public domain under [CC0](LICENSE.txt).
