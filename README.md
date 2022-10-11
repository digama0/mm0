# Metamath Zero

The MM0 project consists of a number of tools and verifiers and a specification centered on the language Metamath Zero.


## Quick Start

There are a bunch of interrelated projects in this repository. If you want to install something to play with, I recommend `mm0-rs` + `vscode-mm0` to get a decent MM0 IDE. There is also a [video tutorial](https://www.youtube.com/watch?v=A7WfrW7-ifw) for this combination.

* `mm0-rs`: An MM0/MM1 server written in Rust. See [`mm0-rs/README.md`](mm0-rs/README.md).
* `vscode-mm0`: VSCode plugin for MM0/MM1 syntax highlighting, with advanced features enabled via an LSP server (either `mm0-hs` or `mm0-rs`). See [`vscode-mm0/README.md`](vscode-mm0/README.md).
* `mm0-c`: A bare bones MM0 verifier, intended for formalization. See [`mm0-c/README.md`](mm0-c/README.md).
* `mm0-hs`: Haskell verifier and toolchain, see [`mm0-hs/README.md`](mm0-hs/README.md). Deprecated, but contains most of the translations.
* `mm0-lean`: A collection of lean scratch files and minor formalizations. See [`mm0-lean/README.md`](mm0-lean/README.md).

## Introduction

Metamath Zero is a language for writing specifications and proofs. Its emphasis is on balancing simplicity of verification and human readability of the specification. That is, it should be easy to see what exactly is the meaning of a proven theorem, but at the same time the language is as pared down as possible to minimize the number of complications in potential verifiers.

The language was inspired by Metamath and Lean, two proof languages at opposite ends of a spectrum.

* [Metamath](http://us.metamath.org/) is a logical framework with a focus on simplicity of the verifier and as a result a multitude of different verifiers exist for it. It has a strong specification, and proof checking is seriously fast (on the order of 1-10s to check the entire considerable library [set.mm](https://github.com/metamath/set.mm/)).

  However, it suffers from a number of soundness issues. These are not bugs because the verifier checks exactly what it claims, but rather issues with the semantics of a reasonable Metamath axiomatization.
  * Proof expressions in Metamath are strings of symbols, not trees. This is good for verification speed because computers can handle strings well, but it means that if the input expression grammar is ambiguous (and Metamath does not check this), then it is possible for proofs to take advantage of this and possibly derive a contradiction. (So one can view this as a kind of analogue to C "undefined behavior" in that the verifier is not checking this condition but needs it for the intended model to work.)
  * Definitions are just axioms in Metamath. There are tools in the Metamath ecosystem to check that definitions are conservative, but they are not built in to the verifier and yet are important for the semantic model.

* [Lean](http://leanprover.github.io/) is an interactive theorem prover based on dependent type theory. It has a robust tactic interface and a server mode for interacting with text editors to give live feedback, which helps considerably with proof authoring.

  However, it uses a very strong axiomatic framework, which cannot be "turned off", so it's not easy to verify proofs in a weak logic except by deep embedding, where many of the tactic features no longer apply. It is also monolithic - there is only one program that can read `.lean` files (although it does have an export format which can be checked by an external typechecker), and this program is huge and full of bugs. (To date, there have been no proofs of false in the most paranoid mode, but verification of the full program is impractical.)

Metamath Zero aims to be Metamath without the verification gaps. It is interpretable as a subset of HOL, but with checking times comparable to Metamath. On the other hand, because there is no substitute for human appraisal of the definitions and the endpoint theorems themselves, the specification format is designed to be clear and straightforward, and visually resembles Lean.

We embrace the difference between fully explicit *proofs* that are verified by a trusted verifier, and *proof scripts* that are used by front-end tools like Lean to generate proofs. Metamath Zero is focused on the proof side, with the expectation that proofs will not be written by hand but rather compiled from a more user friendly but untrusted language. So MM0 proofs tend to be very verbose and explicit (but not repetitive, because that is a performance issue).

The goal of this project is to build a formally verified (in MM0) verifier for MM0, down to the hardware, to build a strong trust base on which to build verifiers for more mainstream languages or other verified programs. This has lead to a number of subprojects that are contained in this repository.

## Metamath One and Metamath Zero

Metamath zero is a specification-only language, and it is paired with proofs with a defined theory but an implementation-defined concrete syntax. Currently the lisp-like MMU format and the binary MMB format are supported by `mm0-rs` and `mm0-hs`, and the `mm0-c` verifier supports only MMB. But neither of these is intended for being written by humans. If MM0 is the specification, then these are the compiled program meeting the specification.

But then what plays the role of the source text in this analogy? Metamath One is a language which extends the syntax of MM0 with the ability to write proofs, including elaboration and unification, and with a metaprogramming environment to allow the writing of tactics. The result of processing an MM1 file is an MM0 specification file and a MMU or MMB proof file (alternatively, an MM0 file can be written separately and matched against the MM1 file). Because the process is proof producing, it need not be trusted.

The MM1 files in the `examples/` directory have been written using the VSCode extension, which uses the [Language Server Protocol](https://microsoft.github.io/language-server-protocol/) to communicate to `mm0-rs server` (`mm0-rs` can also communicate to any other [LSP-compliant editor](https://microsoft.github.io/language-server-protocol/implementors/tools/)), which enables support for syntax highlighting, go-to-definition and hover. Most importantly, it supports live diagnostics (red squiggles on errors), which allows for rapid feedback on proof progress. (The interface is strongly inspired by [`vscode-lean`](https://github.com/leanprover/vscode-lean/).)

## What you will find in this repository

* [`mm0.md`](mm0.md) is an informal specification of the language.
* The `examples/` directory contains a number of MM0 test files.
  * [`peano.mm0`](examples/peano.mm0) and its proof [`peano.mm1`](examples/peano.mm1) is a formalization of Peano Arithmetic in MM0. The formalization of MM0 in MM0 occurs in this axiom system, so it is built for practical use.
    * [`peano_hex.mm1`](examples/peano_hex.mm1), [`mm0.mm1`](examples/mm0.mm1), [`x86.mm1`](examples/x86.mm1), [`compiler.mm1`](examples/compiler.mm1), and [`verifier.mm1`](examples/compiler.mm1) all extend this library of results of PA.
  * [`hello.mm0`](examples/hello.mm0) / [`hello.mmu`](examples/hello.mmu) is a test of the `output` command of MM0, a somewhat unusual feature for producing verified output.
  * [`string.mm0`](examples/string.mm0) / [`string.mmu`](examples/string.mmu) is a more elaborate test of the `output` and `input` commands, to build a program that reads its own specification.
  * [`set.mm0`](examples/set.mm0) is a hand-translation of the axiom system of [`set.mm`](https://github.com/metamath/set.mm/) into MM0. (The corresponding proof file [`set.mmu`](examples/set.mmu) is WIP.)
  * [`mm0.mm0`](examples/mm0.mm0) and its proof [`mm0.mm1`](examples/mm0.mm1) is a complete formal specification of the `.mm0` specification file format and verification, from input strings, through the parser, to the checking of proofs. For the formally minded this may be a better reference than [`mm0.md`](mm0.md).
  * [`x86.mm0`](examples/x86.mm0) and its proof [`x86.mm1`](examples/x86.mm1) is a formalization of the x86 architecture, used as the target for the MMC compiler.
  * [`verifier.mm0`](examples/verifier.mm0) is the main goal theorem of the project, the statement of implementation correctness of an MM0 verifier. Eventually [`verifier.mm1`](examples/verifier.mm1) will be a proof of this statement.
* `mm0-rs` is a compiler and LSP server for MM1.
  * [`mm1.md`](mm0-hs/mm1.md) is a description of the MM1 language (this is in the `mm0-hs` directory but it is up to date for `mm0-rs`).
  * `mm0-rs compile` can be used to run an MM1 file to produce an MMU or MMB output. If there are errors in the file, it will provide similar information to the server mode.
  * `mm0-rs server` is not meant to be used directly, but starts the program in server mode, where it sends and receives JSON data along stdin and stdout according to the [LSP](https://microsoft.github.io/language-server-protocol/) specification. This is used by the [`vscode-mm0`](vscode-mm0/) extension.
* `mm0-c` is a verifier written in C that defines the MMB binary proof file format.
  * [`mmb.md`](mm0-c/mmb.md) is an informal specification of the MMB format.
  * You can compile the verifier using `gcc main.c -o mm0-c`, and run it with `./mm0-c file.mmb`.
* The `mm0-hs` program is a verifier written in Haskell that contains most of the "tooling" for MM0. Most importers and exporters are implemented as subparts of this program. See [`mm0-hs/README.md`](mm0-hs/README.md) for a more complete description of capabilities.
  * [`mm1.md`](mm0-hs/mm1.md) is a description of the MM1 language.
  * `mm0-hs verify` can be used to check a MM0 specification and MMU proof.
  * `mm0-hs export` will translate an MMU file to MMB format.
  * `mm0-hs compile` can be used to run a MM1 file to produce an MMB output, similar to `mm0-rs`. (However, the MM1 implementation is out of date and this will not work on most mm1 files in the examples directory).
  * `mm0-hs server` is also similar to `mm0-rs server` and also out of date.
  * `mm0-hs from-mm` performs wholescale translations from Metamath to MM0 + MMU or MM0 + MMB. This is the best way to obtain a large test set, because `set.mm` is quite large and advanced.
  * `mm0-hs to-hol` will show MM0 theorems and proofs in HOL syntax. Currently the syntax is only meant to be somewhat representative of a HOL based system; this is mostly a IR for other translations.
  * `mm0-hs to-othy` will translate MM0 theorems into [OpenTheory](http://www.gilith.com/opentheory/), which can be further translated into production systems including [HOL Light](https://www.cl.cam.ac.uk/~jrh13/hol-light/index.html), [HOL4](https://hol-theorem-prover.org/), [ProofPower](http://www.lemma-one.com/ProofPower/index/) and [Isabelle](https://www.cl.cam.ac.uk/research/hvg/Isabelle/). (Unfortunately there is a ~30x blow up in this translation due to limitations of the OpenTheory axiom system. It is possible that the secondary targets can obtain better results by a direct translation.)
  * `mm0-hs to-lean` translates MM0 into [Lean](leanprover.github.io/) source files.
* `mm0-lean` contains a tactic framework for writing MM0 proofs using Lean. [WIP]
  * `mm0-lean/x86.lean` is a Lean formalization of the Intel x86 semantics.
* `vim` contains some basic vim files for syntax coloring.
  Copy them into `$HOME/.vim/`
  (e.g. with `cp -r vim/* ~/.vim/`) to install them.

## Third party MM0 verifiers

Since MM0 has a simple specification, there have been a few alternative verifiers written for MM0. (I ([@digama0](https://github.com/digama0)) am not directly affiliated with these verifier projects, and some of them are in WIP status. See the linked repositories for more information.)

* [`ammkrn/second_opinion`](https://github.com/ammkrn/second_opinion) is a third-party alternate verifier for MM0 + MMB, like `mm0-c`, written in Rust by [@ammkrn](https://github.com/ammkrn).
* [`trivial-rs`](https://github.com/trivial-rs/kernel) contains an MMB verifier, as well as an [`mmb-objdump`](https://github.com/trivial-rs/mmb-binutils/tree/main/objdump) program for debugging MMB files. Written in Rust by [@IvoWingelaar](https://github.com/IvoWingelaar).
* [`mm0kt`](https://github.com/Lakedaemon/mm0kt/) is a work in progress MM0 + MMU (text mode) verifier, written in Kotlin by [@Lakedaemon](https://github.com/Lakedaemon).
