Metamath Zero
===

The MM0 project consists of a number of tools and verifiers and a specification centered on the language Metamath Zero.


Introduction
---

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

What you will find in this repository
---

* [`mm0.md`](mm0.md) is an informal specification of the language.
* The `examples/` directory contains a number of MM0 test files.
  * [`set.mm0`](examples/set.mm0) is a hand-translation of the axiom system of [`set.mm`](https://github.com/metamath/set.mm/) into MM0. (The corresponding proof file [`set.mmu`](examples/set.mmu) is WIP.)
  * [`peano.mm0`](examples/peano.mm0) is a formalization of Peano Arithmetic in MM0. The formalization of MM0 in MM0 will occur in this axiom system, so it is built for practical use. [WIP]
  * [`hello.mm0`](examples/hello.mm0) / [`hello.mmu`](examples/hello.mmu) is a test of the `output` command of MM0, a somewhat unusual feature for producing verified output.
  * [`string.mm0`](examples/string.mm0) / [`string.mmu`](examples/string.mmu) is a more elaborate test of the `output` and `input` commands, to build a program that reads its own specification.
  * [`mm0.mm0`](examples/mm0.mm0) is a complete formal specification of the `.mm0` specification file format and verification, from input strings, through the parser, to the checking of proofs. For the formally minded this may be a better reference than [`mm0.md`](mm0.md).
* The `mm0-hs` program is a verifier written in Haskell that contains most of the "tooling" for MM0. Most importers and exporters are implemented as subparts of this program. See [`mm0-hs/README.md`](mm0-hs/README.md) for a more complete description of capabilities.
  * `mm0-hs verify` can be used to check a MM0 specification and proof.
  * `mm0-hs from-mm` performs wholescale translations from Metamath to MM0. This is the best way to obtain a large test set, because `set.mm` is quite large and advanced.
  * `mm0-hs to-hol` will show MM0 theorems and proofs in HOL syntax. Currently the syntax is only meant to be somewhat representative of a HOL based system; this is mostly a IR for other translations.
  * `mm0-hs to-othy` will translate MM0 theorems into [OpenTheory](http://www.gilith.com/opentheory/), which can be further translated into production systems including [HOL Light](https://www.cl.cam.ac.uk/~jrh13/hol-light/index.html), [HOL4](https://hol-theorem-prover.org/), [ProofPower](http://www.lemma-one.com/ProofPower/index/) and [Isabelle](https://www.cl.cam.ac.uk/research/hvg/Isabelle/). (Unfortunately there is a ~30x blow up in this translation due to limitations of the OpenTheory axiom system. It is possible that the secondary targets can obtain better results by a direct transaltion.)
  * `mm0-hs to-lean` translates MM0 into [Lean](leanprover.github.io/) source files compatible with `mm0-lean`. [WIP]
* `mm0-c` is a verifier written in C that defines the binary proof file format. [WIP]
* `mm0-lean` contains a tactic framework for writing MM0 proofs using Lean. [WIP]
  * `mm0-lean/x86.lean` is a Lean formalization of the Intel x86 semantics. [WIP]
