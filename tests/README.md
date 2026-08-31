**Test files for mm0 and mmu**

This folder holds various tests for MM0, MM1, MMU, and MMB.

* `mm0_mmu/{pass, fail}`: Integration tests for MM0 + MMU that should pass or fail.
* `mm1/pass`: MM1 files that should elaborate successfully.
* `mmb/{run, fail, fail-index, pass}`: MMB binaries, grouped by the verdict
  each verifier is expected to reach.
* `spec-x86`: Differential tests of the `x86.mm0` instruction decoder against
  real hardware; see `spec-x86/README.md`.

Run everything with `./run-tests.sh`, from this directory.

### The mmb groups

A group is a combination of verdicts, not a severity. Two verifiers look at
these files and they do not always agree, which is the point of the split:

| group         | mm0-c            | mm0-js         |
| ------------- | ---------------- | -------------- |
| `run/`        | either, with its `.mm0` | not run |
| `fail/`       | rejects          | rejects        |
| `fail-index/` | **accepts**      | rejects        |
| `pass/`       | accepts          | accepts        |

`fail-index/` is where they part company. The MMB index -- names, notation,
variable names -- is advisory: nothing in it affects verification, so a
verifier is entitled to ignore it however broken it is, and mm0-c does. Those
files verify and are still not *readable*, which only a tool that reads them
can say. `pass/no_index` is the control: having no index at all is valid, and
must not be confused with having one that is broken.

Everything outside `run/` was cut from a compiled library by
`mmb/mutate.py`, which documents what each mutation breaks and can check that
the checked-in files still match its recipe (`./mutate.py --check`).

### What has to be on your path

    mm0-rs                                                  # mm0_mmu/, mm1/
    mm0-c        gcc mm0-c/main.c -O2 -Wall -o mm0-c        # mmb/run
    mm0-c-np     gcc mm0-c/main.c -O2 -Wall -DNO_PARSER \
                     -o mm0-c-np                            # the other mmb groups

plus a built mm0-js (`cd mm0-js && npm ci && npx tsc`) for the mm0-js column.

`mm0-c-np` is a second build rather than a flag because `NO_PARSER` is a
compile-time stub for `parse_until`, the `.mm0` interface check. The mutant
groups have no `.mm0` companion to check against, so under an ordinary build
every one of them fails in the parser before mm0-c ever reads the `.mmb` --
and a group that fails for that reason passes its test while proving nothing.
