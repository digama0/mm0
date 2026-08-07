**Test files for mm0 and mmu**

This folder holds various tests for MM0, MM1, MMU, and MMB.

* `mm0_mmu/{pass, fail}`: Integration tests for MM0 + MMU that should pass or fail.
* `mm1/pass`: MM1 files that should elaborate successfully.
* `mmb/{pass, fail}`: MMB files that `mm0-c` should accept or reject.
* `mmb/run`: MMB files that `mm0-c` may accept or reject, but must not crash on.
  These are mostly regressions for malformed-input handling.
* `spec-x86`: Differential tests of the `x86.mm0` instruction decoder against
  real hardware; see `spec-x86/README.md`.
