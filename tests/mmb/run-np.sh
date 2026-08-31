#!/bin/sh

# Runs one .mmb under a NO_PARSER build of mm0-c, which must be on your path
# as `mm0-c-np`:
#
#   gcc mm0-c/main.c -O2 -Wall -DNO_PARSER -o mm0-c-np
#
# Usage: ./run-np.sh fail/TEST
#              or    fail-index/TEST
#              or    pass/TEST
#
# NO_PARSER stubs out `parse_until`, the .mm0 interface check. These tests are
# mutants of a compiled library rather than hand-written pairs, so they have no
# .mm0 to check against: under a parser build every one of them fails at
# `invalid command keyword` before mm0-c reaches the .mmb, which would make the
# whole group pass for the wrong reason.
#
# Use ./run.sh for the run/ group, which does have .mm0 companions.

mm0-c-np $1.mmb < /dev/null
