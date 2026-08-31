#!/bin/sh

# Runs one .mmb through mm0-js, which must be built first:
#
#   cd mm0-js && npm ci && npx tsc
#
# Usage: ./run-mm0-js.sh fail/TEST
#              or        fail-index/TEST
#              or        pass/TEST
#
# `--index` asks for the stronger claim: not just that the proofs check, but
# that the file can be read -- names, notation, variable names. mm0-c cannot
# make that claim, because the index is advisory and it ignores the thing
# entirely, so this is the only place the fail-index/ group is decided.

exec node "$(dirname "$0")/../../mm0-js/dist/tools/check.js" --index "$1.mmb"
