#!/bin/sh

# Runs one .mmb under an ordinary (parser) build of mm0-c, checking it against
# its .mm0 interface where it has one.
#
# Usage: ./run.sh run/TEST
#
# This is for the run/ group only. The fail/, fail-index/ and pass/ groups are
# mutants with no .mm0 companion, and a parser build rejects those at
# `invalid command keyword` whatever the .mmb contains -- use ./run-np.sh,
# which builds mm0-c with NO_PARSER, and ./run-mm0-js.sh.

if [ -f $1.mm0 ]; then
  mm0-c $1.mmb < $1.mm0
else
  mm0-c $1.mmb < /dev/null
fi
