#!/bin/sh

# Usage: ./run-mm0-rs.sh pass/TEST
#                     or fail/TEST

base=${1%.*}
if [ -f $base.mmu ]; then
  mm0-rs compile $base.mmu $base.mmb && ../../mm0-c/mm0-c $base.mmb < $base.mm0
else
  mm0-rs compile $base.mm0
fi
