#!/bin/sh

# Usage: ./run.sh pass/TEST
#              or fail/TEST

if [ -f $1.mm0 ]; then
  ../../mm0-c/mm0-c $1.mmb < $1.mm0
else
  ../../mm0-c/mm0-c $1.mmb < /dev/null
fi
