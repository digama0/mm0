#! /bin/sh

# This does profile guided optimization using peano.mmb.
# You can also just compile with "gcc main.c -o mm0-c" for the simple version.

set -e

gcc main.c -O2 -Wall -fprofile-generate -o mm0-c
./mm0-c ../examples/peano.mmb < ../examples/peano.mm0
gcc main.c -O2 -Wall -fprofile-use -o mm0-c
rm mm0-c-main.gcda
