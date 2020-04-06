#! /bin/sh
# This does profile guided optimization using peano.mmb.
# You can also just compile with "gcc main.c" for the simple version.
gcc main.c -O2 -Wall -fprofile-generate
./a.out ../examples/peano.mmb < ../examples/peano.mm0
gcc main.c -O2 -Wall -fprofile-use
rm main.gcda
