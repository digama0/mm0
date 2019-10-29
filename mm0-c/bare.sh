#! /bin/sh
# This does profile guided optimization using peano.mmb, and also emits the
# generated assembly with gcc cruft removed.
# You can also just compile with "gcc main.c" for the simple version.
gcc main.c -O2 -Wall -fprofile-generate -D BARE
./a.out ../examples/peano.mmb
gcc main.c -O2 -Wall -fprofile-use -D BARE -fno-asynchronous-unwind-tables \
   -fomit-frame-pointer -fno-stack-protector
rm main.gcda
