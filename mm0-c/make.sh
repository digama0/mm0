#! /bin/sh
# This does profile guided optimization using peano.mmb, and also emits the
# generated assembly with gcc cruft removed.
# You can also just compile with "gcc main.c" for the simple version.
gcc main.c -O2 -fprofile-generate
./a.out ../examples/peano.mmb
gcc main.c -O2 -fprofile-use -S -fno-asynchronous-unwind-tables \
  -fno-pie -fomit-frame-pointer -fno-stack-protector
rm main.gcda
