#!/bin/sh
# This is used by CI to run clippy on all subcrates in this directory,
# but you can also use it directly

cargo +nightly clippy --all-features -- -D warnings
error=$?
for i in components/*; do
  cd $i
  cp ../../Cargo.lock .
  CARGO_TARGET_DIR=../../target cargo +nightly clippy --all-features -- -D warnings || error=$?
  rm Cargo.lock
  cd ../..
done
exit $error
