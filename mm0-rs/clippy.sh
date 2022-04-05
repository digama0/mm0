#!/bin/sh
# This is used by CI to run clippy on all subcrates in this directory,
# but you can also use it directly

cargo clippy --all-features -- -D warnings
for i in components/*; do
  cd $i
  cp ../../Cargo.lock .
  CARGO_TARGET_DIR=../../target cargo clippy --all-features -- -D warnings
  rm Cargo.lock
  cd ../..
done
