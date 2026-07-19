#!/bin/sh
# This is used by CI to run clippy on all subcrates in this directory,
# but you can also use it directly

cargo +nightly clippy --workspace --all-targets --all-features -- -D warnings
