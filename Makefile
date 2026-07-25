SHELL := /bin/sh

# -------------------------
# Tool paths (single source of truth)
# -------------------------
# export MM0_RS := ./mm0-rs/target/release/mm0-rs
# export MM0_HS := ./mm0-hs/.stack-work/dist/x86_64-linux-nix/ghc-9.10.3/build/mm0-hs/mm0-hs
# export MM0_C  := ./mm0-c/mm0-c

# -------------------------
# Default target
# -------------------------
.PHONY: all
all: test

# -------------------------
# Rebuild targets
# -------------------------
.PHONY: rebuild-rs
rebuild-rs:
	@echo "🔧 rebuilding mm0-rs"
	cd ./mm0-rs && cargo build --release

.PHONY: rebuild-hs
rebuild-hs:
	@echo "🔧 rebuilding mm0-hs"
	cd ./mm0-hs && stack build

.PHONY: rebuild-c
rebuild-c:
	@echo "🔧 rebuilding mm0-c"
	cd ./mm0-c && ./make.sh

.PHONY: rebuild-all
rebuild-all: rebuild-rs rebuild-hs rebuild-c

# -------------------------
# Tests
# -------------------------
.PHONY: test
test:
	@echo "🧪 running tests"
	./tests/run-tests.sh

# -------------------------
# Examples build
# -------------------------
.PHONY: examples
examples:
	@echo "🏗 building examples"
	./examples/build.sh

# -------------------------
# Combined
# -------------------------
.PHONY: full
full: rebuild-all test examples
