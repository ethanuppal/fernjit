# Copyright (C) 2024 Ethan Uppal. All rights reserved.
# currently a hack until I get it working on Apple Silicon

UNAME := $(shell uname)

ifeq ($(UNAME), Darwin)
	RUST_PREFIX := rustup run stable-x86_64-apple-darwin
endif

ifeq ($(UNAME), Darwin)
	NATIVE_PREFIX := arch -x86_64 
endif

.PHONY: test_native
test_native:
	cargo nextest run

.PHONY: deps
deps:
ifeq ($(UNAME), Darwin)
	rustup toolchain install stable-x86_64-apple-darwin --force-non-host
endif
	curl -L --proto '=https' --tlsv1.2 -sSf https://raw.githubusercontent.com/cargo-bins/cargo-binstall/main/install-from-binstall-release.sh | bash
	cargo binstall cargo-tarpaulin

.PHONY: test
test:
	$(RUST_PREFIX) cargo test

.PHONY: test_cov_vm
test_cov_vm:
	$(RUST_PREFIX) cargo tarpaulin -p fern-vm --coveralls $(COVERALLS)

.PHONY: build
build:
	$(RUST_PREFIX) cargo build

.PHONY: run
run: build
	$(NATIVE_PREFIX) target/debug/fernjit

.PHONY: asm
asm:
	cargo build --release
	objdump -d target/release/fernjit | less
