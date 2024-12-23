# Copyright (C) 2024 Ethan Uppal. All rights reserved.
# currently a hack until I get it working on Apple Silicon

UNAME := $(shell uname)
ifeq ($(UNAME), Darwin)
PREFIX := rustup run stable-x86_64-apple-darwin
endif

.PHONY: test_native
test_native:
	cargo nextest run

.PHONY: deps
deps:
ifeq ($(UNAME), Darwin)
	rustup toolchain install stable-x86_64-apple-darwin
endif
	cargo install cargo-tarpaulin 

.PHONY: test
test:
	$(PREFIX) cargo test

.PHONY: test_cov_vm
test_cov_vm:
	cargo tarpaulin -p fern --coveralls $(COVERALLS)

.PHONY: build
build:
	$(PREFIX) cargo build

.PHONY: run
run: build
ifeq ($(UNAME), Darwin)
	arch -x86_64 target/debug/fernjit
else
	target/debug/fernjit
endif

.PHONY: asm
asm:
	cargo build --release
	objdump -d target/release/fernjit | less

.PHONY: lint
lint:
	cargo clippy
