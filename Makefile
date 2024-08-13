# Copyright (C) 2024 Ethan Uppal. All rights reserved.
# currently a hack until I get it working on Apple Silicon

.PHONY: test_native
test_native:
	cargo nextest run

.PHONY: test
test:
	rustup run stable-x86_64-apple-darwin cargo test

.PHONY: build
build:
	rustup run stable-x86_64-apple-darwin cargo build

.PHONY: run
run: build
	arch -x86_64 target/debug/jit

.PHONY: asm
asm:
	cargo build --release
	objdump -d target/release/fernjit | less
