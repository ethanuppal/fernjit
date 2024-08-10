# Copyright (C) 2024 Ethan Uppal. All rights reserved.
# currently a hack until I get it working on Apple Silicon

.PHONY: build
build:
	rustup run stable-x86_64-apple-darwin cargo build

.PHONY: run
run: build
	arch -x86_64 target/debug/jit
