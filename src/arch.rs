// Copyright (C) 2024 Ethan Uppal. All rights reserved.

pub type Word = u64;

/// Usage: `bits![T]`.
macro_rules! bits {
    ($T:ty) => {
        (8 * std::mem::size_of::<$T>())
    };
}

pub type Register = usize;
pub type Address = Word;

pub const REGISTER_COUNT: Register = 128;
pub const REGISTER_BITS: usize =
    bits![usize] - 1 - REGISTER_COUNT.leading_zeros() as usize;
pub const MEMORY_SIZE: usize = 1024;

pub struct Context {
    pub registers: [Word; REGISTER_COUNT],
    pub memory: [Word; MEMORY_SIZE]
}

impl Default for Context {
    fn default() -> Self {
        Self {
            registers: [0; REGISTER_COUNT],
            memory: [0; MEMORY_SIZE]
        }
    }
}
