// Copyright (C) 2024 Ethan Uppal. All rights reserved.

pub type Word = u32;
pub type SignedWord = i32;

/// Usage: `bits![T]`.
#[macro_export]
macro_rules! bits {
    ($T:ty) => {
        (8 * std::mem::size_of::<$T>())
    };
}

pub type Register = usize;
pub type Address = Word;

pub const REGISTER_COUNT: Register = 256;
pub const REGISTER_BITS: usize =
    bits![usize] - 1 - REGISTER_COUNT.leading_zeros() as usize;
pub const MEMORY_SIZE: usize = 1024;
pub const CODE_SIZE: usize = 1024;

pub trait IsValid {
    fn is_valid(&self) -> bool;
}

impl IsValid for Register {
    fn is_valid(&self) -> bool {
        *self < REGISTER_COUNT
    }
}
