// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

pub type Word = u64;
pub type SignedWord = i64;

/// Usage: `bits![T]`.
#[macro_export]
macro_rules! bits {
    ($T:ty) => {
        (8 * std::mem::size_of::<$T>())
    };
}

pub type Address = Word;
pub type Offset = SignedWord;

pub const ADDRESS_BITS: usize = 19;
pub const STACK_SIZE: usize = 1usize << ADDRESS_BITS;
pub const CODE_SIZE: usize = 1024;
