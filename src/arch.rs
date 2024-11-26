// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

pub type Word = u32;

/// Usage: `bits![T]`.
#[macro_export]
macro_rules! bits {
    ($T:ty) => {
        (8 * std::mem::size_of::<$T>())
    };
}

pub type LocalAddress = u8;

pub const LOCAL_ADDRESS_BITS: usize = LocalAddress::BITS as usize;
pub const LOCALS_SIZE: usize = 1usize << LOCAL_ADDRESS_BITS;
pub const CODE_SIZE: usize = 1024;
