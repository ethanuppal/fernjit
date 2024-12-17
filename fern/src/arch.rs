// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

use core::ops::Range;

pub type Word = u32;
pub type InstructionAddress = usize; // TODO: better name?
pub type LocalAddress = u8;

pub const fn bitmask(bits: usize) -> Word {
    ((1 as Word) << bits).wrapping_sub(1)
}

pub const LOCAL_ADDRESS_BITS: usize = LocalAddress::BITS as usize;

pub const LOCALS_COUNT: usize = 1usize << LOCAL_ADDRESS_BITS;
pub const MAX_CODE_LENGTH: usize = 1024;

pub const ARGUMENT_LOCALS: Range<usize> = 0..8;
pub const RETURN_LOCALS: Range<usize> = 0..2;
