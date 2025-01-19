// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.
use static_assertions::const_assert;
use std::ops::Range;

pub type Word = u32;

#[must_use]
pub struct FunctionId(pub usize);

pub type InstructionAddress = usize;
pub type LocalAddress = u8;

pub const LOCAL_ADDRESS_BITS: usize = 8;
const_assert!(LOCAL_ADDRESS_BITS <= LocalAddress::BITS as usize);

pub const LOCALS_COUNT: usize = 256;
const_assert!(LOCALS_COUNT <= LocalAddress::MAX as usize + 1);

pub const ARGUMENT_LOCALS: Range<usize> = 0..8;
const_assert!(ARGUMENT_LOCALS.end <= LOCALS_COUNT);

pub const RETURN_LOCALS: Range<usize> = 0..2;
const_assert!(RETURN_LOCALS.end <= LOCALS_COUNT);
