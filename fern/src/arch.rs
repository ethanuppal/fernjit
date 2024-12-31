// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

use core::ops::Range;
use static_assertions::const_assert;

pub type Word = u32;

#[derive(Clone, Copy)]
pub struct FunctionId(usize);

impl FunctionId {
    pub fn new(id: usize) -> Self {
        Self(id)
    }

    pub fn as_usize(&self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy)]
pub struct InstructionAddress(usize);

impl InstructionAddress {
    pub fn new(id: usize) -> Self {
        Self(id)
    }

    pub fn as_usize(&self) -> usize {
        self.0
    }

    pub fn next(&self) -> Self {
        Self(self.0 + 1)
    }
}

pub struct LocalAddress(u8);
impl LocalAddress {
    pub fn new(id: u8) -> Option<Self> {
        if id <= Self::MAX {
            Some(Self(id))
        } else {
            None
        }
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }

    pub const MAX: u8 = u8::MAX;
}

pub const LOCALS_COUNT: usize = LocalAddress::MAX as usize + 1;

pub const ARGUMENT_LOCALS: Range<usize> = 0..8;
const_assert!(ARGUMENT_LOCALS.end <= LOCALS_COUNT);

pub const RETURN_LOCALS: Range<usize> = 0..2;
const_assert!(RETURN_LOCALS.end <= LOCALS_COUNT);
