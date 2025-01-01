// Copyright (C) 2024 Ethan Uppal. All rights reserved.

use enum_tags::enum_tags;

use crate::arch::Word;
use static_assertions::const_assert;

/// Smallest sized integer type that can fit an op code.
pub type RawOpCode = u8;

/// Smallest sized integer type that can fit a local address.
pub type Address = u8;

/// Smallest sized integer type that can fit an immediate value.
pub type Immediate = u16;

/// Smallest sized integer type that can fit an extended immediate value.
pub type ExtendedImmediate = u32;

/// Bits for opcode.
pub const OPCODE_BITS: usize = 8; // not using `::BITS` here because types are
                                  // just smallest thing that can fit; this is
                                  // the actual number of bits, which may be
                                  // less.
const_assert!(OPCODE_BITS <= RawOpCode::BITS as usize);

/// Bits for local address.
pub const ADDRESS_BITS: usize = 8;
const_assert!(ADDRESS_BITS <= Address::BITS as usize);

/// Bits for immediate value.
pub const IMM_BITS: usize = 16;
const_assert!(IMM_BITS <= Immediate::BITS as usize);

/// Bits for extended immediate value.
pub const IMM_EXT_BITS: usize = 24;
const_assert!(IMM_EXT_BITS <= ExtendedImmediate::BITS as usize);

#[rustfmt::skip]
mod encoding_spec {
    use super::*;

//  +------------------------------------------------------------------------------------+
//  | Encodings (inspired by Lua). `Op`s fit in one `Word`.                              |
//  +------------------------------------------------------------------------------------+
//  | ABC (3 addresses):                                                                 |
      const_assert!(OPCODE_BITS + 3 * ADDRESS_BITS <= Word::BITS as usize); 
//  | AB (2 addresses):                                                                  |
      const_assert!(OPCODE_BITS + 2 * ADDRESS_BITS <= Word::BITS as usize); 
//  | AI (address + immediate)                                                           |
      const_assert!(OPCODE_BITS + ADDRESS_BITS + IMM_BITS <= Word::BITS as usize); 
//  | IX (extended immediate)                                                            |
      const_assert!(OPCODE_BITS + IMM_EXT_BITS <= Word::BITS as usize);
//  | N (no operands)                                                                    | 
      const_assert!(OPCODE_BITS <= Word::BITS as usize);
//  +------------------------------------------------------------------------------------+
}

/// A VM operation.
#[derive(Clone, Copy)]
#[enum_tags(private, repr(RawOpCode))]
pub enum Op {
    /// `Self::Mov(a, b)` copies the contents at address `b` to `a`.
    Mov(Address, Address),
    /// `Self::MovI(a, i)` loads `i` at address `a`.
    MovI(Address, Immediate),
    /// `Self::Add(a, b, c)` loads the sum of the contents at addresses `b` and
    /// `c`  at address `a`.
    Add(Address, Address, Address),
    /// `Self::Call(ix)` saves the instruction pointer and jumps to the `ix`th
    /// VM function, pushing a new call frame.
    Call(ExtendedImmediate),
    /// `Self::Jump(ix)` jumps to the instruction within the current VM
    /// function offset by `ix`. `ix` is treated as an `IMM_EXT_BITS`-bit
    /// twos-complement integer.
    Jump(ExtendedImmediate),
    /// `Self::Ret` restores the previous call frame and restores the
    /// instruction pointer.
    Ret,
    /// `Self::Nop` has no effect.
    Nop,
}

impl Op {
    /// Encodes this operation as a [`Word`].
    pub const fn encode_packed(&self) -> Word {
        let encoded_args = match *self {
            Self::Mov(a, b) => Self::encode_packed_ab_args(a, b),
            Self::MovI(a, i) => Self::encode_packed_ai_args(a, i),
            Self::Add(a, b, c) => Self::encode_packed_abc_args(a, b, c),
            Self::Call(ix) => Self::encode_packed_ix_args(ix),
            Self::Jump(ix) => Self::encode_packed_ix_args(ix),
            Self::Ret | Self::Nop => 0,
        };

        (self.opcode() as Word) | (encoded_args << OPCODE_BITS)
    }

    /// Decodes this operation from a [`Word`].
    pub fn decode_packed(word: Word) -> Option<Self> {
        let opcode = (word & bitmask(OPCODE_BITS)) as RawOpCode;
        let args = word >> OPCODE_BITS;
        match opcode {
            Self::MOV_TAG => Self::decode_packed_ab_args(args, Self::Mov),
            Self::MOVI_TAG => Self::decode_packed_ai_args(args, Self::MovI),
            Self::ADD_TAG => Self::decode_packed_abc_args(args, Self::Add),
            Self::CALL_TAG => Self::decode_packed_ix_args(args, Self::Call),
            Self::RET_TAG => Some(Self::Ret),
            Self::NOP_TAG => Some(Self::Nop),
            _ => None,
        }
    }

    pub const fn opcode(&self) -> RawOpCode {
        self.tag()
    }

    const fn encode_packed_ab_args(a: Address, b: Address) -> Word {
        (a as Word) | ((b as Word) << ADDRESS_BITS)
    }

    fn decode_packed_ab_args(
        args: Word,
        f: impl FnOnce(Address, Address) -> Self,
    ) -> Option<Self> {
        let a = args & bitmask(ADDRESS_BITS);
        let b = (args >> ADDRESS_BITS) & bitmask(ADDRESS_BITS);
        Some(f(a as Address, b as Address))
    }

    const fn encode_packed_abc_args(
        a: Address,
        b: Address,
        c: Address,
    ) -> Word {
        (a as Word)
            | ((b as Word) << ADDRESS_BITS)
            | ((c as Word) << (2 * ADDRESS_BITS))
    }

    fn decode_packed_abc_args(
        args: Word,
        f: impl FnOnce(Address, Address, Address) -> Self,
    ) -> Option<Self> {
        let a = args & bitmask(ADDRESS_BITS);
        let b = (args >> ADDRESS_BITS) & bitmask(ADDRESS_BITS);
        let c = (args >> (2 * ADDRESS_BITS)) & bitmask(ADDRESS_BITS);
        Some(f(a as Address, b as Address, c as Address))
    }

    const fn encode_packed_ai_args(a: Address, i: Immediate) -> Word {
        (a as Word) | ((i as Word) << ADDRESS_BITS)
    }

    fn decode_packed_ai_args(
        args: Word,
        f: impl FnOnce(Address, Immediate) -> Self,
    ) -> Option<Self> {
        let a = args & bitmask(ADDRESS_BITS);
        let i = (args >> ADDRESS_BITS) & bitmask(IMM_BITS);
        Some(f(a as Address, i as Immediate))
    }

    const fn encode_packed_ix_args(ix: ExtendedImmediate) -> Word {
        ix as Word
    }

    fn decode_packed_ix_args(
        args: Word,
        f: impl FnOnce(ExtendedImmediate) -> Self,
    ) -> Option<Self> {
        let ix = args & bitmask(IMM_EXT_BITS);
        Some(f(ix as ExtendedImmediate))
    }
}

pub const fn bitmask(bits: usize) -> Word {
    ((1 as Word) << bits).wrapping_sub(1)
}

#[cfg(test)]
mod tests {
    use crate::{
        arch::Word,
        op::{Op, ADDRESS_BITS, OPCODE_BITS},
    };

    #[test]
    fn encodes_correctly() {
        assert_eq!(0, Op::Mov(0, 0).encode_packed());
        assert_eq!(1, Op::MovI(0, 0).encode_packed());
        assert_eq!(
            (1 << OPCODE_BITS) | (1 << (OPCODE_BITS + ADDRESS_BITS)),
            Op::Mov(1, 1).encode_packed()
        );
        assert_eq!(Op::Ret.opcode() as Word, Op::Ret.encode_packed());
    }
}
