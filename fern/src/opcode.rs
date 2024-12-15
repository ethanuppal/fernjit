// Copyright (C) 2024 Ethan Uppal. All rights reserved.

use enum_tags::enum_tags;

use crate::arch::{bitmask, LocalAddress, Word, LOCAL_ADDRESS_BITS};

/// Smallest sized integer type that can fit an op code.
pub type RawOpCode = u8;

/// Smallest sized integer type that can fit an immediate value.
pub type Immediate = u16;

/// Smallest sized integer type that can fit an extended immediate value.
pub type ExtendedImmediate = u32;

/// Bits for opcode.
pub const OPCODE_BITS: usize = 8; // not using `::BITS` here because types
                                  // are just smallest thing that can fit,                                    //
                                  // this is actual number of bits, which may be less.
/// Bits for immediate value.
pub const IMM_BITS: usize = 16;

/// Bits for extended immediate value.
pub const IMM_EXT_BITS: usize = 24;

#[rustfmt::skip]
 mod encoding_spec {
     use super::*;
     use static_assertions::{const_assert, const_assert_eq};

     macro_rules! bits {
         ($T:ty) => {
             (8 * std::mem::size_of::<$T>())
         };
     }

//   +---------------------------------------------------------------------------------+
//   | Encodings (inspired by Lua). Ops fit in one `Word`.                             |
//   +---------------------------------------------------------------------------------+
//   | ABC (3 addresses):                                                              |
       const_assert_eq!(bits![Word], OPCODE_BITS + 3 * LOCAL_ADDRESS_BITS); 
//   | AB (2 addresses):                                                               |
       const_assert!(OPCODE_BITS + 2 * LOCAL_ADDRESS_BITS <= bits![Word]); 
//   | AI (address + immediate)                                                        |
       const_assert_eq!(bits![Word], OPCODE_BITS + LOCAL_ADDRESS_BITS + IMM_BITS); 
//   | IX (extended immediate)                                                         |
       const_assert_eq!(bits![Word], OPCODE_BITS + IMM_EXT_BITS);
//   | N (no operands)                                                                 | 
       const_assert!(OPCODE_BITS <= bits![Word]);
//   +---------------------------------------------------------------------------------+
}

/// A VM operation.
#[repr(u8)]
#[enum_tags]
#[derive(Clone, Copy)]
pub enum Op {
    /// `Self::Mov(a, b)` copies the contents at address `b` to `a`.
    Mov(LocalAddress, LocalAddress),
    /// `Self::MovI(a, i)` loads `i` at address `a`.
    MovI(LocalAddress, Immediate),
    /// `Self::Add(a, b, c)` loads the sum of the contents at addresses `b` and
    /// `c`  at address `a`.
    Add(LocalAddress, LocalAddress, LocalAddress),
    /// `Self::Call(ix)` saves the instruction pointer and jumps to the `ix`th
    /// code instruction, pushing a new call frame.
    Call(ExtendedImmediate),
    /// `Self::Ret` restores the previous call frame and restores the
    /// instruction pointer.
    Ret,
    /// `Self::Nop` has no effect.
    Nop,
}

impl Op {
    /// Encodes this operation as a [`Word`].
    pub fn encode_packed(&self) -> Word {
        let encoded_args = match *self {
            Self::Mov(a, b) => Self::encode_packed_ab_args(a, b),
            Self::MovI(a, i) => Self::encode_packed_ai_args(a, i),
            Self::Add(a, b, c) => Self::encode_packed_abc_args(a, b, c),
            Self::Call(ix) => Self::encode_packed_ix_args(ix),
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

    /// # Safety
    /// See <https://doc.rust-lang.org/std/mem/fn.discriminant.html>
    pub fn opcode(&self) -> RawOpCode {
        unsafe { *<*const _>::from(self).cast::<RawOpCode>() }
    }

    fn encode_packed_ab_args(a: LocalAddress, b: LocalAddress) -> Word {
        (a as Word) | ((b as Word) << LOCAL_ADDRESS_BITS)
    }

    fn decode_packed_ab_args(
        args: Word,
        f: impl FnOnce(LocalAddress, LocalAddress) -> Self,
    ) -> Option<Self> {
        let a = args & bitmask(LOCAL_ADDRESS_BITS);
        let b = (args >> LOCAL_ADDRESS_BITS) & bitmask(LOCAL_ADDRESS_BITS);
        Some(f(a as LocalAddress, b as LocalAddress))
    }

    fn encode_packed_abc_args(
        a: LocalAddress,
        b: LocalAddress,
        c: LocalAddress,
    ) -> Word {
        (a as Word)
            | ((b as Word) << LOCAL_ADDRESS_BITS)
            | ((c as Word) << (2 * LOCAL_ADDRESS_BITS))
    }
    fn decode_packed_abc_args(
        args: Word,
        f: impl FnOnce(LocalAddress, LocalAddress, LocalAddress) -> Self,
    ) -> Option<Self> {
        let a = args & bitmask(LOCAL_ADDRESS_BITS);
        let b = (args >> LOCAL_ADDRESS_BITS) & bitmask(LOCAL_ADDRESS_BITS);
        let c =
            (args >> (2 * LOCAL_ADDRESS_BITS)) & bitmask(LOCAL_ADDRESS_BITS);
        Some(f(a as LocalAddress, b as LocalAddress, c as LocalAddress))
    }

    fn encode_packed_ai_args(a: LocalAddress, i: Immediate) -> Word {
        (a as Word) | ((i as Word) << LOCAL_ADDRESS_BITS)
    }

    fn decode_packed_ai_args(
        args: Word,
        f: impl FnOnce(LocalAddress, Immediate) -> Self,
    ) -> Option<Self> {
        let a = args & bitmask(LOCAL_ADDRESS_BITS);
        let i = (args >> LOCAL_ADDRESS_BITS) & bitmask(IMM_BITS);
        Some(f(a as LocalAddress, i as Immediate))
    }

    fn encode_packed_ix_args(ix: ExtendedImmediate) -> Word {
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

#[cfg(test)]
mod tests {
    use crate::{
        arch::{Word, LOCAL_ADDRESS_BITS},
        opcode::{Op, OPCODE_BITS},
    };

    #[test]
    fn encodes_correctly() {
        assert_eq!(0, Op::Mov(0, 0).encode_packed());
        assert_eq!(1, Op::MovI(0, 0).encode_packed());
        assert_eq!(
            (1 << OPCODE_BITS) | (1 << (OPCODE_BITS + LOCAL_ADDRESS_BITS)),
            Op::Mov(1, 1).encode_packed()
        );
        assert_eq!(Op::Ret.opcode() as Word, Op::Ret.encode_packed());
    }
}
