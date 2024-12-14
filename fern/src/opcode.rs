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
    Mov(LocalAddress, LocalAddress),
    MovI(LocalAddress, Immediate),
    Add(LocalAddress, LocalAddress, LocalAddress),
    Call(ExtendedImmediate),
    Ret,
}

impl Op {
    pub fn encode_packed(&self) -> Word {
        let encoded_args = match *self {
            Self::Mov(a, b) => Self::encode_packed_ab_args(a, b),
            Self::MovI(a, i) => Self::encode_packed_ai_args(a, i),
            Self::Add(a, b, c) => Self::encode_packed_abc_args(a, b, c),
            Self::Call(ix) => Self::encode_packed_ix_args(ix),
            Self::Ret => 0,
        };

        (self.opcode() as Word) | (encoded_args << OPCODE_BITS)
    }

    pub fn decode_packed(word: Word) -> Option<Self> {
        let opcode = (word & bitmask(OPCODE_BITS)) as RawOpCode;
        let args = word >> OPCODE_BITS;
        match opcode {
            Self::MOV_TAG => Self::decode_packed_ab_args(args, Self::Mov),
            Self::MOVI_TAG => Self::decode_packed_ai_args(args, Self::MovI),
            Self::ADD_TAG => Self::decode_packed_abc_args(args, Self::Add),
            Self::CALL_TAG => Self::decode_packed_ix_args(args, Self::Call),
            Self::RET_TAG => Some(Self::Ret),
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
        args: Word, f: impl FnOnce(LocalAddress, LocalAddress) -> Self,
    ) -> Option<Self> {
        let a = args & bitmask(LOCAL_ADDRESS_BITS);
        let b = (args >> LOCAL_ADDRESS_BITS) & bitmask(LOCAL_ADDRESS_BITS);
        Some(f(a as LocalAddress, b as LocalAddress))
    }

    fn encode_packed_abc_args(
        a: LocalAddress, b: LocalAddress, c: LocalAddress,
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
        args: Word, f: impl FnOnce(LocalAddress, Immediate) -> Self,
    ) -> Option<Self> {
        let a = args & bitmask(LOCAL_ADDRESS_BITS);
        let i = (args >> LOCAL_ADDRESS_BITS) & bitmask(IMM_BITS);
        Some(f(a as LocalAddress, i as Immediate))
    }

    fn encode_packed_ix_args(ix: ExtendedImmediate) -> Word {
        ix as Word
    }

    fn decode_packed_ix_args(
        args: Word, f: impl FnOnce(ExtendedImmediate) -> Self,
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

// do we still want this?
//
// // pub enum OpCodingError {
//     NoSpace,
//     Other,
// }
//
// pub trait EncodeIntoOpStream {
//     /// Encodes a representation of an operation into a `stream` at the given
//     /// `index`.
//     fn encode_into(
//         &self, stream: &mut [Word], index: &mut usize,
//     ) -> Result<(), OpCodingError>;
// }
//
// impl Op {
//     /// Decodes an `Op` from a `stream` starting at the given `index`.
// Returns     /// the `Op` and the length used from the stream, in the case of
//     /// multi-word encoding.
//     pub fn decode_from(
//         stream: &[Word], index: usize,
//     ) -> Result<(Op, usize), OpCodingError> {
//         Ok((
//             Self::decode_packed(stream[index]).ok_or(OpCodingError::Other)?,
//             1,
//         ))
//     }
// }
//
// // so I can easily switch between packed and VL encoding
// impl EncodeIntoOpStream for Op {
//     fn encode_into(
//         &self, stream: &mut [Word], index: &mut usize,
//     ) -> Result<(), OpCodingError> {
//         if *index >= stream.len() {
//             return Err(OpCodingError::NoSpace);
//         }
//         stream[*index] = self.encode_packed().ok_or(OpCodingError::Other)?;
//         *index += 1;
//         Ok(())
//     }
// }
//
// impl EncodeIntoOpStream for Word {
//     fn encode_into(
//         &self, stream: &mut [Word], index: &mut usize,
//     ) -> Result<(), OpCodingError> {
//         stream[*index] = *self;
//         *index += 1;
//         Ok(())
//     }
// }
