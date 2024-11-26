// Copyright (C) 2024 Ethan Uppal. All rights reserved.

// TODO: casting to signed probably doesn't work
use crate::{
    arch::{LocalAddress, Word, LOCAL_ADDRESS_BITS},
    bits,
    coding::Encodable,
    decode, encode
};

/// Smallest sized integer type that can fit an op code.
pub type RawOpCode = u8;

/// Smallest sized integer type that can fit an immediate value.
pub type Immediate = u16;

/// Smallest sized integer type that can fit an extended immediate value.
pub type ExtendedImmediate = u32;

/// Bits for opcode.
pub const OP_CODE_BITS: usize = 8; // not using ::BITS here because types are just smallest thing that can fit,
                                   // this is actual number of bits, which may be less.
/// Bits for immediate value.
pub const IMM_BITS: usize = 16;
/// Bits for extended immediate value.
pub const IMM_EXT_BITS: usize = 24;

/// The encodings are defined in:
/// 
/// - [`encode_opcode!`]
/// - [`decoded_opcode!`]
/// - [`check_encoding!`]
/// 
/// Adding a new encoding involves adding a new branch to each of these.
#[rustfmt::skip]
mod encoding {

    use super::*;
    use static_assertions::{const_assert, const_assert_eq};

//     +---------------------------------------------------------------------------------+
//     | Encodings (inspired by Lua). Ops fit in one `Word`.                             |
//     +---------------------------------------------------------------------------------+
//     | ABC (3 addresses):                                                              |
         const_assert_eq!(bits![Word], OP_CODE_BITS + 3 * LOCAL_ADDRESS_BITS);
//     | AB (2 addresses):                                                               | 
         const_assert!(OP_CODE_BITS + 2 * LOCAL_ADDRESS_BITS <= bits![Word]);
//     | AI (address+ immediate)                                                         | 
         const_assert_eq!(bits![Word], OP_CODE_BITS + LOCAL_ADDRESS_BITS + IMM_BITS);
//     | IX (extended immediate)                                                         | 
         const_assert_eq!(bits![Word], OP_CODE_BITS + IMM_EXT_BITS);
//     | N (no operands)                                                                 |
         const_assert!(OP_CODE_BITS <= bits![Word]);
//     +---------------------------------------------------------------------------------+
}

impl Encodable<Word> for RawOpCode {
    fn encode_into(&self) -> Word {
        *self as Word
    }

    fn decode_from(encoded: Word) -> Self {
        encoded as RawOpCode
    }
}

impl Encodable<Word> for Immediate {
    fn encode_into(&self) -> Word {
        *self as Word
    }

    fn decode_from(encoded: Word) -> Self {
        encoded as Immediate
    }
}

impl Encodable<Word> for ExtendedImmediate {
    fn encode_into(&self) -> Word {
        *self as Word
    }

    fn decode_from(encoded: Word) -> Self {
        encoded as ExtendedImmediate
    }
}

macro_rules! encode_opcode {
    ($self:expr; $opname:ident as ABC) => {
        if let Self::$opname(a, b, c) = $self {
            return Some(encode!(Word;
                [..OP_CODE_BITS..] = $self.opcode(),
                [..LOCAL_ADDRESS_BITS..] = *a,
                [..LOCAL_ADDRESS_BITS..] = *b,
                [..LOCAL_ADDRESS_BITS..] = *c
            ));
        }
    };
    ($self:expr; $opname:ident as AB) => {
        if let Self::$opname(a, b) = $self {
            return Some(encode!(Word;
                [..OP_CODE_BITS..] = $self.opcode(),
                [..LOCAL_ADDRESS_BITS..] = *a,
                [..LOCAL_ADDRESS_BITS..] = *b
            ));
        }
    };
    ($self:expr; $opname:ident as AI) => {
        if let Self::$opname(a, i) = $self {
            return Some(encode!(Word;
                [..OP_CODE_BITS..] = $self.opcode(),
                [..LOCAL_ADDRESS_BITS..] = *a,
                [..IMM_BITS..] = *i
            ));
        }
    };
    ($self:expr; $opname:ident as N) => {
        return Some(encode!(Word;
            [..OP_CODE_BITS..] = $self.opcode()
        ));
    };
}

macro_rules! decoded_opcode {
    ($encoded:expr; $opname:ident as ABC) => {
        decode!($encoded; Word;
            @(
                _op: RawOpCode = [..OP_CODE_BITS..],
                a: $crate::arch::LocalAddress = [..LOCAL_ADDRESS_BITS..],
                b: $crate::arch::LocalAddress = [..LOCAL_ADDRESS_BITS..],
                c: $crate::arch::LocalAddress = [..LOCAL_ADDRESS_BITS..]
            ) => Self::$opname(a, b, c)
        )
    };
    ($encoded:expr; $opname:ident as AB) => {
        decode!($encoded; Word;
            @(
                _op: RawOpCode = [..OP_CODE_BITS..],
                a: $crate::arch::LocalAddress = [..LOCAL_ADDRESS_BITS..],
                b: $crate::arch::LocalAddress = [..LOCAL_ADDRESS_BITS..]
            ) => Self::$opname(a, b)
        )
    };
    ($encoded:expr; $opname:ident as AI) => {
        decode!($encoded; Word;
            @(
                _op: RawOpCode = [..OP_CODE_BITS..],
                a: $crate::arch::LocalAddress = [..LOCAL_ADDRESS_BITS..],
                i: Immediate = [..IMM_BITS..]
            ) => Self::$opname(a, i)
        )
    };
    ($encoded:expr; $opname:ident as N) => {
        decode!($encoded; Word;
            @(
                _op: RawOpCode = [..OP_CODE_BITS..]
            ) => Self::$opname()
        )
    };
}

macro_rules! implement_opcodes {
    ($T:ty; $($opname:ident as $encoding:ident),*) => {
        impl $T {
            pub fn opcode(&self) -> RawOpCode {
                let discr = 0;
                $(
                    if let Self::$opname(..) = self {
                       return discr;
                    }
                    let discr = discr + 1;
                )*
                let _ = discr; // #[allow(unused)] the last usage
                unreachable!()
            }

            pub fn encode_packed(&self) -> Option<Word> {
                $(
                    encode_opcode!(self; $opname as $encoding);
                )*
            }

            pub fn decode_packed(encoded: Word) -> Option<$T> {
                let opcode = encoded & ((1 << OP_CODE_BITS) - 1);
                let discr = 0;
                $(
                    if opcode == discr {
                        return Some(
                            decoded_opcode!(encoded; $opname as $encoding)
                        );
                    }
                    let discr = discr + 1;
                )*
                let _ = discr; // #[allow(unused)] the last usage
                None
            }
        }
    };
}

macro_rules! check_encoding {
    (ABC) => {};
    (AB) => {};
    (AI) => {};
    (Ix) => {};
    (N) => {};
    ($other:ident) => {
        compile_error!(concat!(
            "Invalid encoding: ",
            stringify!($other),
            "; valid encodings include: ABC, AB, AI, Ix, J"
        ));
    };
}

macro_rules! opcodes {
    (#[derive($($derive:ident),* $(,)?)] $vis:vis enum $T:ident {
        $(
            $(#[doc = $doc:literal])?
            $opname:ident($($param:ty),* $(,)?) encode $encoding:ident
        ),* $(,)?
    }) => {
        paste::paste! {
            #[derive($($derive),*)]
            $vis enum $T {
                $(
                    #[doc = $($doc)* "\n\nUses the `" $encoding "` encoding"]
                    $opname($($param),*)
                ),*
            }
        }
        $(
            check_encoding!($encoding);
        )*

        implement_opcodes! { $T; $($opname as $encoding),* }
    };
}

opcodes! {
    #[derive(Clone, Copy, Debug)]
    pub enum Op {
        Mov(LocalAddress, LocalAddress) encode AB,
        MovI(LocalAddress, Immediate) encode AI,
        Add(LocalAddress, LocalAddress, LocalAddress) encode ABC,
        Ret() encode N,  // TODO: avoid parens here?
    }
}

pub enum OpCodingError {
    NoSpace,
    Other
}

pub trait EncodeIntoOpStream {
    /// Encodes a representation of an operation into a `stream` at the given
    /// `index`.
    fn encode_into(
        &self, stream: &mut [Word], index: &mut usize
    ) -> Result<(), OpCodingError>;
}

impl Op {
    /// Decodes an `Op` from a `stream` starting at the given `index`. Returns
    /// the `Op` and the length used from the stream, in the case of
    /// multi-word encoding.
    pub fn decode_from(
        stream: &[Word], index: usize
    ) -> Result<(Op, usize), OpCodingError> {
        Ok((
            Self::decode_packed(stream[index]).ok_or(OpCodingError::Other)?,
            1
        ))
    }
}

// so I can easily switch between packed and VL encoding
impl EncodeIntoOpStream for Op {
    fn encode_into(
        &self, stream: &mut [Word], index: &mut usize
    ) -> Result<(), OpCodingError> {
        if *index >= stream.len() {
            return Err(OpCodingError::NoSpace);
        }
        stream[*index] = self.encode_packed().ok_or(OpCodingError::Other)?;
        *index += 1;
        Ok(())
    }
}

impl EncodeIntoOpStream for Word {
    fn encode_into(
        &self, stream: &mut [Word], index: &mut usize
    ) -> Result<(), OpCodingError> {
        stream[*index] = *self;
        *index += 1;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        arch::LOCAL_ADDRESS_BITS,
        opcode::{Op, OP_CODE_BITS}
    };

    #[test]
    fn encodes_correctly() {
        assert_eq!(Some(0), Op::Mov(0, 0).encode_packed());
        assert_eq!(Some(1), Op::MovI(0, 0).encode_packed());
        assert_eq!(
            Some(
                (1 << OP_CODE_BITS)
                    | (1 << (OP_CODE_BITS + LOCAL_ADDRESS_BITS))
            ),
            Op::Mov(1, 1).encode_packed()
        );
        assert_eq!(Some(Op::Ret().opcode() as u32), Op::Ret().encode_packed());
    }
}
