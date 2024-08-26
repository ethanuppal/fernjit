// Copyright (C) 2024 Ethan Uppal. All rights reserved.

// TODO: casting to signed probably doesn't work

use crate::{
    arch::{Offset, Word, ADDRESS_BITS},
    bits
};

/// Bits for opcode.
pub const OP_BITS: usize = 7;
/// Bits for immediate value.
pub const IMM_BITS: usize = 38;
/// Bits for extended immediate value.
pub const IMM_EXT_BITS: usize = 57;
/// Bits for signed offset.
pub const OFF_BITS: usize = ADDRESS_BITS;

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

//     +-----------------------------------------------------------------------+
//     | Encodings (inspired by Lua)                                           |
//     +-----------------------------------------------------------------------+
//     | ABC (3 addresses):                                                    |
         const_assert_eq!(bits![Word], OP_BITS + 3 * ADDRESS_BITS);
//     | AB (2 addresses):                                                     | 
         const_assert!(OP_BITS + 2 * ADDRESS_BITS <= bits![Word]);
//     | AI (address+ immediate)                                             | 
         const_assert_eq!(bits![Word], OP_BITS + ADDRESS_BITS + IMM_BITS);
//     | IX (extended immediate)                                               | 
         const_assert_eq!(bits![Word], OP_BITS + IMM_EXT_BITS);
//     | J (signed offset)                                                     |
         const_assert!(OP_BITS + OFF_BITS < bits![Word]);
//     +-----------------------------------------------------------------------+
}

/// Iteratively constructs a bitset of a given type from bit fields.
///
/// # Example
///
/// ```
/// use fernjit::encode;
///
/// assert_eq!((1 << 8) | (2 << 16), encode!(u32;
///     [..8..] = 0,
///     [..8..] = 1,
///     [..*] = 2 // optional
/// ));
/// ```
#[macro_export] // for doctest
macro_rules! encode {
    (
        $T:ty;
        $([..$($width:literal)?$($width2:ident)?..] = $int:expr),*
        $(,[..*] = $final:expr)?
    ) => {
        {
            let mut offset = 0;
            let mut result: $T = 0;
            $(
                let transmuted_int: $T = unsafe {
                    std::mem::transmute($int)
                };
                let mask: $T = (((1 as $T) << $($width)* $($width2)*) - 1) as $T;
                result |= ((transmuted_int & mask) << offset);
                offset += $($width)* $($width2)*;
            )*
            $(
                let transmuted_final: $T = unsafe {
                    std::mem::transmute($final)
                };
                let mask: $T = ((1 << offset) - 1) as $T;
                result |= ((transmuted_final & mask) << offset);
            )*
            let _ = offset;
            result
        }
    };
}

/// Deconstructs a bitset of a given type into bitfields of given types.
///
/// # Example
///
/// ```
/// use fernjit::decode;
///
/// decode!((1 << 8) | (2 << 16); u32;
///     @(a: u32 = [..8..], b = [..8..], c = [..8..]) => {
///         assert_eq!(0, a);
///         assert_eq!(1, b);
///         assert_eq!(2, c);
///     }
/// );
/// ```
#[macro_export] // for doctest
macro_rules! decode {
    (
        $encoded:expr; $TEnc:ty;
        @($($out:ident $(: $T:ty)? =
            [..$($width:literal)?$($width2:ident)?..]),*)
        => $block:expr
    ) => {{
        let mut __offset = 0;
        const TENC_BITS: $TEnc = $crate::bits![$TEnc] as $TEnc;
        $(
            let paste::paste!([<__width $out>]) =
                $($width)*$($width2)* as $TEnc;
            let mask = (((1 as $TEnc) << paste::paste!([<__width $out>])) - 1) as $TEnc;
            let unsigned_out = (($encoded >> __offset) & mask) as $TEnc;
            let $out $(: $T)* = (((unsigned_out << (TENC_BITS - paste::paste!([<__width $out>])))) >> (TENC_BITS - paste::paste!([<__width $out>]))).try_into().unwrap();
            __offset += paste::paste!([<__width $out>]);
        )*
        $block
    }};
}

macro_rules! encode_opcode {
    ($self:expr; $opname:ident as ABC) => {
        if let Self::$opname(a, b, c) = $self {
            return Some(encode!(Word;
                [..OP_BITS..] = $self.opcode(),
                [..ADDRESS_BITS..] = *a,
                [..ADDRESS_BITS..] = *b,
                [..ADDRESS_BITS..] = *c
            ));
        }
    };
    ($self:expr; $opname:ident as AB) => {
        if let Self::$opname(a, b) = $self {
            return Some(encode!(Word;
                [..OP_BITS..] = $self.opcode(),
                [..ADDRESS_BITS..] = *a,
                [..ADDRESS_BITS..] = *b
            ));
        }
    };
    ($self:expr; $opname:ident as AI) => {
        if let Self::$opname(a, i) = $self {
            return Some(encode!(Word;
                [..OP_BITS..] = $self.opcode(),
                [..ADDRESS_BITS..] = *a,
                [..IMM_BITS..] = *i
            ));
        }
    };
    ($self:expr; $opname:ident as J) => {
        if let Self::$opname(off) = $self {
            return Some(encode!(Word;
                [..OP_BITS..] = $self.opcode(),
                [..OFF_BITS..] = *off,
            ));
        }
    };
}

macro_rules! decoded_opcode {
    ($encoded:expr; $opname:ident as ABC) => {
        decode!($encoded; $crate::arch::Word;
            @(
                _op: u8 = [..OP_BITS..],
                a: $crate::arch::Offset = [..ADDRESS_BITS..],
                b: $crate::arch::Offset = [..ADDRESS_BITS..],
                c: $crate::arch::Offset = [..ADDRESS_BITS..]
            ) => Self::$opname(a, b, c)
        )
    };
    ($encoded:expr; $opname:ident as AB) => {
        decode!($encoded; $crate::arch::Word;
            @(
                _op: u8 = [..OP_BITS..],
                a: $crate::arch::Offset = [..ADDRESS_BITS..],
                b: $crate::arch::Offset = [..ADDRESS_BITS..]
            ) => Self::$opname(a, b)
        )
    };
    ($encoded:expr; $opname:ident as AI) => {
        decode!($encoded; $crate::arch::Word;
            @(
                _op: u8 = [..OP_BITS..],
                a: $crate::arch::Offset = [..ADDRESS_BITS..],
                i: $crate::arch::Word = [..IMM_BITS..]
            ) => Self::$opname(a, i)
        )
    };
    ($encoded:expr; $opname:ident as J) => {
        decode!($encoded; $crate::arch::Word;
            @(
                _op: u8 = [..OP_BITS..],
                off: $crate::arch::Word = [..OFF_BITS..]
            ) => Self::$opname(off)
        )
    };
}

macro_rules! implement_opcodes {
    ($T:ty; $TEnc:ty; $($opname:ident as $encoding:ident),*) => {
        impl $T {
            pub fn opcode(&self) -> $TEnc {
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

            pub fn encode_packed(&self) -> Option<$TEnc> {
                $(
                    encode_opcode!(self; $opname as $encoding);
                )*
                None
            }

            pub fn decode_packed(encoded: $TEnc) -> Option<$T> {
                let opcode = encoded & ((1 << OP_BITS) - 1);
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
    (J) => {};
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
            $opname:ident($($variant:ty),* $(,)?) encode $encoding:ident
        ),* $(,)?
    }) => {
        paste::paste! {
            #[derive($($derive),*)]
            $vis enum $T {
                $(
                    #[doc = $($doc)* "\n\nUses the `" $encoding "` encoding"]
                    $opname($($variant),*)
                ),*
            }
        }
        $(
            check_encoding!($encoding);
        )*

        implement_opcodes! { $T; Word; $($opname as $encoding),* }
    };
}

opcodes! {
    #[derive(Clone, Copy, Debug)]
    pub enum Op {
        Mov(Offset, Offset) encode AB,
        MovI(Offset, Word) encode AI,
        Add(Offset, Offset, Offset) encode ABC,
    }
}

pub enum OpCodingError {
    NoSpace,
    Other
}

pub trait EncodeAsOp {
    fn encode_into(
        &self, stream: &mut [Word], index: &mut usize
    ) -> Result<(), OpCodingError>;
}

// so I can easily switch between packed and VL encoding
impl EncodeAsOp for Op {
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
impl Op {
    pub fn decode_from(
        stream: &[Word], index: usize
    ) -> Result<(Op, usize), OpCodingError> {
        Ok((
            Self::decode_packed(stream[index]).ok_or(OpCodingError::Other)?,
            1
        ))
    }
}

impl EncodeAsOp for Word {
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
        arch::ADDRESS_BITS,
        opcode::{Op, OP_BITS}
    };

    #[test]
    fn encodes_correctly() {
        assert_eq!(Some(0), Op::Mov(0, 0).encode_packed());
        assert_eq!(Some(1), Op::MovI(0, 0).encode_packed());
        assert_eq!(
            Some((1 << OP_BITS) | (1 << (OP_BITS + ADDRESS_BITS))),
            Op::Mov(1, 1).encode_packed()
        );
    }
}
