// Copyright (C) 2024 Ethan Uppal. All rights reserved.

// TODO: casting to signed probably doesn't work
use crate::{
    arch::{LocalAddress, Word, LOCAL_ADDRESS_BITS},
    bits
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

/// Iteratively constructs a bitset of a given type from bit fields.
///
/// TODO: (once the change happens, add this) One must take great care when
/// encoding structs. Ensure the memory layout is correct. If you try to encode
/// a larger struct into a smaller slot, the top bits will be chopped off, as
/// with any value!
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
                // TODO: wrong, transmute might actually fail to compile if $int is bigger that width, which is a scenario we have to allow
                let encoded_int: $T = $int.encode_into_op();
                let mask: $T = (((1 as $T) << $($width)* $($width2)*) - 1) as $T;
                result |= ((encoded_int & mask) << offset);
                offset += $($width)* $($width2)*;
            )*
            $(
                let encoded_final: $T = $final.encode_into_op();
                let mask: $T = ((1 << offset) - 1) as $T;
                result |= ((encoded_final & mask) << offset);
            )*
            let _ = offset;
            result
        }
    };
}

// TODO: better name?
/// Traits for types that can be encoded as part of an Op
trait EncodeIntoOp {
    // TODO: this doc sucks
    /// Encodes `self` into a raw op. Higher bits will be chopped off if fitting
    /// a larger type into a smaller slot. For example, if you try to encode a
    /// `0b11110000u8` into a 4-bit slot, and your `encode_into_op`
    /// implementation just uses `as Word`, you'll only get `0b0000`
    /// encoded.  
    fn encode_into_op(&self) -> Word;
}

impl EncodeIntoOp for u8 {
    fn encode_into_op(&self) -> Word {
        *self as Word
    }
}

impl EncodeIntoOp for u16 {
    fn encode_into_op(&self) -> Word {
        *self as Word
    }
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
