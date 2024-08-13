// Copyright (C) 2024 Ethan Uppal. All rights reserved.

// this file is a mess
// PLEASE clean it up
// TODO: casting to signed probably doesn't work

use crate::{
    arch::{Word, REGISTER_BITS},
    bits
};
use paste::paste;
use static_assertions::{const_assert, const_assert_eq};

pub const OP_BITS: usize = 8;
pub const IMM_BITS: usize = 16;
pub const OFF_BITS: usize = 24;

// Encodings (inspired by Lua):
// - The least significant 8 bits are the opcode
// - in the ABC encoding, the next three sets of 8 bits represent registers
const_assert_eq!(bits![Word], OP_BITS + 3 * REGISTER_BITS);
// - in the AI encoding, the next 8 bits represent a register and the final 16
//   represent
const_assert_eq!(bits![Word], OP_BITS + REGISTER_BITS + IMM_BITS);
// - in the J encoding, the next 24 bits represent a signed offset
const_assert_eq!(bits![Word], OP_BITS + OFF_BITS);
// - AB encoding
const_assert!(OP_BITS + 2 * REGISTER_BITS <= bits![Word]);
// The encodings are defined in `encode_opcode!`, `decoded_opcode!`, and
// `opcodes!` macros.

macro_rules! encode {
    ($T:ty; $([..$($width:literal)?$($width2:ident)?..] = $int:expr),* $(,[..*] = $final:expr)?) => {
        {
            let mut offset = 0;
            let mut result: $T = 0;
            $(
                result |= (($int as $T) << offset);
                offset += $($width)* $($width2)*;
            )*
            $(
                result |= (($final as $T) << offset);
            )*
            let _ = offset;
            result
        }
    };
}

macro_rules! decode {
    (
        $encoded:expr; $TEnc:ty;
        @($($out:ident $(: $T:ty)? = [..$($width:literal)?$($width2:ident)?..]),*)
        => $block:expr
    ) => {{
        let mut __offset = 0;
        $(
            let paste!([<__width $out>]) = $($width)*$($width2)* as $TEnc;
            let $out $(: $T)* = ((($encoded >> __offset) & ((1 << paste!([<__width $out>])) - 1)) $(as $T)*);
            __offset += paste!([<__width $out>]);
        )*
        $block
    }};
}

macro_rules! encode_opcode {
    ($self:expr; $opname:ident as ABC) => {
        if let Self::$opname(a, b, c) = $self {
            return Some(encode!(Word;
                [..OP_BITS..] = $self.opcode(),
                [..REGISTER_BITS..] = *a,
                [..REGISTER_BITS..] = *b,
                [..REGISTER_BITS..] = *c
            ));
        }
    };
    ($self:expr; $opname:ident as AB) => {
        if let Self::$opname(a, b) = $self {
            return Some(encode!(Word;
                [..OP_BITS..] = $self.opcode(),
                [..REGISTER_BITS..] = *a,
                [..REGISTER_BITS..] = *b
            ));
        }
    };
    ($self:expr; $opname:ident as AI) => {
        if let Self::$opname(a, i) = $self {
            return Some(encode!(Word;
                [..OP_BITS..] = $self.opcode(),
                [..REGISTER_BITS..] = *a,
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
                _op = [..OP_BITS..],
                a: $crate::arch::Register = [..REGISTER_BITS..],
                b: $crate::arch::Register = [..REGISTER_BITS..],
                c: $crate::arch::Register = [..REGISTER_BITS..]
            ) => Self::$opname(a, b, c)
        )
    };
    ($encoded:expr; $opname:ident as AB) => {
        decode!($encoded; $crate::arch::Word;
            @(
                _op = [..OP_BITS..],
                a: $crate::arch::Register = [..REGISTER_BITS..],
                b: $crate::arch::Register = [..REGISTER_BITS..]
            ) => Self::$opname(a, b)
        )
    };
    ($encoded:expr; $opname:ident as AI) => {
        decode!($encoded; $crate::arch::Word;
            @(
                _op = [..OP_BITS..],
                a: $crate::arch::Register = [..REGISTER_BITS..],
                i: $crate::arch::Word = [..IMM_BITS..]
            ) => Self::$opname(a, i)
        )
    };
    ($encoded:expr; $opname:ident as J) => {
        decode!($encoded; $crate::arch::Word;
            @(
                _op = [..OP_BITS..],
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
                        return Some(decoded_opcode!(encoded; $opname as $encoding));
                    }
                    let discr = discr + 1;
                )*
                let _ = discr; // #[allow(unused)] the last usage
                None
            }
        }
    };
}

macro_rules! opcodes {
    ($vis:vis enum $T:ident {
        $($opname:ident as $encoding:ident $(: $doc:literal)?),* $(,)?
    }) => {
        opcodes! { @parse
            $vis enum $T;
            {};
            $($opname as $encoding $(: $doc)*),*
        }

        implement_opcodes! { $T; Word; $($opname as $encoding),* }
    };

    (@parse
        $vis:vis enum $T:ident;
        { $($opname_acc:ident($($variant_acc:ty),*)),* };
        $first_opname:ident as ABC $(: $first_doc:literal)?
        $(, $opname:ident as $encoding:ident $(: $doc:literal)?)*
    ) => {
        opcodes! { @parse
            $vis enum $T;
            {
                $($opname_acc($($variant_acc),*),)*
                // #[doc = concat!($($first_doc,)* "\n\nUses the ABC encoding.")]
                $first_opname($crate::arch::Register, $crate::arch::Register, $crate::arch::Register)
            };
            $($opname as $encoding $(: $doc)*),*
        }
    };

    (@parse
        $vis:vis enum $T:ident;
        { $($opname_acc:ident($($variant_acc:ty),*)),* };
        $first_opname:ident as AB $(: $first_doc:literal)?
        $(, $opname:ident as $encoding:ident $(: $doc:literal)?)*
    ) => {
        opcodes! { @parse
            $vis enum $T;
            {
                $($opname_acc($($variant_acc),*),)*
                // #[doc = concat!($($first_doc,)* "\n\nUses the AB encoding.")]
                $first_opname($crate::arch::Register, $crate::arch::Register)
            };
            $($opname as $encoding $(: $doc)*),*
        }
    };

    (@parse
        $vis:vis enum $T:ident;
        { $($opname_acc:ident($($variant_acc:ty),*)),* };
        $first_opname:ident as AI $(: $first_doc:literal)?
        $(, $opname:ident as $encoding:ident $(: $doc:literal)?),*
    ) => {
        opcodes! { @parse
            $vis enum $T;
            {
                $($opname_acc($($variant_acc),*),)*
                // #[doc = concat!($($first_doc,)* "\n\nUses the AI encoding.")]
                $first_opname($crate::arch::Register, $crate::arch::Word)
            };
            $($opname as $encoding $(: $doc)*),*
        }
    };

    (@parse
        $vis:vis enum $T:ident;
        { $($opname_acc:ident($($variant_acc:ty),*)),* };
        $first_opname:ident as J $(: $first_doc:literal)?
        $(, $opname:ident as $encoding:ident $(: $doc:literal)?)*
    ) => {
        opcodes! { @parse
            $vis enum $T;
            {
                $($opname_acc($($variant_acc),*),)*
                $first_opname($crate::arch::SignedWord)
            };
            $($opname as $encoding $(: $doc)*),*
        }
    };

    (@parse
        $vis:vis enum $T:ident;
        { $($opname_acc:ident($($variant_acc:ty),*)),* };
    ) => {
        #[derive(Clone, Copy)]
        $vis enum $T { $($opname_acc($($variant_acc),*)),* }
    };
}

opcodes! {
    pub enum Op {
        Mov as AB,
        MovI as AI,
        Add as ABC,
    }
}

// so I can easily switch between packed and VL encoding
impl Op {
    pub fn encode_into(
        &self, stream: &mut [Word], index: &mut usize
    ) -> Option<()> {
        stream[*index] = self.encode_packed()?;
        *index += 1;
        Some(())
    }

    pub fn decode_from(stream: &[Word], index: usize) -> Option<(Self, usize)> {
        Some((Self::decode_packed(stream[index])?, 1))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        arch::REGISTER_BITS,
        opcode::{Op, OP_BITS}
    };

    #[test]
    fn encodes_correctly() {
        assert_eq!(Some(0), Op::Mov(0, 0).encode_packed());
        assert_eq!(Some(1), Op::MovI(0, 0).encode_packed());
        assert_eq!(
            Some((1 << OP_BITS) | (1 << (OP_BITS + REGISTER_BITS))),
            Op::Mov(1, 1).encode_packed()
        );
    }
}
