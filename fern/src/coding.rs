// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

use crate::arch::Word;

/// Iteratively constructs a bitset of a given type from bit fields.
#[macro_export]
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
                let encoded_int: $T = $int.encode_as_word();
                let mask: $T = (((1 as $T) << $($width)* $($width2)*) - 1) as $T;
                result |= ((encoded_int & mask) << offset);
                offset += $($width)* $($width2)*;
            )*
            $(
                let encoded_final: $T = $final.encode_as_word();
                let mask: $T = ((1 << offset) - 1) as $T;
                result |= ((encoded_final & mask) << offset);
            )*
            let _ = offset;
            result
        }
    };
}

/// Traits for types that can be encoded as part of an [Op].
pub trait CodeAsWord {
    /// Encodes `self` into a `Word`. Higher bits will be chopped off
    /// if fitting a larger type into a smaller slot. For example, if you
    /// try to encode a `0b11110000u8` into a 4-bit slot of a `Word`, and
    /// your `encode_into` implementation just uses `as Word`, you'll only
    /// get `0b0000` encoded.
    fn encode_as_word(&self) -> Word;

    // Decodes `self` from a `Word`. If `Self` is `n` bits, then the least
    // siginificant `n` bits of `encoded` contain the data to decode.
    fn decode_from_word(encoded: Word) -> Self;
}

/// Deconstructs a bitset of a given type into bitfields of given types.
#[macro_export]
macro_rules! decode {
    (
        $encoded:expr; $TEnc:ty;
        @($($out:ident: $T:ty =
            [..$($width:literal)?$($width2:ident)?..]),*)
        => $block:expr
    ) => {{
        let mut __offset = 0;
        $(
            let op_width = $($width)*$($width2)* as $TEnc;
            let mask = (1 as $TEnc).checked_shl(op_width).unwrap_or(0).wrapping_sub(1);
            let unsigned_out = ($encoded >> __offset) & mask;
            let $out = <$T>::decode_from_word(unsigned_out);
            __offset += op_width;
        )*
        $block
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    // so we don't conflict with regular u8 impl
    struct Testu8(u8);
    impl CodeAsWord for Testu8 {
        fn encode_as_word(&self) -> Word {
            self.0 as Word
        }

        fn decode_from_word(encoded: Word) -> Self {
            Self(encoded as u8)
        }
    }

    struct Testu16(u16);
    impl CodeAsWord for Testu16 {
        fn encode_as_word(&self) -> Word {
            self.0 as Word
        }

        fn decode_from_word(encoded: Word) -> Self {
            Self(encoded as u16)
        }
    }

    struct Testi8(i8);
    impl CodeAsWord for Testi8 {
        fn encode_as_word(&self) -> Word {
            self.0.to_ne_bytes()[0] as Word
        }

        fn decode_from_word(encoded: Word) -> Self {
            Self(i8::from_ne_bytes([encoded as u8]))
        }
    }

    struct Testi32(i32);
    impl CodeAsWord for Testi32 {
        fn encode_as_word(&self) -> Word {
            Word::from_ne_bytes(self.0.to_ne_bytes())
        }

        fn decode_from_word(encoded: Word) -> Self {
            Self(i32::from_ne_bytes(encoded.to_ne_bytes()))
        }
    }

    #[test]
    fn encodes_correctly() {
        assert_eq!(
            (1 << 8) | (2 << 16),
            encode!(Word;
                [..8..] = Testu8(0),
                [..8..] = Testu8(1),
                [..*] = Testu16(2) // optional
            )
        );
    }

    #[test]
    fn encodes_signed_correctly() {
        assert_eq!(
            0x000000fe,
            encode!(Word;
                [..8..] = Testi8(-2)
            )
        );
    }

    #[test]
    fn decodes_correctly() {
        decode!(1; Word;
            @(a: Word = [..32..]) => {
                assert_eq!(1, a);
            }
        );

        decode!((1 << 8) | (2 << 16); Word;
            @(a: u8 = [..8..], b: u8 = [..8..], c: u8 = [..8..]) => {
                assert_eq!(0, a);
                assert_eq!(1, b);
                assert_eq!(2, c);
            }
        );
    }

    #[test]
    fn decodes_signed_correctly() {
        decode!(0xfffffffe; Word;
            @(a: Testi32 = [..32..]) => {
                assert_eq!(-2, a.0);
            }
        );

        decode!((1 << 8) | (2 << 16); Word;
            @(a: Testi8 = [..8..], b: Testi8 = [..8..], c: Testi8 = [..8..]) => {
                assert_eq!(0, a.0);
                assert_eq!(1, b.0);
                assert_eq!(2, c.0);
            }
        );
    }
}
