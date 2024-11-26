/// Iteratively constructs a bitset of a given type from bit fields.
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
                let encoded_int: $T = $int.encode_into();
                let mask: $T = (((1 as $T) << $($width)* $($width2)*) - 1) as $T;
                result |= ((encoded_int & mask) << offset);
                offset += $($width)* $($width2)*;
            )*
            $(
                let encoded_final: $T = $final.encode_into();
                let mask: $T = ((1 << offset) - 1) as $T;
                result |= ((encoded_final & mask) << offset);
            )*
            let _ = offset;
            result
        }
    };
}

/// Traits for types that can be encoded as part of an Op
pub trait Encodable<T> {
    /// Encodes `self` into a larger sequence. Higher bits will be chopped off
    /// if fitting a larger type into a smaller slot. For example, if you
    /// try to encode a `0b11110000u8` into a 4-bit slot of a `u32`, and
    /// your `encode_into_op` implementation just uses `as u32`, you'll only
    /// get `0b0000` encoded.  
    fn encode_into(&self) -> T;
}

// TODO: idk if decode is as generic as encode... does it work with signed?
/// Deconstructs a bitset of a given type into bitfields of given types.
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

#[cfg(test)]
mod tests {
    use super::*;

    // so we don't conflict with regular u8 impl
    struct Testu8(u8);
    impl Encodable<u32> for Testu8 {
        fn encode_into(&self) -> u32 {
            self.0 as u32
        }
    }

    struct Testu16(u16);
    impl Encodable<u32> for Testu16 {
        fn encode_into(&self) -> u32 {
            self.0 as u32
        }
    }

    #[test]
    fn encodes_correctly() {
        assert_eq!(
            (1 << 8) | (2 << 16),
            encode!(u32;
                [..8..] = Testu8(0),
                [..8..] = Testu8(1),
                [..*] = Testu16(2) // optional
            )
        );
    }

    #[test]
    fn decodes_correctly() {
        decode!((1 << 8) | (2 << 16); u32;
            @(a: u32 = [..8..], b = [..8..], c = [..8..]) => {
                assert_eq!(0, a);
                assert_eq!(1, b);
                assert_eq!(2, c);
            }
        );
    }
}
