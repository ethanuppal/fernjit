// Copyright (C) 2024 Ethan Uppal. All rights reserved.

use crate::arch::{Address, Register, Word, REGISTER_BITS};

pub type InstructionRaw = Word;

#[derive(Clone, Copy)]
pub enum Instruction {
    Mov(Register, Register),
    MovI(Register, Word),
    Load(Address, Register),
    LoadI(Address, Word),
    DebugReg(Register)
}

macro_rules! slice {
    ([$low:literal..$high:literal] in $int:expr) => {{
        let mask = 1 << ($high - $low) - 1;
        ($int >> $low) & mask
    }};
    ([($low:expr)..($high:expr)] in $int:expr) => {{
        let mask = 1 << ($high - $low) - 1;
        ($int >> $low) & mask
    }};
}

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
            result
        }
    };
}

macro_rules! decode {
    ([$low:literal..$high:literal] in $raw:expr; $($pat:pat => @($($out:ident = [..$($width:literal)?$($width2:ident)?..]),*) $block:expr),+) => {
        {
            let mut offset = $high;
            match slice!([$low..$high] in $raw) {
                $(
                    $pat => {
                        $(
                            let $out = slice!([(offset)..(offset + $($width)*$($width2)*)] in $raw);
                            offset += $($width)*$($width2)*;
                        )*
                        $block
                    }
                ),+
            }
        }
    };
}

impl Instruction {
    pub fn encode(&self) -> Option<InstructionRaw> {
        Some(match *self {
            Self::Mov(dest, src) => encode!(InstructionRaw;
                [..4..] = 0,
                [..REGISTER_BITS..] = dest,
                [..REGISTER_BITS..] = src
            ),
            Self::MovI(dest, value) => encode!(InstructionRaw;
                [..4..] = 1,
                [..REGISTER_BITS..] = dest,
                [..*] = value
            ),
            Self::Load(load, src) => encode!(InstructionRaw;
                [..4..] = 2,
                [..REGISTER_BITS..] = load,
                [..REGISTER_BITS..] = src
            ),
            Self::LoadI(load, value) => encode!(InstructionRaw;
                [..4..] = 3,
                [..REGISTER_BITS..] = load,
                [..*] = value
            ),
            Self::DebugReg(reg) => encode!(InstructionRaw;
                [..4..] = 4,
                [..REGISTER_BITS..] = reg
            )
        })
    }

    pub fn decode(raw: InstructionRaw) -> Option<Instruction> {
        decode!([0..4] in raw;
            0 => @(dest = [..REGISTER_BITS..], src = [..REGISTER_BITS..]) {
                Some(Self::Mov(dest as Register, src as Register))
            },
            _ => @() None
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::{arch::REGISTER_BITS, instruction::Instruction};

    #[test]
    fn encodes_correctly() {
        assert_eq!(Some(0), Instruction::Mov(0, 0).encode());
        assert_eq!(Some(1), Instruction::MovI(0, 0).encode());
        assert_eq!(
            Some((1 << 4) | (1 << (4 + REGISTER_BITS))),
            Instruction::Mov(1, 1).encode()
        );
    }
}
