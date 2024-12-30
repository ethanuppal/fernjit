// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

use crate::{arch::Word, op::Op};

pub type EncodedFunction = Vec<Word>;
pub type EncodedProgram = Vec<EncodedFunction>;
pub type DecodedFunction = Vec<Op>;
pub type DecodedProgram = Vec<DecodedFunction>;

pub fn encode_program(program: DecodedProgram) -> EncodedProgram {
    program
        .iter()
        .map(|func| func.iter().map(|op| op.encode_packed()).collect())
        .collect()
}

pub fn decode_program(program: EncodedProgram) -> Option<DecodedProgram> {
    program
        .iter()
        .map(|func| func.iter().map(|&word| Op::decode_packed(word)).collect())
        .collect()
}
