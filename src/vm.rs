// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

use crate::{
    arch::{Address, Offset, Word, CODE_SIZE, STACK_SIZE},
    opcode::{EncodeAsOp, Op, OpCodingError}
};

pub struct VM {
    pub code: Box<[Word]>,
    pub stack: Box<[Word]>,
    ip: usize,
    sp: Address,
    bp: Address,
    code_length: usize
}

#[derive(Debug)]
pub enum VMError {
    InvalidOp,
    InvalidArgs,
    CodeOversized
}

impl From<OpCodingError> for VMError {
    fn from(value: OpCodingError) -> Self {
        match value {
            OpCodingError::NoSpace => VMError::CodeOversized,
            OpCodingError::Other => VMError::InvalidOp
        }
    }
}

impl Default for VM {
    fn default() -> Self {
        Self {
            code: vec![0; CODE_SIZE].into_boxed_slice(),
            stack: vec![0; STACK_SIZE].into_boxed_slice(),
            ip: 0,
            sp: 0,
            bp: 0,
            code_length: 0
        }
    }
}

impl VM {
    pub fn load<O: EncodeAsOp>(
        &mut self, program: &[O]
    ) -> Result<(), VMError> {
        let mut pos = 0;
        for op in program {
            op.encode_into(self.code.as_mut(), &mut pos)?;
        }
        self.code_length = pos;
        self.ip = 0;
        Ok(())
    }

    pub fn run(&mut self) -> Result<(), VMError> {
        while self.ip != self.code_length {
            self.step()?;
        }
        Ok(())
    }

    fn next(&self) -> (Op, usize) {
        unsafe {
            Op::decode_from(self.code.as_ref(), self.ip).unwrap_unchecked()
        }
    }

    fn next_validate(&self) -> Result<(Op, usize), VMError> {
        let (op, length) = Op::decode_from(self.code.as_ref(), self.ip)?;
        Ok((op, length))
    }

    fn step(&mut self) -> Result<(), VMError> {
        let (op, length) = if cfg!(feature = "validate") {
            self.next_validate()?
        } else {
            self.next()
        };

        println!("running {:?}", op);

        self.ip += length
            + match op {
                Op::Mov(a, b) => {
                    self.stack[self.index_from_local(a)] =
                        self.stack[self.index_from_local(b)];
                    0
                }
                Op::MovI(a, i) => {
                    self.stack[self.index_from_local(a)] = i;
                    0
                }
                Op::Add(a, b, c) => {
                    self.stack[self.index_from_local(a)] = self.stack
                        [self.index_from_local(b)]
                        + self.stack[self.index_from_local(c)];
                    0
                }
            };
        Ok(())
    }

    fn index_from_local(&self, offset: Offset) -> usize {
        ((self.bp as Offset) + offset) as usize
    }
}

#[cfg(test)]
mod tests {
    use super::VM;
    use crate::opcode::Op;

    #[test]
    fn basic_program() {
        println!("start");
        let mut vm = VM::default();
        println!("test");
        vm.load(&[Op::MovI(0, 1), Op::MovI(1, 2), Op::Add(2, 0, 1)])
            .expect("invalid program");
        vm.run().expect("failed to run program");
        assert_eq!(1, vm.stack[0]);
        assert_eq!(2, vm.stack[1]);
        assert_eq!(3, vm.stack[2]);
    }
}
