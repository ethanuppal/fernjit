// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

use std::vec;

use crate::{
    arch::{LocalAddress, Word, CODE_SIZE, LOCALS_SIZE},
    opcode::{EncodeAsOp, Op, OpCodingError}
};

struct StackFrame {
    locals: [Word; LOCALS_SIZE],
    ip: usize
}

pub struct VM {
    code: Box<[Word]>,
    code_length: usize,
    call_stack: Vec<StackFrame>
}

#[derive(Debug)]
pub enum VMError {
    InvalidOp,
    InvalidArgs,
    CodeOversized,
    InvalidIP
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
            code_length: 0,
            call_stack: vec![]
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
        self.call_stack.clear();
        self.call_stack.push(StackFrame {
            locals: [0; LOCALS_SIZE],
            ip: 0
        });
        Ok(())
    }

    pub fn run(&mut self) -> Result<(), VMError> {
        while !self.call_stack.is_empty() {
            self.step()?;
        }
        Ok(())
    }

    fn next(&self) -> (Op, usize) {
        unsafe {
            Op::decode_from(self.code.as_ref(), self.ip()).unwrap_unchecked()
        }
    }

    fn next_validate(&self) -> Result<(Op, usize), VMError> {
        let (op, length) = Op::decode_from(self.code.as_ref(), self.ip())?;
        Ok((op, length))
    }

    fn step(&mut self) -> Result<(), VMError> {
        let (op, length) = if cfg!(feature = "validate") {
            self.next_validate()?
        } else {
            self.next()
        };

        let ip = self.ip();

        let new_ip = match op {
            Op::Mov(to, from) => {
                self.write_local(to, self.read_local(from));
                ip + length
            }
            Op::MovI(to, constant) => {
                self.write_local(to, constant);
                ip + length
            }
            Op::Add(to, first, second) => {
                self.write_local(
                    to,
                    self.read_local(first) + self.read_local(second)
                );
                ip + length
            }
        };

        self.move_ip(new_ip)?;

        Ok(())
    }

    fn ip(&self) -> usize {
        self.top_frame().ip
    }

    fn move_ip(&mut self, new_ip: usize) -> Result<(), VMError> {
        if new_ip >= self.code_length {
            return Err(VMError::InvalidIP);
        };

        self.top_frame_mut().ip = new_ip;

        Ok(())
    }

    fn read_local(&self, address: LocalAddress) -> Word {
        self.top_frame().locals[address as usize]
    }

    fn write_local(
        &mut self, address: LocalAddress, value: impl Into<Word>
    ) -> () {
        self.top_frame_mut().locals[address as usize] = value.into()
    }

    fn top_frame(&self) -> &StackFrame {
        self.call_stack.last().expect(
            "call stack expected to always have one frame while running."
        )
    }

    fn top_frame_mut(&mut self) -> &mut StackFrame {
        self.call_stack.last_mut().expect(
            "call stack expected to always have one frame while running."
        )
    }
}

#[cfg(test)]
mod tests {
    use super::VM;
    use crate::opcode::Op;

    #[test]
    fn basic_program() {
        let mut vm = VM::default();
        vm.load(&[Op::MovI(0, 1), Op::MovI(1, 2), Op::Add(2, 0, 1)])
            .expect("invalid program");
        vm.run().expect("failed to run program");
        // assert_eq!(1, vm.stack[0]);
        // assert_eq!(2, vm.stack[1]);
        // assert_eq!(3, vm.stack[2]);
    }
}
