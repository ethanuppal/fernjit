// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

use std::vec;

use crate::{
    arch::{LocalAddress, Word, CODE_SIZE, LOCALS_SIZE},
    opcode::{EncodeIntoOpStream, Op, OpCodingError}
};

struct StackFrame {
    locals: [Word; LOCALS_SIZE],
    return_address: usize
}

pub struct VM {
    code: Box<[Word]>,
    code_length: usize,
    call_stack: Vec<StackFrame>,
    ip: usize
}

#[derive(Debug)]
pub enum VMError {
    InvalidOp,
    InvalidArgs,
    CodeOversized,
    InvalidIP
}

pub type VMResult = Result<(), VMError>;

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
            call_stack: vec![],
            ip: 0
        }
    }
}

impl VM {
    pub fn load<O: EncodeIntoOpStream>(&mut self, program: &[O]) -> VMResult {
        let mut pos = 0;
        for op in program {
            op.encode_into(self.code.as_mut(), &mut pos)?;
        }
        self.code_length = pos;
        self.call_stack.clear();
        self.call_stack.push(StackFrame {
            locals: [0; LOCALS_SIZE],
            return_address: 0  // we will never return to this address, as if the first frame is popped, the VM will stop
        });
        Ok(())
    }

    pub fn run(&mut self) -> VMResult {
        while !self.call_stack.is_empty() {
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

    fn step(&mut self) -> VMResult {
        let (op, length) = if cfg!(feature = "validate") {
            self.next_validate()?
        } else {
            self.next()
        };

        match op {
            Op::Mov(to, from) => {
                self.write_local(to, self.read_local(from));
                self.move_ip(self.ip + length)
            }
            Op::MovI(to, constant) => {
                self.write_local(to, constant);
                self.move_ip(self.ip + length)
            }
            Op::Add(to, first, second) => {
                let sum = self.read_local(first) + self.read_local(second);
                self.write_local(to, sum);
                self.move_ip(self.ip + length)
            }
            Op::Ret() => {
                let ra = self.current_frame().return_address;
                self.call_stack.pop();
                self.move_ip(ra)
            }
        }?;

        Ok(())
    }

    fn move_ip(&mut self, new_ip: usize) -> VMResult {
        if new_ip >= self.code_length {
            return Err(VMError::InvalidIP);
        };

        self.ip = new_ip;

        Ok(())
    }

    fn read_local(&self, address: LocalAddress) -> Word {
        self.current_frame().locals[address as usize]
    }

    fn write_local(
        &mut self, address: LocalAddress, value: impl Into<Word>
    ) -> () {
        self.current_frame_mut().locals[address as usize] = value.into()
    }

    fn current_frame(&self) -> &StackFrame {
        self.call_stack.last().expect(
            "call stack expected to always have one frame while running."
        )
    }

    fn current_frame_mut(&mut self) -> &mut StackFrame {
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
        vm.load(&[Op::MovI(0, 1), Op::MovI(1, 2), Op::Add(2, 0, 1), Op::Ret()])
            .expect("invalid program");

        for _ in 0..3 {
            vm.step().expect("failed to run program");
        }

        assert_eq!(1, vm.current_frame().locals[0]);
        assert_eq!(2, vm.current_frame().locals[1]);
        assert_eq!(3, vm.current_frame().locals[2]);

        vm.run().expect("failed to run program");
    }
}
