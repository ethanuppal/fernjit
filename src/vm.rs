// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

use std::vec;

use crate::{
    arch::{
        InstructionAddress, LocalAddress, Word, ARGUMENT_LOCALS, CODE_SIZE,
        LOCALS_SIZE, RETURN_LOCALS
    },
    opcode::{EncodeIntoOpStream, Op, OpCodingError, IMM_BITS, IMM_EXT_BITS}
};

macro_rules! sign_extend_to {
    ($t:ty, $value:expr, $bits:expr) => {{
        let value = $value as $t;
        let sign_bit = 1 << ($bits - 1);
        if value & sign_bit != 0 {
            let extension = !((1 << $bits) - 1);
            value | extension
        } else {
            value
        }
    }};
}

struct StackFrame {
    locals: [Word; LOCALS_SIZE],
    return_address: InstructionAddress
}

pub struct VM {
    code: Box<[Word]>,
    code_length: InstructionAddress,
    call_stack: Vec<StackFrame>,
    ip: InstructionAddress
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
                self.jump(self.ip + length)
            }
            Op::MovI(to, constant) => {
                let extended = sign_extend_to!(Word, constant, IMM_BITS);
                self.write_local(to, extended);
                self.jump(self.ip + length)
            }
            Op::Add(to, first, second) => {
                let sum = self.read_local(first) + self.read_local(second);
                self.write_local(to, sum);
                self.jump(self.ip + length)
            }
            Op::Ret() => {
                let frame = self.current_frame();
                let ra = frame.return_address;

                let popped = self.call_stack.pop().expect(
                    "call stack expected to always have one frame while running."
                );
                if let Some(frame_below) = self.call_stack.last_mut() {
                    frame_below.locals[RETURN_LOCALS]
                        .copy_from_slice(&popped.locals[RETURN_LOCALS]);
                }

                self.jump(ra)
            }
            Op::Call(offset) => {
                let as_usize: usize = offset
                    .try_into()
                    .expect("illegal offset, too large for platform"); // explodes on microcontrollers
                let extended =
                    sign_extend_to!(InstructionAddress, as_usize, IMM_EXT_BITS);
                let new_ip = self.ip.wrapping_add(extended); // handle negative offsets

                let mut new_frame = StackFrame {
                    locals: [0; LOCALS_SIZE],
                    return_address: self.ip + length
                };
                new_frame.locals[ARGUMENT_LOCALS].copy_from_slice(
                    &self.current_frame().locals[ARGUMENT_LOCALS]
                );

                self.call_stack.push(new_frame);

                self.jump(new_ip)
            }
        }?;

        Ok(())
    }

    fn jump(&mut self, new_ip: usize) -> VMResult {
        if new_ip >= self.code_length {
            return Err(VMError::InvalidIP);
        };

        self.ip = new_ip;

        Ok(())
    }

    fn read_local(&self, address: LocalAddress) -> Word {
        self.current_frame().locals[address as usize]
    }

    fn write_local(&mut self, address: LocalAddress, value: Word) -> () {
        self.current_frame_mut().locals[address as usize] = value;
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
    use crate::opcode::{ExtendedImmediate, Op};

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

        vm.step().expect("failed to run program");
        assert!(vm.call_stack.is_empty());
    }

    #[test]
    fn call_return() {
        let mut vm = VM::default();
        vm.load(&[
            // func main
            Op::MovI(0, 1),
            Op::MovI(1, 2),
            Op::Call(2), // call add
            Op::Ret(),
            // func add
            Op::Add(0, 0, 1),
            Op::Ret()
        ])
        .expect("invalid program");

        for _ in 0..5 {
            vm.step().expect("failed to run program");
        }

        assert_eq!(3, vm.current_frame().locals[0]);
        assert_eq!(2, vm.current_frame().locals[1]);

        vm.step().expect("failed to run program");
        assert!(vm.call_stack.is_empty());
    }

    #[test]
    fn call_neg_offset() {
        let mut vm = VM::default();
        let program = [
            // func main
            Op::MovI(0, 3),
            Op::Call(4), // call double
            Op::Ret(),
            // func add
            Op::Add(0, 0, 1),
            Op::Ret(),
            // func double
            Op::Mov(1, 0),
            Op::Call((0 as ExtendedImmediate).wrapping_sub(3)), // call add
            Op::Ret()
        ];

        vm.load(&program).expect("invalid program");

        for _ in 0..7 {
            vm.step().expect("failed to run program");
        }

        assert_eq!(6, vm.current_frame().locals[0]);

        vm.step().expect("failed to run program");
        assert!(vm.call_stack.is_empty());
    }
}
