// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

use std::vec;

use crate::{
    arch::{
        InstructionAddress, LocalAddress, Word, ARGUMENT_LOCALS, LOCALS_COUNT,
        MAX_CODE_LENGTH, RETURN_LOCALS,
    },
    op::{Op, IMM_BITS, IMM_EXT_BITS},
};

// TODO: is this uglier than the macro version?
// TODO: if we use the newtype pattern the `AsPrimitive` won't work
fn sign_extend_to<
    In: num_traits::Unsigned + num_traits::PrimInt + num_traits::AsPrimitive<Out>,
    Out: 'static + num_traits::Unsigned + Copy,
>(
    value: In,
    bits: usize,
) -> Out {
    let sign_bit = In::one() << (bits - 1);
    if value & sign_bit != In::zero() {
        let extension = !((In::one() << bits) - In::one());
        value | extension
    } else {
        value
    }
    .as_()
}

struct StackFrame {
    // TODO: do we wnat this on the heap?
    locals: [Word; LOCALS_COUNT],
    return_address: InstructionAddress,
}

impl StackFrame {
    fn new_returning_to(return_address: InstructionAddress) -> Self {
        Self {
            locals: [0; LOCALS_COUNT],
            return_address,
        }
    }
}

pub struct VM {
    code: Box<[Word]>,
    code_length: InstructionAddress,
    call_stack: Vec<StackFrame>,
    ip: InstructionAddress,
}

#[derive(Debug)]
pub enum VMError {
    InvalidArgs,
    InvalidIP,
}

pub type VMResult = Result<(), VMError>;

impl Default for VM {
    fn default() -> Self {
        Self {
            code: vec![0; MAX_CODE_LENGTH].into_boxed_slice(),
            code_length: 0,
            call_stack: vec![],
            ip: 0,
        }
    }
}

impl VM {
    pub fn load(&mut self, program: &[Op]) {
        // TODO: should this be an assertion or a `VMError`?
        assert!(
            program.len() <= MAX_CODE_LENGTH,
            "program too large to load (length={}, max length={})",
            program.len(),
            MAX_CODE_LENGTH
        );
        for (i, op) in program.iter().enumerate() {
            self.code[i] = op.encode_packed();
        }
        self.code_length = program.len();
        self.call_stack.clear();
        // this return address doesn't matter because execution stops when this
        // frame is popped
        self.call_stack.push(StackFrame::new_returning_to(0));
    }

    pub fn run(&mut self) -> VMResult {
        while !self.call_stack.is_empty() {
            self.step()?;
        }
        Ok(())
    }

    fn step(&mut self) -> VMResult {
        match self.decode_op() {
            Op::Mov(to, from) => {
                self.write_local(to, self.read_local(from));
                self.jump_to(self.ip + 1)
            }
            Op::MovI(to, constant) => {
                let extended = sign_extend_to(constant, IMM_BITS);
                self.write_local(to, extended);
                self.jump_to(self.ip + 1)
            }
            Op::Add(to, first, second) => {
                let sum = self.read_local(first) + self.read_local(second);
                self.write_local(to, sum);
                self.jump_to(self.ip + 1)
            }
            Op::Ret => {
                let callee_frame = self.call_stack.pop().expect(
                    "call stack should always have one frame while running.",
                );
                let return_address = callee_frame.return_address;

                if let Some(caller_frame) = self.call_stack.last_mut() {
                    caller_frame.locals[RETURN_LOCALS]
                        .copy_from_slice(&callee_frame.locals[RETURN_LOCALS]);
                }

                self.jump_to(return_address)
            }
            Op::Call(offset) => {
                let new_ip =
                    self.ip.wrapping_add(sign_extend_to(offset, IMM_EXT_BITS));

                let mut callee_frame =
                    StackFrame::new_returning_to(self.ip + 1);
                callee_frame.locals[ARGUMENT_LOCALS].copy_from_slice(
                    &self.current_frame().locals[ARGUMENT_LOCALS],
                );
                self.call_stack.push(callee_frame);

                self.jump_to(new_ip)
            }
            Op::Nop => Ok(()),
        }?;

        Ok(())
    }

    fn decode_op(&self) -> Op {
        Op::decode_packed(self.code[self.ip]).unwrap()
    }

    fn jump_to(&mut self, new_ip: usize) -> VMResult {
        if new_ip >= self.code_length {
            Err(VMError::InvalidIP)
        } else {
            self.ip = new_ip;
            Ok(())
        }
    }

    fn read_local(&self, address: LocalAddress) -> Word {
        self.current_frame().locals[address as usize]
    }

    fn write_local(&mut self, address: LocalAddress, value: Word) {
        self.current_frame_mut().locals[address as usize] = value;
    }

    fn current_frame(&self) -> &StackFrame {
        self.call_stack
            .last()
            .expect("call stack should always have one frame while running.")
    }

    fn current_frame_mut(&mut self) -> &mut StackFrame {
        self.call_stack
            .last_mut()
            .expect("call stack should always have one frame while running.")
    }
}

#[cfg(test)]
mod tests {
    use super::VM;
    use crate::op::{ExtendedImmediate, Op};

    #[test]
    fn basic_program() {
        let mut vm = VM::default();
        vm.load(&[Op::MovI(0, 1), Op::MovI(1, 2), Op::Add(2, 0, 1), Op::Ret]);

        for _ in 0..3 {
            vm.step().expect("program should run without errors")
        }

        assert_eq!(1, vm.current_frame().locals[0]);
        assert_eq!(2, vm.current_frame().locals[1]);
        assert_eq!(3, vm.current_frame().locals[2]);

        vm.step().expect("program should run without errors");
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
            Op::Ret,
            // func add
            Op::Add(0, 0, 1),
            Op::Ret,
        ]);

        for _ in 0..5 {
            vm.step().expect("program should run without errors");
        }

        assert_eq!(3, vm.current_frame().locals[0]);
        assert_eq!(2, vm.current_frame().locals[1]);

        vm.step().expect("program should run without errors");
        assert!(vm.call_stack.is_empty());
    }

    #[test]
    fn call_neg_offset() {
        let mut vm = VM::default();
        let program = [
            // func main
            Op::MovI(0, 3),
            Op::Call(4), // call double
            Op::Ret,
            // func add
            Op::Add(0, 0, 1),
            Op::Ret,
            // func double
            Op::Mov(1, 0),
            Op::Call((0 as ExtendedImmediate).wrapping_sub(3)), // call add
            Op::Ret,
        ];

        vm.load(&program);

        for _ in 0..7 {
            vm.step().expect("program should run without errors");
        }

        assert_eq!(6, vm.current_frame().locals[0]);

        vm.step().expect("program should run without errors");
        assert!(vm.call_stack.is_empty());
    }
}
