// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

use std::vec;

use crate::{
    arch::{
        FunctionId, InstructionAddress, LocalAddress, Word, ARGUMENT_LOCALS,
        LOCALS_COUNT, RETURN_LOCALS,
    },
    op::{Op, IMM_BITS},
};

pub struct VM {
    functions: Vec<VMFunction>,
    call_stack: Vec<StackFrame>,
    ip: InstructionPointer,
}

struct VMFunction {
    code: Vec<Word>,
}

#[derive(Debug)]
pub enum VMError {
    InvalidArgs,
    InvalidIP,
}

pub type VMResult = Result<(), VMError>;

struct StackFrame {
    locals: [Word; LOCALS_COUNT],
    return_address: InstructionPointer,
}

impl StackFrame {
    fn new_returning_to(return_address: InstructionPointer) -> Self {
        Self {
            locals: [0; LOCALS_COUNT],
            return_address,
        }
    }
}

struct InstructionPointer {
    func: FunctionId,
    instr: InstructionAddress,
}

pub type EncodedFunction = Vec<Word>;
pub type EncodedProgram = Vec<EncodedFunction>;
pub type DecodedFunction = Vec<Op>;
pub type DecodedProgram = Vec<DecodedFunction>;

impl VM {
    /// Creates a VM from an already encoded program.
    pub fn from_encoded_program(program: EncodedProgram) -> VM {
        let functions = program
            .into_iter()
            .map(|code| VMFunction { code })
            .collect();

        Self {
            functions,
            // this return address doesn't matter because execution stops
            // when this frame is popped
            call_stack: vec![StackFrame::new_returning_to(
                InstructionPointer { func: 0, instr: 0 },
            )],
            ip: InstructionPointer { func: 0, instr: 0 },
        }
    }

    /// Runs a VM until the main function returns.
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
                self.jump_within_function(self.ip.instr + 1)
            }
            Op::MovI(to, constant) => {
                let extended = sign_extend_to(constant, IMM_BITS);
                self.write_local(to, extended);
                self.jump_within_function(self.ip.instr + 1)
            }
            Op::Add(to, first, second) => {
                let sum = self.read_local(first) + self.read_local(second);
                self.write_local(to, sum);
                self.jump_within_function(self.ip.instr + 1)
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
            Op::Call(id) => {
                let mut callee_frame =
                    StackFrame::new_returning_to(InstructionPointer {
                        func: self.ip.func,
                        instr: self.ip.instr + 1,
                    });
                callee_frame.locals[ARGUMENT_LOCALS].copy_from_slice(
                    &self.current_frame().locals[ARGUMENT_LOCALS],
                );
                self.call_stack.push(callee_frame);

                self.jump_to_function(id as FunctionId) // zero extension
            }
            Op::Nop => Ok(()),
        }?;

        Ok(())
    }

    fn decode_op(&self) -> Op {
        Op::decode_packed(self.functions[self.ip.func].code[self.ip.instr])
            .unwrap()
    }

    fn jump_to(&mut self, new_ip: InstructionPointer) -> VMResult {
        if new_ip.func >= self.functions.len()
            || new_ip.instr >= self.functions[new_ip.func].code.len()
        {
            Err(VMError::InvalidIP)
        } else {
            self.ip = new_ip;
            Ok(())
        }
    }

    fn jump_to_function(&mut self, func: FunctionId) -> VMResult {
        self.jump_to(InstructionPointer { func, instr: 0 })
    }

    fn jump_within_function(&mut self, instr: InstructionAddress) -> VMResult {
        self.jump_to(InstructionPointer {
            func: self.ip.func,
            instr,
        })
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

#[cfg(test)]
mod tests {
    use std::vec;

    use super::{DecodedProgram, EncodedProgram, VM};
    use crate::op::Op;

    fn encode_program(program: DecodedProgram) -> EncodedProgram {
        program
            .into_iter()
            .map(|func| func.into_iter().map(|op| op.encode_packed()).collect())
            .collect()
    }

    #[test]
    fn basic_program() {
        let main =
            vec![Op::MovI(0, 1), Op::MovI(1, 2), Op::Add(2, 0, 1), Op::Ret];

        let mut vm = VM::from_encoded_program(encode_program(vec![main]));

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
        let main = vec![
            Op::MovI(0, 1),
            Op::MovI(1, 2),
            Op::Call(1), // call add
            Op::Ret,
        ];

        let add = vec![Op::Add(0, 0, 1), Op::Ret];

        let mut vm = VM::from_encoded_program(encode_program(vec![main, add]));

        for _ in 0..5 {
            vm.step().expect("program should run without errors");
        }

        assert_eq!(3, vm.current_frame().locals[0]);
        assert_eq!(2, vm.current_frame().locals[1]);

        vm.step().expect("program should run without errors");
        assert!(vm.call_stack.is_empty());
    }

    #[test]
    fn call_multiple() {
        let main = vec![
            Op::MovI(0, 3),
            Op::Call(2), // call double
            Op::Ret,
        ];

        let add = vec![Op::Add(0, 0, 1), Op::Ret];

        let double = vec![
            Op::Mov(1, 0),
            Op::Call(1), // call add
            Op::Ret,
        ];

        let mut vm =
            VM::from_encoded_program(encode_program(vec![main, add, double]));

        for _ in 0..7 {
            vm.step().expect("program should run without errors");
        }

        assert_eq!(6, vm.current_frame().locals[0]);

        vm.step().expect("program should run without errors");
        assert!(vm.call_stack.is_empty());
    }
}
