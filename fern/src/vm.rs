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
    compiled: Option<unsafe fn(*mut [Word; LOCALS_COUNT])>,
}

#[derive(Debug)]
pub enum VMError {
    InvalidArgs,
    InvalidIP,
    InvalidLocalAddress,
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

impl VM {
    /// Creates a [`VM`] from an already encoded program.
    pub fn from_encoded_program(program: EncodedProgram) -> VM {
        Self {
            functions: program
                .functions
                .into_iter()
                .map(|code| VMFunction {
                    code: code.body,
                    compiled: None,
                })
                .collect(),
            // this return address doesn't matter because execution stops
            // when this frame is popped
            call_stack: vec![StackFrame::new_returning_to(
                InstructionPointer {
                    func: FunctionId::new(0),
                    instr: InstructionAddress::new(0),
                },
            )],
            ip: InstructionPointer {
                func: FunctionId::new(0),
                instr: InstructionAddress::new(0),
            },
        }
    }

    /// Runs the [`VM`] until the main function returns.
    pub fn run(&mut self) -> VMResult {
        while !self.call_stack.is_empty() {
            self.step()?;
        }
        Ok(())
    }

    fn step(&mut self) -> VMResult {
        match self.decode_op() {
            Op::Mov(to, from) => {
                let to_addr = LocalAddress::new(to)
                    .ok_or(VMError::InvalidLocalAddress)?;
                let from_addr = LocalAddress::new(from)
                    .ok_or(VMError::InvalidLocalAddress)?;

                self.write_local(to_addr, self.read_local(from_addr));
                self.jump_within_function(self.ip.instr.next())
            }
            Op::MovI(to, constant) => {
                let to_addr = LocalAddress::new(to)
                    .ok_or(VMError::InvalidLocalAddress)?;
                let extended: Word = sign_extend_to(constant, IMM_BITS);

                self.write_local(to_addr, extended);
                self.jump_within_function(self.ip.instr.next())
            }
            Op::Add(to, first, second) => {
                let to_addr = LocalAddress::new(to)
                    .ok_or(VMError::InvalidLocalAddress)?;
                let first_addr = LocalAddress::new(first)
                    .ok_or(VMError::InvalidLocalAddress)?;
                let second_addr = LocalAddress::new(second)
                    .ok_or(VMError::InvalidLocalAddress)?;

                let sum =
                    self.read_local(first_addr) + self.read_local(second_addr);
                self.write_local(to_addr, sum);
                self.jump_within_function(self.ip.instr.next())
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
            Op::Call(ix) => {
                let func_id = FunctionId::new(ix as usize); // zero extension

                let mut callee_frame =
                    StackFrame::new_returning_to(InstructionPointer {
                        func: self.ip.func,
                        instr: self.ip.instr.next(),
                    });
                callee_frame.locals[ARGUMENT_LOCALS].copy_from_slice(
                    &self.current_frame().locals[ARGUMENT_LOCALS],
                );
                self.call_stack.push(callee_frame);

                self.jump_to_function(func_id)
            }
            Op::Nop => Ok(()),
        }?;

        Ok(())
    }

    fn decode_op(&self) -> Op {
        let word = self.functions[self.ip.func.as_usize()].code
            [self.ip.instr.as_usize()];
        Op::decode_packed(word).unwrap()
    }

    fn jump_to(&mut self, new_ip: InstructionPointer) -> VMResult {
        if new_ip.func.as_usize() >= self.functions.len()
            || new_ip.instr.as_usize()
                >= self.functions[new_ip.func.as_usize()].code.len()
        {
            Err(VMError::InvalidIP)
        } else {
            self.ip = new_ip;
            Ok(())
        }
    }

    fn jump_to_function(&mut self, func: FunctionId) -> VMResult {
        self.jump_to(InstructionPointer {
            func,
            instr: InstructionAddress::new(0),
        })
    }

    fn jump_within_function(&mut self, instr: InstructionAddress) -> VMResult {
        self.jump_to(InstructionPointer {
            func: self.ip.func,
            instr,
        })
    }

    fn read_local(&self, address: LocalAddress) -> Word {
        self.current_frame().locals[address.as_usize()]
    }

    fn write_local(&mut self, address: LocalAddress, value: Word) {
        self.current_frame_mut().locals[address.as_usize()] = value;
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

pub struct EncodedProgram {
    functions: Vec<EncodedFunction>,
}

impl EncodedProgram {
    pub fn decode(&self) -> Option<DecodedProgram> {
        self.functions
            .iter()
            .map(EncodedFunction::decode)
            .collect::<Option<Vec<DecodedFunction>>>()
            .map(|functions| DecodedProgram { functions })
    }
}

pub struct EncodedFunction {
    body: Vec<Word>,
}

impl EncodedFunction {
    pub fn decode(&self) -> Option<DecodedFunction> {
        self.body
            .iter()
            .map(|word| Op::decode_packed(*word))
            .collect::<Option<Vec<Op>>>()
            .map(|body| DecodedFunction { body })
    }
}

pub struct DecodedProgram {
    functions: Vec<DecodedFunction>,
}

impl DecodedProgram {
    pub fn encode(&self) -> EncodedProgram {
        EncodedProgram {
            functions: self
                .functions
                .iter()
                .map(DecodedFunction::encode)
                .collect(),
        }
    }
}

pub struct DecodedFunction {
    body: Vec<Op>,
}

impl DecodedFunction {
    pub fn encode(&self) -> EncodedFunction {
        EncodedFunction {
            body: self.body.iter().map(Op::encode_packed).collect(),
        }
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
    use crate::{
        op::Op,
        vm::{DecodedFunction, DecodedProgram, VM},
    };

    #[test]
    fn basic_program() {
        let main = DecodedFunction {
            body: vec![
                Op::MovI(0, 1),
                Op::MovI(1, 2),
                Op::Add(2, 0, 1),
                Op::Ret,
            ],
        };

        let program = DecodedProgram {
            functions: vec![main],
        };

        let mut vm = VM::from_encoded_program(program.encode());

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
        let main = DecodedFunction {
            body: vec![
                Op::MovI(0, 1),
                Op::MovI(1, 2),
                Op::Call(1), // call add
                Op::Ret,
            ],
        };

        let add = DecodedFunction {
            body: vec![Op::Add(0, 0, 1), Op::Ret],
        };

        let program = DecodedProgram {
            functions: vec![main, add],
        };

        let mut vm = VM::from_encoded_program(program.encode());

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
        let main = DecodedFunction {
            body: vec![
                Op::MovI(0, 3),
                Op::Call(2), // call double
                Op::Ret,
            ],
        };

        let add = DecodedFunction {
            body: vec![Op::Add(0, 0, 1), Op::Ret],
        };

        let double = DecodedFunction {
            body: vec![
                Op::Mov(1, 0),
                Op::Call(1), // call add
                Op::Ret,
            ],
        };

        let program = DecodedProgram {
            functions: vec![main, add, double],
        };

        let mut vm = VM::from_encoded_program(program.encode());

        for _ in 0..7 {
            vm.step().expect("program should run without errors");
        }

        assert_eq!(6, vm.current_frame().locals[0]);

        vm.step().expect("program should run without errors");
        assert!(vm.call_stack.is_empty());
    }
}
