// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

use static_assertions::const_assert;
use std::{ops::Range, vec};

use crate::{
    arch::Word,
    op,
    op::{Op, IMM_BITS},
};

type FunctionId = usize;
type InstructionAddress = usize;
type InstructionOffset = isize;
type LocalAddress = u8;

const LOCALS_COUNT: usize = 256;
const_assert!(LOCALS_COUNT <= LocalAddress::MAX as usize + 1);

const ARGUMENT_LOCALS: Range<usize> = 0..8;
const_assert!(ARGUMENT_LOCALS.end <= LOCALS_COUNT);

const RETURN_LOCALS: Range<usize> = 0..2;
const_assert!(RETURN_LOCALS.end <= LOCALS_COUNT);

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
    InvalidFunctionId,
    InvalidInstructionAddress,
    InvalidJumpOffset,
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
                InstructionPointer { func: 0, instr: 0 },
            )],
            ip: InstructionPointer { func: 0, instr: 0 },
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
                let to_addr = self.validate_local_address(to)?;
                let from_addr = self.validate_local_address(from)?;

                self.write_local(to_addr, self.read_local(from_addr));
                self.jump_within_function(self.ip.instr + 1)
            }
            Op::MovI(to, constant) => {
                let to_addr = self.validate_local_address(to)?;
                let extended: Word = sign_extend_to(constant, IMM_BITS);

                self.write_local(to_addr, extended);
                self.jump_within_function(self.ip.instr + 1)
            }
            Op::Add(to, first, second) => {
                let to_addr = self.validate_local_address(to)?;
                let first_addr = self.validate_local_address(first)?;
                let second_addr = self.validate_local_address(second)?;

                let sum =
                    self.read_local(first_addr) + self.read_local(second_addr);
                self.write_local(to_addr, sum);
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
            Op::Call(ix) => {
                let func_id = self.validate_function_id(ix)?;

                let mut callee_frame =
                    StackFrame::new_returning_to(InstructionPointer {
                        func: self.ip.func,
                        instr: self.ip.instr + 1,
                    });
                callee_frame.locals[ARGUMENT_LOCALS].copy_from_slice(
                    &self.current_frame().locals[ARGUMENT_LOCALS],
                );
                self.call_stack.push(callee_frame);

                self.jump_to_function(func_id)
            }
            Op::Jump(ix) => {
                let offset = self.make_instruction_offset(ix);
                let current_instr = self.ip.instr;
                let new_instr = current_instr
                    .checked_add_signed(offset)
                    .ok_or(VMError::InvalidJumpOffset)?;

                self.jump_within_function(new_instr)
            }
            Op::Nop => Ok(()),
        }?;

        Ok(())
    }

    fn decode_op(&self) -> Op {
        let word = self.functions[self.ip.func].code[self.ip.instr];
        Op::decode_packed(word).unwrap()
    }

    /// Validates an encoded local address. If the address is valid,
    /// the returned [`LocalAddress`] is guaranteed to be a valid index
    /// into the locals array.
    fn validate_local_address(
        &self,
        addr: op::Address,
    ) -> Result<LocalAddress, VMError> {
        if (addr as usize) < LOCALS_COUNT {
            Ok(addr)
        } else {
            Err(VMError::InvalidLocalAddress)
        }
    }

    /// Validates a function ID. If the ID is valid, the returned [`FunctionId`]
    /// is guaranteed to be a valid index into the functions array.
    fn validate_function_id(
        &self,
        ix: op::ExtendedImmediate,
    ) -> Result<FunctionId, VMError> {
        if (ix as usize) < self.functions.len() {
            Ok(ix as usize) // zero extension
        } else {
            Err(VMError::InvalidFunctionId)
        }
    }

    /// Creates an [`InstructionOffset`] from an [`op::ExtendedImmediate`] `ix`,
    /// where `ix` is an `IMM_EXT_BITS`-bit twos complement integer.
    fn make_instruction_offset(
        &self,
        offset: op::ExtendedImmediate,
    ) -> InstructionOffset {
        let sign_extended: usize = sign_extend_to(offset, IMM_BITS);
        sign_extended as isize
    }

    fn jump_to(&mut self, new_ip: InstructionPointer) -> VMResult {
        if new_ip.func >= self.functions.len() {
            Err(VMError::InvalidFunctionId)
        } else if new_ip.instr >= self.functions[new_ip.func].code.len() {
            Err(VMError::InvalidInstructionAddress)
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
