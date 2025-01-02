// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

use crate::{
    arch::{
        FunctionId, InstructionAddress, InstructionOffset, LocalAddress, Word,
        ARGUMENT_LOCALS, LOCALS_COUNT, RETURN_LOCALS,
    },
    op::{Immediate, Op, IMM_BITS},
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
    InvalidFunctionId,
    InvalidInstructionAddress,
    InvalidJumpOffset,
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
                .map(|code| VMFunction { code: code.body })
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
                // note that we do not validate local addresses here
                // it is not a VM responsibility to

                self.write_local(to, self.read_local(from));
                self.jump_within_function(self.ip.instr + 1)
            }
            Op::MovI(to, constant) => {
                let extended: Word = sign_extend_to(constant, IMM_BITS);

                self.write_local(to, extended);
                self.jump_within_function(self.ip.instr + 1)
            }
            Op::Add(to, a, b) => {
                let first = self.read_local(a);
                let second = self.read_local(b);
                let sum = first.wrapping_add(second);

                self.write_local(to, sum);
                self.jump_within_function(self.ip.instr + 1)
            }
            Op::Sub(to, a, b) => {
                let first = self.read_local(a);
                let second = self.read_local(b);
                let difference = first.wrapping_sub(second);

                self.write_local(to, difference);
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
                let func_id = ix as FunctionId;

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
            Op::Bnz(a, offset) => {
                let value = self.read_local(a);
                if value != 0 {
                    let instr_offset = make_instruction_offset(offset);
                    let new_ip = InstructionPointer {
                        func: self.ip.func,
                        instr: self.ip.instr.wrapping_add_signed(instr_offset),
                    };
                    self.jump_to(new_ip)
                } else {
                    self.jump_within_function(self.ip.instr + 1)
                }
            }
            Op::Nop => Ok(()),
        }?;

        Ok(())
    }

    fn decode_op(&self) -> Op {
        let word = self.functions[self.ip.func].code[self.ip.instr];
        Op::decode_packed(word).unwrap()
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

/// Creates an [`InstructionOffset`] from an [`Immediate`]
/// `offset`, where `offset` is an `IMM_BITS`-bit twos complement
/// integer.
fn make_instruction_offset(offset: Immediate) -> InstructionOffset {
    let sign_extended: usize = sign_extend_to(offset, IMM_BITS);
    sign_extended as InstructionOffset
}

fn sign_extend_to<
    In: num_traits::Unsigned + num_traits::PrimInt + num_traits::AsPrimitive<Out>,
    Out: 'static
        + num_traits::Unsigned
        + num_traits::PrimInt
        + num_traits::WrappingShl,
>(
    value: In,
    bits: usize,
) -> Out {
    let sign_bit = In::one() << (bits - 1);
    if value & sign_bit != In::zero() {
        let extension = Out::max_value().wrapping_shl(bits as u32);
        value.as_() | extension
    } else {
        value.as_()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        op::{Immediate, Op},
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

    #[test]
    fn basic_loop() {
        // computes the sum of the first 10 natural numbers
        let main = DecodedFunction {
            body: vec![
                // init
                Op::MovI(0, 10), // i = 10
                Op::MovI(1, 0),  // sum = 0
                // loop
                Op::Add(1, 1, 0), // sum += i
                Op::MovI(3, 1),   // tmp = 1
                Op::Sub(0, 0, 3), // i -= tmp
                Op::Bnz(0, (0 as Immediate).wrapping_sub(3)), /* if i != 0, jump to loop */
                Op::Ret,
            ],
        };

        let program = DecodedProgram {
            functions: vec![main],
        };

        let mut vm = VM::from_encoded_program(program.encode());

        while !matches!(vm.decode_op(), Op::Ret) {
            vm.step().expect("program should run without errors");
        }

        assert_eq!(55, vm.current_frame().locals[1]);

        vm.step().expect("program should run without errors");
        assert!(vm.call_stack.is_empty());
    }
}
