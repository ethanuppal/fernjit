// Copyright (C) 2024 Ethan Uppal and Utku Melemetci. All rights reserved.

use std::vec;

use crate::{
    arch::{
        FunctionId, InstructionAddress, LocalAddress, Word, ARGUMENT_LOCALS,
        LOCALS_COUNT, RETURN_LOCALS,
    },
    op::{Op, IMM_BITS},
};

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

// TODO: this might need to be split apart into what we take as input and what
// we use internally. Internally we probably want to store trace info, whether
// the functions is JITed, etc.
pub struct VMFunction {
    code: Vec<Word>,
}

impl VMFunction {
    pub fn from_ops(ops: &[Op]) -> Self {
        let mut code = vec![0; ops.len()];
        for (i, op) in ops.iter().enumerate() {
            code[i] = op.encode_packed();
        }
        Self { code }
    }
}

struct IP {
    func: FunctionId,
    instr: InstructionAddress,
}

struct StackFrame {
    locals: [Word; LOCALS_COUNT],
    return_address: IP,
}

impl StackFrame {
    fn new_returning_to(return_address: IP) -> Self {
        Self {
            locals: [0; LOCALS_COUNT],
            return_address,
        }
    }
}

pub struct VM {
    functions: Vec<VMFunction>,
    call_stack: Vec<StackFrame>,
    ip: IP,
}

#[derive(Debug)]
pub enum VMError {
    InvalidArgs,
    InvalidIP,
}

pub type VMResult = Result<(), VMError>;

impl VM {
    // TODO: this should take a slice of functions, idk how to do it nicely yet
    /// Creates a new VM from a set of `functions`. Execution begins at the
    /// first op of the first function.
    pub fn from_functions(functions: Vec<VMFunction>) -> Self {
        Self {
            functions,
            // this return address doesn't matter because execution stops
            // when this frame is popped
            call_stack: vec![StackFrame::new_returning_to(IP {
                func: 0,
                instr: 0,
            })],
            ip: IP { func: 0, instr: 0 },
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
                let mut callee_frame = StackFrame::new_returning_to(IP {
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

    fn jump_to(&mut self, new_ip: IP) -> VMResult {
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
        self.jump_to(IP { func, instr: 0 })
    }

    fn jump_within_function(&mut self, instr: InstructionAddress) -> VMResult {
        self.jump_to(IP {
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

#[cfg(test)]
mod tests {
    use std::vec;

    use super::VM;
    use crate::{op::Op, vm::VMFunction};

    #[test]
    fn basic_program() {
        let main = VMFunction::from_ops(&[
            Op::MovI(0, 1),
            Op::MovI(1, 2),
            Op::Add(2, 0, 1),
            Op::Ret,
        ]);

        let mut vm = VM::from_functions(vec![main]);

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
        let main = VMFunction::from_ops(&[
            Op::MovI(0, 1),
            Op::MovI(1, 2),
            Op::Call(1), // call add
            Op::Ret,
        ]);

        let add = VMFunction::from_ops(&[Op::Add(0, 0, 1), Op::Ret]);

        let mut vm = VM::from_functions(vec![main, add]);

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
        let main = VMFunction::from_ops(&[
            Op::MovI(0, 3),
            Op::Call(2), // call double
            Op::Ret,
        ]);

        let add = VMFunction::from_ops(&[Op::Add(0, 0, 1), Op::Ret]);

        let double = VMFunction::from_ops(&[
            Op::Mov(1, 0),
            Op::Call(1), // call add
            Op::Ret,
        ]);

        let mut vm = VM::from_functions(vec![main, add, double]);

        for _ in 0..7 {
            vm.step().expect("program should run without errors");
        }

        assert_eq!(6, vm.current_frame().locals[0]);

        vm.step().expect("program should run without errors");
        assert!(vm.call_stack.is_empty());
    }
}
