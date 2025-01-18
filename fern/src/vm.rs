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
    code: Vec<Word>,
    functions: Vec<InstructionAddress>,
    call_stack: Vec<StackFrame>,
    ip: InstructionAddress,
}

/// Used to mark uninitialized functions in `VM::functions`
const UNINITIALIZED_FUNCTION: InstructionAddress = InstructionAddress::MAX;

#[derive(Debug)]
pub enum VMError {
    InvalidFunctionId,
    InvalidInstructionAddress,
    InvalidJumpOffset,
}

pub type VMResult = Result<(), VMError>;

struct StackFrame {
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

impl Default for VM {
    fn default() -> Self {
        Self {
            code: vec![],
            functions: vec![],
            // this return address doesn't matter because execution stops
            // when this frame is popped
            call_stack: vec![StackFrame::new_returning_to(0)],
            ip: 0,
        }
    }
}

impl VM {
    /// Creates a VM function, returning a [`FunctionId`] that can be used to
    /// refer to it. You must later assign code to the given function ID using
    /// `initialize_function`.
    pub fn create_function(&mut self) -> FunctionId {
        self.functions.push(UNINITIALIZED_FUNCTION);
        self.functions.len() - 1
    }

    /// Initializes the function with `function_id` with bytecode. `function_id`
    /// must be an ID obtained from `create_function`, and must not have been
    /// initialized previously.
    pub fn initialize_function(
        &mut self,
        function_id: FunctionId,
        function_code: Box<[Word]>,
    ) {
        assert!(
            function_id < self.functions.len(),
            "Invalid function ID {}. Valid function IDs are up to (but not including) {}.",
            function_id,
            self.functions.len()
        );

        assert!(
            self.functions[function_id] == UNINITIALIZED_FUNCTION,
            "Function {} has been initialized before.",
            function_id
        );

        let start_addr = self.code.len();
        self.code.extend(function_code);
        self.functions[function_id] = start_addr
    }

    /// Runs the [`VM`] until the call stack is empty. Execution begins at the
    /// first instruction of the first function.
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
                // it is not a VM responsibility to validate the program

                self.write_local(to, self.read_local(from));
                self.jump_to(self.ip + 1)
            }
            Op::MovI(to, constant) => {
                let extended: Word = sign_extend_to(constant, IMM_BITS);

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
            Op::Call(ix) => {
                let func_id = ix as FunctionId; // zero extension

                let mut callee_frame =
                    StackFrame::new_returning_to(self.ip + 1);
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
        let word = self.code[self.ip];
        Op::decode_packed(word).unwrap()
    }

    fn jump_to(&mut self, instr: InstructionAddress) -> VMResult {
        if instr >= self.code.len() {
            return Err(VMError::InvalidInstructionAddress);
        }

        self.ip = instr;
        Ok(())
    }

    fn jump_to_function(&mut self, function_id: FunctionId) -> VMResult {
        if function_id >= self.functions.len() {
            return Err(VMError::InvalidFunctionId);
        }

        let start_address = self.functions[function_id];
        self.jump_to(start_address)
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
    use crate::{
        op::{ExtendedImmediate, Op},
        vm::VM,
    };

    fn encode_func(ops: Vec<Op>) -> Vec<u32> {
        ops.into_iter().map(|op| op.encode_packed()).collect()
    }

    #[test]
    fn basic_program() {
        let mut vm = VM::default();

        let main_id = vm.create_function();
        let main =
            vec![Op::MovI(0, 1), Op::MovI(1, 2), Op::Add(2, 0, 1), Op::Ret];
        vm.initialize_function(main_id, encode_func(main).into_boxed_slice());

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

        let main_id = vm.create_function();
        let add_id = vm.create_function();

        let main = vec![
            Op::MovI(0, 1),
            Op::MovI(1, 2),
            Op::Call(add_id as ExtendedImmediate), // call add
            Op::Ret,
        ];
        vm.initialize_function(main_id, encode_func(main).into_boxed_slice());

        let add = vec![Op::Add(0, 0, 1), Op::Ret];
        vm.initialize_function(add_id, encode_func(add).into_boxed_slice());

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
        let mut vm = VM::default();

        let main_id = vm.create_function();
        let add_id = vm.create_function();
        let double_id = vm.create_function();

        let main = vec![
            Op::MovI(0, 3),
            Op::Call(double_id as ExtendedImmediate), // call double
            Op::Ret,
        ];
        vm.initialize_function(main_id, encode_func(main).into_boxed_slice());

        let add = vec![Op::Add(0, 0, 1), Op::Ret];
        vm.initialize_function(add_id, encode_func(add).into_boxed_slice());

        let double = vec![
            Op::Mov(1, 0),
            Op::Call(add_id as ExtendedImmediate), // call add
            Op::Ret,
        ];
        vm.initialize_function(
            double_id,
            encode_func(double).into_boxed_slice(),
        );

        for _ in 0..7 {
            vm.step().expect("program should run without errors");
        }

        assert_eq!(6, vm.current_frame().locals[0]);

        vm.step().expect("program should run without errors");
        assert!(vm.call_stack.is_empty());
    }
}
