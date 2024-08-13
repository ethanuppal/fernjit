// Copyright (C) 2024 Ethan Uppal. All rights reserved.
use crate::{
    arch::{IsValid, Word, CODE_SIZE, MEMORY_SIZE, REGISTER_COUNT},
    opcode::Op
};

pub struct VM {
    pub code: [Word; CODE_SIZE],
    pub registers: [Word; REGISTER_COUNT],
    pub memory: [Word; MEMORY_SIZE],
    ip: usize
}

#[derive(Debug)]
pub enum ExecuteError {
    InvalidOp,
    InvalidArgs
}

impl Default for VM {
    fn default() -> Self {
        Self {
            code: [0; CODE_SIZE],
            registers: [0; REGISTER_COUNT],
            memory: [0; MEMORY_SIZE],
            ip: 0
        }
    }
}

impl VM {
    pub fn jump(&mut self, pos: usize) {
        assert!(pos < self.code.len());
        self.ip = pos;
    }

    pub fn validate(&self) -> Result<(Op, usize), ExecuteError> {
        let (op, length) = Op::decode_from(&self.code, self.ip)
            .ok_or(ExecuteError::InvalidOp)?;
        match op {
            Op::Mov(a, b) => {
                if a.is_valid() && b.is_valid() {
                    Ok(())
                } else {
                    Err(ExecuteError::InvalidArgs)
                }
            }
            Op::MovI(a, _) => {
                if a.is_valid() {
                    Ok(())
                } else {
                    Err(ExecuteError::InvalidArgs)
                }
            }
            Op::Add(a, b, c) => {
                if a.is_valid() && b.is_valid() && c.is_valid() {
                    Ok(())
                } else {
                    Err(ExecuteError::InvalidArgs)
                }
            }
        }
        .and(Ok((op, length)))
    }

    pub fn step(&mut self) -> Result<(), ExecuteError> {
        let (op, length) = {
            #[cfg(feature = "validate")]
            self.validate()?;

            #[cfg(not(feature = "validate"))]
            unsafe {
                Op::decode_from(&self.code, self.ip).unwrap_unchecked()
            }
        };

        self.ip += length
            + match op {
                Op::Mov(a, b) => {
                    self.registers[a] = self.registers[b];
                    0
                }
                Op::MovI(a, i) => {
                    self.registers[a] = i;
                    0
                }
                Op::Add(a, b, c) => {
                    self.registers[a] = self.registers[b] + self.registers[c];
                    0
                }
            };
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::VM;
    use crate::opcode::Op;

    #[test]
    fn basic_program() {
        let mut vm = VM::default();
        for (i, op) in [Op::MovI(0, 1), Op::MovI(1, 2), Op::Add(2, 0, 1)]
            .iter()
            .enumerate()
        {
            vm.code[i] =
                op.encode_packed().expect("constructed malformed program");
        }
        vm.jump(0);
        for _ in 0..3 {
            vm.step().expect("failed to execute operation");
        }
        assert_eq!(1, vm.registers[0]);
        assert_eq!(2, vm.registers[1]);
        assert_eq!(3, vm.registers[2]);
    }
}
