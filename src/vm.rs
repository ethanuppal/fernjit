// Copyright (Copyright (c) 2024 Ethan Uppal. All rightsrReserved.

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

    pub fn step(&mut self) -> Result<(), ExecuteError> {
        self.ip += match Op::decode_from(&self.code, &mut self.ip)
            .ok_or(ExecuteError::InvalidOp)?
        {
            Op::Mov(a, b) => {
                if a.is_valid() && b.is_valid() {
                    self.registers[a] = self.registers[b];
                    Ok(0)
                } else {
                    Err(ExecuteError::InvalidArgs)
                }
            }
            Op::MovI(a, i) => {
                if a.is_valid() {
                    self.registers[a] = i;
                    Ok(0)
                } else {
                    Err(ExecuteError::InvalidArgs)
                }
            }
            Op::Add(a, b, c) => {
                if a.is_valid() && b.is_valid() && c.is_valid() {
                    self.registers[a] = self.registers[b] + self.registers[c];
                    Ok(0)
                } else {
                    Err(ExecuteError::InvalidArgs)
                }
            }
        }?;
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
