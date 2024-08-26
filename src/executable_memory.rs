// Copyright (C) 2024 Ethan Uppal. All rights reserved.

use std::{io, ptr, slice};

/// Memory mapped with execute permissions.
pub struct ExecutableMemory {
    start: *mut u8,
    length: usize
}

impl ExecutableMemory {
    /// Maps executable memory of size at least `length`.
    pub fn of_size(length: usize) -> io::Result<ExecutableMemory> {
        unsafe {
            let page_size = {
                let result = libc::sysconf(libc::_SC_PAGESIZE);
                if result == -1 {
                    Err(io::Error::last_os_error())
                } else {
                    Ok(result as usize)
                }
            }?;
            let aligned_length = (length + page_size - 1) & !(page_size - 1);

            #[cfg(target_os = "macos")]
            let flags = libc::MAP_JIT | libc::MAP_ANON | libc::MAP_PRIVATE;

            #[cfg(not(target_os = "macos"))]
            let flags = libc::MAP_ANON | libc::MAP_PRIVATE;

            let start = libc::mmap(
                ptr::null_mut(),
                aligned_length,
                libc::PROT_READ | libc::PROT_WRITE | libc::PROT_EXEC,
                flags,
                -1,
                0
            );
            if start == libc::MAP_FAILED {
                return Err(io::Error::last_os_error());
            }
            // doesn't work on apple silicon :(
            // if libc::mprotect(
            //     start,
            //     aligned_length,
            //     libc::PROT_READ | libc::PROT_WRITE | libc::PROT_EXEC,
            // ) == -1
            // {
            //     return Err(io::Error::last_os_error());
            // }
            Ok(ExecutableMemory {
                start: start as *mut u8,
                length: aligned_length
            })
        }
    }

    pub fn start(&mut self) -> *mut u8 {
        self.start
    }

    pub fn length(&self) -> usize {
        self.length
    }

    pub fn as_slice_mut(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.start, self.length) }
    }
}

#[cfg(test)]
mod tests {
    use std::mem;

    use super::ExecutableMemory;

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn simple_func() {
        let mut jit_mem = ExecutableMemory::of_size(1024 * 1024)
            .expect("failed to map memory");

        // mov eax, 42
        // ret
        for (i, byte) in [0xB8, 0x2A, 0x00, 0x00, 0x00, 0xC3].iter().enumerate()
        {
            jit_mem.as_slice_mut()[i] = *byte;
        }

        unsafe {
            let ret_42: unsafe fn() -> i32 = mem::transmute(jit_mem.start());
            assert_eq!(42, ret_42());
        };
    }
}
