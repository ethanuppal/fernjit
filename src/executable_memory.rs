// Copyright (C) 2024 Ethan Uppal. All rights reserved.

use std::{io, ptr, slice};

pub struct ExecutableMemory {
    start: *mut u8,
    length: usize
}

impl ExecutableMemory {
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
            let start = libc::mmap(
                ptr::null_mut(),
                aligned_length,
                libc::PROT_READ | libc::PROT_WRITE | libc::PROT_EXEC,
                libc::MAP_JIT | libc::MAP_ANON | libc::MAP_PRIVATE,
                -1,
                0
            );
            if start == libc::MAP_FAILED {
                return Err(io::Error::last_os_error());
            }
            // doesn't work on silicon :(
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

    pub fn as_slice_mut(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.start, self.length) }
    }
}
