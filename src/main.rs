// Copyright (C) 2024 Ethan Uppal. All rights reserved.

use fernjit::executable_memory::ExecutableMemory;
use std::{io, mem};

fn main() -> io::Result<()> {
    let mut jit_mem = ExecutableMemory::of_size(1024 * 1024)?;

    for (i, byte) in [
        0x48, 0xC7, 0xC0, 0x01, 0x00, 0x00, 0x02, 0x48, 0xC7, 0xC7, 0x2A, 0x00,
        0x00, 0x00, 0x0F, 0x05
    ]
    .iter()
    .enumerate()
    {
        jit_mem.as_slice_mut()[i] = *byte;
    }

    let func: fn() -> () = unsafe { mem::transmute(jit_mem.start()) };
    func();
    Ok(())
}
