// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::block_index::{FileBlockIndex, FsBlockIndex};
use crate::util::u64_to_hilo;

/// Contiguous range of blocks that contain file data.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct Extent {
    /// Offset of the block within the file.
    pub(crate) block_within_file: FileBlockIndex,

    /// This is the actual block within the filesystem.
    pub(crate) start_block: FsBlockIndex,

    /// Number of blocks (both within the file, and on the filesystem).
    pub(crate) num_blocks: u16,

    pub(crate) is_initialized: bool,
}

impl Extent {
    pub(crate) fn new(
        block_within_file: FileBlockIndex,
        start_block: FsBlockIndex,
        num_blocks: u16,
    ) -> Self {
        // MSB of num_blocks is used to indicate whether the extent is initialized or not.
        let is_initialized = (num_blocks & 0x8000) == 0;
        let num_blocks = num_blocks & 0x7FFF;
        Self {
            block_within_file,
            start_block,
            num_blocks,
            is_initialized,
        }
    }

    #[expect(unused)]
    pub(crate) fn to_bytes(&self) -> [u8; 12] {
        let mut bytes = [0u8; 12];
        bytes[0..4].copy_from_slice(&self.block_within_file.to_le_bytes());
        // ee_len
        let ee_len = if self.is_initialized {
            self.num_blocks
        } else {
            self.num_blocks | 0x8000
        };
        bytes[4..6].copy_from_slice(&ee_len.to_le_bytes());
        let (ee_start_hi, ee_start_low) = u64_to_hilo(self.start_block);
        let ee_start_hi = u16::try_from(ee_start_hi).expect("start_block must fit in 48 bits");
        bytes[6..8].copy_from_slice(&ee_start_hi.to_le_bytes());
        bytes[8..12].copy_from_slice(&ee_start_low.to_le_bytes());
        bytes
    }
}
