// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::error::CorruptKind;
use crate::inode::Inode;
use crate::iters::AsyncIterator;
use crate::iters::file_blocks::FsBlockIndex;
use crate::util::read_u32le;
use crate::{Ext4, Ext4Error};
use alloc::vec;
use alloc::vec::Vec;

enum BlockLocation {
    Direct(u8),
    Indirect(u32),
    DoubleIndirect(u32, u32),
    TripleIndirect(u32, u32, u32),
}

impl BlockLocation {
    fn new(block_within_file: u32) -> Self {
        if block_within_file <= 11 {
            Self::Direct(block_within_file as u8)
        } else if block_within_file <= 11 + 256 {
            Self::Indirect(block_within_file - 12)
        } else if block_within_file <= 11 + 256 + 256 * 256 {
            let block_within_indirect = block_within_file - 12 - 256;
            Self::DoubleIndirect(
                block_within_indirect / 256,
                block_within_indirect % 256,
            )
        } else {
            let block_within_double_indirect =
                block_within_file - 12 - 256 - 256 * 256;
            Self::TripleIndirect(
                block_within_double_indirect / (256 * 256),
                (block_within_double_indirect / 256) % 256,
                block_within_double_indirect % 256,
            )
        }
    }

    #[expect(unused)]
    fn next(&self, block_size: u32) -> Option<Self> {
        let blocks_per_indirect = block_size / 4;
        match self {
            Self::Direct(i) if *i < 11 => Some(Self::Direct(*i + 1)),
            Self::Direct(_) => Some(Self::Indirect(0)),
            Self::Indirect(i) if *i < blocks_per_indirect => {
                Some(Self::Indirect(*i + 1))
            }
            Self::Indirect(_) => Some(Self::DoubleIndirect(0, 0)),
            Self::DoubleIndirect(i, j) if *j < blocks_per_indirect => {
                Some(Self::DoubleIndirect(*i, *j + 1))
            }
            Self::DoubleIndirect(i, _) if *i < blocks_per_indirect => {
                Some(Self::DoubleIndirect(*i + 1, 0))
            }
            Self::DoubleIndirect(_, _) => Some(Self::TripleIndirect(0, 0, 0)),
            Self::TripleIndirect(i, j, k) if *k < blocks_per_indirect => {
                Some(Self::TripleIndirect(*i, *j, *k + 1))
            }
            Self::TripleIndirect(i, j, _) if *j < blocks_per_indirect => {
                Some(Self::TripleIndirect(*i, *j + 1, 0))
            }
            Self::TripleIndirect(i, _, _) if *i < blocks_per_indirect => {
                Some(Self::TripleIndirect(*i + 1, 0, 0))
            }
            Self::TripleIndirect(_, _, _) => None,
        }
    }

    #[expect(unused)]
    fn prev(&self, block_size: u32) -> Option<Self> {
        let blocks_per_indirect = block_size / 4;
        match self {
            Self::Direct(i) if *i > 0 => Some(Self::Direct(*i - 1)),
            Self::Direct(_) => None,
            Self::Indirect(i) if *i > 0 => Some(Self::Indirect(*i - 1)),
            Self::Indirect(_) => Some(Self::Direct(11)),
            Self::DoubleIndirect(i, j) if *j > 0 => {
                Some(Self::DoubleIndirect(*i, *j - 1))
            }
            Self::DoubleIndirect(i, _) if *i > 0 => {
                Some(Self::DoubleIndirect(*i - 1, blocks_per_indirect))
            }
            Self::DoubleIndirect(_, _) => {
                Some(Self::Indirect(blocks_per_indirect))
            }
            Self::TripleIndirect(i, j, k) if *k > 0 => {
                Some(Self::TripleIndirect(*i, *j, *k - 1))
            }
            Self::TripleIndirect(i, j, _) if *j > 0 => {
                Some(Self::TripleIndirect(*i, *j - 1, blocks_per_indirect))
            }
            Self::TripleIndirect(i, _, _) if *i > 0 => {
                Some(Self::TripleIndirect(
                    *i - 1,
                    blocks_per_indirect,
                    blocks_per_indirect,
                ))
            }
            Self::TripleIndirect(_, _, _) => Some(Self::DoubleIndirect(
                blocks_per_indirect,
                blocks_per_indirect,
            )),
        }
    }
}

/// Block map iterator.
///
/// Block maps are how file data was stored prior to extents. Unlike
/// extents, each block of the file is stored. This makes block maps
/// much less storage efficient.
///
/// The root of the block map structure is stored directly in the
/// inode. It consists of 15 block indices. Here, as in the rest of the
/// block map structure, a block index is a `u32` containing the
/// absolute index of a block in the filesystem.
///
/// Indices `0..=11` in the root node are direct. That is, they point
/// directly to a block of file data.
///
/// Index 12 points to an indirect block. This block contains an array
/// of direct block indices. The size of the array depends on the block
/// size; a 1KiB block can store 256 indices (1024÷4).
///
/// Index 13 points to a doubly-indirect block. This block contains an
/// array of indirect block indices. Each of those indices points to a
/// block containing direct indices.
///
/// Index 14 points to a triply-indirect block. This block contains an
/// array of indirect block indices, each of which points to a block
/// that also contains indirect indices, each of which points to a block
/// containing direct indices.
///
/// Indices are only initialized up to the size of the file.
///
/// A block index of zero indicates a hole.
pub(super) struct BlockMap {
    fs: Ext4,

    /// Root of the block map. This is copied directly from the inode.
    level_0: [u32; 15],

    /// Index within `level_0`.
    level_0_index: usize,

    /// Number of blocks the iterator has yielded so far.
    num_blocks_yielded: u32,

    /// Total number of blocks in the file.
    num_blocks_total: u32,

    /// Iterators through the deeper levels of the block map.
    level_1: Option<IndirectBlockIter>,
    level_2: Option<DoubleIndirectBlockIter>,
    level_3: Option<TripleIndirectBlockIter>,

    is_done: bool,
}

impl BlockMap {
    const NUM_ENTRIES: usize = 15;

    pub(super) fn new(fs: Ext4, inode: &Inode) -> Self {
        let mut level_0 = [0; Self::NUM_ENTRIES];
        for (i, dst) in level_0.iter_mut().enumerate() {
            // OK to unwrap: `i` is at most 14, so the product is at
            // most `14*4=56`, which fits in a `usize`.
            let src_offset: usize = i.checked_mul(size_of::<u32>()).unwrap();
            *dst = read_u32le(&inode.inline_data(), src_offset);
        }

        Self {
            fs,
            level_0,
            num_blocks_yielded: 0,
            num_blocks_total: inode.file_size_in_blocks(),
            level_0_index: 0,
            level_1: None,
            level_2: None,
            level_3: None,
            is_done: false,
        }
    }

    /// Returns 0 if the block is a hole
    async fn get_indirect_block(
        &self,
        block_index: u32,
        block_within_indirect: u32,
    ) -> Result<u32, Ext4Error> {
        let mut dst = [0; 4];
        self.fs
            .read_from_block(
                block_index as FsBlockIndex,
                block_within_indirect,
                &mut dst,
            )
            .await?;
        Ok(read_u32le(&dst, 0))
    }

    /// Returns Ok(None) if the block within the file is out of bounds.
    pub(crate) async fn get(
        &self,
        block_within_file: u32,
    ) -> Result<Option<u32>, Ext4Error> {
        if block_within_file >= self.num_blocks_total {
            return Ok(None);
        }
        match BlockLocation::new(block_within_file) {
            BlockLocation::Direct(i) => Ok(Some(self.level_0[i as usize])),
            BlockLocation::Indirect(i) => {
                if self.level_0[12] == 0 {
                    return Err(CorruptKind::MissingPointerBlock {
                        block: block_within_file,
                        level: 1,
                    })?;
                }
                Ok(Some(self.get_indirect_block(self.level_0[12], i).await?))
            }
            BlockLocation::DoubleIndirect(i, j) => {
                if self.level_0[13] == 0 {
                    return Err(CorruptKind::MissingPointerBlock {
                        block: block_within_file,
                        level: 1,
                    })?;
                }
                let indirect_block =
                    self.get_indirect_block(self.level_0[13], i).await?;
                if indirect_block == 0 {
                    return Err(CorruptKind::MissingPointerBlock {
                        block: block_within_file,
                        level: 2,
                    })?;
                }
                Ok(Some(self.get_indirect_block(indirect_block, j).await?))
            }
            BlockLocation::TripleIndirect(i, j, k) => {
                if self.level_0[14] == 0 {
                    return Err(CorruptKind::MissingPointerBlock {
                        block: block_within_file,
                        level: 1,
                    })?;
                }
                let double_indirect_block =
                    self.get_indirect_block(self.level_0[14], i).await?;
                if double_indirect_block == 0 {
                    return Err(CorruptKind::MissingPointerBlock {
                        block: block_within_file,
                        level: 2,
                    })?;
                }
                let indirect_block =
                    self.get_indirect_block(double_indirect_block, j).await?;
                if indirect_block == 0 {
                    return Err(CorruptKind::MissingPointerBlock {
                        block: block_within_file,
                        level: 3,
                    })?;
                }
                Ok(Some(self.get_indirect_block(indirect_block, k).await?))
            }
        }
    }

    async fn allocate_one_inner(
        &mut self,
        inode: &Inode,
        id: FsBlockIndex,
    ) -> Result<(), Ext4Error> {
        match BlockLocation::new(self.num_blocks_total) {
            BlockLocation::Direct(i) => {
                self.level_0[i as usize] = id
                    .try_into()
                    .map_err(|_| Ext4Error::BlockMapTooManyBlocks)?
            }
            BlockLocation::Indirect(i) => {
                if self.level_0[12] == 0 {
                    self.level_0[12] = self
                        .fs
                        .alloc_block(inode)
                        .await?
                        .try_into()
                        .map_err(|_| Ext4Error::BlockMapTooManyBlocks)?;
                }
                self.fs
                    .write_to_block(
                        FsBlockIndex::from(self.level_0[12]),
                        i,
                        &id.to_le_bytes(),
                    )
                    .await?;
            }
            BlockLocation::DoubleIndirect(i, j) => {
                if self.level_0[13] == 0 {
                    self.level_0[13] = self
                        .fs
                        .alloc_block(inode)
                        .await?
                        .try_into()
                        .map_err(|_| Ext4Error::BlockMapTooManyBlocks)?;
                }
                let indirect_block =
                    self.get_indirect_block(self.level_0[13], i).await?;
                if indirect_block == 0 {
                    let new_indirect_block = self.fs.alloc_block(inode).await?;
                    self.fs
                        .write_to_block(
                            FsBlockIndex::from(self.level_0[13]),
                            i,
                            &new_indirect_block.to_le_bytes(),
                        )
                        .await?;
                    self.fs
                        .write_to_block(
                            FsBlockIndex::from(new_indirect_block),
                            j,
                            &id.to_le_bytes(),
                        )
                        .await?;
                } else {
                    self.fs
                        .write_to_block(
                            FsBlockIndex::from(indirect_block),
                            j,
                            &id.to_le_bytes(),
                        )
                        .await?;
                }
            }
            _ => todo!(),
        }
        self.num_blocks_total = self
            .num_blocks_total
            .checked_add(1)
            .ok_or(Ext4Error::FileTooLarge)?;
        if self.is_done && self.num_blocks_yielded < self.num_blocks_total {
            self.is_done = false;
        }
        Ok(())
    }

    async fn allocate_one(&mut self, inode: &Inode) -> Result<(), Ext4Error> {
        let id = self.fs.alloc_block(inode).await?;
        self.allocate_one_inner(inode, id).await
    }

    pub(crate) async fn allocate(
        &mut self,
        inode: &mut Inode,
        amount: u32,
    ) -> Result<(), Ext4Error> {
        if self.num_blocks_total.checked_add(amount).is_none() {
            return Err(Ext4Error::FileTooLarge);
        }
        for _ in 0..amount {
            self.allocate_one(inode).await?;
        }
        let mut new_inline_data =
            vec![0; self.level_0.len() * size_of::<u32>()];
        for (i, block_index) in self.level_0.iter().enumerate() {
            // OK to unwrap: `i` is at most 14, so the product is at
            // most `14*4=56`, which fits in a `usize`.
            let dst_offset: usize = i.checked_mul(size_of::<u32>()).unwrap();
            new_inline_data[dst_offset..dst_offset + 4]
                .copy_from_slice(&block_index.to_le_bytes());
        }
        inode.set_inline_data(new_inline_data.try_into().unwrap());
        inode.write(&self.fs).await?;
        Ok(())
    }

    async fn free_one(&mut self) -> Result<(), Ext4Error> {
        let block_index = self
            .get(self.num_blocks_total - 1)
            .await?
            .ok_or(Ext4Error::NoSpace)?; // TODO: Better error
        let block_location = BlockLocation::new(self.num_blocks_total - 1);
        self.fs.free_block(block_index as FsBlockIndex).await?;
        match block_location {
            BlockLocation::Direct(i) => self.level_0[i as usize] = 0,
            BlockLocation::Indirect(i) => {
                if self.level_0[12] == 0 {
                    return Err(CorruptKind::MissingPointerBlock {
                        block: self.num_blocks_total - 1,
                        level: 1,
                    })?;
                }
                self.fs
                    .write_to_block(
                        FsBlockIndex::from(self.level_0[12]),
                        i,
                        &0u32.to_le_bytes(),
                    )
                    .await?;
                if i == 0 {
                    // If this was the last block in the indirect block, free the indirect block as well.
                    self.fs
                        .free_block(self.level_0[12] as FsBlockIndex)
                        .await?;
                    self.level_0[12] = 0;
                }
            }
            BlockLocation::DoubleIndirect(i, j) => {
                if self.level_0[13] == 0 {
                    return Err(CorruptKind::MissingPointerBlock {
                        block: self.num_blocks_total - 1,
                        level: 1,
                    })?;
                }
                let indirect_block =
                    self.get_indirect_block(self.level_0[13], i).await?;
                if indirect_block == 0 {
                    return Err(CorruptKind::MissingPointerBlock {
                        block: self.num_blocks_total - 1,
                        level: 2,
                    })?;
                }
                self.fs
                    .write_to_block(
                        FsBlockIndex::from(indirect_block),
                        j,
                        &0u32.to_le_bytes(),
                    )
                    .await?;
                if j == 0 {
                    // If this was the last block in the indirect block, free the indirect block as well.
                    self.fs.free_block(indirect_block as FsBlockIndex).await?;
                    self.fs
                        .write_to_block(
                            FsBlockIndex::from(self.level_0[13]),
                            i,
                            &0u32.to_le_bytes(),
                        )
                        .await?;
                    if i == 0 {
                        // If this was the last block in the double indirect block, free the double indirect block as well.
                        self.fs
                            .free_block(self.level_0[13] as FsBlockIndex)
                            .await?;
                        self.level_0[13] = 0;
                    }
                }
            }
            _ => todo!(),
        }
        self.num_blocks_total = self
            .num_blocks_total
            .checked_sub(1)
            .ok_or(Ext4Error::NoSpace)?; // TODO: Better error
        if self.num_blocks_yielded > self.num_blocks_total {
            self.num_blocks_yielded = self.num_blocks_total;
            self.is_done = true;
        }
        Ok(())
    }

    pub(crate) async fn free(
        &mut self,
        inode: &mut Inode,
        amount: u32,
    ) -> Result<(), Ext4Error> {
        if amount > self.num_blocks_total {
            // TODO: Better error
            return Err(Ext4Error::NoSpace);
        }
        for _ in 0..amount {
            self.free_one().await?;
        }
        let mut new_inline_data =
            vec![0; self.level_0.len() * size_of::<u32>()];
        for (i, block_index) in self.level_0.iter().enumerate() {
            // OK to unwrap: `i` is at most 14, so the product is at
            // most `14*4=56`, which fits in a `usize`.
            let dst_offset: usize = i.checked_mul(size_of::<u32>()).unwrap();
            new_inline_data[dst_offset..dst_offset + 4]
                .copy_from_slice(&block_index.to_le_bytes());
        }
        inode.set_inline_data(new_inline_data.try_into().unwrap());
        inode.write(&self.fs).await?;
        Ok(())
    }

    pub(crate) async fn reallocate_hole(
        &mut self,
        inode: &mut Inode,
        id_in_file: u32,
    ) -> Result<(), Ext4Error> {
        if id_in_file >= self.num_blocks_total {
            return Err(Ext4Error::FileTooLarge); // TODO: Better error
        }
        if self.get(id_in_file).await?.is_some() {
            return Err(Ext4Error::NoSpace); // TODO: Better error
        }
        let id = self.fs.alloc_block(inode).await?;
        match BlockLocation::new(id_in_file) {
            BlockLocation::Direct(i) => {
                self.level_0[i as usize] = id
                    .try_into()
                    .map_err(|_| Ext4Error::BlockMapTooManyBlocks)?
            }
            BlockLocation::Indirect(i) => {
                if self.level_0[12] == 0 {
                    self.level_0[12] = self
                        .fs
                        .alloc_block(inode)
                        .await?
                        .try_into()
                        .map_err(|_| Ext4Error::BlockMapTooManyBlocks)?;
                }
                self.fs
                    .write_to_block(
                        FsBlockIndex::from(self.level_0[12]),
                        i,
                        &id.to_le_bytes(),
                    )
                    .await?;
            }
            BlockLocation::DoubleIndirect(i, j) => {
                if self.level_0[13] == 0 {
                    self.level_0[13] = self
                        .fs
                        .alloc_block(inode)
                        .await?
                        .try_into()
                        .map_err(|_| Ext4Error::BlockMapTooManyBlocks)?;
                }
                let indirect_block =
                    self.get_indirect_block(self.level_0[13], i).await?;
                if indirect_block == 0 {
                    let new_indirect_block = self.fs.alloc_block(inode).await?;
                    self.fs
                        .write_to_block(
                            FsBlockIndex::from(self.level_0[13]),
                            i,
                            &new_indirect_block.to_le_bytes(),
                        )
                        .await?;
                    self.fs
                        .write_to_block(
                            FsBlockIndex::from(new_indirect_block),
                            j,
                            &id.to_le_bytes(),
                        )
                        .await?;
                } else {
                    self.fs
                        .write_to_block(
                            FsBlockIndex::from(indirect_block),
                            j,
                            &id.to_le_bytes(),
                        )
                        .await?;
                }
            }
            _ => todo!(),
        }
        Ok(())
    }

    pub(crate) async fn allocate_hole(
        &mut self,
        inode: &mut Inode,
        amount: u32,
    ) -> Result<(), Ext4Error> {
        if self.num_blocks_total.checked_add(amount).is_none() {
            return Err(Ext4Error::FileTooLarge);
        }
        for _ in 0..amount {
            self.allocate_one_inner(inode, 0).await?;
        }
        if self.is_done && self.num_blocks_yielded < self.num_blocks_total {
            self.is_done = false;
        }
        Ok(())
    }

    #[track_caller]
    fn increment_num_blocks_yielded(&mut self) {
        // OK to unwrap: `num_blocks_yielded` is less than
        // `num_blocks_total` (checked at the beginning of `next_impl`),
        // so adding 1 cannot fail.
        self.num_blocks_yielded =
            self.num_blocks_yielded.checked_add(1).unwrap();
    }

    async fn next_impl(&mut self) -> Result<Option<FsBlockIndex>, Ext4Error> {
        if self.num_blocks_yielded >= self.num_blocks_total {
            self.is_done = true;
            return Ok(None);
        }

        let Some(block_0) = self.level_0.get(self.level_0_index).copied()
        else {
            self.is_done = true;
            return Ok(None);
        };

        let ret: u32 = if self.level_0_index <= 11 {
            // OK to unwrap: `level_0_index` is at most `11`.
            self.level_0_index = self.level_0_index.checked_add(1).unwrap();
            self.increment_num_blocks_yielded();
            block_0
        } else if self.level_0_index == 12 {
            if let Some(level_1) = &mut self.level_1 {
                if let Some(block_index) = level_1.next() {
                    self.increment_num_blocks_yielded();
                    return Ok(Some(FsBlockIndex::from(block_index)));
                } else {
                    self.level_1 = None;
                    self.level_0_index = 13;
                    return Ok(None);
                }
            } else {
                self.level_1 = Some(
                    IndirectBlockIter::new(self.fs.clone(), block_0).await?,
                );
                return Ok(None);
            }
        } else if self.level_0_index == 13 {
            if let Some(level_2) = &mut self.level_2 {
                if let Some(block_index) = level_2.next().await {
                    let block_index = block_index?;
                    self.increment_num_blocks_yielded();
                    return Ok(Some(FsBlockIndex::from(block_index)));
                } else {
                    self.level_2 = None;
                    self.level_0_index = 14;
                    return Ok(None);
                }
            } else {
                self.level_2 = Some(
                    DoubleIndirectBlockIter::new(self.fs.clone(), block_0)
                        .await?,
                );
                return Ok(None);
            }
        } else if self.level_0_index == 14 {
            if let Some(level_3) = &mut self.level_3 {
                if let Some(block_index) = level_3.next().await {
                    let block_index = block_index?;
                    self.increment_num_blocks_yielded();
                    return Ok(Some(FsBlockIndex::from(block_index)));
                } else {
                    self.level_3 = None;
                    self.level_0_index = 15;
                    return Ok(None);
                }
            } else {
                self.level_3 = Some(
                    TripleIndirectBlockIter::new(self.fs.clone(), block_0)
                        .await?,
                );
                return Ok(None);
            }
        } else {
            todo!();
        };

        Ok(Some(FsBlockIndex::from(ret)))
    }
}

impl_result_iter!(BlockMap, FsBlockIndex);

struct IndirectBlockIter {
    /// Indirect block data. The block contains an array of `u32`, each
    /// of which is a block number.
    block: Vec<u8>,

    /// Current index within the block. This is a byte index, so each
    /// iterator step moves it forward by four (the size of a `u32`).
    index_within_block: usize,
}

impl IndirectBlockIter {
    async fn new(fs: Ext4, block_index: u32) -> Result<Self, Ext4Error> {
        let mut block = vec![0u8; fs.0.superblock.block_size().to_usize()];
        fs.read_from_block(FsBlockIndex::from(block_index), 0, &mut block)
            .await?;

        Ok(Self {
            block,
            index_within_block: 0,
        })
    }
}

impl Iterator for IndirectBlockIter {
    /// Absolute block index.
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        if self.index_within_block >= self.block.len() {
            return None;
        }

        let block_index = read_u32le(&self.block, self.index_within_block);

        // OK to unwrap: `index_within_block` is less than `block.len()`
        // (checked above). The index is always incremented by 4, and
        // the `BlockSize` is guaranteed to be an even multiple of 4, so
        // the index is at most `block.len() - 4` at this point.
        self.index_within_block = self
            .index_within_block
            .checked_add(size_of::<u32>())
            .unwrap();

        Some(block_index)
    }
}

struct DoubleIndirectBlockIter {
    fs: Ext4,
    indirect_0: IndirectBlockIter,
    indirect_1: Option<IndirectBlockIter>,
    is_done: bool,
}

impl DoubleIndirectBlockIter {
    async fn new(fs: Ext4, block_index: u32) -> Result<Self, Ext4Error> {
        Ok(Self {
            indirect_0: IndirectBlockIter::new(fs.clone(), block_index).await?,
            indirect_1: None,
            fs,
            is_done: false,
        })
    }

    async fn next_impl(&mut self) -> Result<Option<u32>, Ext4Error> {
        if let Some(indirect_1) = &mut self.indirect_1 {
            if let Some(block_index) = indirect_1.next() {
                Ok(Some(block_index))
            } else {
                self.indirect_1 = None;
                Ok(None)
            }
        } else if let Some(block_index) = self.indirect_0.next() {
            self.indirect_1 = Some(
                IndirectBlockIter::new(self.fs.clone(), block_index).await?,
            );
            Ok(None)
        } else {
            self.is_done = true;
            Ok(None)
        }
    }
}

impl_result_iter!(DoubleIndirectBlockIter, u32);

struct TripleIndirectBlockIter {
    fs: Ext4,
    indirect_0: IndirectBlockIter,
    indirect_1: Option<DoubleIndirectBlockIter>,
    is_done: bool,
}

impl TripleIndirectBlockIter {
    async fn new(fs: Ext4, block_index: u32) -> Result<Self, Ext4Error> {
        Ok(Self {
            indirect_0: IndirectBlockIter::new(fs.clone(), block_index).await?,
            indirect_1: None,
            fs,
            is_done: false,
        })
    }

    async fn next_impl(&mut self) -> Result<Option<u32>, Ext4Error> {
        if let Some(indirect_1) = &mut self.indirect_1 {
            if let Some(block_index) = indirect_1.next().await {
                let block_index = block_index?;
                Ok(Some(block_index))
            } else {
                self.indirect_1 = None;
                Ok(None)
            }
        } else if let Some(block_index) = self.indirect_0.next() {
            self.indirect_1 = Some(
                DoubleIndirectBlockIter::new(self.fs.clone(), block_index)
                    .await?,
            );
            Ok(None)
        } else {
            self.is_done = true;
            Ok(None)
        }
    }
}

impl_result_iter!(TripleIndirectBlockIter, u32);
