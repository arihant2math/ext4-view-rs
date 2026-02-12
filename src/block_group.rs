// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::Ext4Read;
use crate::block_index::FsBlockIndex;
use crate::checksum::Checksum;
use crate::error::{CorruptKind, Ext4Error};
use crate::features::{IncompatibleFeatures, ReadOnlyCompatibleFeatures};
use crate::superblock::Superblock;
use crate::util::{
    read_u16le, read_u32le, u32_from_hilo, u64_from_hilo, usize_from_u32,
};
use alloc::vec;
use alloc::vec::Vec;
use core::ops::Deref;

pub(crate) type BlockGroupIndex = u32;

#[derive(Copy, Clone, Debug)]
enum BlockGroupDescriptorBytes {
    OnDisk32([u8; BlockGroupDescriptor::SIZE_IN_BYTES_ON_DISK_32]),
    OnDisk64([u8; BlockGroupDescriptor::SIZE_IN_BYTES_ON_DISK_64]),
}

impl Deref for BlockGroupDescriptorBytes {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        match self {
            BlockGroupDescriptorBytes::OnDisk32(bytes) => bytes,
            BlockGroupDescriptorBytes::OnDisk64(bytes) => bytes,
        }
    }
}

#[derive(Debug)]
pub(crate) struct BlockGroupDescriptor {
    bytes: BlockGroupDescriptorBytes,
}

#[expect(dead_code)]
impl BlockGroupDescriptor {
    pub(crate) const SIZE_IN_BYTES_ON_DISK_32: usize = 32;
    pub(crate) const SIZE_IN_BYTES_ON_DISK_64: usize = 64;
    const BG_CHECKSUM_OFFSET: usize = 0x1e;

    /// Parse a block group descriptor from raw bytes read from disk.
    ///
    /// # Panics
    /// If `bytes` is not at least [`Self::SIZE_IN_BYTES_ON_DISK`] bytes long.
    fn from_bytes(superblock: &Superblock, bytes: &[u8]) -> Self {
        if superblock
            .incompatible_features()
            .contains(IncompatibleFeatures::IS_64BIT)
        {
            assert_eq!(bytes.len(), Self::SIZE_IN_BYTES_ON_DISK_64);
            Self {
                bytes: BlockGroupDescriptorBytes::OnDisk64(
                    bytes[..Self::SIZE_IN_BYTES_ON_DISK_64].try_into().unwrap(),
                ),
            }
        } else {
            assert_eq!(bytes.len(), Self::SIZE_IN_BYTES_ON_DISK_32);
            Self {
                bytes: BlockGroupDescriptorBytes::OnDisk32(
                    bytes[..Self::SIZE_IN_BYTES_ON_DISK_32].try_into().unwrap(),
                ),
            }
        }
    }

    pub(crate) fn block_bitmap_block(&self) -> FsBlockIndex {
        const LO_OFFSET: usize = 0x0;
        const HI_OFFSET: usize = 0x20;
        let (bg_block_bitmap_hi, bg_block_bitmap_lo) = match self.bytes {
            BlockGroupDescriptorBytes::OnDisk32(bytes) => {
                (0, read_u32le(&bytes, LO_OFFSET))
            }
            BlockGroupDescriptorBytes::OnDisk64(bytes) => {
                (read_u32le(&bytes, HI_OFFSET), read_u32le(&bytes, LO_OFFSET))
            }
        };

        u64_from_hilo(bg_block_bitmap_hi, bg_block_bitmap_lo)
            .try_into()
            .unwrap()
    }

    pub(crate) fn inode_bitmap_block(&self) -> FsBlockIndex {
        const LO_OFFSET: usize = 0x4;
        const HI_OFFSET: usize = 0x24;
        let (bg_inode_bitmap_hi, bg_inode_bitmap_lo) = match self.bytes {
            BlockGroupDescriptorBytes::OnDisk32(bytes) => {
                (0, read_u32le(&bytes, LO_OFFSET))
            }
            BlockGroupDescriptorBytes::OnDisk64(bytes) => {
                (read_u32le(&bytes, HI_OFFSET), read_u32le(&bytes, LO_OFFSET))
            }
        };

        u64_from_hilo(bg_inode_bitmap_hi, bg_inode_bitmap_lo)
            .try_into()
            .unwrap()
    }

    pub(crate) fn inode_table_first_block(&self) -> FsBlockIndex {
        const LO_OFFSET: usize = 0x8;
        const HI_OFFSET: usize = 0x28;
        let (bg_inode_table_hi, bg_inode_table_lo) = match self.bytes {
            BlockGroupDescriptorBytes::OnDisk32(bytes) => {
                (0, read_u32le(&bytes, LO_OFFSET))
            }
            BlockGroupDescriptorBytes::OnDisk64(bytes) => {
                (read_u32le(&bytes, HI_OFFSET), read_u32le(&bytes, LO_OFFSET))
            }
        };

        u64_from_hilo(bg_inode_table_hi, bg_inode_table_lo)
            .try_into()
            .unwrap()
    }

    pub(crate) fn free_blocks_count(&self) -> u32 {
        const LO_OFFSET: usize = 0xC;
        const HI_OFFSET: usize = 0x2C;
        let (bg_free_blocks_count_hi, bg_free_blocks_count_lo) = match self
            .bytes
        {
            BlockGroupDescriptorBytes::OnDisk32(bytes) => {
                (0, read_u16le(&bytes, LO_OFFSET))
            }
            BlockGroupDescriptorBytes::OnDisk64(bytes) => {
                (read_u16le(&bytes, HI_OFFSET), read_u16le(&bytes, LO_OFFSET))
            }
        };

        u32_from_hilo(bg_free_blocks_count_hi, bg_free_blocks_count_lo)
    }

    pub(crate) fn free_inodes_count(&self) -> u32 {
        const LO_OFFSET: usize = 0xE;
        const HI_OFFSET: usize = 0x2E;
        let (bg_free_inodes_count_hi, bg_free_inodes_count_lo) = match self
            .bytes
        {
            BlockGroupDescriptorBytes::OnDisk32(bytes) => {
                (0, read_u16le(&bytes, LO_OFFSET))
            }
            BlockGroupDescriptorBytes::OnDisk64(bytes) => {
                (read_u16le(&bytes, HI_OFFSET), read_u16le(&bytes, LO_OFFSET))
            }
        };

        u32_from_hilo(bg_free_inodes_count_hi, bg_free_inodes_count_lo)
    }

    pub(crate) fn used_dirs_count(&self) -> u32 {
        const LO_OFFSET: usize = 0x10;
        const HI_OFFSET: usize = 0x30;
        let (bg_used_dirs_count_hi, bg_used_dirs_count_lo) = match self.bytes {
            BlockGroupDescriptorBytes::OnDisk32(bytes) => {
                (0, read_u16le(&bytes, LO_OFFSET))
            }
            BlockGroupDescriptorBytes::OnDisk64(bytes) => {
                (read_u16le(&bytes, HI_OFFSET), read_u16le(&bytes, LO_OFFSET))
            }
        };

        u32_from_hilo(bg_used_dirs_count_hi, bg_used_dirs_count_lo)
    }

    pub(crate) fn checksum(&self) -> u16 {
        read_u16le(self.bytes.deref(), Self::BG_CHECKSUM_OFFSET)
    }

    /// Map from a block group descriptor index to the absolute byte
    /// within the file where the descriptor starts.
    fn get_start_byte(
        sb: &Superblock,
        bgd_index: BlockGroupIndex,
    ) -> Option<u64> {
        let bgd_start_block: u32 = if sb.block_size() == 1024 { 2 } else { 1 };
        let bgd_per_block = sb
            .block_size()
            .to_u32()
            .checked_div(u32::from(sb.block_group_descriptor_size()))?;
        let block_index = bgd_start_block
            .checked_add(bgd_index.checked_div(bgd_per_block)?)?;
        let offset_within_block = (bgd_index.checked_rem(bgd_per_block)?)
            .checked_mul(u32::from(sb.block_group_descriptor_size()))?;

        u64::from(block_index)
            .checked_mul(sb.block_size().to_u64())?
            .checked_add(u64::from(offset_within_block))
    }

    /// Read a block group descriptor.
    async fn read(
        sb: &Superblock,
        reader: &mut dyn Ext4Read,
        bgd_index: BlockGroupIndex,
    ) -> Result<Self, Ext4Error> {
        // Allocate a byte vec to read the raw data into.
        let block_group_descriptor_size =
            usize::from(sb.block_group_descriptor_size());
        let mut data = vec![0; block_group_descriptor_size];

        let start = Self::get_start_byte(sb, bgd_index)
            .ok_or(CorruptKind::BlockGroupDescriptor(bgd_index))?;
        reader.read(start, &mut data).await.map_err(Ext4Error::Io)?;

        let block_group_descriptor = Self::from_bytes(sb, &data);

        let has_metadata_checksums = sb
            .read_only_compatible_features()
            .contains(ReadOnlyCompatibleFeatures::METADATA_CHECKSUMS);

        // Verify the descriptor checksum.
        if has_metadata_checksums {
            let mut checksum = Checksum::with_seed(sb.checksum_seed());
            checksum.update_u32_le(bgd_index);
            // Up to the checksum field.
            checksum.update(&data[..Self::BG_CHECKSUM_OFFSET]);
            // Zero'd checksum field.
            checksum.update_u16_le(0);
            // Rest of the block group descriptor.
            checksum.update(&data[Self::BG_CHECKSUM_OFFSET + 2..]);
            // Truncate to the lower 16 bits.
            let checksum = u16::try_from(checksum.finalize() & 0xffff).unwrap();

            if checksum != block_group_descriptor.checksum() {
                return Err(CorruptKind::BlockGroupDescriptorChecksum(
                    bgd_index,
                )
                .into());
            }
        } else if sb
            .read_only_compatible_features()
            .contains(ReadOnlyCompatibleFeatures::GROUP_DESCRIPTOR_CHECKSUMS)
        {
            // TODO: prior to general checksum metadata being added,
            // there was a separate feature just for block group
            // descriptors. Add support for that here.
        }

        Ok(block_group_descriptor)
    }

    /// Read all block group descriptors.
    pub(crate) async fn read_all(
        sb: &Superblock,
        reader: &mut dyn Ext4Read,
    ) -> Result<Vec<Self>, Ext4Error> {
        let mut block_group_descriptors =
            Vec::with_capacity(usize_from_u32(sb.num_block_groups()));

        for bgd_index in 0..sb.num_block_groups() {
            let bgd = Self::read(sb, reader, bgd_index).await?;
            block_group_descriptors.push(bgd);
        }

        Ok(block_group_descriptors)
    }
}
