// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::Ext4;
use crate::block_index::{FileBlockIndex, FsBlockIndex};
use crate::checksum::Checksum;
use crate::error::{CorruptKind, Ext4Error};
use crate::extent::Extent;
use crate::inode::{Inode, InodeIndex};
use crate::util::{
    read_u16le, read_u32le, u64_from_hilo, u64_to_hilo, usize_from_u32,
};
use alloc::vec;
use alloc::vec::Vec;
use core::num::NonZeroU32;

/// Size of each entry within an extent node (including the header
/// entry).
const ENTRY_SIZE_IN_BYTES: usize = 12;

const EXTENT_MAGIC: u16 = 0xf30a;

/// Header at the start of a node in an extent tree.
///
/// An extent tree is made up of nodes. Each node may be internal or
/// leaf. Leaf nodes contain `Extent`s. Internal nodes point at other
/// nodes.
///
/// Each node starts with a `NodeHeader` that includes the node's depth
/// (depth 0 is a leaf node) and the number of entries in the node.
#[derive(Copy, Clone)]
struct NodeHeader {
    /// Number of entries in this node, not including the header.
    num_entries: u16,

    /// Maximum number of entries in this node, not including the header.
    max_entries: u16,

    /// Depth of this node in the tree. Zero means it's a leaf node. The
    /// maximum depth is five.
    depth: u16,

    /// The generation number of this node. Used by lustre
    generation: u32,
}

/// Returns `(n + 1) * ENTRY_SIZE_IN_BYTES`.
///
/// The maximum value this returns is 786432.
fn add_one_mul_entry_size(n: u16) -> usize {
    // OK to unwrap: the maximum value of `n` is `2^16-1`, so the
    // maximum value of this sum is `2^16`. That fits in a `u32`, and we
    // assume `usize` is at least as big as a `u32`.
    let n_plus_one = usize::from(n).checked_add(1).unwrap();
    // OK to unwrap: `n_plus_one` is at most `2^16` and
    // `ENTRY_SIZE_IN_BYTES` is 12, so the maximum product is 786432,
    // which fits in a `u32`. We assume `usize` is at least as big as a
    // `u32`.
    n_plus_one.checked_mul(ENTRY_SIZE_IN_BYTES).unwrap()
}

impl NodeHeader {
    /// Size of the node, including the header.
    fn node_size_in_bytes(&self) -> usize {
        add_one_mul_entry_size(self.num_entries)
    }

    /// Offset of the node's extent data.
    ///
    /// Per `add_one_mul_entry_size`, the maximum value this returns is
    /// 786432.
    fn checksum_offset(&self) -> usize {
        add_one_mul_entry_size(self.max_entries)
    }
}

impl NodeHeader {
    /// Read a `NodeHeader` from a byte slice.
    fn from_bytes(data: &[u8], inode: InodeIndex) -> Result<Self, Ext4Error> {
        if data.len() < ENTRY_SIZE_IN_BYTES {
            return Err(CorruptKind::ExtentNotEnoughData(inode).into());
        }

        let eh_magic = read_u16le(data, 0);
        let eh_entries = read_u16le(data, 2);
        let eh_max = read_u16le(data, 4);
        let eh_depth = read_u16le(data, 6);
        let eh_generation = read_u32le(data, 8);

        if eh_magic != EXTENT_MAGIC {
            return Err(CorruptKind::ExtentMagic(inode).into());
        }

        if eh_depth > 5 {
            return Err(CorruptKind::ExtentDepth(inode).into());
        }

        Ok(Self {
            depth: eh_depth,
            num_entries: eh_entries,
            max_entries: eh_max,
            generation: eh_generation,
        })
    }

    fn to_bytes(&self) -> [u8; ENTRY_SIZE_IN_BYTES] {
        let mut bytes = [0u8; ENTRY_SIZE_IN_BYTES];
        bytes[0..2].copy_from_slice(&EXTENT_MAGIC.to_le_bytes());
        bytes[2..4].copy_from_slice(&self.num_entries.to_le_bytes());
        bytes[4..6].copy_from_slice(&self.max_entries.to_le_bytes());
        bytes[6..8].copy_from_slice(&self.depth.to_le_bytes());
        bytes[8..12].copy_from_slice(&self.generation.to_le_bytes());
        bytes
    }
}

#[derive(Copy, Clone)]
struct ExtentInternalNode {
    /// Offset of the block within the file.
    pub(crate) block_within_file: FileBlockIndex,

    /// This is the actual block within the filesystem.
    pub(crate) block: FsBlockIndex,
}

impl ExtentInternalNode {
    pub(crate) fn from_bytes(
        data: &[u8],
        inode: InodeIndex,
    ) -> Result<Self, Ext4Error> {
        if data.len() < ENTRY_SIZE_IN_BYTES {
            return Err(CorruptKind::ExtentNotEnoughData(inode).into());
        }

        let ei_block = read_u32le(data, 0);
        let (ei_start_lo, ei_start_hi) =
            (read_u32le(data, 4), read_u16le(data, 8));
        let ei_start = u64_from_hilo(ei_start_hi as u32, ei_start_lo);

        Ok(Self {
            block_within_file: ei_block,
            block: ei_start,
        })
    }

    pub(crate) fn to_bytes(&self) -> [u8; 12] {
        let mut bytes = [0u8; 12];
        bytes[0..4].copy_from_slice(&self.block_within_file.to_le_bytes());
        let (ei_start_hi, ei_start_lo) = u64_to_hilo(self.block);
        let ei_start_hi =
            u16::try_from(ei_start_hi).expect("block must fit in 48 bits");
        bytes[4..8].copy_from_slice(&ei_start_lo.to_le_bytes());
        bytes[8..10].copy_from_slice(&ei_start_hi.to_le_bytes());
        // The last two bytes are unused.
        bytes
    }
}

#[derive(Clone)]
enum ExtentNodeEntries {
    Internal(Vec<ExtentInternalNode>),
    Leaf(Vec<Extent>),
}

impl ExtentNodeEntries {
    fn from_bytes(
        data: &[u8],
        header: &NodeHeader,
        inode: InodeIndex,
    ) -> Result<Self, Ext4Error> {
        if header.depth == 0 {
            let mut entries = Vec::with_capacity(usize_from_u32(u32::from(
                header.num_entries,
            )));
            for i in 0..header.num_entries {
                let offset = add_one_mul_entry_size(i);
                let entry = Extent::from_bytes(
                    &data[offset..offset + ENTRY_SIZE_IN_BYTES],
                );
                entries.push(entry);
            }
            Ok(Self::Leaf(entries))
        } else {
            let mut entries = Vec::with_capacity(usize_from_u32(u32::from(
                header.num_entries,
            )));
            for i in 0..header.num_entries {
                let offset = add_one_mul_entry_size(i);
                let entry = ExtentInternalNode::from_bytes(
                    &data[offset..offset + ENTRY_SIZE_IN_BYTES],
                    inode,
                )?;
                entries.push(entry);
            }
            Ok(Self::Internal(entries))
        }
    }
}

#[derive(Clone)]
pub(crate) struct ExtentNode {
    block: Option<FsBlockIndex>,
    header: NodeHeader,
    entries: ExtentNodeEntries,
}

impl ExtentNode {
    fn from_bytes(
        block: Option<FsBlockIndex>,
        data: &[u8],
        inode: InodeIndex,
        checksum_base: Checksum,
        ext4: &Ext4,
    ) -> Result<Self, Ext4Error> {
        let header = NodeHeader::from_bytes(data, inode)?;
        let entries = ExtentNodeEntries::from_bytes(data, &header, inode)?;
        if ext4.has_metadata_checksums() {
            let checksum_offset = header.checksum_offset();
            if data.len() < checksum_offset + 4 {
                return Err(CorruptKind::ExtentNotEnoughData(inode).into());
            }
            let expected_checksum = read_u32le(data, checksum_offset);
            let mut checksum = checksum_base.clone();
            checksum.update(&data[..checksum_offset]);
            if checksum.finalize() != expected_checksum {
                return Err(CorruptKind::ExtentChecksum(inode).into());
            }
        }
        Ok(Self { block, header, entries })
    }

    pub(crate) fn to_bytes(&self, checksum_base: Option<Checksum>) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(self.header.checksum_offset() + 4);
        bytes.extend_from_slice(&self.header.to_bytes());
        match &self.entries {
            ExtentNodeEntries::Leaf(extents) => {
                for extent in extents {
                    bytes.extend_from_slice(&extent.to_bytes());
                }
            }
            ExtentNodeEntries::Internal(internal_nodes) => {
                for internal_node in internal_nodes {
                    bytes.extend_from_slice(&internal_node.to_bytes());
                }
            }
        }
        if let Some(checksum_base) = checksum_base {
            let mut checksum = checksum_base.clone();
            checksum.update(&bytes);
            bytes.extend_from_slice(&checksum.finalize().to_le_bytes());
        }
        bytes
    }

    pub(crate) fn push_extent(&mut self, extent: Extent) -> Result<(), ()> {
        match &mut self.entries {
            ExtentNodeEntries::Leaf(extents) => {
                if extents.len()
                    >= usize_from_u32(u32::from(self.header.max_entries))
                {
                    return Err(());
                }
                extents.push(extent);
                self.header.num_entries += 1;
                Ok(())
            }
            ExtentNodeEntries::Internal(_) => Err(()),
        }
    }

    pub(crate) async fn write(&self, ext4: &Ext4) -> Result<(), Ext4Error> {
        if let Some(block) = self.block {
            let bytes = self.to_bytes(None);
            ext4.write_to_block(block, 0, &bytes).await?;
        }
        Ok(())
    }
}

/// Iterator of an inode's extent tree.
pub(crate) struct ExtentTree {
    ext4: Ext4,
    inode: InodeIndex,
    node: ExtentNode,
    checksum_base: Checksum,
}

impl ExtentTree {
    pub(crate) fn initialize(
        ext4: Ext4,
        inode: &Inode,
    ) -> Result<Self, Ext4Error> {
        // TODO: linux claims some initial blocks for the extent tree
        Ok(Self {
            ext4,
            inode: inode.index,
            node: ExtentNode {
                block: None,
                header: NodeHeader {
                    num_entries: 0,
                    max_entries: 4,
                    depth: 0,
                    generation: 0,
                },
                entries: ExtentNodeEntries::Leaf(vec![]),
            },
            checksum_base: inode.checksum_base().clone(),
        })
    }

    pub(crate) fn to_bytes(&self) -> [u8; 60] {
        let bytes = self.node.to_bytes(None);
        let mut result = [0u8; 60];
        result[..bytes.len()].copy_from_slice(&bytes);
        result
    }

    pub(crate) fn from_inode(
        ext4: Ext4,
        inode: &Inode,
    ) -> Result<Self, Ext4Error> {
        let header = NodeHeader::from_bytes(&inode.inline_data(), inode.index)?;
        let entries = ExtentNodeEntries::from_bytes(
            &inode.inline_data(),
            &header,
            inode.index,
        )?;
        assert_eq!(header.max_entries, 4);
        Ok(Self {
            ext4,
            inode: inode.index,
            node: ExtentNode { block: None, header, entries },
            checksum_base: inode.checksum_base().clone(),
        })
    }

    /// Get the extent that contains the given block index, if any.
    async fn get_extent(
        &self,
        block_index: FileBlockIndex,
    ) -> Result<Option<Extent>, Ext4Error> {
        let mut node = self.node.clone();
        loop {
            match &node.entries {
                ExtentNodeEntries::Leaf(extents) => {
                    for extent in extents {
                        if block_index >= extent.block_within_file
                            && block_index
                                < extent.block_within_file
                                    + FileBlockIndex::from(extent.num_blocks)
                        {
                            return Ok(Some(*extent));
                        }
                    }
                    return Ok(None);
                }
                ExtentNodeEntries::Internal(internal_nodes) => {
                    // Internal nodes are sorted by `block_within_file`.
                    // Find the last internal node whose `block_within_file` is less than or equal to `block_index`.
                    let mut next_node_index = None;
                    for (i, internal_node) in internal_nodes.iter().enumerate()
                    {
                        if internal_node.block_within_file > block_index {
                            break;
                        }
                        next_node_index = Some(i);
                    }
                    let next_node_index = match next_node_index {
                        Some(i) => i,
                        None => return Ok(None),
                    };
                    let next_node_block = internal_nodes[next_node_index].block;
                    let next_node_data =
                        self.ext4.read_block(next_node_block).await?;
                    node = ExtentNode::from_bytes(
                        Some(next_node_block),
                        &next_node_data,
                        self.inode,
                        self.checksum_base.clone(),
                        &self.ext4,
                    )?;
                }
            }
        }
    }

    pub(crate) async fn get_block(
        &self,
        block_index: FileBlockIndex,
    ) -> Result<Option<FsBlockIndex>, Ext4Error> {
        if let Some(extent) = self.get_extent(block_index).await? {
            let offset_within_extent = block_index - extent.block_within_file;
            Ok(Some(
                extent.start_block + FsBlockIndex::from(offset_within_extent),
            ))
        } else {
            Ok(None)
        }
    }

    async fn last_allocated_extent(
        &self,
    ) -> Result<Option<(Vec<ExtentNode>, Extent)>, Ext4Error> {
        let mut node = self.node.clone();
        let mut path = Vec::new();
        loop {
            path.push(node.clone());
            match &node.entries {
                ExtentNodeEntries::Leaf(extents) => {
                    // TODO: avoid unwrapping
                    if extents.is_empty() {
                        return Ok(None);
                    }
                    return Ok(Some((path, extents.last().copied().unwrap())));
                }
                ExtentNodeEntries::Internal(internal_nodes) => {
                    if internal_nodes.is_empty() {
                        return Ok(None);
                    }
                    let next_node_block = internal_nodes.last().unwrap().block;
                    let next_node_data =
                        self.ext4.read_block(next_node_block).await?;
                    node = ExtentNode::from_bytes(
                        Some(next_node_block),
                        &next_node_data,
                        self.inode,
                        self.checksum_base.clone(),
                        &self.ext4,
                    )?;
                }
            }
        }
    }

    pub(crate) async fn allocate(
        &mut self,
        start: FileBlockIndex,
        amount: NonZeroU32,
        initialized: bool,
    ) -> Result<(), Ext4Error> {
        // Find the rightmost leaf node.
        // If there's space, allocate the new extent there.
        // Otherwise, panic for now
        let last_allocated = self.last_allocated_extent().await?;
        if let Some((path, last_extent)) = last_allocated {
            if last_extent.block_within_file + last_extent.num_blocks as u32 >= start {
                panic!("can't allocate overlapping extent");
            }
            if !last_extent.is_initialized && initialized {
                panic!("can't allocate initialized extent after uninitialized extent");
            }
            if let ExtentNodeEntries::Leaf(extents) = &path.last().unwrap().entries {
                if extents.len()
                    < usize_from_u32(u32::from(self.node.header.max_entries))
                {
                    let start_block = self
                        .ext4
                        .alloc_contiguous_blocks(self.inode, amount)
                        .await?;
                    if initialized {
                        self.ext4
                            .clear_blocks(start_block, amount)
                            .await?;
                    }
                    self.node
                        .push_extent(Extent {
                            block_within_file: start,
                            start_block,
                            num_blocks: u16::try_from(amount.get()).unwrap(),
                            is_initialized: initialized,
                        })
                        .unwrap();
                    return Ok(());
                }
            } else {
                unreachable!()
            }
            todo!()
        } else {
            let start_block = self
                .ext4
                .alloc_contiguous_blocks(self.inode, amount)
                .await?;
            if initialized {
                self.ext4
                    .clear_blocks(start_block, amount)
                    .await?;
            }
            self.node
                .push_extent(Extent {
                    block_within_file: start,
                    start_block,
                    num_blocks: u16::try_from(amount.get()).unwrap(),
                    is_initialized: initialized,
                })
                .unwrap();
        }
        Ok(())
    }

    pub(crate) async fn extend(
        &mut self,
        start: FileBlockIndex,
        amount: NonZeroU32,
    ) -> Result<(), Ext4Error> {
        if let Some(extent) = self.get_extent(start).await? {
            todo!()
        }
        self.allocate(start, amount, true).await
    }
}
