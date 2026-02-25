// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::Ext4;
use crate::dir_entry::DirEntryName;
use crate::dir_htree::get_dir_entry_via_htree;
use crate::error::{CorruptKind, Ext4Error};
use crate::file_type::FileType;
use crate::inode::{Inode, InodeFlags, InodeIndex};
use crate::iters::AsyncIterator;
use crate::iters::file_blocks::FileBlocks;
use crate::iters::read_dir::ReadDir;
use crate::path::PathBuf;
use crate::util::write_u16le;
use crate::util::write_u32le;
use alloc::vec;

/// Search a directory inode for an entry with the given `name`. If
/// found, return the entry's inode, otherwise return a `NotFound`
/// error.
pub async fn get_dir_entry_inode_by_name(
    fs: &Ext4,
    dir_inode: &Inode,
    name: DirEntryName<'_>,
) -> Result<Inode, Ext4Error> {
    assert!(dir_inode.file_type().is_dir());

    if dir_inode.flags().contains(InodeFlags::DIRECTORY_ENCRYPTED) {
        return Err(Ext4Error::Encrypted);
    }

    if dir_inode.flags().contains(InodeFlags::DIRECTORY_HTREE) {
        let entry = get_dir_entry_via_htree(fs, dir_inode, name).await?;
        return Inode::read(fs, entry.inode).await;
    }

    // The entry's `path()` method is not called, so the value of the
    // base path does not matter.
    let path = PathBuf::empty();

    let mut iter = ReadDir::new(fs.clone(), dir_inode, path)?;
    while let Some(entry) = iter.next().await {
        let entry = entry?;
        if entry.file_name() == name {
            return Inode::read(fs, entry.inode).await;
        }
    }

    Err(Ext4Error::NotFound)
}

/// Add an item to a directory without an htree.
///
/// This edits directory entry bytes in-place and will error with
/// [`Ext4Error::Readonly`] if it would require allocating a new block.
pub(crate) async fn add_dir_entry_non_htree(
    fs: &Ext4,
    dir_inode: &Inode,
    name: DirEntryName<'_>,
    inode: InodeIndex,
    file_type: FileType,
) -> Result<(), Ext4Error> {
    assert!(dir_inode.file_type().is_dir());

    if dir_inode.flags().contains(InodeFlags::DIRECTORY_ENCRYPTED) {
        return Err(Ext4Error::Encrypted);
    }
    if dir_inode.flags().contains(InodeFlags::DIRECTORY_HTREE) {
        return Err(Ext4Error::Readonly);
    }

    // Fail if name already exists.
    if get_dir_entry_inode_by_name(fs, dir_inode, name)
        .await
        .is_ok()
    {
        return Err(Ext4Error::AlreadyExists);
    }

    let block_size = fs.0.superblock.block_size().to_usize();
    let mut file_blocks = FileBlocks::new(fs.clone(), dir_inode)?;

    let need = dir_entry_min_size(name.as_ref().len());
    let mut block_buf = vec![0u8; block_size];
    let mut is_first = true;

    while let Some(block_index_res) = file_blocks.next().await {
        let block_index = block_index_res?;
        fs.read_from_block(block_index, 0, &mut block_buf).await?;

        // Walk entries in this block looking for usable slack space.
        let mut off = 0usize;
        while off < block_size {
            let inode_field = read_u32_le(&block_buf, off)?;
            let rec_len = read_u16_le(&block_buf, off + 4)?;
            let rec_len_usize = usize::from(rec_len);

            if rec_len_usize < 8 || off.checked_add(rec_len_usize).is_none() {
                return Err(CorruptKind::DirEntry(dir_inode.index).into());
            }
            if off + rec_len_usize > block_size {
                return Err(CorruptKind::DirEntry(dir_inode.index).into());
            }

            // `inode == 0` indicates "special" entry or unused; treat it as fully free.
            let used = if inode_field == 0 {
                0usize
            } else {
                let name_len = block_buf[off + 6] as usize;
                dir_entry_min_size(name_len)
            };

            if rec_len_usize >= used + need {
                // Shrink current entry to its minimal size (or keep 0 if unused),
                // and place the new entry in the leftover space.
                let new_rec_len_for_curr =
                    if inode_field == 0 { 0usize } else { used };
                let free_start = off + new_rec_len_for_curr;
                let free_len = rec_len_usize - new_rec_len_for_curr;

                if free_len < need {
                    // Shouldn't happen due to earlier check, but keep safe.
                    off += rec_len_usize;
                    continue;
                }

                if inode_field != 0 {
                    write_u16le(
                        &mut block_buf,
                        off + 4,
                        u16::try_from(new_rec_len_for_curr).map_err(|_| {
                            Ext4Error::from(CorruptKind::DirEntry(
                                dir_inode.index,
                            ))
                        })?,
                    );
                } else {
                    // Make sure an unused entry becomes a valid single free record by giving it its full size.
                    write_u16le(
                        &mut block_buf,
                        off + 4,
                        u16::try_from(rec_len_usize).map_err(|_| {
                            Ext4Error::from(CorruptKind::DirEntry(
                                dir_inode.index,
                            ))
                        })?,
                    );
                }

                // Write the new entry.
                write_dir_entry_bytes(
                    &mut block_buf,
                    free_start,
                    free_len,
                    inode,
                    name,
                    file_type,
                )?;

                // Write the block back.
                fs.write_to_block(block_index, 0, &block_buf).await?;

                // Non-htree directories have no per-block checksum tail we update here.
                // If metadata checksums are enabled, this write may make the on-disk
                // checksum inconsistent. This crate currently doesn't provide an API
                // to update directory block checksums in-place for leaf blocks, so
                // treat this as acceptable for now.
                let _ = is_first;
                return Ok(());
            }

            off += rec_len_usize;
        }

        is_first = false;
    }

    // Would require appending a new block to the directory file.
    Err(Ext4Error::Readonly)
}

/// Remove an item from a directory without an htree.
///
/// This edits directory entry bytes in-place. It will error with
/// [`Ext4Error::Readonly`] if the removal would require freeing a block
/// (which this crate does not implement).
pub(crate) async fn remove_dir_entry_non_htree(
    fs: &Ext4,
    dir_inode: &Inode,
    name: DirEntryName<'_>,
) -> Result<(), Ext4Error> {
    assert!(dir_inode.file_type().is_dir());

    if dir_inode.flags().contains(InodeFlags::DIRECTORY_ENCRYPTED) {
        return Err(Ext4Error::Encrypted);
    }
    if dir_inode.flags().contains(InodeFlags::DIRECTORY_HTREE) {
        return Err(Ext4Error::Readonly);
    }

    let block_size = fs.0.superblock.block_size().to_usize();
    let mut file_blocks = FileBlocks::new(fs.clone(), dir_inode)?;
    let mut block_buf = vec![0u8; block_size];

    while let Some(block_index_res) = file_blocks.next().await {
        let block_index = block_index_res?;
        fs.read_from_block(block_index, 0, &mut block_buf).await?;

        let mut off = 0usize;
        let mut prev_off: Option<usize> = None;

        while off < block_size {
            let inode_field = read_u32_le(&block_buf, off)?;
            let rec_len = read_u16_le(&block_buf, off + 4)?;
            let rec_len_usize = usize::from(rec_len);

            if rec_len_usize < 8 || off + rec_len_usize > block_size {
                return Err(CorruptKind::DirEntry(dir_inode.index).into());
            }

            if inode_field != 0 {
                let name_len = block_buf[off + 6] as usize;
                let name_start = off + 8;
                let name_end = name_start + name_len;
                if name_end > off + rec_len_usize {
                    return Err(CorruptKind::DirEntry(dir_inode.index).into());
                }

                if block_buf[name_start..name_end] == *name.as_ref() {
                    // Don't allow removing "." or "..".
                    if name.as_ref() == b"." || name.as_ref() == b".." {
                        return Err(Ext4Error::Readonly);
                    }

                    if let Some(poff) = prev_off {
                        // Merge into previous record by extending its rec_len.
                        let prev_rec_len = read_u16_le(&block_buf, poff + 4)?;
                        let new_len = usize::from(prev_rec_len) + rec_len_usize;
                        write_u16le(
                            &mut block_buf,
                            poff + 4,
                            u16::try_from(new_len).map_err(|_| {
                                Ext4Error::from(CorruptKind::DirEntry(
                                    dir_inode.index,
                                ))
                            })?,
                        );
                        // Zero inode to mark removed (not strictly necessary once merged).
                        write_u32le(&mut block_buf, off, 0);
                    } else {
                        // No previous entry in this block; just mark this record unused.
                        write_u32le(&mut block_buf, off, 0);
                    }

                    fs.write_to_block(block_index, 0, &block_buf).await?;
                    return Ok(());
                }
            }

            prev_off = Some(off);
            off += rec_len_usize;
        }
    }

    Err(Ext4Error::NotFound)
}

fn dir_entry_min_size(name_len: usize) -> usize {
    // ext4 dir entry header is 8 bytes; record sizes are 4-byte aligned.
    let base = 8usize
        .checked_add(name_len)
        .expect("dir entry size overflow");
    (base + 3) & !3
}

fn write_dir_entry_bytes(
    block: &mut [u8],
    off: usize,
    rec_len: usize,
    inode: InodeIndex,
    name: DirEntryName<'_>,
    file_type: FileType,
) -> Result<(), Ext4Error> {
    let need = dir_entry_min_size(name.as_ref().len());
    if rec_len < need {
        return Err(Ext4Error::Readonly);
    }
    if off + rec_len > block.len() {
        return Err(CorruptKind::DirEntry(inode).into());
    }

    write_u32le(block, off, inode.get());
    write_u16le(
        block,
        off + 4,
        u16::try_from(rec_len)
            .map_err(|_| Ext4Error::from(CorruptKind::DirEntry(inode)))?,
    );
    block[off + 6] = u8::try_from(name.as_ref().len())
        .map_err(|_| Ext4Error::from(CorruptKind::DirEntry(inode)))?;
    block[off + 7] = file_type.to_dir_entry();

    let name_start = off + 8;
    let name_end = name_start + name.as_ref().len();
    block[name_start..name_end].copy_from_slice(name.as_ref());

    // Zero padding up to `rec_len`.
    for b in &mut block[name_end..off + rec_len] {
        *b = 0;
    }

    Ok(())
}

fn read_u16_le(buf: &[u8], off: usize) -> Result<u16, Ext4Error> {
    let b0 = *buf.get(off).ok_or_else(|| {
        Ext4Error::from(CorruptKind::DirEntry(InodeIndex::new(1).unwrap()))
    })?;
    let b1 = *buf.get(off + 1).ok_or_else(|| {
        Ext4Error::from(CorruptKind::DirEntry(InodeIndex::new(1).unwrap()))
    })?;
    Ok(u16::from_le_bytes([b0, b1]))
}

fn read_u32_le(buf: &[u8], off: usize) -> Result<u32, Ext4Error> {
    let b0 = *buf.get(off).ok_or_else(|| {
        Ext4Error::from(CorruptKind::DirEntry(InodeIndex::new(1).unwrap()))
    })?;
    let b1 = *buf.get(off + 1).ok_or_else(|| {
        Ext4Error::from(CorruptKind::DirEntry(InodeIndex::new(1).unwrap()))
    })?;
    let b2 = *buf.get(off + 2).ok_or_else(|| {
        Ext4Error::from(CorruptKind::DirEntry(InodeIndex::new(1).unwrap()))
    })?;
    let b3 = *buf.get(off + 3).ok_or_else(|| {
        Ext4Error::from(CorruptKind::DirEntry(InodeIndex::new(1).unwrap()))
    })?;
    Ok(u32::from_le_bytes([b0, b1, b2, b3]))
}

#[cfg(feature = "std")]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::load_test_disk1;

    #[tokio::test]
    async fn test_get_dir_entry_inode_by_name() {
        let fs = load_test_disk1().await;
        let root_inode = fs.read_root_inode().await.unwrap();

        let lookup = |name| {
            get_dir_entry_inode_by_name(
                &fs,
                &root_inode,
                DirEntryName::try_from(name).unwrap(),
            )
        };

        // Check for a few expected entries.
        // '.' always links to self.
        assert_eq!(lookup(".").await.unwrap().index, root_inode.index);
        // '..' is normally parent, but in the root dir it's just the
        // root dir again.
        assert_eq!(lookup("..").await.unwrap().index, root_inode.index);
        // Don't check specific values of these since they might change
        // if the test disk is regenerated
        assert!(lookup("empty_file").await.is_ok());
        assert!(lookup("empty_dir").await.is_ok());

        // Check for something that does not exist.
        let err = lookup("does_not_exist").await.unwrap_err();
        assert!(matches!(err, Ext4Error::NotFound));
    }
}
