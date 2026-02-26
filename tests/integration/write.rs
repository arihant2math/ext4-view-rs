// Copyright 2026 Google LLC
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use ext4_view::{
    Ext4Error, File, FileType, FollowSymlinks, Inode, InodeCreationOptions,
    InodeFlags, InodeMode, Path,
};
use tokio;

use super::test_util::{load_compressed_filesystem, load_test_disk1_rw};

#[tokio::test]
async fn test_write_requires_writer() {
    // Load filesystem without writer.
    let fs = load_compressed_filesystem("test_disk1.bin.zst").await;

    // Open a small file and attempt to write.
    let mut file = fs.open("/small_file").await.unwrap();
    let err = file.write_bytes(b"ABC").await.unwrap_err();
    assert!(matches!(err, Ext4Error::Readonly));
}

#[tokio::test]
async fn test_write_into_hole_is_error() {
    // Load filesystem with writer.
    let fs = load_test_disk1_rw().await;

    // Open the file with holes. The first two blocks are holes.
    let mut file = fs.open("/holes").await.unwrap();

    // Try to write at the start (in a hole). Should be Readonly.
    let err = file.write_bytes(b"XYZ").await.unwrap_err();
    assert!(matches!(err, Ext4Error::Readonly));
}

#[tokio::test]
async fn test_write_caps_to_file_end_and_block_boundary() {
    // Load filesystem with writer.
    let fs = load_test_disk1_rw().await;

    // Small file is "hello, world!" (13 bytes) and fits in a single block.
    let mut file = fs.open("/small_file").await.unwrap();

    // Seek near end and attempt to write more than remaining.
    file.seek_to(12).await.unwrap();
    let written = file.write_bytes(b". We're writing").await.unwrap();

    // Everything should be written up
    assert_eq!(written, 15);
    assert_eq!(file.position(), 27);
    file.seek_to(0).await.unwrap();
    // Verify file contents
    let mut buf = vec![0u8; 27];
    let n = file.read_bytes(&mut buf).await.unwrap();
    assert_eq!(n, 27);
    assert_eq!(&buf, b"hello, world. We're writing");
    // File contents should be "hello, worABCDEFGHIJ"
    let data = fs.read("/small_file").await.unwrap();
    assert_eq!(&data, b"hello, world. We're writing");
}

#[tokio::test]
async fn test_write_persists_data() {
    // Load filesystem with shared reader/writer to the same buffer.
    let fs = load_test_disk1_rw().await;

    // Open small_file and write within allocated space.
    let mut file = fs.open("/small_file").await.unwrap();
    // Overwrite first 5 bytes with "HELLO".
    file.seek_to(0).await.unwrap();
    let n = file.write_bytes(b"HELLO").await.unwrap();
    assert_eq!(n, 5);

    // Read back the file and verify the change persisted.
    let data = fs.read("/small_file").await.unwrap();
    assert!(data.starts_with(b"HELLO"));
}

#[tokio::test]
async fn test_inode_modification_time() {
    let fs = load_test_disk1_rw().await;

    let mut inode = fs
        .path_to_inode(
            Path::try_from("/empty_file").unwrap(),
            FollowSymlinks::All,
        )
        .await
        .unwrap();
    let new_atime = core::time::Duration::new(6000, 0);
    let now = core::time::Duration::new(5000, 0);
    inode.set_atime(new_atime);
    inode.set_mtime(now);
    inode.write(&fs).await.unwrap();
    // Reload inode to verify change persisted.
    let reloaded = fs
        .path_to_inode(
            Path::try_from("/empty_file").unwrap(),
            FollowSymlinks::All,
        )
        .await
        .unwrap();
    assert_eq!(reloaded.metadata().mtime, now);
    assert_eq!(reloaded.metadata().atime, new_atime);
}

#[tokio::test]
async fn test_inode_creation() {
    let fs = load_test_disk1_rw().await;

    // Create a new file in the root directory.
    let mut new_inode = fs
        .create_inode(InodeCreationOptions {
            file_type: FileType::Regular,
            mode: InodeMode::S_IRUSR | InodeMode::S_IWUSR | InodeMode::S_IFREG,
            uid: 0,
            gid: 0,
            time: Default::default(),
            flags: InodeFlags::INLINE_DATA,
        })
        .await
        .unwrap();
    assert_eq!(new_inode.metadata().file_type, FileType::Regular);
    assert_eq!(
        new_inode.metadata().mode,
        InodeMode::S_IRUSR | InodeMode::S_IWUSR | InodeMode::S_IFREG
    );
    assert_eq!(new_inode.metadata().uid, 0);
    assert_eq!(new_inode.metadata().gid, 0);
    let root_inode = fs
        .path_to_inode(Path::try_from("/").unwrap(), FollowSymlinks::All)
        .await
        .unwrap();
    // Link the new inode into the root directory.
    fs.link(&root_inode, "new_file".to_string(), &mut new_inode)
        .await
        .unwrap();
    // Ensure the new file is visible at the expected path.
    let new_file_inode = fs
        .path_to_inode("/new_file".try_into().unwrap(), FollowSymlinks::All)
        .await
        .unwrap();
    assert_eq!(new_file_inode.index, new_inode.index);
    assert_eq!(new_file_inode.links_count(), 1);
}

#[tokio::test]
async fn test_inode_deletion() {
    let fs = load_test_disk1_rw().await;

    let root_inode = fs
        .path_to_inode(Path::try_from("/").unwrap(), FollowSymlinks::All)
        .await
        .unwrap();
    let empty_inode = fs
        .path_to_inode("/empty_file".try_into().unwrap(), FollowSymlinks::All)
        .await
        .unwrap();
    let inode = fs
        .unlink(&root_inode, "empty_file".to_string(), empty_inode)
        .await
        .unwrap();
    assert!(inode.is_none());
    // Ensure the file is no longer visible.
    let err = fs
        .path_to_inode("/empty_file".try_into().unwrap(), FollowSymlinks::All)
        .await
        .unwrap_err();
    assert!(matches!(err, Ext4Error::NotFound));
}

#[tokio::test]
async fn test_new_file_grow() {
    let fs = load_test_disk1_rw().await;
    let new_inode = fs
        .create_inode(InodeCreationOptions {
            file_type: FileType::Regular,
            mode: InodeMode::S_IRUSR | InodeMode::S_IWUSR | InodeMode::S_IFREG,
            uid: 0,
            gid: 0,
            time: Default::default(),
            flags: InodeFlags::INLINE_DATA,
        })
        .await
        .unwrap();
    let index = new_inode.index;
    let mut file = File::open_inode(&fs, new_inode).unwrap();
    let data = b"Hello, world! This file will grow as we write to it.";
    let n = file.write_bytes(data).await.unwrap();
    assert_eq!(n, data.len());
    // Read back the inode and verify new length.
    let inode = Inode::read(&fs, index).await.unwrap();
    assert_eq!(inode.size_in_bytes(), data.len() as u64);
}
