// Copyright 2026 Google LLC
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use ext4_view::{
    Ext4, Ext4Error, FileType, FollowSymlinks, InodeCreationOptions,
    InodeFlags, InodeMode, Path,
};
use tokio;

use super::test_util::load_compressed_filesystem;

use async_trait::async_trait;
use ext4_view::Ext4Read;
use ext4_view::Ext4Write;
use std::error::Error as StdError;
use std::fmt::{self, Display, Formatter};
use std::sync::{Arc, Mutex};

// Simple error for MemWriter failures.
#[derive(Debug)]
struct MemWriterError;
impl Display for MemWriterError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "mem writer error")
    }
}
impl StdError for MemWriterError {}

// Local writer backed by a Mutex<Vec<u8>>.
struct MemWriter(Mutex<Vec<u8>>);

// Reader+Writer backed by a shared Arc<Mutex<Vec<u8>>> to verify persistence.
struct MemRw(Arc<Mutex<Vec<u8>>>);

#[async_trait]
impl Ext4Read for MemRw {
    async fn read(
        &self,
        start_byte: u64,
        dst: &mut [u8],
    ) -> Result<(), Box<dyn StdError + Send + Sync + 'static>> {
        let guard = self.0.lock().unwrap();
        let start = start_byte as usize;
        let end = start.checked_add(dst.len()).ok_or_else(|| {
            Box::new(MemWriterError)
                as Box<dyn StdError + Send + Sync + 'static>
        })?;
        if end > guard.len() {
            return Err(Box::new(MemWriterError));
        }
        dst.copy_from_slice(&guard[start..end]);
        Ok(())
    }
}

#[async_trait]
impl Ext4Write for MemRw {
    async fn write(
        &self,
        start_byte: u64,
        src: &[u8],
    ) -> Result<(), Box<dyn StdError + Send + Sync + 'static>> {
        let mut guard = self.0.lock().unwrap();
        let start = start_byte as usize;
        let end = start.checked_add(src.len()).ok_or_else(|| {
            Box::new(MemWriterError)
                as Box<dyn StdError + Send + Sync + 'static>
        })?;
        if end > guard.len() {
            return Err(Box::new(MemWriterError));
        }
        guard[start..end].copy_from_slice(src);
        Ok(())
    }
}

#[async_trait]
impl Ext4Write for MemWriter {
    async fn write(
        &self,
        start_byte: u64,
        src: &[u8],
    ) -> Result<(), Box<dyn StdError + Send + Sync + 'static>> {
        let mut guard = self.0.lock().unwrap();
        let start = start_byte as usize;
        let end = start.checked_add(src.len()).ok_or_else(|| {
            Box::new(MemWriterError)
                as Box<dyn StdError + Send + Sync + 'static>
        })?;
        if end > guard.len() {
            return Err(Box::new(MemWriterError));
        }
        guard[start..end].copy_from_slice(src);
        Ok(())
    }
}

async fn load_fs_with_writer(name: &str) -> Ext4 {
    // Decompress into memory
    let output = std::process::Command::new("zstd")
        .args(["--decompress", "--stdout", &format!("test_data/{name}")])
        .output()
        .unwrap();
    assert!(output.status.success());

    let data: Vec<u8> = output.stdout;
    // Reader uses a clone of the data; writer uses our MemWriter.
    Ext4::load_with_writer(
        Box::new(data.clone()),
        Some(Box::new(MemWriter(Mutex::new(data)))),
    )
    .await
    .unwrap()
}

async fn load_fs_shared_rw(name: &str) -> Ext4 {
    // Decompress into memory
    let output = std::process::Command::new("zstd")
        .args(["--decompress", "--stdout", &format!("test_data/{name}")])
        .output()
        .unwrap();
    assert!(output.status.success());

    let data: Vec<u8> = output.stdout;
    let shared = Arc::new(Mutex::new(data));
    let reader = Box::new(MemRw(shared.clone())) as Box<dyn Ext4Read>;
    let writer = Some(Box::new(MemRw(shared.clone())) as Box<dyn Ext4Write>);

    Ext4::load_with_writer(reader, writer).await.unwrap()
}

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
    let fs = load_fs_with_writer("test_disk1.bin.zst").await;

    // Open the file with holes. The first two blocks are holes.
    let mut file = fs.open("/holes").await.unwrap();

    // Try to write at the start (in a hole). Should be Readonly.
    let err = file.write_bytes(b"XYZ").await.unwrap_err();
    assert!(matches!(err, Ext4Error::Readonly));
}

#[tokio::test]
async fn test_write_caps_to_file_end_and_block_boundary() {
    // Load filesystem with writer.
    let fs = load_fs_shared_rw("test_disk1.bin.zst").await;

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
    let fs = load_fs_shared_rw("test_disk1.bin.zst").await;

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
    let fs = load_fs_shared_rw("test_disk1.bin.zst").await;

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
    let fs = load_fs_shared_rw("test_disk1.bin.zst").await;

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
}

#[tokio::test]
async fn test_inode_deletion() {
    let fs = load_fs_shared_rw("test_disk1.bin.zst").await;

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
