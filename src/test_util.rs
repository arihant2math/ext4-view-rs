// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// In addition to being used as a regular module in lib.rs, this module
// is used in `tests` via the `include!` macro.

use core::fmt::{Display, Formatter};
use std::error::Error;
use std::fmt;
use std::sync::{Arc, Mutex};
use async_trait::async_trait;
use super::{Ext4, Ext4Read, Ext4Write};

/// Decompress a file with zstd, then load it into an `Ext4`.
pub(crate) async fn load_compressed_filesystem(name: &str) -> Ext4 {
    // This function executes quickly, so don't bother caching.
    let output = std::process::Command::new("zstd")
        .args([
            "--decompress",
            // Write to stdout and don't delete the input file.
            "--stdout",
            &format!("test_data/{name}"),
        ])
        .output()
        .unwrap();
    assert!(output.status.success());
    Ext4::load(Box::new(output.stdout)).await.unwrap()
}

pub(crate) async fn load_test_disk1() -> Ext4 {
    load_compressed_filesystem("test_disk1.bin.zst").await
}


// Simple error for MemWriter failures.
#[derive(Debug)]
struct MemWriterError;
impl Display for MemWriterError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "mem writer error")
    }
}
impl Error for MemWriterError {}

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
    ) -> Result<(), Box<dyn Error + Send + Sync + 'static>> {
        let guard = self.0.lock().unwrap();
        let start = start_byte as usize;
        let end = start.checked_add(dst.len()).ok_or_else(|| {
            Box::new(MemWriterError)
                as Box<dyn Error + Send + Sync + 'static>
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
    ) -> Result<(), Box<dyn Error + Send + Sync + 'static>> {
        let mut guard = self.0.lock().unwrap();
        let start = start_byte as usize;
        let end = start.checked_add(src.len()).ok_or_else(|| {
            Box::new(MemWriterError)
                as Box<dyn Error + Send + Sync + 'static>
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
    ) -> Result<(), Box<dyn Error + Send + Sync + 'static>> {
        let mut guard = self.0.lock().unwrap();
        let start = start_byte as usize;
        let end = start.checked_add(src.len()).ok_or_else(|| {
            Box::new(MemWriterError)
                as Box<dyn Error + Send + Sync + 'static>
        })?;
        if end > guard.len() {
            return Err(Box::new(MemWriterError));
        }
        guard[start..end].copy_from_slice(src);
        Ok(())
    }
}

pub async fn load_fs_with_writer(name: &str) -> Ext4 {
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

pub async fn load_fs_shared_rw(name: &str) -> Ext4 {
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
