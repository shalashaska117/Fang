// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Bounded hashing of one regular file, as `_hash_descriptor` and `digest` in tools/v8_szs/capability.py.

use std::fs::{File, OpenOptions};
use std::io::Read;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::Path;

use crate::{Hasher, hex};

// Linux open(2) flags; std has no names for them. O_NONBLOCK is the same on both architectures.
#[cfg(target_arch = "x86_64")]
const O_NOFOLLOW: i32 = 0o400000;
#[cfg(target_arch = "aarch64")]
const O_NOFOLLOW: i32 = 0o100000;
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
compile_error!("O_NOFOLLOW is written down for x86_64 and aarch64 only");
const O_NONBLOCK: i32 = 0o4000;

/// The default bound of `digest` and `verify_run`.
pub const DEFAULT_FILE_LIMIT: u64 = 512 << 20;
const CHUNK: u64 = 1 << 20;

/// `capability.identity`: device, inode, size and the two change times in nanoseconds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Identity {
    pub dev: u64,
    pub ino: u64,
    pub size: u64,
    pub mtime_ns: i128,
    pub ctime_ns: i128,
}

impl Identity {
    pub fn of(metadata: &std::fs::Metadata) -> Identity {
        Identity {
            dev: metadata.dev(),
            ino: metadata.ino(),
            size: metadata.size(),
            mtime_ns: i128::from(metadata.mtime()) * 1_000_000_000
                + i128::from(metadata.mtime_nsec()),
            ctime_ns: i128::from(metadata.ctime()) * 1_000_000_000
                + i128::from(metadata.ctime_nsec()),
        }
    }

    /// The identity of the path itself, not following a final symlink (`os.stat(path, follow_symlinks=False)`).
    pub fn of_path(path: &Path) -> std::io::Result<Identity> {
        Ok(Identity::of(&std::fs::symlink_metadata(path)?))
    }

    /// `[dev, ino, size, mtime_ns, ctime_ns]`, the list the manifests record.
    pub fn as_array(&self) -> [i128; 5] {
        [
            i128::from(self.dev),
            i128::from(self.ino),
            i128::from(self.size),
            self.mtime_ns,
            self.ctime_ns,
        ]
    }
}

/// Open read-only with O_NOFOLLOW and O_NONBLOCK, so a symlink fails and a FIFO cannot block,
/// and return the file with the identity of the opened inode. Anything but a regular file is refused.
pub fn open_regular(path: &Path) -> std::io::Result<(File, Identity)> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(O_NOFOLLOW | O_NONBLOCK)
        .open(path)?;
    let metadata = file.metadata()?;
    if !metadata.file_type().is_file() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "not a regular file",
        ));
    }
    Ok((file, Identity::of(&metadata)))
}

#[derive(Debug)]
pub enum HashFileError<E> {
    Io(std::io::Error),
    /// Not a regular file, or larger than the bound when opened.
    NotBounded,
    /// The file grew beyond the bound while it was read.
    Grew,
    Check(E),
    /// `hash_file_chunked`: the file was shorter than at open, or its identity (size, change
    /// times, inode) differed after the last chunk.
    Changed,
}

/// Hash a regular file of at most `limit` bytes in 1 MiB reads, calling `check` before every read.
/// Returns the hex digest and the identity taken from the opened file before the first read.
pub fn hash_file<E>(
    path: &Path,
    limit: u64,
    check: &mut dyn FnMut() -> Result<(), E>,
) -> Result<(String, Identity), HashFileError<E>> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(O_NOFOLLOW | O_NONBLOCK)
        .open(path)
        .map_err(HashFileError::Io)?;
    let metadata = file.metadata().map_err(HashFileError::Io)?;
    if !metadata.file_type().is_file() || metadata.size() > limit {
        return Err(HashFileError::NotBounded);
    }
    let identity = Identity::of(&metadata);
    let mut file = file;
    let mut hasher = Hasher::new();
    let mut buffer = vec![0u8; CHUNK as usize];
    let mut remaining = limit.saturating_add(1);
    while remaining > 0 {
        check().map_err(HashFileError::Check)?;
        let want = remaining.min(CHUNK) as usize;
        let read = loop {
            match file.read(&mut buffer[..want]) {
                Ok(read) => break read,
                Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
                Err(error) => return Err(HashFileError::Io(error)),
            }
        };
        if read == 0 {
            return Ok((hex(&hasher.finish()), identity));
        }
        hasher.update(&buffer[..read]);
        remaining -= read as u64;
    }
    Err(HashFileError::Grew)
}

/// The chunked digest (`crate::chunked`) of a regular file of at most `limit` bytes, read by up
/// to `threads` scoped threads (0: automatic, at most `THREAD_CAP`). The file is opened once,
/// as `open_regular` does, and its identity is taken then. Each thread reads whole chunks with
/// positioned reads. `check` runs in the calling thread before the first chunk and after each
/// finished chunk; its error stops the threads. A short read, or a different identity at the
/// final fstat, is `Changed`. Returns the hex digest and the identity.
pub fn hash_file_chunked<E>(
    path: &Path,
    limit: u64,
    threads: usize,
    check: &mut dyn FnMut() -> Result<(), E>,
) -> Result<(String, Identity), HashFileError<E>> {
    hash_file_chunked_sized(path, limit, threads, crate::chunked::CHUNK_BYTES, check)
}

/// `hash_file_chunked` with the chunk size as a parameter, for the measurements and the tests.
pub fn hash_file_chunked_sized<E>(
    path: &Path,
    limit: u64,
    threads: usize,
    chunk_bytes: u64,
    check: &mut dyn FnMut() -> Result<(), E>,
) -> Result<(String, Identity), HashFileError<E>> {
    use std::os::unix::fs::FileExt;
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
    assert!(chunk_bytes > 0, "chunk size must be positive");
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(O_NOFOLLOW | O_NONBLOCK)
        .open(path)
        .map_err(HashFileError::Io)?;
    let metadata = file.metadata().map_err(HashFileError::Io)?;
    if !metadata.file_type().is_file() || metadata.size() > limit {
        return Err(HashFileError::NotBounded);
    }
    let identity = Identity::of(&metadata);
    let size = identity.size;
    let chunks = size.div_ceil(chunk_bytes);
    let wanted = if threads == 0 {
        std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(crate::chunked::THREAD_CAP)
    } else {
        threads
    };
    let workers = wanted
        .min(usize::try_from(chunks).unwrap_or(usize::MAX))
        .max(1);
    check().map_err(HashFileError::Check)?;
    let mut digests =
        vec![[0u8; 32]; usize::try_from(chunks).map_err(|_| HashFileError::NotBounded)?];
    let next = AtomicU64::new(0);
    let stop = AtomicBool::new(false);
    let (sender, receiver) = std::sync::mpsc::channel::<(u64, std::io::Result<[u8; 32]>)>();
    std::thread::scope(|scope| -> Result<(), HashFileError<E>> {
        for _ in 0..workers {
            let sender = sender.clone();
            let (file, next, stop) = (&file, &next, &stop);
            scope.spawn(move || {
                let mut buffer = vec![0u8; usize::try_from(chunk_bytes).unwrap_or(usize::MAX)];
                while !stop.load(Ordering::Relaxed) {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    if index >= chunks {
                        break;
                    }
                    let offset = index * chunk_bytes;
                    let length = usize::try_from((size - offset).min(chunk_bytes)).unwrap_or(0);
                    let result = file
                        .read_exact_at(&mut buffer[..length], offset)
                        .map(|()| crate::sha256(&buffer[..length]));
                    if sender.send((index, result)).is_err() {
                        break;
                    }
                }
            });
        }
        drop(sender);
        let mut handle = |index: u64, result: std::io::Result<[u8; 32]>| {
            let digest = result.map_err(|error| {
                if error.kind() == std::io::ErrorKind::UnexpectedEof {
                    HashFileError::Changed
                } else {
                    HashFileError::Io(error)
                }
            })?;
            digests[usize::try_from(index).map_err(|_| HashFileError::Changed)?] = digest;
            check().map_err(HashFileError::Check)
        };
        for (index, result) in receiver {
            if let Err(error) = handle(index, result) {
                // The threads stop at their next chunk; the scope waits for them.
                stop.store(true, Ordering::Relaxed);
                return Err(error);
            }
        }
        Ok(())
    })?;
    let after = file.metadata().map_err(HashFileError::Io)?;
    if Identity::of(&after) != identity {
        return Err(HashFileError::Changed);
    }
    Ok((hex(&crate::chunked::combine(&digests, size)), identity))
}
