// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The chunked SHA-256 (INTEGRATION.md, findings of the tptp1000 differential, item 8): the
//! SHA-256 of each `CHUNK_BYTES` chunk of the input, in order, then the SHA-256 of those
//! 32-byte digests followed by the input length as 8 bytes big-endian. The chunks are
//! independent, so a file is hashed by several threads. An empty input has no chunks, so its
//! digest is the SHA-256 of eight zero bytes.

use crate::{Hasher, hex, sha256};

/// The chunk size of the digest the manifests record. Changing it changes every digest. 1 MiB
/// was fastest at every thread count measured (1 to 16) and keeps the buffers small: one chunk
/// per thread (diagnostics/fang-hash-chunked-measure-v1-20261110).
pub const CHUNK_BYTES: u64 = 1 << 20;

/// The most threads `hash_file_chunked` uses when asked for 0 (automatic). 8 threads hash the
/// 1,080 MiB pinned set at about 2.6 GB/s; 16 reach about 4.3 GB/s on an idle machine, but the
/// launcher runs beside the provers, so the cap stays at 8. A caller may ask for more.
pub const THREAD_CAP: usize = 8;

/// The tag of the recorded text form, naming the chunk size in MiB (a test ties it to
/// `CHUNK_BYTES`): the text is the tag followed by the 64 hexadecimal digits.
pub const CHUNKED_TAG: &str = "csha256-1m:";

/// The recorded text form of a chunked digest given as 64 hexadecimal digits.
pub fn chunked_text(hex_digest: &str) -> String {
    format!("{CHUNKED_TAG}{hex_digest}")
}

/// The digest in a recorded text form, or None unless the text is exactly the tag and 64
/// lowercase hexadecimal digits.
pub fn parse_chunked(text: &str) -> Option<[u8; 32]> {
    crate::parse_hex32(text.strip_prefix(CHUNKED_TAG)?)
}

/// The digest over the chunk digests, in order, and the total length.
pub(crate) fn combine(digests: &[[u8; 32]], length: u64) -> [u8; 32] {
    let mut outer = Hasher::new();
    for digest in digests {
        outer.update(digest);
    }
    outer.update(&length.to_be_bytes());
    outer.finish()
}

/// The definition with the chunk size as a parameter, in one thread.
pub fn chunked_sha256(data: &[u8], chunk_bytes: usize) -> [u8; 32] {
    assert!(chunk_bytes > 0, "chunk size must be positive");
    let digests: Vec<[u8; 32]> = data.chunks(chunk_bytes).map(sha256).collect();
    combine(&digests, data.len() as u64)
}

/// The recorded digest of `data` (`CHUNK_BYTES` chunks), as 64 lowercase hexadecimal digits.
pub fn chunked_digest(data: &[u8]) -> String {
    hex(&chunked_sha256(data, CHUNK_BYTES as usize))
}
