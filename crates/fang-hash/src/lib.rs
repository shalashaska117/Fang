// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! SHA-256 and the bounded regular-file hashing of the Fang tools.
//!
//! `sha256` is the one-shot function of tptp-coverage, with its bytes unchanged.
//! `Hasher` is a streaming implementation of the same function. `hash_file`
//! mirrors `_hash_descriptor` of tools/v8_szs/capability.py. `hash_file_chunked` is the
//! chunked digest, hashed by several threads (`chunked`).
#![forbid(unsafe_code)]

mod chunked;
mod sha256;
mod stream;

#[cfg(target_os = "linux")]
mod file;

pub use chunked::{
    CHUNK_BYTES, CHUNKED_TAG, THREAD_CAP, chunked_digest, chunked_sha256, chunked_text,
    parse_chunked,
};
pub use sha256::sha256;
pub use stream::Hasher;

#[cfg(target_os = "linux")]
pub use file::{
    DEFAULT_FILE_LIMIT, HashFileError, Identity, hash_file, hash_file_chunked,
    hash_file_chunked_sized, open_regular,
};

const HEX: &[u8; 16] = b"0123456789abcdef";

/// Lowercase hexadecimal, two digits per byte.
pub fn hex(bytes: &[u8]) -> String {
    let mut text = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        text.push(HEX[usize::from(byte >> 4)] as char);
        text.push(HEX[usize::from(byte & 15)] as char);
    }
    text
}

/// The lowercase hexadecimal SHA-256 of `data`, as `hashlib.sha256(data).hexdigest()`.
pub fn sha256_hex(data: &[u8]) -> String {
    hex(&sha256(data))
}

/// Exactly 64 lowercase hexadecimal digits, as `hexdigest` writes them.
pub fn parse_hex32(text: &str) -> Option<[u8; 32]> {
    let bytes = text.as_bytes();
    if bytes.len() != 64 {
        return None;
    }
    let digit = |byte: u8| match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    };
    let mut output = [0u8; 32];
    for (index, slot) in output.iter_mut().enumerate() {
        *slot = digit(bytes[2 * index])? << 4 | digit(bytes[2 * index + 1])?;
    }
    Some(output)
}
