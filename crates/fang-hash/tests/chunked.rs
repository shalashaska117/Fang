// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The chunked digest against vectors computed once with Python's hashlib (the comparison
//! exception): SHA-256 over the chunk SHA-256 digests, in order, then the length as 8 bytes
//! big-endian. The data is byte i = (31 i + 7) mod 251.
use std::path::PathBuf;

use fang_hash::{
    CHUNK_BYTES, CHUNKED_TAG, HashFileError, chunked_digest, chunked_sha256, chunked_text,
    hash_file_chunked, hash_file_chunked_sized, hex, parse_chunked, sha256_hex,
};

const C: u64 = 1 << 20;

const SMALL: [(usize, &str); 7] = [
    (
        0,
        "af5570f5a1810b7af78caf4bc70a660f0df51e42baf91d4de5b2328de0e83dfc",
    ),
    (
        1,
        "d84053f45932b99bb89b672319c80c235d4e1ce117a6354bac4540db61a1c193",
    ),
    (
        63,
        "f866dd48c966c9bdf0afbd436887b2947909dc269e1b02a1fe7298a255111f24",
    ),
    (
        64,
        "603679251f3f178d8886524ec1d06fb73e042a0430ef9344d2563f0fb6d09bb0",
    ),
    (
        65,
        "769f2c979c8f83a1fea199e56ba7cca10de1420f4d63c692e867e10774068ca9",
    ),
    (
        128,
        "dbd949ff05670e8b06a69d4a75fe1684a41051f8b8d3928fc089ade49c0e22ad",
    ),
    (
        1000,
        "7c7d6b38bc94b88b511e8566c58925047cd65495e3b0fa1b970d0968fbae2bfc",
    ),
];

/// Empty, one byte, one chunk less one, exactly one, one more, exactly two, and odd.
const RECORDED: [(u64, &str); 7] = [
    (
        0,
        "af5570f5a1810b7af78caf4bc70a660f0df51e42baf91d4de5b2328de0e83dfc",
    ),
    (
        1,
        "d84053f45932b99bb89b672319c80c235d4e1ce117a6354bac4540db61a1c193",
    ),
    (
        C - 1,
        "356d94420e063d123fd5b6646ae2c2bd36c0be665e62fb1b80cd51b9bf948c91",
    ),
    (
        C,
        "a3b9417ecee586cb08eb00d8c564fb3f70a19f67544e3c27bcb8056c1c44b93a",
    ),
    (
        C + 1,
        "2507d41bec5adbcba575830adfed395f466bea74bc5a9c986df6b36c0c26f985",
    ),
    (
        2 * C,
        "b22f81401432f65ab416c9d0a65e92ef5a7d1013ebcac13b9b7eb6431cc1e8b3",
    ),
    (
        3 * C + 12345,
        "7979714d640e5d5872d9af748b698bdbecfe8a24e8f00ec1a1a9b4c8e4b0ca9d",
    ),
];

fn pattern(length: u64) -> Vec<u8> {
    (0..length)
        .map(|index| ((31 * index + 7) % 251) as u8)
        .collect()
}

struct Scratch(PathBuf);

impl Scratch {
    fn new(name: &str) -> Scratch {
        let directory =
            std::env::temp_dir().join(format!("fang-chunked-test-{}-{name}", std::process::id()));
        std::fs::create_dir(&directory).unwrap();
        Scratch(directory)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn no_check() -> Result<(), ()> {
    Ok(())
}

#[test]
fn definition_matches_hashlib() {
    assert_eq!(CHUNK_BYTES, C);
    let data = pattern(1000);
    assert_eq!(
        sha256_hex(&data),
        "008549d94fa71e7a0a483d84380d05a923a4b18e79ba1f8a8ddac923956d32ef"
    );
    for (length, expected) in SMALL {
        assert_eq!(
            hex(&chunked_sha256(&data[..length], 64)),
            expected,
            "{length}"
        );
    }
    let big = pattern(3 * C + 12345);
    for (length, expected) in RECORDED {
        assert_eq!(
            chunked_digest(&big[..length as usize]),
            expected,
            "{length}"
        );
    }
}

#[test]
fn files_match_the_vectors_at_every_thread_count() {
    let scratch = Scratch::new("vectors");
    let big = pattern(3 * C + 12345);
    for (length, expected) in RECORDED {
        let path = scratch.0.join(format!("data-{length}"));
        std::fs::write(&path, &big[..length as usize]).unwrap();
        for threads in [0, 1, 2, 3, 8] {
            let (digest, identity) =
                hash_file_chunked(&path, u64::MAX, threads, &mut no_check).unwrap();
            assert_eq!(
                (digest.as_str(), identity.size),
                (expected, length),
                "{length} with {threads}"
            );
        }
    }
    let path = scratch.0.join("small");
    std::fs::write(&path, &big[..1000]).unwrap();
    let (digest, _) = hash_file_chunked_sized(&path, u64::MAX, 4, 64, &mut no_check).unwrap();
    assert_eq!(digest, SMALL[6].1);
}

#[test]
fn text_form_names_the_chunk_size() {
    assert_eq!(CHUNKED_TAG, format!("csha256-{}m:", CHUNK_BYTES >> 20));
    let digest = RECORDED[3].1;
    let text = chunked_text(digest);
    assert_eq!(text, format!("csha256-1m:{digest}"));
    assert_eq!(
        parse_chunked(&text).map(|bytes| hex(&bytes)),
        Some(digest.to_owned())
    );
    for wrong in [
        digest.to_owned(),
        format!("csha256-8m:{digest}"),
        format!("{CHUNKED_TAG}{}", digest.to_uppercase()),
        format!("{text}0"),
    ] {
        assert_eq!(parse_chunked(&wrong), None, "{wrong}");
    }
}

#[test]
fn refusals_checks_and_changes() {
    let scratch = Scratch::new("refusals");
    let path = scratch.0.join("data");
    std::fs::write(&path, pattern(3 * C)).unwrap();
    let link = scratch.0.join("link");
    std::os::unix::fs::symlink(&path, &link).unwrap();
    assert!(matches!(
        hash_file_chunked(&link, u64::MAX, 2, &mut no_check),
        Err(HashFileError::Io(_))
    ));
    assert!(matches!(
        hash_file_chunked(&scratch.0, u64::MAX, 2, &mut no_check),
        Err(HashFileError::NotBounded)
    ));
    assert!(matches!(
        hash_file_chunked(&path, 3 * C - 1, 2, &mut no_check),
        Err(HashFileError::NotBounded)
    ));
    hash_file_chunked(&path, 3 * C, 2, &mut no_check).unwrap();
    // check runs before the first chunk and after each of the three.
    let mut calls = 0;
    hash_file_chunked(&path, u64::MAX, 2, &mut || {
        calls += 1;
        Ok::<(), ()>(())
    })
    .unwrap();
    assert_eq!(calls, 4);
    // A failing check stops the hash with its own error.
    let mut calls = 0;
    let stopped = hash_file_chunked(&path, u64::MAX, 2, &mut || {
        calls += 1;
        if calls == 2 { Err("stop") } else { Ok(()) }
    });
    assert!(matches!(stopped, Err(HashFileError::Check("stop"))));
    // A write while the chunks are read changes the identity: Changed.
    let mut appended = false;
    let changed = hash_file_chunked(&path, u64::MAX, 1, &mut || {
        if !appended {
            appended = true;
            use std::io::Write;
            std::fs::OpenOptions::new()
                .append(true)
                .open(&path)
                .unwrap()
                .write_all(b"x")
                .unwrap();
        }
        Ok::<(), ()>(())
    });
    assert!(matches!(changed, Err(HashFileError::Changed)));
}
