// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang_hash::{Hasher, hex, parse_hex32, sha256, sha256_hex};

const VECTORS: [(&[u8], &str); 4] = [
    (b"", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    (b"abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    (
        b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
    ),
    (
        b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
        "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1",
    ),
];

#[test]
fn fips_vectors() {
    for (message, expected) in VECTORS {
        assert_eq!(sha256_hex(message), expected);
        let mut hasher = Hasher::new();
        hasher.update(message);
        assert_eq!(hex(&hasher.finish()), expected);
    }
    let million = vec![b'a'; 1_000_000];
    assert_eq!(
        sha256_hex(&million),
        "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
    );
    let mut hasher = Hasher::new();
    for chunk in million.chunks(997) {
        hasher.update(chunk);
    }
    assert_eq!(
        hex(&hasher.finish()),
        "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
    );
}

#[test]
fn streaming_equals_one_shot_at_every_split() {
    let data: Vec<u8> = (0..300u32)
        .map(|index| (index * 7 + index / 3) as u8)
        .collect();
    for length in [0, 1, 55, 56, 57, 63, 64, 65, 119, 120, 127, 128, 129, 300] {
        let message = &data[..length];
        let expected = sha256(message);
        for split in 0..=length {
            let mut hasher = Hasher::new();
            hasher.update(&message[..split]);
            hasher.update(&message[split..]);
            assert_eq!(hasher.finish(), expected, "length {length} split {split}");
        }
    }
}

#[test]
fn hex_round_trip_is_lowercase_and_exact() {
    let digest = sha256(b"abc");
    let text = hex(&digest);
    assert_eq!(parse_hex32(&text), Some(digest));
    assert_eq!(parse_hex32(&text.to_uppercase()), None);
    assert_eq!(parse_hex32(&text[..63]), None);
    assert_eq!(parse_hex32(&format!("{text}0")), None);
    assert_eq!(parse_hex32(&text.replace('a', "g")), None);
}

#[cfg(target_os = "linux")]
mod files {
    use fang_hash::{HashFileError, Identity, hash_file, open_regular, sha256_hex};
    use std::path::PathBuf;

    fn scratch(name: &str) -> PathBuf {
        let directory =
            std::env::temp_dir().join(format!("fang-hash-test-{}-{name}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir(&directory).unwrap();
        directory
    }

    fn no_check() -> Result<(), ()> {
        Ok(())
    }

    #[test]
    fn regular_file_hash_and_identity() {
        let directory = scratch("regular");
        let path = directory.join("data");
        let data = vec![7u8; 3 << 20];
        std::fs::write(&path, &data).unwrap();
        let (digest, identity) = hash_file(&path, 4 << 20, &mut no_check).unwrap();
        assert_eq!(digest, sha256_hex(&data));
        assert_eq!(identity, Identity::of_path(&path).unwrap());
        assert_eq!(identity.size, data.len() as u64);
        let (_, opened) = open_regular(&path).unwrap();
        assert_eq!(opened, identity);
    }

    #[test]
    fn check_runs_before_every_read() {
        let directory = scratch("check");
        let path = directory.join("data");
        std::fs::write(&path, vec![1u8; (2 << 20) + 5]).unwrap();
        let mut calls = 0;
        let mut counting = || -> Result<(), ()> {
            calls += 1;
            Ok(())
        };
        hash_file(&path, 8 << 20, &mut counting).unwrap();
        // Three reads with data and the final empty read, as in _hash_descriptor.
        assert_eq!(calls, 4);
        let mut refusing = || -> Result<(), &'static str> { Err("stop") };
        assert!(matches!(
            hash_file(&path, 8 << 20, &mut refusing),
            Err(HashFileError::Check("stop"))
        ));
    }

    #[test]
    fn symlink_fifo_directory_and_oversize_are_refused() {
        let directory = scratch("refused");
        let target = directory.join("target");
        std::fs::write(&target, b"abc").unwrap();
        let link = directory.join("link");
        std::os::unix::fs::symlink(&target, &link).unwrap();
        assert!(matches!(
            hash_file(&link, 10, &mut no_check),
            Err(HashFileError::Io(_))
        ));
        assert!(open_regular(&link).is_err());
        let fifo = directory.join("fifo");
        assert!(
            std::process::Command::new("mkfifo")
                .arg(&fifo)
                .status()
                .unwrap()
                .success()
        );
        // O_NONBLOCK: opening the FIFO returns at once instead of waiting for a writer.
        assert!(matches!(
            hash_file(&fifo, 10, &mut no_check),
            Err(HashFileError::NotBounded)
        ));
        assert!(open_regular(&fifo).is_err());
        assert!(matches!(
            hash_file(&directory, 10, &mut no_check),
            Err(HashFileError::NotBounded)
        ));
        assert!(matches!(
            hash_file(&target, 2, &mut no_check),
            Err(HashFileError::NotBounded)
        ));
        assert!(hash_file(&target, 3, &mut no_check).is_ok());
    }
}
