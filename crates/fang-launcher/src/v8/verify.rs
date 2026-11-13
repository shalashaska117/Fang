// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Per-run verification. Once a run knows which binaries it may execute, `start` hashes them in background
//! threads, each by the chunked SHA-256 its pin holds (the chunks in parallel), or by the plain SHA-256 when the
//! pin has no chunked digest. `verify` waits for a file's hash before its first execution and fails unless it
//! matches. Before a positive status every file hashed must keep its identity (device, inode, size, mtime_ns,
//! ctime_ns); ctime cannot be set by a user, so an in-place rewrite that restores mtime is still seen.
//!
//! A hash that was started and never waited for decides nothing: the file did not run.

use std::collections::{BTreeMap, HashMap};
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::{self, JoinHandle};
use std::time::Duration;

use fang_supervisor::Fault;

use crate::capability::{CHUNKED_TAG, Pin};

/// A file's identity as the after-run check compares it.
pub type Identity = [i128; 5];

fn identity(metadata: &std::fs::Metadata) -> Identity {
    [
        i128::from(metadata.dev()),
        i128::from(metadata.ino()),
        i128::from(metadata.size()),
        i128::from(metadata.mtime()) * 1_000_000_000 + i128::from(metadata.mtime_nsec()),
        i128::from(metadata.ctime()) * 1_000_000_000 + i128::from(metadata.ctime_nsec()),
    ]
}

/// The texts of a profile's verification failures.
#[derive(Clone, Copy, Debug)]
pub struct Messages {
    /// A pinned file whose hash differs from its pin, or that changed while it was hashed.
    pub changed: fn(&Path) -> String,
    /// A file that is about to run without a pin.
    pub unpinned: fn(&Path) -> String,
    /// A hashed file whose identity changed by the end of the run.
    pub executed_changed: fn(&str) -> String,
}

/// The version-8 profile's texts.
pub const V8_MESSAGES: Messages = Messages {
    changed: |path| format!("Pinned version-8 dependency changed: {}", path.display()),
    unpinned: |path| {
        format!(
            "Executable is not pinned by the installation: {}",
            path.display()
        )
    },
    executed_changed: |path| {
        format!("Executed version-8 dependency changed during the run: {path}")
    },
};

type Hashing = JoinHandle<Result<Identity, Fault>>;

/// The pinned files of a run, the hashes started and the identities of the files verified.
#[derive(Debug)]
pub struct Verifier {
    pins: HashMap<PathBuf, Pin>,
    pending: HashMap<PathBuf, Hashing>,
    identities: BTreeMap<String, Identity>,
    messages: Messages,
    stop: Arc<AtomicBool>,
}

/// Hash one pinned file: its digest must equal the pin and its identity must not change while it is read.
fn hash_one(pin: &Pin, messages: Messages, stop: &AtomicBool) -> Result<Identity, Fault> {
    let path = pin.path.as_path();
    let changed = || Fault::Value((messages.changed)(path));
    let mut check = || {
        if stop.load(Ordering::Relaxed) {
            Err(())
        } else {
            Ok(())
        }
    };
    let limit = fang_hash::DEFAULT_FILE_LIMIT;
    let (matches, opened) = match &pin.chunked_sha256 {
        Some(chunked) => {
            let (digest, opened) =
                fang_hash::hash_file_chunked(path, limit, 0, &mut check).map_err(|_| changed())?;
            (format!("{CHUNKED_TAG}{digest}") == *chunked, opened)
        }
        None => {
            let (digest, opened) =
                fang_hash::hash_file(path, limit, &mut check).map_err(|_| changed())?;
            (digest == pin.sha256, opened)
        }
    };
    let after = identity(&std::fs::symlink_metadata(path).map_err(|_| changed())?);
    if !matches || after != opened.as_array() {
        return Err(changed());
    }
    Ok(after)
}

impl Verifier {
    /// A verifier for the given pins.
    pub fn new(pins: impl IntoIterator<Item = Pin>, messages: Messages) -> Verifier {
        Verifier {
            pins: pins
                .into_iter()
                .map(|pin| (pin.path.clone(), pin))
                .collect(),
            pending: HashMap::new(),
            identities: BTreeMap::new(),
            messages,
            stop: Arc::new(AtomicBool::new(false)),
        }
    }

    /// Start hashing every pinned path not hashed or started yet, each in its own background thread. A path
    /// without a pin is left for `verify` to refuse.
    pub fn start(&mut self, paths: &[&Path]) {
        for path in paths {
            if self.identities.contains_key(&path.display().to_string())
                || self.pending.contains_key(*path)
            {
                continue;
            }
            let Some(pin) = self.pins.get(*path).cloned() else {
                continue;
            };
            let messages = self.messages;
            let stop = self.stop.clone();
            self.pending.insert(
                path.to_path_buf(),
                thread::spawn(move || hash_one(&pin, messages, &stop)),
            );
        }
    }

    /// Before the first execution of `paths`: each must be pinned, and its hash, started now unless it already
    /// was, must match.
    pub fn verify(&mut self, paths: &[&Path]) -> Result<(), Fault> {
        self.verify_checked(paths, &mut || Ok(()))
    }

    /// Wait under the caller's deadline and cancellation checks. A stopped wait cannot authorize an
    /// execution; background workers stop at their next hash block without delaying the refusal.
    pub fn verify_checked(
        &mut self,
        paths: &[&Path],
        check: &mut dyn FnMut() -> Result<(), Fault>,
    ) -> Result<(), Fault> {
        let result = self.wait_checked(paths, check);
        if result.is_err() {
            self.stop.store(true, Ordering::Relaxed);
        }
        result
    }

    fn wait_checked(
        &mut self,
        paths: &[&Path],
        check: &mut dyn FnMut() -> Result<(), Fault>,
    ) -> Result<(), Fault> {
        check()?;
        if let Some(path) = paths.iter().find(|path| !self.pins.contains_key(**path)) {
            return Err(Fault::Value((self.messages.unpinned)(path)));
        }
        self.start(paths);
        for path in paths {
            if let Some(hashing) = self.pending.remove(*path) {
                while !hashing.is_finished() {
                    check()?;
                    thread::sleep(Duration::from_millis(5));
                }
                check()?;
                let result = hashing
                    .join()
                    .unwrap_or_else(|_| Err(Fault::Value("A hashing thread failed".to_string())));
                self.identities.insert(path.display().to_string(), result?);
            }
        }
        Ok(())
    }

    /// Before a positive status: every file verified in this run must still be the same inode, unmodified.
    pub fn check_identities(&self) -> Result<(), Fault> {
        for (path, expected) in &self.identities {
            let current = std::fs::symlink_metadata(path).map(|metadata| identity(&metadata));
            if current.ok().as_ref() != Some(expected) {
                return Err(Fault::Value((self.messages.executed_changed)(path)));
            }
        }
        Ok(())
    }

    /// The files verified so far, sorted, for the run record's `verified_before_run`.
    pub fn listed(&self) -> Vec<String> {
        self.identities.keys().cloned().collect()
    }
}

impl Drop for Verifier {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Relaxed);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pin(path: &Path, data: &[u8], chunked: bool) -> Pin {
        Pin {
            path: path.to_path_buf(),
            sha256: fang_hash::sha256_hex(data),
            chunked_sha256: chunked
                .then(|| format!("{CHUNKED_TAG}{}", fang_hash::chunked_digest(data))),
        }
    }

    #[test]
    fn hashes_once_refuses_changes_and_unpinned_files() {
        let directory =
            std::env::temp_dir().join(format!("fang-verify-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).unwrap();
        let first = directory.join("a");
        let second = directory.join("b");
        let third = directory.join("c");
        std::fs::write(&first, b"abc").unwrap();
        std::fs::write(&second, b"def").unwrap();
        std::fs::write(&third, vec![7u8; (9 << 20) + 5]).unwrap();
        let pins = [
            pin(&first, b"abc", true),
            pin(&second, b"xyz", true),
            pin(&third, &vec![7u8; (9 << 20) + 5], true),
        ];
        let mut verifier = Verifier::new(pins, V8_MESSAGES);
        verifier.start(&[&first, &third]);
        verifier.verify(&[&first]).unwrap();
        assert_eq!(verifier.listed(), vec![first.display().to_string()]);
        verifier.verify(&[&third]).unwrap();
        let error = verifier.verify(&[&second]).unwrap_err();
        assert!(
            error
                .python_str()
                .starts_with("Pinned version-8 dependency changed")
        );
        let error = verifier.verify(&[Path::new("/bin/sh")]).unwrap_err();
        assert!(error.python_str().starts_with("Executable is not pinned"));
        verifier.check_identities().unwrap();
        std::fs::write(&first, b"abd").unwrap();
        assert!(verifier.check_identities().is_err());
        let _ = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn a_plain_pin_is_checked_by_the_plain_digest() {
        let directory =
            std::env::temp_dir().join(format!("fang-verify-plain-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).unwrap();
        let file = directory.join("installation.json");
        std::fs::write(&file, b"{}").unwrap();
        let mut verifier = Verifier::new([pin(&file, b"{}", false)], V8_MESSAGES);
        verifier.verify(&[&file]).unwrap();
        let mut wrong = Verifier::new([pin(&file, b"[]", false)], V8_MESSAGES);
        assert!(wrong.verify(&[&file]).is_err());
        let _ = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn waiting_for_a_hash_observes_timeout_and_cancellation() {
        use fang_supervisor::{Failure, Status};
        use std::sync::mpsc;
        use std::time::Instant;

        for status in [Status::Timeout, Status::Forced] {
            let path = Path::new("/pending-review-hash");
            let mut verifier = Verifier::new([pin(path, b"", false)], V8_MESSAGES);
            let (release, wait) = mpsc::channel();
            verifier.pending.insert(
                path.to_path_buf(),
                thread::spawn(move || {
                    wait.recv().unwrap();
                    Ok([0; 5])
                }),
            );
            let started = Instant::now();
            let mut checks = 0;
            let result = verifier.verify_checked(&[path], &mut || {
                checks += 1;
                if checks >= 3 {
                    Err(Fault::Failure(Failure::new(status, "test stop", "adapter")))
                } else {
                    Ok(())
                }
            });
            release.send(()).unwrap();
            assert!(matches!(result, Err(Fault::Failure(error)) if error.status == status));
            assert!(started.elapsed() < Duration::from_secs(1));
            assert!(verifier.listed().is_empty());
            assert!(verifier.stop.load(Ordering::Relaxed));
        }
    }
}
