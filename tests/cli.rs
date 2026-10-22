// Copyright (c) 2026 Pietro Pellegrino.
use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT_CASE: AtomicUsize = AtomicUsize::new(0);

struct Case {
    dir: PathBuf,
    input: PathBuf,
    proof: PathBuf,
}
impl Case {
    fn new(bytes: &[u8]) -> Self {
        let dir = std::env::temp_dir().join(format!(
            "fang-cli-{}-{}",
            std::process::id(),
            NEXT_CASE.fetch_add(1, Ordering::SeqCst)
        ));
        fs::create_dir(&dir).unwrap();
        let input = dir.join("input.p");
        let proof = dir.join("proof.fang");
        fs::write(&input, bytes).unwrap();
        Self { dir, input, proof }
    }
    fn run(&self, extra: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_fang"))
            .arg(&self.input)
            .arg("--proof")
            .arg(&self.proof)
            .args(extra)
            .output()
            .unwrap()
    }
}
impl Drop for Case {
    fn drop(&mut self) {
        // Delete only this test's explicitly created files, never recursively.
        let _ = fs::remove_file(&self.input);
        let _ = fs::remove_file(&self.proof);
        let _ = fs::remove_dir(&self.dir);
    }
}

#[test]
fn cli_writes_candidate_and_never_calls_it_certified() {
    let case = Case::new(b"cnf(c0,axiom,(p)).cnf(c1,axiom,(~p)).");
    let result = case.run(&[]);
    assert_eq!(result.status.code(), Some(0));
    assert_eq!(result.stdout, b"candidate-refutation\n");
    assert!(
        fs::read_to_string(&case.proof)
            .unwrap()
            .starts_with("(fang-proof 1\n")
    );
    assert!(String::from_utf8_lossy(&result.stderr).contains("independent checking required"));
}

#[test]
fn cli_distinguishes_unknown_invalid_unsupported_and_resource() {
    for (bytes, expected, extra) in [
        (&b"cnf(c,axiom,(p))."[..], 2, vec![]),
        (&b"cnf(c,axiom,(p()))."[..], 3, vec![]),
        (&b"cnf(c,axiom,($true))."[..], 4, vec![]),
        (
            &b"cnf(c0,axiom,(p)).cnf(c1,axiom,(~p))."[..],
            5,
            vec!["--max-steps", "0"],
        ),
    ] {
        let case = Case::new(bytes);
        let result = case.run(&extra);
        assert_eq!(
            result.status.code(),
            Some(expected),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert!(!case.proof.exists());
        assert!(!String::from_utf8_lossy(&result.stdout).contains("SAT"));
    }
}

#[test]
fn cli_reports_usage_and_io_separately() {
    let result = Command::new(env!("CARGO_BIN_EXE_fang")).output().unwrap();
    assert_eq!(result.status.code(), Some(6));
    let case = Case::new(b"");
    fs::remove_file(&case.input).unwrap();
    assert_eq!(case.run(&[]).status.code(), Some(6));
}

#[test]
fn cli_does_not_report_candidate_when_certificate_write_fails() {
    let case = Case::new(b"cnf(c0,axiom,(p)).cnf(c1,axiom,(~p)).");
    // A directory is an invalid output file on every supported platform.
    let result = Command::new(env!("CARGO_BIN_EXE_fang"))
        .arg(&case.input)
        .arg("--proof")
        .arg(&case.dir)
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(6));
    assert!(result.stdout.is_empty());
    assert!(String::from_utf8_lossy(&result.stderr).contains("certificate I/O error"));
    assert!(!case.proof.exists());
    assert_eq!(
        fs::read(&case.input).unwrap(),
        b"cnf(c0,axiom,(p)).cnf(c1,axiom,(~p))."
    );
}
