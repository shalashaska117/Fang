// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The internal stage entry never speaks for a run: whatever its name and arguments, it prints no SZS line and
//! writes no run record, and the public help does not name it.

use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const NAMES: [&str; 3] = ["ground-fof-replay", "cnf-decompose", "no-such-stage"];

fn launcher() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_fang-launcher"))
}

/// Run the launcher with `arguments` in an empty directory and return its exit code and output.
fn run(arguments: &[&str]) -> (Option<i32>, String, Vec<String>) {
    let directory = std::env::temp_dir().join(format!(
        "fang-internal-control-{}-{}",
        std::process::id(),
        arguments.join("_").replace('/', "_")
    ));
    let _ = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).unwrap();
    let mut child = Command::new(launcher())
        .args(arguments)
        .current_dir(&directory)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    while child.try_wait().unwrap().is_none() {
        if Instant::now() > deadline {
            let _ = child.kill();
            panic!("the internal entry did not finish: {arguments:?}");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    let output = child.wait_with_output().unwrap();
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let mut left: Vec<String> = Vec::new();
    for entry in walk(&directory) {
        left.push(entry);
    }
    let _ = std::fs::remove_dir_all(&directory);
    (output.status.code(), text, left)
}

fn walk(directory: &std::path::Path) -> Vec<String> {
    let mut found = Vec::new();
    for entry in std::fs::read_dir(directory).unwrap().flatten() {
        found.push(entry.path().display().to_string());
        if entry.file_type().unwrap().is_dir() {
            found.extend(walk(&entry.path()));
        }
    }
    found
}

#[test]
fn every_internal_name_prints_no_status_and_writes_no_record() {
    let mut cases: Vec<Vec<&str>> = vec![vec!["--fang-internal"]];
    for name in NAMES {
        cases.push(vec!["--fang-internal", name]);
        cases.push(vec![
            "--fang-internal",
            name,
            "missing-input.p",
            "missing-output",
        ]);
        cases.push(vec!["--fang-internal", name, "--help"]);
    }
    for arguments in &cases {
        let (code, text, left) = run(arguments);
        assert!(!text.contains("% SZS"), "{arguments:?}: {text}");
        assert!(!text.contains("% Fang profile"), "{arguments:?}: {text}");
        assert!(
            !left.iter().any(|path| path.ends_with("manifest.json")),
            "{arguments:?}: {left:?}"
        );
        if arguments.len() < 2 || arguments[1] == "no-such-stage" {
            assert_eq!(code, Some(64), "{arguments:?}: {text}");
        }
    }
}

#[test]
fn internal_entry_is_matched_only_as_the_first_argument() {
    let (_, text, _) = run(&["problem.p", "--fang-internal", "cnf-decompose"]);
    assert!(text.contains("% SZS status Error for"), "{text}");
}

#[test]
fn public_help_does_not_name_the_internal_entry() {
    for arguments in [
        &["--help"][..],
        &["help"],
        &["--profile", "cnf", "--help"],
        &["--profile", "ground-fof", "--help"],
    ] {
        let (_, text, _) = run(arguments);
        assert!(!text.contains("fang-internal"), "{arguments:?}");
        assert!(
            !text.contains("cnf-decompose") && !text.contains("ground-fof-replay"),
            "{arguments:?}"
        );
    }
}
