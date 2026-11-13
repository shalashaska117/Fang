// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! fang-check-sources prints check_tree's JSON and exits as tools/check-v8-sources.py does.
use std::path::{Path, PathBuf};
use std::process::Command;

use fang_json::{DumpOptions, dumps};

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .find(|path| path.join("tools/v8_szs/rust-sources.json").is_file())
        .expect("repository root")
        .to_path_buf()
}

fn run(arguments: &[&str], directory: &Path) -> (i32, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_fang-check-sources"))
        .args(arguments)
        .current_dir(directory)
        .output()
        .unwrap();
    (
        output.status.code().unwrap(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn prints_the_report_and_exits_by_status() {
    let root = root().canonicalize().unwrap();
    let expected = dumps(
        &fang_source_checks::check_tree(&root, false, true),
        &DumpOptions::default(),
    )
    .unwrap();
    assert!(
        expected.starts_with("{\"status\": \"passed\", \"rust_files\": "),
        "{expected}"
    );
    let relative = format!("{}/./crates/..", root.display());
    for arguments in [
        vec!["--root", root.to_str().unwrap(), "--skip-lean"],
        vec!["--skip-lean", "--root", &relative],
    ] {
        assert_eq!(
            run(&arguments, Path::new("/")),
            (0, format!("{expected}\n"), String::new())
        );
    }
    assert_eq!(
        run(&["--skip-lean"], &root),
        (0, format!("{expected}\n"), String::new())
    );
    let missing = root.join("no-such-tree");
    let (code, stdout, stderr) = run(&["--root", missing.to_str().unwrap()], Path::new("/"));
    let error = format!(
        "[Errno 2] No such file or directory: '{}'",
        missing.join("Cargo.toml").display()
    );
    assert_eq!(
        (code, stdout, stderr),
        (
            1,
            format!("{{\"status\": \"failed\", \"error\": \"{error}\"}}\n"),
            String::new()
        )
    );
    let (code, stdout, stderr) = run(&["--rec"], Path::new("/"));
    assert_eq!((code, stdout.as_str()), (2, ""));
    assert!(
        stderr.ends_with("fang-check-sources: error: unrecognized arguments: --rec\n"),
        "{stderr}"
    );
}
