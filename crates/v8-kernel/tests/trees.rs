// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The tree inventory on synthetic trees: unchanged, an added file, a changed file, a recorded
//! directory that disappears, an absent entry that appears, and a symbolic link recorded by
//! target (revision 7's trees controls, finding EV6-2).

use std::fs;
use std::path::{Path, PathBuf};

use fang_json::{Object, Value};
use fang_v8_kernel::trees;

fn scratch(name: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fang-v8-kernel-trees-{name}-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("scratch directory");
    path
}

fn record(directories: &[(&str, &Path)]) -> Object {
    let mut recorded = Object::new();
    for (name, directory) in directories {
        let item = trees::record(&directory.to_string_lossy()).expect("record");
        recorded.set(*name, item);
    }
    recorded
}

fn unchanged(recorded: &Object) -> bool {
    trees::verify(recorded).expect("verify").0
}

#[test]
fn inventory_controls() {
    let base = scratch("controls");
    let present = base.join("present");
    let absent = base.join("absent");
    fs::create_dir_all(present.join("lib")).expect("tree");
    fs::write(present.join("lib/a.olean"), b"one").expect("file");
    std::os::unix::fs::symlink("lib/a.olean", present.join("link")).expect("link");
    let recorded = record(&[("present", &present), ("absent", &absent)]);
    let item = recorded.get("present").expect("present");
    let files = item
        .get("files_sha256")
        .and_then(Value::as_object)
        .expect("files");
    assert_eq!(
        files.get("link").and_then(Value::as_str),
        Some("link:lib/a.olean")
    );
    assert_eq!(
        recorded.get("absent").and_then(|item| item.get("exists")),
        Some(&Value::Bool(false))
    );
    assert!(unchanged(&recorded), "a fresh record is unchanged");

    fs::write(present.join("lib/b.olean"), b"two").expect("added");
    assert!(!unchanged(&recorded), "an added file is a change");
    fs::remove_file(present.join("lib/b.olean")).expect("remove");
    assert!(unchanged(&recorded));

    fs::write(present.join("lib/a.olean"), b"One").expect("changed");
    assert!(!unchanged(&recorded), "a changed file is a change");
    fs::write(present.join("lib/a.olean"), b"one").expect("restored");
    assert!(unchanged(&recorded));

    fs::create_dir_all(&absent).expect("appears");
    assert!(
        !unchanged(&recorded),
        "an absent entry that appears is a change"
    );
    fs::remove_dir_all(&absent).expect("gone again");
    assert!(unchanged(&recorded));

    fs::rename(&present, base.join("moved")).expect("moved");
    assert!(
        !unchanged(&recorded),
        "a recorded directory that disappears is a change"
    );
    let _ = fs::remove_dir_all(&base);
}

#[test]
fn summary_is_python_sorted_json() {
    let mut files = trees::Files::new();
    files.insert("b".to_owned(), "2".to_owned());
    files.insert("a".to_owned(), "1".to_owned());
    // sha256 of '{"a": "1", "b": "2"}', json.dumps(files, sort_keys=True).
    let expected = fang_hash::sha256_hex(br#"{"a": "1", "b": "2"}"#);
    assert_eq!(trees::summary(&files).expect("summary"), expected);
}
