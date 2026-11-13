// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Error texts and reads that must match Python exactly: UnicodeDecodeError, Path.read_text's
//! universal newlines and json.loads's BOM refusal. The expected texts were printed by CPython 3.14.
use std::path::PathBuf;

use fang_json::Value;
use fang_source_checks::v8::{self, Suffix};

fn ok() -> Result<(), fang_supervisor::Failure> {
    Ok(())
}

#[test]
fn utf8_errors_carry_cpython_text() {
    for (data, expected) in [
        (&b"\xff"[..], "byte 0xff in position 0: invalid start byte"),
        (
            b"a\xe2\x82",
            "bytes in position 1-2: unexpected end of data",
        ),
        (
            b"\xe2\x28\xa1",
            "byte 0xe2 in position 0: invalid continuation byte",
        ),
        (
            b"\xf0\x90\x28",
            "bytes in position 0-1: invalid continuation byte",
        ),
        (
            b"\xed\xa0\x80",
            "byte 0xed in position 0: invalid continuation byte",
        ),
        (b"\xc0\x80", "byte 0xc0 in position 0: invalid start byte"),
        (b"\xe2", "byte 0xe2 in position 0: unexpected end of data"),
        (
            b"\xf4\x90\x80\x80",
            "byte 0xf4 in position 0: invalid continuation byte",
        ),
        (
            b"ok\xf0\x9f\x98",
            "bytes in position 2-4: unexpected end of data",
        ),
    ] {
        let error = v8::check_comment_rewrite(data, &Value::Null, Suffix::Lean).unwrap_err();
        assert_eq!(
            error.to_string(),
            format!("'utf-8' codec can't decode {expected}")
        );
        let error = v8::remove_imports(data, &[]).unwrap_err();
        assert_eq!(
            error.to_string(),
            format!("'utf-8' codec can't decode {expected}")
        );
    }
}

struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn backend_scan_resolves_and_walks_as_python() {
    use std::os::unix::fs::symlink;
    let scratch =
        Scratch(std::env::temp_dir().join(format!("fang-python-scan-{}", std::process::id())));
    let d = &scratch.0;
    for directory in ["a/b", "p", "q/z", "q/y"] {
        std::fs::create_dir_all(d.join(directory)).unwrap();
    }
    for file in ["a/file", "q/z/f", "q/y/g"] {
        std::fs::write(d.join(file), "").unwrap();
    }
    for (link, target) in [
        ("p/dangling", "nowhere"),
        ("a/loop", "loop"),
        ("q/zz", "z"),
        ("q/a", "y"),
    ] {
        symlink(target, d.join(link)).unwrap();
    }
    let text = d.to_str().unwrap();
    let scan = |relative: &str| {
        fang_source_checks::backend::scan(&d.join(relative), &mut ok)
            .map_err(|error| error.to_string().replace(text, "D"))
    };
    for (relative, expected) in [
        ("a/b/c/d", "[Errno 2] No such file or directory: 'D/a/b/c'"),
        ("a/file/x", "[Errno 20] Not a directory: 'D/a/file'"),
        (
            "a/loop",
            "[Errno 40] Too many levels of symbolic links: 'D/a/loop'",
        ),
        ("p", "[Errno 2] No such file or directory: 'D/p/nowhere'"),
        ("q", "Backend directory symlink: D/q/a"),
    ] {
        assert_eq!(scan(relative).unwrap_err(), expected, "{relative}");
    }
    assert!(scan("a/b/../b").unwrap().is_empty());
}

#[test]
fn dependency_inputs_use_their_own_messages() {
    let scratch =
        Scratch(std::env::temp_dir().join(format!("fang-python-deps-{}", std::process::id())));
    std::fs::create_dir_all(scratch.0.join("real")).unwrap();
    let manifest = scratch.0.join("Cargo.toml");
    std::fs::write(scratch.0.join("real/Cargo.toml"), "[package]\n").unwrap();
    std::os::unix::fs::symlink("real/Cargo.toml", &manifest).unwrap();
    let error = fang_source_checks::deps::dependency_files(&scratch.0, &mut ok).unwrap_err();
    assert_eq!(
        error.to_string(),
        format!(
            "Dependency input must be a regular file: {}",
            manifest.display()
        )
    );
    std::fs::remove_file(&manifest).unwrap();
    std::fs::write(
        &manifest,
        "[package]\nname = \"fang\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    std::fs::write(scratch.0.join("Cargo.lock"), "version = 4\n").unwrap();
    let error = fang_source_checks::deps::dependency_files(&scratch.0, &mut ok).unwrap_err();
    assert_eq!(
        error.to_string(),
        format!(
            "Unreviewed Cargo lockfile graph: {}",
            scratch.0.join("Cargo.lock").display()
        )
    );
}

#[test]
fn maps_are_read_as_path_read_text_and_json_loads() {
    let scratch =
        Scratch(std::env::temp_dir().join(format!("fang-python-texts-{}", std::process::id())));
    let maps = scratch.0.join("tools/v8_szs");
    std::fs::create_dir_all(&maps).unwrap();
    let map = maps.join("rust-sources.json");
    let load = || v8::load_map(&scratch.0, v8::RUST_MAP, v8::RUST_SCHEMA, &mut ok);
    std::fs::write(
        &map,
        "{\r\n  \"schema\": \"fang-v8-rust-source-map-v1\",\r\n  \"x\": 1\r}\n",
    )
    .unwrap();
    assert_eq!(load().unwrap().get("x").and_then(Value::as_u64), Some(1));
    std::fs::write(&map, "\u{feff}{\"schema\": \"fang-v8-rust-source-map-v1\"}").unwrap();
    assert_eq!(
        load().unwrap_err().to_string(),
        "Unexpected UTF-8 BOM (decode using utf-8-sig): line 1 column 1 (char 0)"
    );
    // A lone CR inside a string is read as LF, which json.loads refuses as a control character.
    std::fs::write(&map, "{\"schema\": \"a\rb\"}").unwrap();
    assert_eq!(
        load().unwrap_err().to_string(),
        "Invalid control character at: line 1 column 14 (char 13)"
    );
    std::fs::write(&map, b"{\"schema\": \"\xff\"}").unwrap();
    assert_eq!(
        load().unwrap_err().to_string(),
        "'utf-8' codec can't decode byte 0xff in position 12: invalid start byte"
    );
}
