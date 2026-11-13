// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! SourceMapTests of tools/tests/test_v8_szs.py, ported. Two of its eleven cases test other
//! components and are ported with them: test_lean_build_allows_only_pinned_external_imports
//! (build-v8-lean.check_closures, the installer) and test_capability_caps_equal_the_limits_record
//! (capability, the launcher).
use std::path::{Path, PathBuf};

use fang_json::{Object, Value};
use fang_source_checks::Error;
use fang_source_checks::backend::{self, PackageRows, Row};
use fang_source_checks::v8::{self, Suffix};

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .find(|path| path.join("tools/v8_szs/rust-sources.json").is_file())
        .expect("repository root")
        .to_path_buf()
}

fn ok() -> Result<(), fang_supervisor::Failure> {
    Ok(())
}

/// tempfile.TemporaryDirectory: a fresh directory, removed when the test ends.
struct Scratch(PathBuf);

impl Scratch {
    fn new(name: &str) -> Scratch {
        let directory =
            std::env::temp_dir().join(format!("fang-source-map-{}-{name}", std::process::id()));
        std::fs::create_dir(&directory).unwrap();
        Scratch(directory)
    }
}

impl std::ops::Deref for Scratch {
    type Target = Path;
    fn deref(&self) -> &Path {
        &self.0
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn scratch(name: &str) -> Scratch {
    Scratch::new(name)
}

fn copy(from: &Path, to: &Path) {
    std::fs::create_dir_all(to.parent().unwrap()).unwrap();
    std::fs::copy(from, to).unwrap();
}

/// The text of a ValueError; any other error fails the test, as assertRaisesRegex(ValueError) does.
fn value_text(error: Error) -> String {
    match error {
        Error::Value(text) => text,
        other => panic!("expected a ValueError, got {other:?}"),
    }
}

fn message(result: Result<impl std::fmt::Debug, Error>) -> String {
    value_text(result.unwrap_err())
}

fn map(name: &str, schema: &str) -> Value {
    v8::load_map(&root(), name, schema, &mut ok).unwrap()
}

fn includes(source_map: &Value) -> Vec<(String, Value)> {
    let mut found = Vec::new();
    for (name, entry) in source_map.get("files").unwrap().as_object().unwrap().iter() {
        for rewrite in entry
            .get("include_rewrites")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            found.push((name.to_owned(), rewrite.clone()));
        }
    }
    found
}

#[test]
fn product_tree_matches_the_maps() {
    let rust_map = map(v8::RUST_MAP, v8::RUST_SCHEMA);
    let targets: std::collections::BTreeSet<String> = includes(&rust_map)
        .into_iter()
        .map(|(_, rewrite)| rewrite.get("target").unwrap().as_str().unwrap().to_owned())
        .collect();
    let data = rust_map
        .get("data_files")
        .and_then(Value::as_object)
        .map_or(0, Object::len);
    assert_eq!(
        v8::rust_files(&root(), &mut ok).unwrap().len(),
        rust_map.get("files").unwrap().as_object().unwrap().len() + data + targets.len()
    );
    let lean_map = map(v8::LEAN_MAP, v8::LEAN_SCHEMA);
    assert_eq!(
        v8::lean_files(&root(), &mut ok).unwrap().len(),
        lean_map.get("files").unwrap().as_object().unwrap().len()
    );
}

#[test]
fn changed_moved_file_is_rejected() {
    let source_map = map(v8::RUST_MAP, v8::RUST_SCHEMA);
    let tree = scratch("moved");
    let data: Vec<(String, Value)> = source_map
        .get("data_files")
        .and_then(Value::as_object)
        .map(|object| {
            object
                .iter()
                .map(|(name, entry)| (name.to_owned(), entry.clone()))
                .collect()
        })
        .unwrap_or_default();
    let rewrites = includes(&source_map);
    let mut relatives: Vec<String> = Vec::new();
    relatives.extend(
        source_map
            .get("files")
            .unwrap()
            .as_object()
            .unwrap()
            .keys()
            .map(str::to_owned),
    );
    relatives.extend(
        source_map
            .get("path_targets")
            .unwrap()
            .as_object()
            .unwrap()
            .keys()
            .map(str::to_owned),
    );
    relatives.push(v8::RUST_MAP.to_owned());
    relatives.extend(data.iter().map(|(name, _)| name.clone()));
    relatives.extend(data.iter().filter_map(|(_, entry)| {
        entry
            .get("same_as")
            .and_then(Value::as_str)
            .map(str::to_owned)
    }));
    relatives.extend(
        rewrites
            .iter()
            .map(|(_, rewrite)| rewrite.get("target").unwrap().as_str().unwrap().to_owned()),
    );
    for relative in &relatives {
        copy(&root().join(relative), &tree.join(relative));
    }
    let targets: std::collections::BTreeSet<&str> = rewrites
        .iter()
        .map(|(_, rewrite)| rewrite.get("target").unwrap().as_str().unwrap())
        .collect();
    let files = source_map.get("files").unwrap().as_object().unwrap().len();
    assert_eq!(
        v8::rust_files(&tree, &mut ok).unwrap().len(),
        files + data.len() + targets.len()
    );
    if let Some((name, rewrite)) = rewrites.first() {
        let reader = tree.join(name);
        let saved = std::fs::read(&reader).unwrap();
        let to = format!("\"{}\"", rewrite.get("to").unwrap().as_str().unwrap());
        let changed = String::from_utf8(saved.clone()).unwrap().replacen(
            &to,
            "\"../../NativeLimits.lean\"",
            1,
        );
        std::fs::write(&reader, changed).unwrap();
        assert!(
            message(v8::check_rust_include(&tree, &reader, rewrite, &mut ok))
                .contains("Include does not read")
        );
        std::fs::write(&reader, saved).unwrap();
    }
    if let Some((name, _)) = data.first() {
        let record = tree.join(name);
        let saved = std::fs::read(&record).unwrap();
        std::fs::write(&record, [saved.as_slice(), b"\n"].concat()).unwrap();
        assert!(message(v8::rust_files(&tree, &mut ok)).contains("data file differs"));
        std::fs::write(&record, saved).unwrap();
    }
    let target = tree.join("crates/fang-v8/src/lib.rs");
    let saved = std::fs::read(&target).unwrap();
    std::fs::write(&target, [saved.as_slice(), b"\n"].concat()).unwrap();
    assert!(message(v8::rust_files(&tree, &mut ok)).contains("differs from its receipt"));
    std::fs::write(&target, saved).unwrap();
    std::fs::write(tree.join("crates/fang-v8/src/extra.rs"), "// unlisted\n").unwrap();
    assert!(message(v8::rust_files(&tree, &mut ok)).contains("inventory differs"));
}

#[test]
fn lean_adaptation_is_only_the_recorded_comment_edits() {
    let mut source_map = map(v8::LEAN_MAP, v8::LEAN_SCHEMA);
    assert_eq!(
        source_map.get("module_renames"),
        Some(&Value::Object(Object::new()))
    );
    let files = source_map.get("files").unwrap().as_object().unwrap();
    // A later gate can pin the edited bytes directly, without an adaptation.
    // Any remaining adaptations still have the original narrow scope.
    for (relative, entry) in files.iter() {
        if let Some(adaptation) = entry.get("adaptation") {
            assert!(["GoalDocumentV8.lean", "NativeLimits.lean"].contains(&relative));
            assert_eq!(
                adaptation.get("kind").and_then(Value::as_str),
                Some("comment-rewrite")
            );
        }
    }
    let project = scratch("adaptation");
    let source_project = root().join(source_map.get("project").unwrap().as_str().unwrap());
    for relative in files.keys() {
        copy(&source_project.join(relative), &project.join(relative));
        assert_eq!(
            fang_hash::sha256_hex(&std::fs::read(project.join(relative)).unwrap()),
            files
                .get(relative)
                .unwrap()
                .get("sha256")
                .unwrap()
                .as_str()
                .unwrap(),
            "{relative}"
        );
    }
    v8::check_adaptations(&project, &source_map, &mut ok).unwrap();
    let files = source_map
        .as_object_mut()
        .unwrap()
        .get_mut("files")
        .unwrap()
        .as_object_mut()
        .unwrap();
    let absorb = files
        .get_mut("Absorb.lean")
        .unwrap()
        .as_object_mut()
        .unwrap();
    let sha = absorb.get("sha256").unwrap().clone();
    absorb.set("original_sha256", sha);
    assert!(
        message(v8::check_adaptations(&project, &source_map, &mut ok))
            .contains("Unrecorded adaptation")
    );
}

#[test]
fn recorded_lean_comment_adaptation_rejects_changed_code_and_comments() {
    // Exercise the adaptation branch even when the current gate pins every file
    // directly and therefore has no adaptations of its own.
    let original = "-- Original note.\ndef namingThreshold : Nat := 8\n";
    let (mut adaptation, edited) = record(original, &[(1, "-- Reviewed note.")], Suffix::Lean);
    adaptation
        .as_object_mut()
        .unwrap()
        .set("kind", "comment-rewrite");
    let mut entry = Object::new();
    entry.set("original", "Limits.lean");
    entry.set(
        "original_sha256",
        fang_hash::sha256_hex(original.as_bytes()),
    );
    entry.set("sha256", fang_hash::sha256_hex(edited.as_bytes()));
    entry.set("adaptation", adaptation);
    let mut files = Object::new();
    files.set("Limits.lean", entry);
    let mut source_map = Object::new();
    source_map.set("files", files);
    let source_map = Value::Object(source_map);
    let project = scratch("recorded-adaptation");
    let target = project.join("Limits.lean");
    std::fs::write(&target, &edited).unwrap();
    v8::check_adaptations(&project, &source_map, &mut ok).unwrap();
    for (changed, expected) in [
        (
            edited.replace("Nat := 8", "Nat := 9"),
            "beyond comment text",
        ),
        (
            edited.replace("Reviewed note", "Unrecorded note"),
            "does not match the file",
        ),
    ] {
        assert_ne!(changed, edited);
        std::fs::write(&target, changed).unwrap();
        assert!(
            message(v8::check_adaptations(&project, &source_map, &mut ok)).contains(expected),
            "{expected}"
        );
    }
}

fn row(digest: char) -> Row {
    Row {
        kind: "file".into(),
        sha256: digest.to_string().repeat(64),
        size: 1,
        target: None,
    }
}

fn rows(entries: &[(&str, char)]) -> PackageRows {
    entries
        .iter()
        .map(|(name, digest)| ((*name).to_owned(), row(*digest)))
        .collect()
}

fn with(base: &PackageRows, changes: &[(&str, char)]) -> PackageRows {
    let mut rows = base.clone();
    for (name, digest) in changes {
        rows.insert((*name).to_owned(), row(*digest));
    }
    rows
}

#[test]
fn content_digest_leaves_out_only_lake_hash_files() {
    let base = rows(&[
        ("A.olean", '1'),
        ("A.olean.hash", '2'),
        ("A.trace", '3'),
        (".lake/config/x", '4'),
    ]);
    let rehashed = with(&base, &[("A.olean.hash", '5')]);
    let changed = with(&base, &[("A.olean", '6')]);
    let traced = with(&base, &[("A.trace", '7')]);
    assert_eq!(
        backend::package_digest(&base, true, false),
        backend::package_digest(&rehashed, true, false)
    );
    assert_ne!(
        backend::package_digest(&base, false, false),
        backend::package_digest(&rehashed, false, false)
    );
    for other in [&changed, &traced] {
        assert_ne!(
            backend::package_digest(&base, true, false),
            backend::package_digest(other, true, false)
        );
    }
    let pins = backend::load_pins(&root()).unwrap();
    assert!(pins.get("content_reason").is_some());
    for (_, pin) in pins.get("packages").unwrap().as_object().unwrap().iter() {
        for key in ["digest", "files", "content_digest", "content_files", "rev"] {
            assert!(pin.get(key).is_some(), "{key}");
        }
    }
}

#[test]
fn fetch_digest_leaves_out_only_build_records_and_names_kinds() {
    let base = rows(&[
        ("A.lean", '1'),
        ("A.olean", '2'),
        ("A.olean.hash", '3'),
        ("A.trace", '4'),
        ("A.setup.json", '5'),
        ("bin/x.rsp", '6'),
        ("lake-manifest.json", '7'),
    ]);
    let mut pin = Object::new();
    pin.set("fetch_files", 3u8);
    pin.set("fetch_digest", backend::package_digest(&base, false, true));
    pin.set("kinds", backend::kind_digests(&base));
    pin.set("files", base.len());
    pin.set("digest", backend::package_digest(&base, false, false));
    let pin = Value::Object(pin);
    let records = with(
        &base,
        &[
            ("A.trace", '8'),
            ("A.setup.json", '9'),
            ("bin/x.rsp", 'a'),
            ("A.c.o.export.trace", 'b'),
        ],
    );
    assert_eq!(
        backend::package_digest(&records, false, true),
        pin.get("fetch_digest").unwrap().as_str().unwrap()
    );
    assert_eq!(
        backend::differing_kinds(&records, &pin).unwrap(),
        (
            Vec::<String>::new(),
            vec![
                "c.o.export.trace".into(),
                "rsp".into(),
                "setup.json".into(),
                "trace".into()
            ]
        )
    );
    for (changes, kind) in [
        (vec![("A.olean", 'c')], "olean"),
        (vec![("A.lean", 'd')], "lean"),
        (vec![("lake-manifest.json", 'e')], "json"),
        (vec![("B.so", 'f')], "so"),
    ] {
        let changed = with(&base, &changes);
        assert_ne!(
            backend::package_digest(&changed, false, true),
            pin.get("fetch_digest").unwrap().as_str().unwrap()
        );
        assert_eq!(
            backend::differing_kinds(&changed, &pin).unwrap().0,
            vec![kind.to_owned()]
        );
    }
    let pins = backend::load_pins(&root()).unwrap();
    assert_eq!(
        pins.get("fetch_left_out").unwrap(),
        &Value::Array(
            [".hash", ".trace", ".setup.json", ".rsp"]
                .iter()
                .map(|item| Value::from(*item))
                .collect()
        )
    );
    assert!(pins.get("fetch_reason").is_some());
    for (_, pin) in pins.get("packages").unwrap().as_object().unwrap().iter() {
        for key in [
            "digest",
            "content_digest",
            "fetch_digest",
            "fetch_files",
            "kinds",
        ] {
            assert!(pin.get(key).is_some(), "{key}");
        }
    }
}

fn record(original: &str, edits: &[(usize, &str)], suffix: Suffix) -> (Value, String) {
    let mut lines: Vec<String> = original.split('\n').map(str::to_owned).collect();
    let mut rewrite = Object::new();
    rewrite.set(
        "code_view_sha256",
        v8::code_view_sha256(original, suffix).unwrap(),
    );
    let mut list = Vec::new();
    for (number, after) in edits {
        let mut edit = Object::new();
        edit.set("line", *number);
        edit.set("to", *after);
        edit.set(
            "from_sha256",
            fang_hash::sha256_hex(lines[number - 1].as_bytes()),
        );
        list.push(Value::Object(edit));
        lines[number - 1] = (*after).to_owned();
    }
    rewrite.set("edits", Value::Array(list));
    (Value::Object(rewrite), lines.join("\n"))
}

fn check(
    original: &str,
    edits: &[(usize, &str)],
    suffix: Suffix,
    current: Option<&str>,
) -> Result<(Value, String), String> {
    let (rewrite, edited) = record(original, edits, suffix);
    v8::check_comment_rewrite(current.unwrap_or(&edited).as_bytes(), &rewrite, suffix)
        .map_err(value_text)?;
    Ok((rewrite, edited))
}

#[test]
fn comment_rewrite_changes_only_comment_text() {
    let lean = "/- Header (local note).\n   more -/\ndef a : String := \"-- x\"\ndef c : Char := '\"'\n-- note one\ntheorem t : True := trivial -- one\n";
    let (rewrite, edited) = check(
        lean,
        &[(1, "/- Header."), (5, "-- note")],
        Suffix::Lean,
        None,
    )
    .unwrap();
    assert_eq!(
        v8::apply_comment_rewrite(lean.as_bytes(), &rewrite, Suffix::Lean).unwrap(),
        edited.as_bytes()
    );
    assert!(
        !fang_json::dumps(&rewrite, &Default::default())
            .unwrap()
            .contains("local note")
    );
    for (edits, expected) in [
        (
            vec![(3, "def a : String := \"-- y\"")],
            "beyond comment text",
        ),
        (vec![(1, "/-- Header.")], "beyond comment text"),
        (
            vec![(2, "   more -/ def b := 1 /- x -/")],
            "beyond comment text",
        ),
        (vec![(2, "   more -/ #exit /-")], "Unclosed block comment"),
        (
            vec![(6, "theorem t : True := trivial -- two")],
            "lies outside comments",
        ),
    ] {
        assert!(
            check(lean, &edits, Suffix::Lean, None)
                .unwrap_err()
                .contains(expected),
            "{expected}"
        );
    }
    assert!(
        check(lean, &[(1, "/- Header.")], Suffix::Lean, Some(lean))
            .unwrap_err()
            .contains("does not match the file")
    );
    let (rewrite, edited) = record(lean, &[(1, "/- Header.")], Suffix::Lean);
    let unrecorded = edited.replace("-- note one", "-- note two");
    v8::check_comment_rewrite(unrecorded.as_bytes(), &rewrite, Suffix::Lean).unwrap();
    assert_ne!(
        v8::apply_comment_rewrite(lean.as_bytes(), &rewrite, Suffix::Lean).unwrap(),
        unrecorded.as_bytes()
    );
    assert!(
        message(v8::apply_comment_rewrite(
            edited.as_bytes(),
            &rewrite,
            Suffix::Lean
        ))
        .contains("does not match the reviewed bytes")
    );
    let rust = "// Header; see the old note.\n/// Doc.\nlet s = r#\"// x\"#;\nlet q = '\"';\n";
    check(rust, &[(1, "// Header.")], Suffix::Rust, None).unwrap();
    for edits in [
        vec![(2, "// Doc.")],
        vec![(3, "let s = r#\"// y\"#;")],
        vec![(4, "let q = '\\'';")],
    ] {
        assert!(
            check(rust, &edits, Suffix::Rust, None)
                .unwrap_err()
                .contains("beyond comment text")
        );
    }
}

#[test]
fn left_out_gate_modules_stay_out() {
    let build = |reason: &str| {
        let mut left_out = Object::new();
        left_out.set("OldMain.lean", reason);
        let mut gate = Object::new();
        gate.set("left_out", left_out);
        let mut gates = Object::new();
        gates.set("g", gate);
        let mut files = Object::new();
        files.set("A.lean", Object::new());
        files.set("B.lean", Object::new());
        let mut map = Object::new();
        map.set("gates", gates);
        map.set("files", files);
        Value::Object(map)
    };
    let source_map = build("superseded native main");
    let project = scratch("left-out");
    std::fs::write(project.join("A.lean"), "import B\n").unwrap();
    std::fs::write(project.join("B.lean"), "def b := 1\n").unwrap();
    v8::check_left_out(&project, &source_map, &mut ok).unwrap();
    std::fs::write(project.join("A.lean"), "import B\nimport OldMain\n").unwrap();
    assert!(
        message(v8::check_left_out(&project, &source_map, &mut ok))
            .contains("imports a left-out module")
    );
    std::fs::write(project.join("A.lean"), "import B\n").unwrap();
    std::fs::write(
        project.join("OldMain.lean"),
        "def main : IO Unit := pure ()\n",
    )
    .unwrap();
    assert!(
        message(v8::check_left_out(&project, &source_map, &mut ok)).contains("staged in lean-v8")
    );
    std::fs::remove_file(project.join("OldMain.lean")).unwrap();
    assert!(
        message(v8::check_left_out(&project, &build(""), &mut ok)).contains("without a reason")
    );
}

#[test]
fn generated_sources_name_no_machine_paths() {
    let source_map = map(v8::LEAN_MAP, v8::LEAN_SCHEMA);
    // The selected checker can move to a later gate. Its generated source must
    // still be the unadapted bytes from that same recorded gate.
    let checkers: Vec<&Value> = source_map
        .get("executables")
        .unwrap()
        .as_object()
        .unwrap()
        .values()
        .filter(|entry| entry.get("installed_as").and_then(Value::as_str) == Some("fang-v8-check"))
        .collect();
    assert_eq!(checkers.len(), 1, "exactly one installed checker");
    let gate = checkers[0].get("gate").unwrap().as_str().unwrap();
    assert!(source_map.get("gates").unwrap().get(gate).is_some());
    assert!(source_map.get("receipts").unwrap().get(gate).is_some());
    for name in [
        "BinderRemoval.lean",
        "Fof.lean",
        "FofEqualityBridge.lean",
        "Skolem.lean",
    ] {
        let entry = source_map.get("files").unwrap().get(name).unwrap();
        assert_eq!(
            entry.get("origin").and_then(Value::as_str),
            Some("union-gate")
        );
        assert_eq!(
            (
                entry.get("receipt").and_then(Value::as_str),
                entry.get("original").and_then(Value::as_str),
                entry.get("imports_added").is_some(),
                entry.get("adaptation").is_some()
            ),
            (Some(gate), Some(name), false, false)
        );
        assert!(
            std::fs::read_to_string(root().join("lean-v8").join(name))
                .unwrap()
                .contains("public import FangFastVec\n")
        );
    }
    let mut paths: Vec<PathBuf> = std::fs::read_dir(root().join("lean-v8"))
        .unwrap()
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "lean")
        })
        .collect();
    for crate_entry in std::fs::read_dir(root().join("crates")).unwrap().flatten() {
        let mut pending = vec![crate_entry.path().join("src")];
        while let Some(directory) = pending.pop() {
            let Ok(entries) = std::fs::read_dir(&directory) else {
                continue;
            };
            // pathlib's "**" does not follow symbolic links to directories.
            for entry in entries.flatten() {
                let path = entry.path();
                if entry.file_type().is_ok_and(|kind| kind.is_dir()) {
                    pending.push(path);
                } else if path.extension().is_some_and(|extension| extension == "rs") {
                    paths.push(path);
                }
            }
        }
    }
    for path in paths {
        let relative = path
            .strip_prefix(root())
            .unwrap()
            .to_string_lossy()
            .into_owned();
        for (index, line) in std::fs::read_to_string(&path).unwrap().lines().enumerate() {
            assert!(
                portable_line(&relative, line),
                "{}:{}",
                path.display(),
                index + 1
            );
        }
    }
}

// These are OS interface paths, a temporary-directory pattern, and a quoting
// fixture. They are not generated-code provenance. Permit the exact line only
// in its integration file; every other line in those files is still checked.
const PLATFORM_LINES: &[(&str, &str)] = &[
    (
        "crates/fang-kernel-workspace/src/lib.rs",
        "/// Create `/var/tmp/fang-kernel-*`, record its path before anything else can fail, and add the public root",
    ),
    (
        "crates/fang-install/src/v8_install.rs",
        "let fsutil = \"/mnt/c/Windows/System32/fsutil.exe\".to_string();",
    ),
    (
        "crates/fang-install/src/v8_install.rs",
        "assert_eq!(shell_quote(\"/var/tmp/x-1/bin\"), \"/var/tmp/x-1/bin\");",
    ),
    (
        "crates/v8-kernel/src/entry.rs",
        "//! starts before a refusal, ReviewPending included. For an output directory under /mnt/c,",
    ),
    (
        "crates/v8-kernel/src/entry.rs",
        "/// The version-8 library has case-only module pairs: make a new /mnt/c output case-sensitive",
    ),
    (
        "crates/v8-kernel/src/entry.rs",
        "if windows && directory.starts_with(\"/mnt/c/\") {",
    ),
    (
        "crates/v8-kernel/src/entry.rs",
        "let mut child = Command::new(\"/mnt/c/Windows/System32/fsutil.exe\")",
    ),
];

fn machine_path(text: &str) -> bool {
    text.contains("/var/tmp/") || text.contains("/mnt/") || text.contains("/home/")
        // Python's drive-path pattern matches a letter, a colon and two backslashes.
        || text.as_bytes().windows(4).any(|window| {
            window[0].is_ascii_alphabetic() && window[1] == b':' && window[2] == b'\\' && window[3] == b'\\'
        })
}

fn portable_line(relative: &str, line: &str) -> bool {
    !machine_path(line) || PLATFORM_LINES.contains(&(relative, line.trim()))
}

#[test]
fn platform_path_exceptions_cannot_hide_source_paths() {
    for &(path, line) in PLATFORM_LINES {
        assert!(portable_line(path, line));
        assert!(!portable_line("crates/fang-v8/src/lib.rs", line));
        assert!(!portable_line("lean-v8/Fof.lean", line));
        assert!(!portable_line(
            path,
            &format!("{line} // /home/user/source")
        ));
        assert!(
            !portable_line(path, &line.replace("/mnt/c", "/mnt/d")) || !line.contains("/mnt/c")
        );
    }
    for source in [
        "/home/user/source",
        "/mnt/c/Users/user/source",
        "/var/tmp/build/source",
        r"C:\\Users\\user\\source",
    ] {
        for path in [
            "crates/fang-install/src/v8_install.rs",
            "crates/v8-kernel/src/entry.rs",
            "crates/fang-v8/src/lib.rs",
            "lean-v8/Fof.lean",
        ] {
            assert!(!portable_line(path, source));
        }
    }
    assert!(!portable_line(
        "crates/fang-install/src/v8_install.rs",
        "let fsutil = \"/mnt/c/Windows/System32/fsutil.exe-other\".to_string();"
    ));
}

#[test]
fn path_rewrites_rebuild_the_moved_manifest() {
    let original = b"[dependencies]\nfang = { path = \"../..\" }\nx = { path = \"../../a/b\" }\n";
    let mut rewrite = Object::new();
    rewrite.set("line", 3u8);
    rewrite.set("from", "../../a/b");
    rewrite.set("to", "../b");
    let rebuilt =
        v8::apply_rewrites(original, &[Value::Object(rewrite.clone())], &[], &[]).unwrap();
    assert_eq!(
        rebuilt,
        b"[dependencies]\nfang = { path = \"../..\" }\nx = { path = \"../b\" }\n"
    );
    rewrite.set("line", 2u8);
    message(v8::apply_rewrites(
        original,
        &[Value::Object(rewrite)],
        &[],
        &[],
    ));
}
