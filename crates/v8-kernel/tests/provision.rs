// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use std::ffi::OsString;
use std::fs;

use fang_json::{Object, Value};
use fang_v8_kernel::{provision, util};

#[test]
fn changed_workspace_manifest_invalidates_the_entry_review() {
    let root = fang_supervisor::make_temp_dir(&std::env::temp_dir(), "fang-kernel-policy-")
        .expect("fresh test directory");
    for name in provision::FILES {
        fs::write(root.join(name), b"original\n").unwrap();
    }
    for name in provision::CRATES {
        let directory = root.join(name);
        fs::create_dir_all(directory.join("src")).unwrap();
        fs::write(directory.join("Cargo.toml"), b"[package]\n").unwrap();
        fs::write(directory.join("src/lib.rs"), b"#![forbid(unsafe_code)]\n").unwrap();
    }
    fs::create_dir_all(root.join("tools/v8_kernel")).unwrap();
    let policy = provision::unprovisioned(&root).unwrap();
    assert_eq!(
        policy
            .get("files")
            .and_then(|files| files.get("Cargo.toml"))
            .and_then(Value::as_str),
        Some(fang_hash::sha256_hex(b"original\n").as_str()),
    );
    let mut sources = Object::new();
    sources.set(
        "policy.json",
        fang_hash::sha256_hex(&util::manifest_bytes(&Value::Object(policy)).unwrap()),
    );
    let mut inputs = Object::new();
    inputs.set("entry_sources_sha256", Value::Object(sources));
    let mut review = Object::new();
    review.set("status", "passed");
    review.set("inputs", Value::Object(inputs));
    let bytes = util::manifest_bytes(&Value::Object(review)).unwrap();
    fs::write(root.join("review.json"), &bytes).unwrap();
    let args: Vec<OsString> = vec![
        "provision".into(),
        "--repository".into(),
        root.as_os_str().to_owned(),
        "--entry-review".into(),
        "review.json".into(),
        "--entry-review-sha256".into(),
        fang_hash::sha256_hex(&bytes).into(),
    ];
    provision::main(&args).expect("the unchanged workspace uses the reviewed policy");
    fs::write(
        root.join("Cargo.toml"),
        b"[profile.release]\noverflow-checks = false\n",
    )
    .unwrap();
    assert_eq!(
        provision::main(&args).unwrap_err(),
        "Entry review does not name this policy"
    );
    fs::remove_dir_all(&root).unwrap();
}
