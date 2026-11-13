// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use std::ffi::OsString;
use std::fs;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use fang_json::{Object, Value};
use fang_supervisor::{Limits, Status, Supervisor};
use fang_v8_kernel::{internal, trees, util};

fn scratch() -> PathBuf {
    fang_supervisor::make_temp_dir(&std::env::temp_dir(), "fang-kernel-internal-").unwrap()
}

fn command(flag: &str, args: &[PathBuf]) -> Vec<OsString> {
    let mut command = vec![env!("CARGO_BIN_EXE_fang-v8-kernel").into(), flag.into()];
    command.extend(args.iter().map(|path| path.as_os_str().to_owned()));
    command
}

#[test]
fn inventory_is_data_only_and_detects_changes() {
    let root = scratch();
    let tree = root.join("tree");
    fs::create_dir(&tree).unwrap();
    fs::write(tree.join("file"), b"before").unwrap();
    let mut record = Object::new();
    record.set("test", trees::record(tree.to_str().unwrap()).unwrap());
    let path = root.join("trees.json");
    let data = util::manifest_bytes(&Value::Object(record)).unwrap();
    fs::write(&path, &data).unwrap();
    let mut argv = command(internal::INVENTORY, &[path]);
    argv.push(fang_hash::sha256_hex(&data).into());
    let mut supervisor = Supervisor::new(Limits::default(), None).unwrap();
    for (name, unchanged) in [("before", true), ("after", false)] {
        let result =
            internal::supervised(&mut supervisor, &argv, name, &root.join(name), &root).unwrap();
        assert_eq!(
            result.get("unchanged").and_then(Value::as_bool),
            Some(unchanged)
        );
        assert!(result.get("status").is_none());
        let stdout = fs::read(root.join(name).join("stdout")).unwrap();
        assert!(!String::from_utf8_lossy(&stdout).contains("KernelChecked"));
        fs::write(tree.join("file"), b"after").unwrap();
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn inventory_child_checks_the_canonical_record_pin() {
    let root = scratch();
    let tree = root.join("tree");
    fs::create_dir(&tree).unwrap();
    let mut record = Object::new();
    record.set("test", trees::record(tree.to_str().unwrap()).unwrap());
    let value = Value::Object(record);
    let canonical = util::manifest_bytes(&value).unwrap();
    let path = root.join("trees.json");
    // Noncanonical whitespace has the same canonical hash, as in the original entry.
    fs::write(&path, util::sorted_line(&value).unwrap()).unwrap();
    let mut argv = command(internal::INVENTORY, std::slice::from_ref(&path));
    argv.push(fang_hash::sha256_hex(&canonical).into());
    let mut supervisor = Supervisor::new(Limits::default(), None).unwrap();
    let result =
        internal::supervised(&mut supervisor, &argv, "same", &root.join("same"), &root).unwrap();
    assert_eq!(result.get("unchanged").and_then(Value::as_bool), Some(true));
    fs::write(&path, b"{}").unwrap();
    let error = internal::supervised(
        &mut supervisor,
        &argv,
        "changed",
        &root.join("changed"),
        &root,
    )
    .unwrap_err();
    assert!(
        error
            .python_str()
            .contains("Tree record differs from the installation record")
    );
    assert!(
        !String::from_utf8_lossy(&fs::read(root.join("changed/stdout")).unwrap())
            .contains("KernelChecked")
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn real_inventory_is_stopped_at_the_parent_deadline() {
    let root = scratch();
    let tree = root.join("tree");
    let out = root.join("out");
    fs::create_dir(&tree).unwrap();
    fs::create_dir(&out).unwrap();
    let mut record = Object::new();
    record.set("test", trees::record(tree.to_str().unwrap()).unwrap());
    // Hashing this sparse file takes longer than the declared deadline, even in release mode.
    fs::File::create(tree.join("large"))
        .unwrap()
        .set_len(1 << 30)
        .unwrap();
    let path = root.join("trees.json");
    let data = util::manifest_bytes(&Value::Object(record)).unwrap();
    fs::write(&path, &data).unwrap();
    let mut argv = command(internal::INVENTORY, &[path]);
    argv.push(fang_hash::sha256_hex(&data).into());
    let mut supervisor = Supervisor::new(
        Limits {
            wall_seconds: 0.5,
            ..Limits::default()
        },
        None,
    )
    .unwrap();
    let start = Instant::now();
    let error = internal::supervised(&mut supervisor, &argv, "inventory", &out.join("scan"), &out)
        .unwrap_err();
    assert_eq!(error.status(), Status::Timeout);
    assert!(start.elapsed() < Duration::from_secs(5));
    assert!(
        supervisor
            .records
            .last()
            .unwrap()
            .terminated_owned_pids
            .as_ref()
            .is_some_and(|pids| !pids.is_empty())
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn internal_stage_preserves_memory_failure_and_reaps_children() {
    let root = scratch();
    let argv = vec![
        OsString::from("/bin/sh"),
        "-c".into(),
        "x=$(head -c 209715200 /dev/zero | tr '\\0' a); sleep 30".into(),
    ];
    let mut supervisor = Supervisor::new(
        Limits {
            memory_mib: 64,
            wall_seconds: 10.0,
            ..Limits::default()
        },
        None,
    )
    .unwrap();
    let error = internal::supervised(
        &mut supervisor,
        &argv,
        "memory",
        &root.join("memory"),
        &root,
    )
    .unwrap_err();
    assert_eq!(error.status(), Status::MemoryOut);
    assert!(
        supervisor
            .records
            .last()
            .unwrap()
            .terminated_owned_pids
            .as_ref()
            .is_some_and(|pids| !pids.is_empty())
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn invalid_generator_input_is_a_data_refusal() {
    let root = scratch();
    let files: Vec<_> = ["input.p", "proof.fang", "witness.json", "source"]
        .iter()
        .map(|name| root.join(name))
        .collect();
    for path in &files[..3] {
        fs::write(path, b"invalid").unwrap();
    }
    fs::create_dir(&files[3]).unwrap();
    let argv = command(internal::GENERATE, &files);
    let mut supervisor = Supervisor::new(Limits::default(), None).unwrap();
    let result = internal::supervised(
        &mut supervisor,
        &argv,
        "generate",
        &root.join("generate"),
        &root,
    )
    .unwrap();
    assert_eq!(
        result.get("status").and_then(Value::as_str),
        Some("refused")
    );
    assert_eq!(
        result.get("class").and_then(Value::as_str),
        Some("Rejected")
    );
    assert_eq!(fs::read_dir(&files[3]).unwrap().count(), 0);
    fs::remove_dir_all(root).unwrap();
}
