// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Real nested guard startup and cancellation through the installer's child helpers.
#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use fang_install::common::{run_captured, run_inherited};
use fang_supervisor::guard::MARKER;

const PROBE: &str = "FANG_INSTALL_NESTED_GUARD_PROBE";
const KEPT: &str = "FANG_INSTALL_NESTED_GUARD_KEPT";

fn directory() -> PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "fang-install-nested-guard-{}-{nonce}",
        std::process::id()
    ));
    fs::create_dir(&path).unwrap();
    path
}

fn command(test: &str) -> Vec<String> {
    vec![
        std::env::current_exe()
            .unwrap()
            .to_string_lossy()
            .into_owned(),
        "--exact".into(),
        test.into(),
        "--nocapture".into(),
    ]
}

fn helper(test: &str, mode: &str, directory: &Path) -> Command {
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args(["--exact", test, "--nocapture"])
        .env(PROBE, mode)
        .env(KEPT, "retained")
        .env("FANG_INSTALL_NESTED_GUARD_DIRECTORY", directory)
        .env_remove(MARKER);
    command
}

#[test]
fn guarded_parent_probe() {
    let Ok(mode) = std::env::var(PROBE) else {
        return;
    };
    let worker = fang_install::guarded();
    assert!(std::env::var_os(MARKER).is_some());
    let directory = PathBuf::from(std::env::var_os("FANG_INSTALL_NESTED_GUARD_DIRECTORY").unwrap());
    fs::write(
        directory.join("parent-worker.pid"),
        std::process::id().to_string(),
    )
    .unwrap();
    if mode == "wait" {
        let _ = run_inherited(
            &command("guarded_waiting_child_probe"),
            Duration::from_secs(20),
        );
        panic!("waiting child should be cancelled with its parent");
    }
    assert_eq!(
        run_inherited(&command("guarded_child_probe"), Duration::from_secs(5)).unwrap(),
        0
    );
    let environment: BTreeMap<String, String> = std::env::vars().collect();
    assert!(environment.contains_key(MARKER));
    let result = run_captured(
        &command("guarded_child_probe"),
        None,
        Some(&environment),
        Duration::from_secs(5),
    )
    .unwrap();
    assert_eq!(
        result.returncode,
        0,
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(String::from_utf8_lossy(&result.stdout).contains("nested guard child accepted"));
    worker
        .finalize(|| println!("nested guard parent accepted"))
        .unwrap();
    std::process::exit(0);
}

#[test]
fn guarded_child_probe() {
    if std::env::var_os(PROBE).is_none() {
        return;
    }
    let worker = fang_install::guarded();
    assert_eq!(std::env::var(KEPT).unwrap(), "retained");
    assert_eq!(worker.outer(), std::os::unix::process::parent_id());
    worker
        .finalize(|| println!("nested guard child accepted"))
        .unwrap();
    std::process::exit(0);
}

#[test]
fn guarded_waiting_child_probe() {
    if std::env::var(PROBE).as_deref() != Ok("wait") {
        return;
    }
    let _worker = fang_install::guarded();
    let directory = PathBuf::from(std::env::var_os("FANG_INSTALL_NESTED_GUARD_DIRECTORY").unwrap());
    fs::write(
        directory.join("child-worker.pid"),
        std::process::id().to_string(),
    )
    .unwrap();
    loop {
        std::thread::sleep(Duration::from_millis(20));
    }
}

#[test]
fn inherited_and_explicit_environments_start_new_guards() {
    let directory = directory();
    let result = helper("guarded_parent_probe", "normal", &directory)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "stdout={} stderr={}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(String::from_utf8_lossy(&result.stdout).contains("nested guard parent accepted"));
    fs::remove_dir_all(directory).unwrap();
}

fn live(pid: &str) -> bool {
    fs::read_to_string(format!("/proc/{pid}/stat"))
        .ok()
        .and_then(|text| {
            text.rsplit_once(") ")
                .map(|(_, tail)| !matches!(tail.as_bytes().first(), Some(b'Z' | b'X' | b'x')))
        })
        .unwrap_or(false)
}

#[test]
fn cancelling_outer_installer_stops_both_nested_workers() {
    let directory = directory();
    let mut parent = helper("guarded_parent_probe", "wait", &directory)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(5);
    let child_path = directory.join("child-worker.pid");
    while !child_path.exists() && Instant::now() < deadline {
        std::thread::sleep(Duration::from_millis(20));
    }
    let ready = child_path.exists();
    assert!(
        Command::new("/bin/kill")
            .args(["-TERM", &parent.id().to_string()])
            .status()
            .unwrap()
            .success()
    );
    let _ = parent.wait().unwrap();
    assert!(ready, "nested guarded child did not start");
    let pids = [
        fs::read_to_string(directory.join("parent-worker.pid")).unwrap(),
        fs::read_to_string(child_path).unwrap(),
    ];
    let deadline = Instant::now() + Duration::from_secs(5);
    while pids.iter().any(|pid| live(pid)) && Instant::now() < deadline {
        std::thread::sleep(Duration::from_millis(20));
    }
    assert!(
        pids.iter().all(|pid| !live(pid)),
        "nested worker survived cancellation: {pids:?}"
    );
    fs::remove_dir_all(directory).unwrap();
}
