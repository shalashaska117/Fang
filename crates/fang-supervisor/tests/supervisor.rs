// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Controls of the supervisor against the behaviour of tools/fang_szs/supervisor.py.
//! Each child is /bin/sh or a coreutils program, so the controls need no other binary.
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use fang_supervisor::{Fault, Limits, Snapshot, Stage, Status, Supervisor, read_regular};

fn scratch(name: &str) -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "fang-supervisor-test-{}-{name}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&directory);
    std::fs::create_dir(&directory).unwrap();
    directory
}

fn shell(script: &str) -> Vec<OsString> {
    vec!["/bin/sh".into(), "-c".into(), script.into()]
}

fn stage<'a>(
    name: &'a str,
    command: &'a [OsString],
    directory: &'a Path,
    root: &'a Path,
) -> Stage<'a> {
    Stage {
        name,
        command,
        directory,
        run_root: root,
        environment: None,
        stdin: None,
        stdout_limit: None,
        cwd: None,
    }
}

fn failure(fault: Fault) -> (Status, String) {
    match fault {
        Fault::Failure(failure) => (failure.status, failure.reason),
        other => panic!("expected a Failure, got {other:?}"),
    }
}

#[test]
fn completed_stage_record_and_streams() {
    let root = scratch("completed");
    let mut supervisor = Supervisor::new(Limits::default(), None).unwrap();
    let command = shell("printf out; printf err >&2; exit 0");
    let output = supervisor
        .run(&stage("echo", &command, &root.join("echo"), &root))
        .unwrap();
    assert_eq!(output.stdout, b"out");
    assert_eq!(output.stderr, b"err");
    let record = &output.record;
    assert_eq!(record.classification, "completed");
    assert_eq!(record.exit_code, Some(0));
    assert_eq!(record.stdout, "echo/stdout");
    assert_eq!(record.stdout_hash_status.as_deref(), Some("complete"));
    assert_eq!(
        record.stdout_sha256.as_deref(),
        Some(fang_hash::sha256_hex(b"out").as_str())
    );
    assert_eq!(record.stdout_bytes, Some(3));
    assert_eq!(record.terminated_owned_pids.as_deref(), Some(&[][..]));
    assert_eq!(supervisor.records.len(), 1);
    let json = record.to_json();
    assert!(json.get("elapsed_seconds").unwrap().as_f64().is_some());
    assert!(json.get("exit_code").unwrap().as_i64().is_some());
}

#[test]
fn classifications_and_exit_codes() {
    let root = scratch("classes");
    let mut supervisor = Supervisor::new(Limits::default(), None).unwrap();
    let nonzero = shell("exit 3");
    let record = supervisor
        .run(&stage("three", &nonzero, &root.join("three"), &root))
        .unwrap()
        .record;
    assert_eq!(
        (record.classification.as_str(), record.exit_code),
        ("nonzero-exit", Some(3))
    );
    let killed = shell("kill -s KILL $$");
    let record = supervisor
        .run(&stage("killed", &killed, &root.join("killed"), &root))
        .unwrap()
        .record;
    assert_eq!(
        (record.classification.as_str(), record.exit_code),
        ("signal", Some(-9))
    );
}

#[test]
fn existing_stage_directory_and_unapproved_environment() {
    let root = scratch("environment");
    let mut supervisor = Supervisor::new(Limits::default(), None).unwrap();
    let command = shell("true");
    std::fs::create_dir(root.join("taken")).unwrap();
    assert!(matches!(
        supervisor.run(&stage("taken", &command, &root.join("taken"), &root)),
        Err(Fault::OsAt(..))
    ));
    let mut environment = fang_supervisor::child_environment();
    environment.set("LD_PRELOAD", "/tmp/x");
    let directory = root.join("env");
    let mut spec = stage("env", &command, &directory, &root);
    spec.environment = Some(&environment);
    let (status, reason) = failure(supervisor.run(&spec).err().unwrap());
    assert_eq!(
        (status, reason.as_str()),
        (
            Status::Error,
            "Child environment contains unapproved variables"
        )
    );
    assert_eq!(supervisor.records.last().unwrap().classification, "Error");
}

#[test]
fn stdout_limit_and_log_growth() {
    let root = scratch("logs");
    let mut supervisor = Supervisor::new(Limits::default(), None).unwrap();
    let command = shell("head -c 100000 /dev/zero; sleep 5");
    let directory = root.join("big");
    let mut spec = stage("big", &command, &directory, &root);
    spec.stdout_limit = Some(1000);
    let (status, reason) = failure(supervisor.run(&spec).err().unwrap());
    assert_eq!(
        (status, reason.as_str()),
        (
            Status::ResourceOut,
            "Child stdout/stderr byte limit reached"
        )
    );
    let record = supervisor.records.last().unwrap();
    assert_eq!(
        record.stdout_hash_status.as_deref(),
        Some("skipped-over-log-limit")
    );
}

#[test]
fn deadline_and_cancellation() {
    let root = scratch("deadline");
    let limits = Limits {
        wall_seconds: 1.0,
        ..Limits::default()
    };
    let mut supervisor = Supervisor::new(limits, None).unwrap();
    let command = shell("sleep 30");
    let started = Instant::now();
    let (status, reason) = failure(
        supervisor
            .run(&stage("sleep", &command, &root.join("sleep"), &root))
            .err()
            .unwrap(),
    );
    assert_eq!(
        (status, reason.as_str()),
        (Status::Timeout, "Whole-pipeline deadline reached")
    );
    assert!(started.elapsed() < Duration::from_secs(5));
    let record = supervisor.records.last().unwrap();
    assert_eq!(
        record.stdout_hash_status.as_deref(),
        Some("skipped-after-deadline-or-cancellation")
    );
    // The shell and its sleep, or the sleep alone when the shell executes it in place.
    let killed = record.terminated_owned_pids.as_ref().map_or(0, Vec::len);
    assert!((1..=2).contains(&killed), "killed {killed}");

    let mut supervisor = Supervisor::new(Limits::default(), None).unwrap();
    supervisor.set_deadline(Instant::now() + Duration::from_millis(500));
    assert!(supervisor.check("x", 0.0).is_ok());
    assert_eq!(
        supervisor.check("x", 1.0).unwrap_err().status,
        Status::Timeout
    );
    supervisor.cancel_token().cancel();
    let forced = supervisor.check("stage-name", 0.0).unwrap_err();
    assert_eq!(
        (forced.status, forced.reason.as_str(), forced.stage.as_str()),
        (Status::Forced, "External cancellation", "stage-name")
    );
}

#[test]
fn memory_limit() {
    let root = scratch("memory");
    let limits = Limits {
        memory_mib: 64,
        ..Limits::default()
    };
    let mut supervisor = Supervisor::new(limits, None).unwrap();
    // A 200 MiB string held by the shell.
    let command = shell("x=$(head -c 209715200 /dev/zero | tr '\\0' a); sleep 30");
    let (status, reason) = failure(
        supervisor
            .run(&stage("grow", &command, &root.join("grow"), &root))
            .err()
            .unwrap(),
    );
    assert_eq!(
        (status, reason.as_str()),
        (
            Status::MemoryOut,
            "Sampled adapter-plus-descendant RSS limit reached"
        )
    );
    assert!(supervisor.peak_kib > 64 * 1024);
}

#[test]
fn artifact_limits_and_nonregular_artifacts() {
    let root = scratch("artifacts");
    let limits = Limits {
        artifact_bytes: 10_000,
        ..Limits::default()
    };
    let mut supervisor = Supervisor::new(limits, None).unwrap();
    let command = shell("head -c 20000 /dev/zero > big; sleep 30");
    let (status, reason) = failure(
        supervisor
            .run(&stage("fill", &command, &root.join("fill"), &root))
            .err()
            .unwrap(),
    );
    assert_eq!(
        (status, reason.as_str()),
        (
            Status::ResourceOut,
            "Aggregate run artifact byte limit reached"
        )
    );
    let link = shell("ln -s /etc/passwd link; sleep 30");
    let mut supervisor = Supervisor::new(Limits::default(), None).unwrap();
    let (status, reason) = failure(
        supervisor
            .run(&stage("link", &link, &root.join("link"), &root))
            .err()
            .unwrap(),
    );
    assert_eq!(
        (status, reason.as_str()),
        (Status::Error, "Child created a nonregular artifact")
    );
}

#[test]
fn live_descendants_are_an_error_and_are_killed() {
    let root = scratch("descendants");
    let mut supervisor = Supervisor::new(Limits::default(), None).unwrap();
    let command = shell("sleep 30 & exit 0");
    let (status, reason) = failure(
        supervisor
            .run(&stage("fork", &command, &root.join("fork"), &root))
            .err()
            .unwrap(),
    );
    assert_eq!(
        (status, reason.as_str()),
        (Status::Error, "Child exited with live descendants")
    );
    let record = supervisor.records.last().unwrap();
    assert_eq!(record.terminated_owned_pids.as_ref().map(Vec::len), Some(1));
    assert!(supervisor.confirm_clean("output", &[]).is_ok());
}

#[test]
fn a_detached_grandchild_leaves_the_view() {
    // The documented subreaper gap: setsid moves the grandchild out of the stage's group, and
    // once its parent exits its parent PID is no longer in the tree.
    let root = scratch("setsid");
    let mut supervisor = Supervisor::new(Limits::default(), None).unwrap();
    let marker = root.join("pid");
    let script = format!(
        "setsid sh -c 'echo $$ > {}; exec sleep 3' & sleep 0.5; exit 0",
        marker.display()
    );
    let command = shell(&script);
    let output = supervisor.run(&stage("detach", &command, &root.join("detach"), &root));
    assert!(output.is_ok());
    let pid = std::fs::read_to_string(&marker).unwrap();
    assert!(Path::new(&format!("/proc/{}", pid.trim())).exists());
    let _ = std::process::Command::new("/bin/kill")
        .args(["-s", "KILL", pid.trim()])
        .status();
    // Keep this intentional escape local to the control. An outer test subreaper may
    // adopt its zombie, but must never inherit a running shell child from the fixture.
    let stopped = Instant::now() + Duration::from_secs(2);
    loop {
        let state = match std::fs::read_to_string(format!("/proc/{}/stat", pid.trim())) {
            Ok(stat) => stat
                .rsplit_once(") ")
                .and_then(|(_, fields)| fields.chars().next())
                .expect("process state"),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => break,
            Err(error) => panic!("cannot inspect detached control: {error}"),
        };
        if matches!(state, 'Z' | 'X' | 'x') {
            break;
        }
        assert!(
            Instant::now() < stopped,
            "detached control is still running"
        );
        std::thread::sleep(Duration::from_millis(5));
    }
}

#[test]
fn read_regular_refuses_links_fifos_and_oversize() {
    let root = scratch("read");
    let file = root.join("file");
    std::fs::write(&file, b"12345").unwrap();
    let mut ok = || Ok(());
    assert_eq!(read_regular(&file, 5, &mut ok).unwrap(), b"12345");
    let (status, reason) = failure(read_regular(&file, 4, &mut ok).unwrap_err());
    assert_eq!(
        (status, reason.as_str()),
        (Status::ResourceOut, "Declared byte limit exceeded")
    );
    std::os::unix::fs::symlink(&file, root.join("link")).unwrap();
    assert!(matches!(
        read_regular(&root.join("link"), 5, &mut ok),
        Err(Fault::OsAt(..))
    ));
    assert!(
        std::process::Command::new("mkfifo")
            .arg(root.join("fifo"))
            .status()
            .unwrap()
            .success()
    );
    let (status, reason) = failure(read_regular(&root.join("fifo"), 5, &mut ok).unwrap_err());
    assert_eq!(
        (status, reason.as_str()),
        (Status::Error, "A required artifact is not a regular file")
    );
}

#[test]
fn snapshot_changes_are_detected() {
    let root = scratch("snapshot");
    let snapshot = Snapshot::create(&root.join("input.p"), b"cnf(a, axiom, p).").unwrap();
    let mut ok = || Ok(());
    snapshot.verify(&mut ok).unwrap();
    use std::os::unix::fs::PermissionsExt;
    assert_eq!(
        std::fs::metadata(snapshot.argument())
            .unwrap()
            .permissions()
            .mode()
            & 0o777,
        0o400
    );
    std::fs::set_permissions(snapshot.argument(), std::fs::Permissions::from_mode(0o600)).unwrap();
    std::fs::write(snapshot.argument(), b"cnf(a, axiom, q).").unwrap();
    let (status, reason) = failure(snapshot.verify(&mut ok).unwrap_err());
    assert_eq!(
        (status, reason.as_str()),
        (Status::Error, "Captured disk artifact changed")
    );
}

#[test]
fn stdin_from_a_file_and_working_directory() {
    let root = scratch("stdin");
    let input = root.join("input");
    std::fs::write(&input, b"from stdin").unwrap();
    let mut supervisor = Supervisor::new(Limits::default(), None).unwrap();
    let command = shell("cat; pwd >&2");
    let directory = root.join("cat");
    let mut spec = stage("cat", &command, &directory, &root);
    spec.stdin = Some(&input);
    spec.cwd = Some(&root);
    let output = supervisor.run(&spec).unwrap();
    assert_eq!(output.stdout, b"from stdin");
    assert_eq!(
        String::from_utf8(output.stderr).unwrap().trim(),
        root.canonicalize().unwrap().to_str().unwrap()
    );
}

#[test]
fn positive_lines_need_a_clean_check() {
    let mut supervisor = Supervisor::new(Limits::default(), None).unwrap();
    let clean = supervisor.confirm_clean("output", &[]).unwrap();
    assert_eq!(
        fang_supervisor::positive_status_line(clean, "Unsatisfiable", "SYN000-1").as_deref(),
        Some("% SZS status Unsatisfiable for SYN000-1")
    );
    let clean = supervisor.confirm_clean("output", &[]).unwrap();
    assert_eq!(
        fang_supervisor::positive_status_line(clean, "GaveUp", "SYN000-1"),
        None
    );
}

#[test]
fn limits_record_matches_asdict() {
    assert_eq!(
        fang_json::dumps_manifest(&Limits::default().to_json()).unwrap(),
        concat!(
            "{\n  \"artifact_bytes\": 268435456,\n  \"certificate_bytes\": 67108864,\n  \"input_bytes\": 1048576,\n",
            "  \"log_bytes\": 4194304,\n  \"memory_mib\": 2048,\n  \"poll_seconds\": 0.02,\n  \"wall_seconds\": 60.0\n}"
        )
    );
}

#[test]
fn strict_json_refuses_duplicates_and_nonfinite_numbers() {
    // ProtocolTests.test_strict_json_duplicate and test_strict_json_nonfinite: ValueError with
    // the texts of supervisor.strict_json.
    for (text, expected) in [
        (&b"{\"a\":1,\"a\":2}"[..], "Duplicate JSON field"),
        (b"{\"a\":NaN}", "Nonfinite JSON number"),
        (b"{\"a\":-Infinity}", "Nonfinite JSON number"),
    ] {
        match fang_supervisor::strict_json(text) {
            Err(Fault::Value(message)) => assert_eq!(message, expected),
            other => panic!("expected a ValueError, got {other:?}"),
        }
    }
    assert!(fang_supervisor::strict_json(b"{\"a\": [1, 2.5, \"x\"]}").is_ok());
}

#[test]
fn sealed_snapshot_cannot_be_written() {
    // ProtocolTests.test_sealed_snapshot_cannot_be_written: Python's sealed memfd refused the
    // write; the 0400 copy refuses an opening for writing, and verify still holds.
    let root = scratch("sealed");
    let snapshot = Snapshot::create(&root.join("input.p"), b"cnf(a, axiom, p).").unwrap();
    let error = std::fs::OpenOptions::new()
        .write(true)
        .open(snapshot.argument())
        .unwrap_err();
    assert_eq!(error.kind(), std::io::ErrorKind::PermissionDenied);
    snapshot.verify(&mut || Ok(())).unwrap();
}
