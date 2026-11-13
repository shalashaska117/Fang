// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The guard pattern end to end. This test binary is also the guarded program: with
//! FANG_GUARD_TEST_DIRECTORY set it runs as one (outer, then worker); without it, it starts
//! itself, signals the outer process, and checks what is left.
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use fang_supervisor::guard::{self, Role};
use fang_supervisor::{Limits, Stage, Supervisor};

const DIRECTORY: &str = "FANG_GUARD_TEST_DIRECTORY";
const PROBE: &str = "FANG_DESCRIPTOR_PROBE";

fn program(directory: PathBuf) {
    let worker = match guard::start().expect("guard start") {
        Role::Outer => guard::run_outer(),
        Role::Worker(worker) => worker,
    };
    let mut supervisor = Supervisor::new(
        Limits {
            wall_seconds: 120.0,
            ..Limits::default()
        },
        None,
    )
    .unwrap();
    supervisor.set_cancel_token(worker.cancel_token());
    let record = directory.join("forced");
    let shares = worker.shares_caller_stdout();
    worker.on_parent_death(move || {
        std::fs::write(&record, "Forced").unwrap();
        if shares {
            println!("% SZS status Forced for guard-test");
        }
    });
    std::fs::write(directory.join("worker-pid"), std::process::id().to_string()).unwrap();
    let command: Vec<OsString> = vec!["/bin/sh".into(), "-c".into(), "sleep 120".into()];
    let stage_directory = directory.join("stage");
    let _ = supervisor.run(&Stage {
        name: "sleep",
        command: &command,
        directory: &stage_directory,
        run_root: &directory,
        environment: None,
        stdin: None,
        stdout_limit: None,
        cwd: None,
    });
    if worker
        .finalize(|| std::fs::write(directory.join("finalized"), "main path"))
        .is_none()
    {
        std::thread::sleep(Duration::from_secs(5));
    }
}

fn wait_for(path: &Path) {
    let limit = Instant::now() + Duration::from_secs(10);
    while !path.exists() {
        assert!(Instant::now() < limit, "{} did not appear", path.display());
        std::thread::sleep(Duration::from_millis(20));
    }
}

fn group_members(group: i32) -> Vec<i32> {
    let mut members = Vec::new();
    for entry in std::fs::read_dir("/proc").unwrap().flatten() {
        let Ok(pid) = entry.file_name().to_string_lossy().parse::<i32>() else {
            continue;
        };
        let Ok(text) = std::fs::read_to_string(format!("/proc/{pid}/stat")) else {
            continue;
        };
        let fields: Vec<&str> = text[text.rfind(')').unwrap() + 2..]
            .split_whitespace()
            .collect();
        if fields[2].parse::<i32>() == Ok(group) && fields[0] != "Z" {
            members.push(pid);
        }
    }
    members
}

fn control(signal: &str, expected_status: i32) {
    let directory =
        std::env::temp_dir().join(format!("fang-guard-test-{}-{signal}", std::process::id()));
    let _ = std::fs::remove_dir_all(&directory);
    std::fs::create_dir(&directory).unwrap();
    let mut outer = Command::new(std::env::current_exe().unwrap())
        .env(DIRECTORY, &directory)
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    wait_for(&directory.join("worker-pid"));
    wait_for(&directory.join("stage").join("stdout"));
    std::thread::sleep(Duration::from_millis(300));
    let worker: i32 = std::fs::read_to_string(directory.join("worker-pid"))
        .unwrap()
        .trim()
        .parse()
        .unwrap();
    assert!(
        group_members(worker).len() >= 2,
        "the stage child runs in the worker's group"
    );
    assert!(
        Command::new("/bin/kill")
            .args(["-s", signal, &outer.id().to_string()])
            .status()
            .unwrap()
            .success()
    );
    let status = outer.wait().unwrap();
    use std::os::unix::process::ExitStatusExt;
    assert_eq!(
        status.signal(),
        Some(expected_status - 128),
        "{signal}: outer status {status:?}"
    );
    let limit = Instant::now() + Duration::from_secs(2);
    while !group_members(worker).is_empty() {
        assert!(
            Instant::now() < limit,
            "{signal}: the worker's group survived: {:?}",
            group_members(worker)
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    assert_eq!(
        std::fs::read_to_string(directory.join("forced")).unwrap(),
        "Forced"
    );
    assert!(!directory.join("finalized").exists());
    let mut output = String::new();
    use std::io::Read;
    outer
        .stdout
        .take()
        .unwrap()
        .read_to_string(&mut output)
        .unwrap();
    assert_eq!(
        output.matches("% SZS status Forced for guard-test").count(),
        1,
        "{signal}: {output:?}"
    );
    println!("guard control {signal}: passed");
}

/// Inherited descriptors: a shell opens descriptor 9 without close-on-exec and execs this binary,
/// which must list it with its target, both from inherited_descriptors() and in Supervisor::new.
fn descriptors() {
    let directory =
        std::env::temp_dir().join(format!("fang-descriptor-test-{}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    let file = directory.join("held");
    std::fs::write(&file, "held\n").unwrap();
    let expected = format!("9 {}", file.canonicalize().unwrap().display());
    let output = Command::new("/bin/sh")
        .args([
            "-c",
            "exec 9<\"$1\"; exec \"$0\"",
            std::env::current_exe().unwrap().to_str().unwrap(),
            file.to_str().unwrap(),
        ])
        .env(PROBE, "1")
        .output()
        .unwrap();
    let _ = std::fs::remove_dir_all(&directory);
    assert!(output.status.success(), "{output:?}");
    let text = String::from_utf8(output.stdout).unwrap();
    let lines: Vec<&str> = text.lines().collect();
    assert!(lines.contains(&expected.as_str()), "{text}");
    assert!(
        lines.iter().all(|line| !line.starts_with("0 ")
            && !line.starts_with("1 ")
            && !line.starts_with("2 ")),
        "{text}"
    );
    println!("guard control descriptors: passed");
}

fn probe() {
    let found = fang_supervisor::inherited_descriptors();
    let supervisor = Supervisor::new(Limits::default(), None).unwrap();
    assert_eq!(supervisor.inherited_descriptors, found);
    for descriptor in found {
        println!("{} {}", descriptor.fd, descriptor.target);
    }
}

fn main() {
    if std::env::var_os(PROBE).is_some() {
        probe();
        return;
    }
    if let Some(directory) = std::env::var_os(DIRECTORY) {
        program(PathBuf::from(directory));
        return;
    }
    descriptors();
    // SIGINT is left out: a shell that starts a job in the background makes it ignore SIGINT,
    // and the test may run under one. The worker handles every death of its parent the same way.
    control("TERM", 143);
    control("KILL", 137);
}
