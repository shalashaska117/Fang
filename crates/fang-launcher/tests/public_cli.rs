// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Public help and automatic artifact controls of the older profiles' shared arguments, and the artifact notice
//! of every profile; no proof runs. Port of tools/tests/test_public_cli.py. The launcher has only the public
//! command, so the Python controls of the non-public entry have no counterpart. A UUID collision is checked
//! through an explicit existing directory, which takes the same refusal.

use std::fs;
use std::io::Write;
use std::path::{Component, Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use fang_launcher::older::cli::{self, Parse};

/// (ground-FOF byte cap, configuration option, certificate byte default, profile name)
const VARIANTS: [(Option<i64>, &str, i64, &str); 2] = [
    (None, "--installation", 64 << 20, "cnf"),
    (Some(1 << 20), "--capability", 1 << 20, "ground-fof"),
];

fn strings(items: &[&str]) -> Vec<String> {
    items.iter().map(|item| item.to_string()).collect()
}

fn parse(items: &[&str], cap: Option<i64>) -> Parse {
    cli::arguments(&strings(items), cap).expect("no I/O failure")
}

fn run(items: &[&str], cap: Option<i64>) -> cli::Arguments {
    match parse(items, cap) {
        Parse::Run(arguments) => arguments,
        Parse::Help(_) => panic!("help for {items:?}"),
        Parse::Error(message) => panic!("{items:?}: {message}"),
    }
}

fn refused(items: &[&str], cap: Option<i64>) -> String {
    match parse(items, cap) {
        Parse::Error(message) => message,
        _ => panic!("accepted {items:?}"),
    }
}

#[test]
fn public_execution_still_requires_launcher_configuration() {
    for (cap, option, _, _) in VARIANTS {
        let message = refused(&["input.p"], cap);
        assert_eq!(
            message,
            format!(
                "Invalid adapter arguments: {option} must be supplied by the installed launcher or explicitly"
            )
        );
    }
}

#[test]
fn defaults_preserve_both_adapter_contracts() {
    for (cap, option, certificate, _) in VARIANTS {
        let args = run(
            &["input.p", option, "config.json", "--artifacts", "run"],
            cap,
        );
        assert_eq!(
            (args.check.as_str(), args.output.as_str()),
            ("kernel", "status")
        );
        assert_eq!((args.wall(), args.memory_mib), (60.0, 2048));
        assert_eq!(
            (args.max_steps, args.max_clauses, args.max_operations),
            (100_000, 1_000, 5_000_000)
        );
        assert_eq!(
            (args.max_input_bytes, args.max_certificate_bytes),
            (1 << 20, certificate)
        );
        assert_eq!(
            (
                args.max_solution_bytes,
                args.max_log_bytes,
                args.max_artifact_bytes
            ),
            (16 << 20, 4 << 20, 256 << 20)
        );
        assert!(!args.auto_artifacts);
        assert_eq!(args.configuration, PathBuf::from("config.json"));
    }
}

#[test]
fn public_paths_are_unique_without_creating_directories() {
    let runs = std::env::current_dir().unwrap().join(".local").join("runs");
    let mut paths = Vec::new();
    for (cap, option, _, _) in VARIANTS {
        for _ in 0..2 {
            let args = run(&["input.p", option, "config.json"], cap);
            assert!(args.auto_artifacts);
            assert_eq!(args.artifacts.parent(), Some(runs.as_path()));
            let name = args
                .artifacts
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .to_string();
            assert!(
                name.len() == 32
                    && name
                        .bytes()
                        .all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f')),
                "{name}"
            );
            assert!(!args.artifacts.exists());
            paths.push(args.artifacts);
        }
    }
    paths.sort();
    paths.dedup();
    assert_eq!(paths.len(), 4);
}

#[test]
fn public_explicit_artifacts_are_preserved() {
    for (cap, option, _, _) in VARIANTS {
        let args = run(
            &["input.p", option, "config.json", "--artifacts", "my run"],
            cap,
        );
        assert_eq!(args.artifacts, PathBuf::from("my run"));
        assert!(!args.auto_artifacts);
    }
}

#[test]
fn invalid_limits_are_refused() {
    let large = (1u128 << 63).to_string();
    let mut bad: Vec<(String, String)> = [
        ("--wall-seconds", "nan"),
        ("--wall-seconds", "inf"),
        ("--wall-seconds", "0.24"),
        ("--wall-seconds", "86401"),
        ("--memory-mib", "15"),
        ("--memory-mib", "1048577"),
        ("--max-solution-bytes", "16777217"),
        ("--check", "unchecked"),
        ("--output", "sat"),
    ]
    .iter()
    .map(|(flag, value)| (flag.to_string(), value.to_string()))
    .collect();
    for name in [
        "steps",
        "clauses",
        "operations",
        "input-bytes",
        "certificate-bytes",
        "log-bytes",
        "artifact-bytes",
    ] {
        bad.push((format!("--max-{name}"), "-1".to_string()));
        bad.push((format!("--max-{name}"), large.clone()));
    }
    for (cap, option, _, _) in VARIANTS {
        for (flag, value) in &bad {
            let message = refused(&["input.p", option, "config.json", flag, value], cap);
            assert!(
                message.starts_with("Invalid adapter arguments: "),
                "{flag} {value}: {message}"
            );
        }
    }
    // A value beyond 64 bits is refused by the range check, as Python's unbounded int is.
    assert_eq!(
        refused(
            &[
                "input.p",
                "--installation",
                "config.json",
                "--max-steps",
                &large
            ],
            None
        ),
        "Invalid adapter arguments: max_steps is outside the supported nonnegative range"
    );
    assert_eq!(
        refused(
            &[
                "input.p",
                "--capability",
                "config.json",
                "--max-steps",
                &large
            ],
            Some(1 << 20)
        ),
        "Invalid adapter arguments: Invalid nonnegative limit: steps"
    );
}

#[test]
fn fof_byte_caps_remain_distinct_from_cnf() {
    let over = ((1 << 20) + 1).to_string();
    for flag in ["--max-input-bytes", "--max-certificate-bytes"] {
        let message = refused(
            &["input.p", "--capability", "config.json", flag, &over],
            Some(1 << 20),
        );
        assert!(message.contains("at most 1 MiB"), "{message}");
        let args = run(
            &["input.p", "--installation", "config.json", flag, &over],
            None,
        );
        let value = if flag == "--max-input-bytes" {
            args.max_input_bytes
        } else {
            args.max_certificate_bytes
        };
        assert_eq!(value, (1 << 20) + 1);
    }
}

#[test]
fn help_and_alias_explain_all_flags() {
    for (cap, option, _, _) in VARIANTS {
        let texts: Vec<String> = [&["help"][..], &["--help"]]
            .iter()
            .map(|items| match parse(items, cap) {
                Parse::Help(text) => text,
                _ => panic!("no help for {items:?}"),
            })
            .collect();
        assert_eq!(texts[0], texts[1]);
        let text = &texts[0];
        assert!(text.starts_with("usage: fang "));
        for flag in [
            option,
            "--help",
            "--artifacts",
            "--check",
            "--output",
            "--wall-seconds",
            "--memory-mib",
            "--max-steps",
            "--max-clauses",
            "--max-operations",
            "--max-input-bytes",
            "--max-certificate-bytes",
            "--max-solution-bytes",
            "--max-log-bytes",
            "--max-artifact-bytes",
        ] {
            assert!(text.contains(flag), "{flag}");
        }
        let normalized = text.split_whitespace().collect::<Vec<_>>().join(" ");
        for description in [
            "no SAT result",
            "default: kernel",
            "default: status",
            "seconds",
            "MiB",
            "bytes",
            "current directory",
            "compiled checker",
            "fresh exact-input Lean proof",
        ] {
            assert!(normalized.contains(description), "{description}");
        }
    }
}

#[test]
fn help_filename_is_not_a_broad_alias() {
    for (cap, option, _, _) in VARIANTS {
        for input in ["help", "./help"] {
            let args = run(&[input, option, "config.json", "--artifacts", "run"], cap);
            let parts: Vec<Component> = args
                .input
                .components()
                .filter(|part| *part != Component::CurDir)
                .collect();
            assert_eq!(parts, [Component::Normal("help".as_ref())]);
        }
    }
}

// The command itself: the artifact notice, its failures, and an existing directory.

fn launcher() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_fang-launcher"))
}

struct Directory(PathBuf);

impl Directory {
    fn new() -> Directory {
        static COUNT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "fang-public-cli-{}-{}",
            std::process::id(),
            COUNT.fetch_add(1, Ordering::SeqCst)
        ));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).unwrap();
        fs::write(path.join("input.p"), b"cnf(a,axiom,($false)).").unwrap();
        Directory(path)
    }
}

impl Drop for Directory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// The command line of `profile` with a configuration file that does not exist, so the run stops with Error
/// after its run directory and first record exist and the notice is given, before any stage.
fn profile_command(directory: &Path, profile: &str, extra: &[&str]) -> Command {
    let mut command = Command::new(launcher());
    command.current_dir(directory).stdin(Stdio::null());
    if profile != "v8" {
        command.args(["--profile", profile]);
    }
    let option = if profile == "cnf" {
        "--installation"
    } else {
        "--capability"
    };
    command
        .args(["input.p", option, "missing-configuration.json"])
        .args(extra);
    command
}

const PROFILES: [&str; 3] = ["v8", "cnf", "ground-fof"];

fn record(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

fn pending_status_of(path: &Path) -> Option<String> {
    let value =
        fang_json::parse(record(path).as_bytes(), &fang_json::ParseLimits::default()).unwrap();
    value
        .get("status")
        .and_then(|status| status.as_str())
        .map(str::to_string)
}

fn status_of(path: &Path) -> String {
    pending_status_of(path).expect("completed run has a status")
}

fn automatic_runs(directory: &Path) -> Vec<PathBuf> {
    match fs::read_dir(directory.join(".local/runs")) {
        Ok(entries) => entries.map(|entry| entry.unwrap().path()).collect(),
        Err(_) => Vec::new(),
    }
}

#[test]
fn main_creates_and_announces_only_automatic_runs() {
    for profile in PROFILES {
        let directory = Directory::new();
        let output: Output = profile_command(&directory.0, profile, &[])
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        let runs = automatic_runs(&directory.0);
        assert_eq!(runs.len(), 1, "{profile}: {stderr}");
        assert_eq!(
            stderr,
            format!("Fang artifacts: {}\n", runs[0].display()),
            "{profile}"
        );
        assert_eq!(
            status_of(&runs[0].join("manifest.json")),
            "Error",
            "{profile}"
        );
        assert!(
            String::from_utf8_lossy(&output.stdout).contains("% SZS status Error for "),
            "{profile}"
        );
        let explicit = directory.0.join("explicit-run");
        let output = profile_command(
            &directory.0,
            profile,
            &["--artifacts", explicit.to_str().unwrap()],
        )
        .output()
        .unwrap();
        assert_eq!(String::from_utf8_lossy(&output.stderr), "", "{profile}");
        assert_eq!(
            status_of(&explicit.join("manifest.json")),
            "Error",
            "{profile}"
        );
        assert_eq!(automatic_runs(&directory.0).len(), 1, "{profile}");
    }
}

#[test]
fn closed_standard_error_stops_the_run_with_error() {
    for profile in PROFILES {
        let directory = Directory::new();
        let (reader, writer) = std::io::pipe().unwrap();
        drop(reader);
        let output = profile_command(&directory.0, profile, &[])
            .stderr(writer)
            .output()
            .unwrap();
        let runs = automatic_runs(&directory.0);
        assert_eq!(runs.len(), 1, "{profile}");
        assert_eq!(
            status_of(&runs[0].join("manifest.json")),
            "Error",
            "{profile}"
        );
        let stage = record(&runs[0].join("manifest.json"));
        assert!(
            stage.contains("\"stage\": \"adapter\""),
            "{profile}: {stage}"
        );
        assert!(
            String::from_utf8_lossy(&output.stdout).contains("% SZS status Error for "),
            "{profile}"
        );
        let names: Vec<String> = fs::read_dir(&runs[0])
            .unwrap()
            .map(|entry| entry.unwrap().file_name().into_string().unwrap())
            .collect();
        assert_eq!(names, ["manifest.json"], "{profile}");
    }
}

/// A standard error that accepts nothing: a pipe whose buffer a thread has filled and that nobody reads.
fn full_pipe() -> (std::io::PipeReader, std::io::PipeWriter) {
    let (reader, writer) = std::io::pipe().unwrap();
    let mut filler = writer.try_clone().unwrap();
    std::thread::spawn(move || {
        let block = [b'x'; 4096];
        loop {
            if filler.write_all(&block).is_err() {
                return;
            }
        }
    });
    std::thread::sleep(Duration::from_millis(300));
    (reader, writer)
}

fn wait(mut child: Child, limit: Duration) -> std::process::ExitStatus {
    let deadline = Instant::now() + limit;
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            return status;
        }
        if Instant::now() > deadline {
            let _ = child.kill();
            panic!("the command did not stop");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

#[test]
fn unaccepted_notice_stops_the_run_with_timeout() {
    for profile in PROFILES {
        let directory = Directory::new();
        let (_reader, writer) = full_pipe();
        let child = profile_command(&directory.0, profile, &["--wall-seconds", "1"])
            .stdout(Stdio::null())
            .stderr(writer)
            .spawn()
            .unwrap();
        let status = wait(child, Duration::from_secs(30));
        assert_eq!(status.code(), Some(7), "{profile}");
        let runs = automatic_runs(&directory.0);
        assert_eq!(
            status_of(&runs[0].join("manifest.json")),
            "Timeout",
            "{profile}"
        );
        assert!(
            record(&runs[0].join("manifest.json")).contains("artifact-output"),
            "{profile}"
        );
    }
}

#[test]
fn termination_during_the_notice_is_forced() {
    for profile in PROFILES {
        let directory = Directory::new();
        let (_reader, writer) = full_pipe();
        let child = profile_command(&directory.0, profile, &[])
            .stdout(Stdio::null())
            .stderr(writer)
            .spawn()
            .unwrap();
        let started = Instant::now();
        while automatic_runs(&directory.0).is_empty()
            || !automatic_runs(&directory.0)[0]
                .join("manifest.json")
                .exists()
        {
            assert!(
                started.elapsed() < Duration::from_secs(20),
                "{profile}: no run directory"
            );
            std::thread::sleep(Duration::from_millis(20));
        }
        std::thread::sleep(Duration::from_millis(200));
        let killed = Command::new("kill")
            .arg("-TERM")
            .arg(child.id().to_string())
            .status()
            .unwrap();
        assert!(killed.success());
        let status = wait(child, Duration::from_secs(20));
        assert_eq!(status.code(), None, "{profile}");
        let path = automatic_runs(&directory.0)[0].join("manifest.json");
        let deadline = Instant::now() + Duration::from_secs(10);
        // The outer process can stop before the worker replaces its initial record with Forced.
        while pending_status_of(&path).as_deref() != Some("Forced") {
            assert!(Instant::now() < deadline, "{profile}: {}", record(&path));
            std::thread::sleep(Duration::from_millis(50));
        }
    }
}

#[test]
fn existing_run_directory_is_never_overwritten() {
    for profile in PROFILES {
        let directory = Directory::new();
        let existing = directory.0.join("existing");
        fs::create_dir(&existing).unwrap();
        fs::write(existing.join("manifest.json"), b"original bytes").unwrap();
        let output = profile_command(
            &directory.0,
            profile,
            &["--artifacts", existing.to_str().unwrap()],
        )
        .output()
        .unwrap();
        assert_eq!(output.status.code(), Some(6), "{profile}");
        assert_eq!(
            fs::read(existing.join("manifest.json")).unwrap(),
            b"original bytes"
        );
        assert_eq!(String::from_utf8_lossy(&output.stderr), "", "{profile}");
        assert!(
            String::from_utf8_lossy(&output.stdout).contains("% SZS status Error for "),
            "{profile}"
        );
    }
}
