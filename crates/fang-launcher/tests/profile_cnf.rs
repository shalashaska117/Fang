// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The CNF profile end to end on synthetic binaries: ports of tools/tests/test_fang_szs.py `ProcessTests` and
//! tools/tests/test_tstp_adapter.py, each test named after the Python test it replaces without its `test_`
//! prefix, plus the checks of the version-3 installation that replace `InstallationTests`. The engine, checker,
//! Lean and exporter are shell scripts that follow each contract; these are contract controls, not proof
//! acceptance evidence.
//!
//! Where the Python control observed something the launcher does differently by design, the test says so: the
//! captured input is a 0400 file instead of a sealed memfd, a signal ends the outer process (status 143) while
//! the worker records Forced, and the kernel profile is exercised with a synthetic Lean instead of a mocked
//! replay function.
//!
//! The deadline is 30 s where the Python controls used 3 s and the deadline is not what a test checks: every run
//! hashes the launcher binary before and after, and a debug build's SHA-256 under parallel tests can spend 3 s.

use std::collections::BTreeMap;
use std::fs;
use std::io::Read;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use fang_json::{Object, ParseLimits, Value};
use fang_launcher::capability::{Pin, Record};
use fang_launcher::profile_cnf::installation::{self, CnfInputs, Library};
use fang_launcher::profile_cnf::protocol;

const INPUT: &[u8] = b"cnf(a,axiom,(p)).cnf(b,axiom,(~p)).\n";
const PROOF: &[u8] =
    b"(fang-proof 1 (input 0 0) (input 1 1) (resolve 2 0 0 1 0 (subst) (clause)) (final 2))\n";
const SOLUTION: &[u8] = b"cnf('a',axiom,(p),file('input.p','a')).\n\
cnf('b',axiom,(~p),file('input.p','b')).\n\
cnf('fang:step:2',plain,($false),inference(fang_resolution,[status(thm)],[a,b])).\n";
const LAST_ROW: &[u8] =
    b"cnf('fang:step:2',plain,($false),inference(fang_resolution,[status(thm)],[a,b])).\n";

/// The engine, checker and Lean stand-in; `MODE` is replaced per test and `ROOT` by the fixture directory.
const FAKE: &str = r#"#!/bin/bash
mode=MODE
role=$(basename "$0")
if [ "$role" = engine ]; then
  case "$mode" in
    timeout-search) sleep 5 ;;
    memory-search) hold=$(head -c 83886080 /dev/zero | tr '\0' x); sleep 5 ;;
    logs) head -c 20000 /dev/zero | tr '\0' x; echo; sleep 5 ;;
    sparse-log) truncate -s 1099511627776 /dev/stdout; sleep 5 ;;
    fifo-log) rm stdout; mkfifo stdout; exit 0 ;;
    orphan) sleep 5 & echo $! > child.pid
      echo unknown; echo 'queue exhausted after 0 clauses and 0 inference attempts' >&2; exit 2 ;;
    signal) kill -KILL $$ ;;
    panic) echo 'ResourceLimit: forged' >&2; exit 101 ;;
    unknown|empty) echo unknown; echo 'queue exhausted after 1 clauses and 0 inference attempts' >&2; exit 2 ;;
    duplicate) echo 'InvalidInput at byte 12: duplicate clause name' >&2; exit 3 ;;
    arity) echo 'InvalidInput at byte 12: inconsistent symbol arity' >&2; exit 3 ;;
    unsupported) echo 'Unsupported at byte 0: only cnf statements are supported' >&2; exit 4 ;;
    uppercase) echo 'InvalidInput at byte 3: uppercase character in a lowercase identifier' >&2; exit 3 ;;
    ascii) echo 'InvalidInput at byte 3: input must contain ASCII bytes only' >&2; exit 3 ;;
    syntax) echo 'InvalidInput at byte 3: expected a term' >&2; exit 3 ;;
    resource) echo 'ResourceLimit: operation budget exhausted' >&2; exit 5 ;;
    invalid-internal) echo 'InvalidInput: bad parent' >&2; exit 3 ;;
    mutate-input) chmod 600 ../input.p; printf different > ../input.p ;;
    cancel-search) echo ready > ready; sleep 5 ;;
  esac
  if [ "$mode" != missing-proof ]; then
    previous=
    for argument in "$@"; do
      [ "$previous" = --proof ] && cat ROOT/proof.fang > "$argument"
      previous=$argument
    done
  fi
  echo candidate-refutation
  echo '3 recorded search nodes; serialized proof keeps only refutation dependencies; independent checking required' >&2
  if [ "$mode" = spoof ]; then echo '% SZS status Unsatisfiable for forged'; fi
  exit 0
elif [ "$role" = checker ]; then
  if [ "$1" = --emit-replay ]; then cat ROOT/replay.lean; exit 0; fi
  case "$mode" in
    timeout-checker|cancel-checker) echo ready > ready; sleep 5 ;;
    reject) echo rejected-certificate >&2; exit 1 ;;
    wrong-source) echo 'invalid-input: mismatch' >&2; exit 2 ;;
    mutate-proof) chmod 600 ../proof.fang; printf different > ../proof.fang ;;
  esac
  echo 'accepted-refutation (compiled checker; no per-instance kernel replay performed)'
  if [ "$mode" = checker-spoof ]; then echo '% SZS status Unsatisfiable for forged'; fi
  exit 0
elif [ "$role" = lean ]; then
  output=; previous=; source=
  for argument in "$@"; do [ "$previous" = -o ] && output=$argument; previous=$argument; source=$argument; done
  name=$(basename "$source" .lean)
  if [ "$mode" = lean-fails ] && [ "$name" = CertificateTokens ]; then echo 'error: synthetic failure' >&2; exit 1; fi
  echo "$name" > "$output"
  if [ "$name" = Audit ]; then
    for theorem in exact_original_bytes_unsat exact_source_decodes exact_certificate_decodes exact_checker_acceptance; do
      echo "'$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]"
    done
  fi
  exit 0
fi
exit 7
"#;

/// The exporter stand-in: it checks the captured pair and its label, then runs `BODY`.
const EXPORTER: &str = r#"#!/bin/bash
cmp -s "$1" ROOT/expected-input.p || exit 90
cmp -s "$2" ROOT/proof.fang || exit 91
[ "$3" = input.p ] || exit 92
[ "$(stat -c %a "$1")" = 400 ] && [ "$(stat -c %a "$2")" = 400 ] || exit 93
BODY
"#;

fn launcher() -> PathBuf {
    fs::canonicalize(env!("CARGO_BIN_EXE_fang-launcher")).unwrap()
}

fn binary_pin(path: &Path) -> Pin {
    let bytes = fs::read(path).unwrap();
    Pin {
        path: path.to_path_buf(),
        sha256: fang_hash::sha256_hex(&bytes),
        chunked_sha256: Some(fang_hash::chunked_text(&fang_hash::chunked_digest(&bytes))),
    }
}

fn record(path: &Path) -> Record {
    Record {
        path: path.to_path_buf(),
        sha256: fang_hash::sha256_hex(&fs::read(path).unwrap()),
    }
}

fn parse(bytes: &[u8]) -> Value {
    fang_json::parse(bytes, &ParseLimits::default()).unwrap()
}

fn text(value: &Value, key: &str) -> String {
    value
        .get(key)
        .and_then(Value::as_str)
        .unwrap_or_default()
        .to_string()
}

fn stages(manifest: &Value) -> Vec<String> {
    manifest
        .get("processes")
        .and_then(Value::as_array)
        .map(|records| records.iter().map(|record| text(record, "stage")).collect())
        .unwrap_or_default()
}

struct Outcome {
    status: ExitStatus,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

/// Wait for a started command with a deadline, reading both streams to their end.
fn finish(mut child: Child, timeout: Duration) -> Outcome {
    let mut stdout = child.stdout.take();
    let mut stderr = child.stderr.take();
    let out = std::thread::spawn(move || {
        let mut data = Vec::new();
        if let Some(stream) = stdout.as_mut() {
            let _ = stream.read_to_end(&mut data);
        }
        data
    });
    let err = std::thread::spawn(move || {
        let mut data = Vec::new();
        if let Some(stream) = stderr.as_mut() {
            let _ = stream.read_to_end(&mut data);
        }
        data
    });
    let deadline = Instant::now() + timeout;
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() > deadline {
            let _ = child.kill();
            panic!("the command did not finish within {timeout:?}");
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    Outcome {
        status,
        stdout: out.join().unwrap(),
        stderr: err.join().unwrap(),
    }
}

/// One test's synthetic installation. Drop removes the directory, whether the test passed or not.
struct Fixture {
    root: PathBuf,
    installation: PathBuf,
    input: PathBuf,
    output: PathBuf,
    exporter: bool,
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = Command::new("chmod")
            .args(["-R", "u+w"])
            .arg(&self.root)
            .status();
        let _ = fs::remove_dir_all(&self.root);
    }
}

impl Fixture {
    fn new(exporter: bool) -> Fixture {
        let root =
            fang_supervisor::make_temp_dir(Path::new("/var/tmp"), "fang-adapter-control-").unwrap();
        fs::create_dir_all(root.join("library/Fang")).unwrap();
        for name in ["FrontendSoundness", "CertificateInput"] {
            fs::write(
                root.join(format!("library/Fang/{name}.olean")),
                b"synthetic",
            )
            .unwrap();
        }
        fs::write(root.join("proof.fang"), PROOF).unwrap();
        fs::write(root.join("expected-input.p"), INPUT).unwrap();
        fs::write(
            root.join("provenance.json"),
            br#"{"scope":"synthetic protocol controls only"}"#,
        )
        .unwrap();
        let input = root.join("source with\nnewline.p");
        fs::write(&input, INPUT).unwrap();
        let fixture = Fixture {
            installation: root.join("installation.json"),
            output: root.join("run"),
            input,
            root,
            exporter,
        };
        fixture.set_mode("candidate");
        fixture.set_exporter(
            &format!("cat {}/solution.bin", fixture.root.display()),
            SOLUTION,
        );
        fixture.configure(None);
        fixture
    }

    fn script(&self, path: &Path, text: &str) {
        let _ = fs::remove_file(path);
        fs::write(path, text.replace("ROOT", &self.root.display().to_string())).unwrap();
        fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
    }

    /// Bake `mode` into the engine, checker and Lean, as the Python control rewrote them.
    fn set_mode(&self, mode: &str) {
        for name in ["engine", "checker", "lean"] {
            self.script(&self.root.join(name), &FAKE.replace("MODE", mode));
        }
    }

    /// The exporter runs `body`; `solution` is what `cat ROOT/solution.bin` prints.
    fn set_exporter(&self, body: &str, solution: &[u8]) {
        fs::write(self.root.join("solution.bin"), solution).unwrap();
        self.script(&self.root.join("exporter"), &EXPORTER.replace("BODY", body));
    }

    /// Write the installation file from the current binaries, with the launcher pin given or the test binary.
    fn configure(&self, launcher_pin: Option<Pin>) -> Value {
        let mut files = BTreeMap::new();
        for name in ["FrontendSoundness", "CertificateInput"] {
            files.insert(
                format!("Fang/{name}.olean"),
                fang_hash::sha256_hex(b"synthetic"),
            );
        }
        let sources = BTreeMap::from([
            ("lean/TstpExport.lean".to_string(), "1".repeat(64)),
            ("lean/TstpMain.lean".to_string(), "2".repeat(64)),
        ]);
        let inputs = CnfInputs {
            launcher: launcher_pin.unwrap_or_else(|| binary_pin(&launcher())),
            engine: binary_pin(&self.root.join("engine")),
            checker: binary_pin(&self.root.join("checker")),
            lean: binary_pin(&self.root.join("lean")),
            exporter: self
                .exporter
                .then(|| binary_pin(&self.root.join("exporter"))),
            source_inventory: sources,
            proof_library: Library {
                path: self.root.join("library"),
                files_sha256: files,
            },
            provenance: vec![record(&self.root.join("provenance.json"))],
        };
        let config = installation::build(&inputs).unwrap();
        let mut bytes = fang_json::dumps_manifest(&config).unwrap();
        bytes.push('\n');
        fs::write(&self.installation, bytes).unwrap();
        config
    }

    /// The replay module the checker's `--emit-replay` prints, for the kernel controls.
    fn write_replay(&self) {
        let replay = format!(
            "{}def originalInput : String := {}\n\ndef originalCertificate : String := {}\n\ndef problem : Problem := []\n\ndef certificate : Certificate := Certificate.mk [] 0\n\n{}",
            protocol::HEADER,
            protocol::quote(std::str::from_utf8(INPUT).unwrap()),
            protocol::quote(std::str::from_utf8(PROOF).unwrap()),
            protocol::FOOTER
        );
        fs::write(self.root.join("replay.lean"), replay).unwrap();
    }

    fn command(&self, check: &str, output: &str, extra: &[&str]) -> Command {
        let mut command = Command::new(launcher());
        command
            .args(["--profile", "cnf"])
            .arg(&self.input)
            .arg("--installation")
            .arg(&self.installation)
            .arg("--artifacts")
            .arg(&self.output)
            .args(["--check", check, "--output", output, "--wall-seconds", "30"])
            .args(extra)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        command
    }

    fn run(&self, check: &str, output: &str, extra: &[&str]) -> Outcome {
        finish(
            self.command(check, output, extra).spawn().unwrap(),
            Duration::from_secs(40),
        )
    }

    fn manifest(&self) -> Option<Value> {
        fs::read(self.output.join("manifest.json"))
            .ok()
            .map(|bytes| parse(&bytes))
    }

    /// `ProcessTests.invoke`: the exit code, the two status lines, no forged line, an empty stderr.
    fn invoke(&self, mode: &str, expected: &str, code: i32, extra: &[&str]) -> Option<Value> {
        if mode != "candidate" {
            self.set_mode(mode);
            self.configure(None);
        }
        let outcome = self.run("compiled", "status", extra);
        let stdout = String::from_utf8_lossy(&outcome.stdout).to_string();
        assert_eq!(
            outcome.status.code(),
            Some(code),
            "{stdout} {}",
            String::from_utf8_lossy(&outcome.stderr)
        );
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(lines.len(), 2, "{stdout}");
        assert_eq!(lines[0], "% Fang checking profile: compiled");
        assert!(
            lines[1].starts_with(&format!("% SZS status {expected} for fang_")),
            "{stdout}"
        );
        assert!(!stdout.contains("forged"));
        if expected != "Unsatisfiable" {
            assert!(!stdout.contains("Unsatisfiable"));
        }
        assert_eq!(outcome.stderr, b"");
        self.manifest()
    }

    /// `TstpAdapterTests.invoke`: the status, the exit code and an empty stderr; returns the output and record.
    fn tstp(&self, expected: &str, extra: &[&str], output: &str) -> (Vec<u8>, Value) {
        let outcome = self.run("compiled", output, extra);
        assert_eq!(
            outcome.stderr,
            b"",
            "{}",
            String::from_utf8_lossy(&outcome.stderr)
        );
        let stdout = outcome.stdout;
        let status_line = format!("% SZS status {expected} for fang_");
        assert!(
            stdout
                .windows(status_line.len())
                .any(|window| window == status_line.as_bytes()),
            "{}",
            String::from_utf8_lossy(&stdout)
        );
        if expected == "Unsatisfiable" {
            assert_eq!(outcome.status.code(), Some(0));
        } else {
            assert!(!String::from_utf8_lossy(&stdout).contains("SZS status Unsatisfiable"));
            assert!(!String::from_utf8_lossy(&stdout).contains("SZS output start"));
            assert_ne!(outcome.status.code(), Some(0));
        }
        let manifest = self.manifest().unwrap();
        assert_eq!(text(&manifest, "status"), expected);
        (stdout, manifest)
    }

    fn fresh_output(&mut self, name: &str) {
        self.output = self.root.join(name);
    }
}

// ProcessTests

#[test]
fn candidate_protocol() {
    let fixture = Fixture::new(false);
    let manifest = fixture
        .invoke("candidate", "Unsatisfiable", 0, &[])
        .unwrap();
    assert_eq!(
        manifest
            .get("compiled_check")
            .and_then(|check| check.get("accepted"))
            .and_then(Value::as_bool),
        Some(true)
    );
    assert!(manifest.get("kernel_check").is_none());
    assert_eq!(fs::read(fixture.output.join("input.p")).unwrap(), INPUT);
}

macro_rules! status_controls {
    ($($name:ident: $mode:expr, $expected:expr, $code:expr, [$($extra:expr),*];)*) => {
        $(
            #[test]
            fn $name() {
                Fixture::new(false).invoke($mode, $expected, $code, &[$($extra),*]);
            }
        )*
    };
}

status_controls! {
    unknown: "unknown", "GaveUp", 2, [];
    duplicate: "duplicate", "InputError", 3, [];
    arity: "arity", "InputError", 3, [];
    unsupported: "unsupported", "Inappropriate", 4, [];
    uppercase: "uppercase", "Inappropriate", 4, [];
    nonascii_boundary: "ascii", "Inappropriate", 4, [];
    uncertain_syntax: "syntax", "Inappropriate", 4, [];
    internal_invalid_input: "invalid-internal", "Error", 6, [];
    resource: "resource", "ResourceOut", 5, [];
    panic_partial_resource: "panic", "Error", 6, [];
    signal_without_resource_evidence: "signal", "Error", 6, [];
    spoofed_status: "spoof", "Error", 6, [];
    missing_certificate: "missing-proof", "Error", 6, [];
    checker_rejects: "reject", "Error", 6, [];
    checker_wrong_source: "wrong-source", "Error", 6, [];
    checker_spoof: "checker-spoof", "Error", 6, [];
    changed_input_snapshot: "mutate-input", "Error", 6, [];
    changed_certificate_snapshot: "mutate-proof", "Error", 6, [];
    input_limit: "candidate", "ResourceOut", 5, ["--max-input-bytes", "2"];
    proof_limit: "candidate", "ResourceOut", 5, ["--max-certificate-bytes", "2"];
    log_limit: "logs", "ResourceOut", 5, ["--max-log-bytes", "100"];
    timeout_search: "timeout-search", "Timeout", 7, ["--wall-seconds", "0.4"];
    timeout_checker: "timeout-checker", "Timeout", 7, ["--wall-seconds", "0.5"];
    memory: "memory-search", "MemoryOut", 8, ["--memory-mib", "48"];
}

fn first_process_hash_status(manifest: &Value) -> String {
    let records = manifest.get("processes").and_then(Value::as_array).unwrap();
    text(&records[0], "stdout_hash_status")
}

#[test]
fn sparse_log_has_bounded_failure_accounting() {
    let manifest = Fixture::new(false)
        .invoke("sparse-log", "ResourceOut", 5, &[])
        .unwrap();
    assert_eq!(
        first_process_hash_status(&manifest),
        "skipped-over-log-limit"
    );
}

#[test]
fn replaced_fifo_log_does_not_block_finalization() {
    let manifest = Fixture::new(false)
        .invoke("fifo-log", "Error", 6, &[])
        .unwrap();
    assert_eq!(
        first_process_hash_status(&manifest),
        "nonregular-or-replaced-path"
    );
}

#[test]
fn orphan_is_killed_and_reaped() {
    let fixture = Fixture::new(false);
    fixture.invoke("orphan", "Error", 6, &[]);
    let pid = fs::read_to_string(fixture.output.join("search/child.pid")).unwrap();
    // The supervisor kills the orphan. It sleeps 5 s, so not running within 3 s means it was killed.
    assert!(
        stops_within(pid.trim().parse().unwrap(), Duration::from_secs(3)),
        "the orphan is still running"
    );
}

/// Whether process `pid` is gone or a zombie within `limit`. Without a child subreaper (rust-tools DESIGN.md) a
/// killed child is reaped by whoever adopts it, so it may stay a zombie for a while; a zombie no longer runs.
fn stops_within(pid: i64, limit: Duration) -> bool {
    let stat = format!("/proc/{pid}/stat");
    let running = || {
        fs::read_to_string(&stat).is_ok_and(|text| {
            text.rsplit_once(") ")
                .is_some_and(|(_, rest)| !rest.starts_with('Z'))
        })
    };
    let deadline = Instant::now() + limit;
    while running() && Instant::now() < deadline {
        std::thread::sleep(Duration::from_millis(20));
    }
    !running()
}

#[test]
fn stale_directory_untouched() {
    let fixture = Fixture::new(false);
    fs::create_dir(&fixture.output).unwrap();
    fs::write(fixture.output.join("sentinel"), b"keep").unwrap();
    fixture.invoke("candidate", "Error", 6, &[]);
    assert_eq!(fs::read(fixture.output.join("sentinel")).unwrap(), b"keep");
    assert_eq!(fs::read_dir(&fixture.output).unwrap().count(), 1);
}

#[test]
fn executable_pin_mismatch() {
    let fixture = Fixture::new(false);
    let mut engine = fs::read_to_string(fixture.root.join("engine")).unwrap();
    engine.push_str("# changed\n");
    fs::write(fixture.root.join("engine"), engine).unwrap();
    fixture.invoke("candidate", "Error", 6, &[]);
}

/// `running_adapter_mismatch`: the launcher pin names another file whose own hash matches, so the installation
/// check passes and the running launcher differs from its pin.
#[test]
fn running_adapter_mismatch() {
    let fixture = Fixture::new(false);
    let other = fixture.root.join("other-launcher");
    fs::write(&other, b"not the running launcher").unwrap();
    fixture.configure(Some(binary_pin(&other)));
    let manifest = fixture.invoke("candidate", "Error", 6, &[]).unwrap();
    assert_eq!(
        text(&manifest, "reason"),
        "Running launcher differs from the installed launcher"
    );
}

#[test]
fn inherited_loader_and_python_overrides_not_forwarded() {
    let fixture = Fixture::new(false);
    let mut command = fixture.command("compiled", "status", &[]);
    command
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("LANG", "C.UTF-8")
        .env("LC_ALL", "C.UTF-8")
        .env("LD_LIBRARY_PATH", "/nonexistent")
        .env("PYTHONHOME", "/nonexistent");
    let outcome = finish(command.spawn().unwrap(), Duration::from_secs(40));
    assert_eq!(
        outcome.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&outcome.stdout)
    );
    let manifest = fixture.manifest().unwrap();
    for process in manifest.get("processes").and_then(Value::as_array).unwrap() {
        let keys: Vec<&str> = process
            .get("environment")
            .and_then(Value::as_object)
            .unwrap()
            .keys()
            .collect();
        assert_eq!(
            keys.iter()
                .copied()
                .collect::<std::collections::BTreeSet<_>>(),
            ["LANG", "LC_ALL", "PATH"].into()
        );
    }
}

#[test]
fn fifo_input_is_rejected_without_waiting() {
    let fixture = Fixture::new(false);
    fs::remove_file(&fixture.input).unwrap();
    let made = Command::new("mkfifo").arg(&fixture.input).status().unwrap();
    assert!(made.success());
    fixture.invoke("candidate", "Error", 6, &[]);
}

/// `cancel`: SIGTERM to the command while a stage runs. The outer process ends by the signal (143 in a shell)
/// where the Python adapter exited 9; the worker still prints and records Forced and stops every child.
fn cancel(mode: &str, stage: &str) {
    let fixture = Fixture::new(false);
    fixture.set_mode(mode);
    fixture.configure(None);
    let child = fixture.command("compiled", "status", &[]).spawn().unwrap();
    let ready = fixture.output.join(stage).join("ready");
    let deadline = Instant::now() + Duration::from_secs(10);
    while !ready.exists() {
        assert!(
            Instant::now() < deadline,
            "the control child did not become ready"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
    let sent = Command::new("/bin/kill")
        .args(["-s", "TERM", &child.id().to_string()])
        .status()
        .unwrap();
    assert!(sent.success());
    let outcome = finish(child, Duration::from_secs(20));
    assert_eq!(outcome.status.signal(), Some(15));
    let stdout = String::from_utf8_lossy(&outcome.stdout);
    assert!(stdout.contains("% SZS status Forced for fang_"), "{stdout}");
    assert!(!stdout.contains("Unsatisfiable"));
    let manifest = fixture.manifest().unwrap();
    assert_eq!(text(&manifest, "status"), "Forced");
    for process in manifest.get("processes").and_then(Value::as_array).unwrap() {
        for pid in process
            .get("terminated_owned_pids")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            // Terminated children may be listed as zombies not yet reaped, as Python listed them.
            assert!(stops_within(pid.as_i64().unwrap(), Duration::from_secs(3)));
        }
    }
}

#[test]
fn cancel_before_candidate() {
    cancel("cancel-search", "search");
}

#[test]
fn cancel_after_candidate() {
    cancel("cancel-checker", "checker");
}

// The version-3 installation, in place of InstallationTests: library and provenance pins are rehashed, while
// executable pins are hashed before first use and identity-checked before a positive result.

#[test]
fn installation_pins_are_rehashed() {
    let fixture = Fixture::new(true);
    let config = fixture.configure(None);
    // The running-launcher half of the check is `running_adapter_mismatch`: this test binary is not the launcher.
    let mut check = || Ok(());
    installation::verify_installation(&config, &mut check).unwrap();
    let refusal = |path: &Path, binary: Option<&str>, reason: &str| {
        let before = fs::read(path).unwrap();
        fs::write(path, [&before[..], b"changed"].concat()).unwrap();
        let mut check = || Ok(());
        let fault = if let Some(name) = binary {
            installation::verify_installation(&config, &mut check).unwrap();
            installation::binaries_of(&config)
                .unwrap()
                .verify(&[name])
                .unwrap_err()
        } else {
            installation::verify_installation(&config, &mut check).unwrap_err()
        };
        assert_eq!(fault.python_str(), reason, "{}", path.display());
        fs::write(path, before).unwrap();
    };
    refusal(
        &fixture.root.join("engine"),
        Some("engine"),
        "Installed executable differs from its pin",
    );
    refusal(
        &fixture.root.join("exporter"),
        Some("exporter"),
        "Installed executable differs from its pin",
    );
    refusal(
        &fixture.root.join("library/Fang/CertificateInput.olean"),
        None,
        "Shared proof-library inventory changed",
    );
    refusal(
        &fixture.root.join("provenance.json"),
        None,
        "Installation build/proof record changed",
    );
    fs::write(fixture.root.join("library/Fang/Extra.olean"), b"unlisted").unwrap();
    let mut check = || Ok(());
    assert_eq!(
        installation::verify_installation(&config, &mut check)
            .unwrap_err()
            .python_str(),
        "Shared proof-library inventory changed"
    );
}

/// `v2_without_exporter_and_v1_with_exporter_rejected` and the missing-source half of
/// `exporter_pin_and_required_source_are_enforced`, on the version-3 fields.
#[test]
fn v2_without_exporter_and_v1_with_exporter_rejected() {
    let fixture = Fixture::new(true);
    let Value::Object(config) = fixture.configure(None) else {
        panic!("not an object")
    };
    let refusal = |config: Object| {
        let mut check = || Ok(());
        installation::verify_installation(&Value::Object(config), &mut check)
            .unwrap_err()
            .python_str()
    };
    let mut missing = config.clone();
    missing.remove("exporter");
    assert_eq!(refusal(missing), "Unsupported installation schema");
    let mut sources = config.clone();
    sources.remove("exporter_sources");
    assert_eq!(
        refusal(sources),
        "TSTP installation is missing exporter source"
    );
    let mut wrong = config.clone();
    wrong.set("schema", "fang-local-installation-v2");
    assert_eq!(refusal(wrong), "Unsupported installation schema");
}

// TstpAdapterTests

#[test]
fn success_captures_exact_bytes_and_complete_closing_marker() {
    let fixture = Fixture::new(true);
    let (stdout, manifest) = fixture.tstp("Unsatisfiable", &[], "tstp");
    assert_eq!(
        fs::read(fixture.output.join("solution.tstp")).unwrap(),
        SOLUTION
    );
    let solution = manifest.get("solution").unwrap();
    assert_eq!(text(solution, "sha256"), fang_hash::sha256_hex(SOLUTION));
    assert_eq!(
        solution
            .get("per_instance_kernel_check_of_printed_bytes")
            .and_then(Value::as_bool),
        Some(false)
    );
    assert_eq!(stages(&manifest), ["search", "checker", "exporter"]);
    for record in manifest.get("processes").and_then(Value::as_array).unwrap() {
        assert_eq!(text(record, "classification"), "completed");
    }
    assert!(
        stdout
            .windows(SOLUTION.len())
            .any(|window| window == SOLUTION)
    );
    let closing = format!(
        "% SZS output end CNFRefutation for {}\n",
        text(&manifest, "problem_id")
    );
    assert!(stdout.ends_with(closing.as_bytes()));
    let delivery = manifest.get("output_delivery").unwrap();
    assert_eq!(
        delivery
            .get("closing_marker_delivered")
            .and_then(Value::as_bool),
        Some(true)
    );
    assert_eq!(text(delivery, "sha256"), fang_hash::sha256_hex(&stdout));
    assert!(!String::from_utf8_lossy(&stdout).contains("source with"));
}

#[test]
fn v1_status_works_and_tstp_fails_before_search() {
    let mut fixture = Fixture::new(false);
    let (stdout, manifest) = fixture.tstp("Unsatisfiable", &[], "status");
    assert_eq!(
        stdout
            .split(|byte| *byte == b'\n')
            .filter(|line| !line.is_empty())
            .count(),
        2
    );
    assert!(manifest.get("solution").is_none());
    fixture.fresh_output("tstp-run");
    let (_, manifest) = fixture.tstp("Error", &[], "tstp");
    assert!(stages(&manifest).is_empty());
    assert_eq!(
        text(&manifest, "reason"),
        "This installation has no pinned TSTP exporter"
    );
}

#[test]
fn status_mode_does_not_execute_exporter() {
    let fixture = Fixture::new(true);
    fixture.set_exporter("echo 'exporter must not execute' >&2; exit 1", SOLUTION);
    fixture.configure(None);
    let (_, manifest) = fixture.tstp("Unsatisfiable", &[], "status");
    assert_eq!(stages(&manifest), ["search", "checker"]);
    let delivery = manifest.get("output_delivery").unwrap();
    assert_eq!(
        delivery
            .get("closing_marker_delivered")
            .and_then(Value::as_bool),
        Some(false)
    );
}

#[test]
fn exporter_pin_and_required_source_are_enforced() {
    let fixture = Fixture::new(true);
    let mut exporter = fs::read_to_string(fixture.root.join("exporter")).unwrap();
    exporter.push_str("\n# changed\n");
    fs::write(fixture.root.join("exporter"), exporter).unwrap();
    let (_, manifest) = fixture.tstp("Error", &[], "tstp");
    // First-use hashing permits the search and checker, but refuses the exporter before it executes.
    assert_eq!(stages(&manifest), ["search", "checker"]);
    assert_eq!(
        text(&manifest, "reason"),
        "Installed executable differs from its pin"
    );
}

#[test]
fn checker_rejection_never_runs_exporter() {
    let fixture = Fixture::new(true);
    fixture.set_mode("reject");
    fixture.configure(None);
    let (_, manifest) = fixture.tstp("Error", &[], "tstp");
    assert_eq!(stages(&manifest), ["search", "checker"]);
}

#[test]
fn exporter_failures_never_publish_positive_output() {
    let mut fixture = Fixture::new(true);
    let solution = format!("cat {}/solution.bin", fixture.root.display());
    let partial = &SOLUTION[..SOLUTION.len() - 1];
    let cases: [(&str, &[u8]); 6] = [
        ("exit 3", SOLUTION),
        (&format!("echo warning >&2; {solution}"), SOLUTION),
        (&solution, partial),
        (&solution, b"% SZS status Unsatisfiable\n"),
        (&solution, b"cnf('x',plain,(p),file('input.p','a')).\n"),
        ("true", SOLUTION),
    ];
    for (index, (body, printed)) in cases.iter().enumerate() {
        fixture.set_exporter(body, printed);
        fixture.configure(None);
        fixture.fresh_output(&format!("run{index}"));
        let (_, manifest) = fixture.tstp("Error", &[], "tstp");
        assert!(manifest.get("solution").is_none(), "case {index}");
    }
}

#[test]
fn recognized_resource_exit_stays_resource_and_partial_stdout_is_error() {
    let mut fixture = Fixture::new(true);
    let diagnostic =
        "echo 'resource-exhaustion: export supports at most 1000 certificate nodes' >&2; exit 2";
    fixture.set_exporter(diagnostic, SOLUTION);
    fixture.configure(None);
    fixture.tstp("ResourceOut", &[], "tstp");
    fixture.set_exporter(&format!("printf partial; {diagnostic}"), SOLUTION);
    fixture.configure(None);
    fixture.fresh_output("partial");
    fixture.tstp("Error", &[], "tstp");
}

#[test]
fn solution_limit_exact_boundary_and_stdout_override() {
    let mut fixture = Fixture::new(true);
    fixture.tstp(
        "Unsatisfiable",
        &["--max-solution-bytes", &SOLUTION.len().to_string()],
        "tstp",
    );
    fixture.fresh_output("below");
    fixture.tstp(
        "ResourceOut",
        &["--max-solution-bytes", &(SOLUTION.len() - 1).to_string()],
        "tstp",
    );
    // The exporter stdout cap may exceed the stderr/log cap.
    let mut many: Vec<u8> = (0..80)
        .flat_map(|index| format!("cnf('x{index}',axiom,(p),file('input.p','a')).\n").into_bytes())
        .collect();
    many.extend_from_slice(LAST_ROW);
    fixture.set_exporter(
        &format!("cat {}/solution.bin", fixture.root.display()),
        &many,
    );
    fixture.configure(None);
    fixture.fresh_output("large-stdout");
    let (_, manifest) = fixture.tstp(
        "Unsatisfiable",
        &[
            "--max-log-bytes",
            "256",
            "--max-solution-bytes",
            &many.len().to_string(),
        ],
        "tstp",
    );
    assert!(
        manifest
            .get("solution")
            .and_then(|solution| solution.get("bytes"))
            .and_then(Value::as_i64)
            .unwrap()
            > 256
    );
    let records = manifest.get("processes").and_then(Value::as_array).unwrap();
    let limits = records.last().unwrap().get("stream_byte_limits").unwrap();
    assert_eq!(
        limits.get("stdout").and_then(Value::as_i64),
        Some(many.len() as i64)
    );
    assert_eq!(limits.get("stderr").and_then(Value::as_i64), Some(256));
}

#[test]
fn stderr_limit_does_not_inherit_solution_limit() {
    let fixture = Fixture::new(true);
    fixture.set_exporter(
        &format!(
            "head -c 257 /dev/zero | tr '\\0' x >&2; cat {}/solution.bin",
            fixture.root.display()
        ),
        SOLUTION,
    );
    fixture.configure(None);
    fixture.tstp(
        "ResourceOut",
        &["--max-log-bytes", "256", "--max-solution-bytes", "10000"],
        "tstp",
    );
}

#[test]
fn captured_source_or_certificate_mutation_is_rejected() {
    let mut fixture = Fixture::new(true);
    for name in ["input.p", "proof.fang"] {
        // The exporter checked the pair first, so the change happens after its checks and before the output.
        fixture.set_exporter(
            &format!(
                "chmod 600 ../{name}; printf changed > ../{name}; cat {}/solution.bin",
                fixture.root.display()
            ),
            SOLUTION,
        );
        fixture.configure(None);
        fixture.fresh_output(&format!("run-{name}"));
        fixture.tstp("Error", &[], "tstp");
        assert!(!fixture.output.join("solution.tstp").exists());
    }
}

/// `kernel_profile_calls_selected_check_before_export`: the replay runs, on a synthetic Lean, before the export.
#[test]
fn kernel_profile_calls_selected_check_before_export() {
    let fixture = Fixture::new(true);
    fixture.write_replay();
    let outcome = finish(
        fixture
            .command("kernel", "tstp", &["--wall-seconds", "60"])
            .spawn()
            .unwrap(),
        Duration::from_secs(90),
    );
    assert_eq!(
        outcome.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&outcome.stdout)
    );
    let manifest = fixture.manifest().unwrap();
    let stages = stages(&manifest);
    let export = stages.iter().position(|stage| stage == "exporter").unwrap();
    let audit = stages
        .iter()
        .position(|stage| stage == "kernel-audit")
        .unwrap();
    assert!(
        stages[..4] == ["search", "checker", "export", "decompose"] && audit < export,
        "{stages:?}"
    );
    let check = manifest.get("kernel_check").unwrap();
    assert_eq!(text(check, "hook"), "fixed-decomposed-v2");
    assert!(manifest.get("solution").is_some());
}

#[test]
fn kernel_failure_has_no_compiled_fallback_or_export() {
    let fixture = Fixture::new(true);
    fixture.write_replay();
    fixture.set_mode("lean-fails");
    fixture.configure(None);
    let outcome = finish(
        fixture
            .command("kernel", "tstp", &["--wall-seconds", "60"])
            .spawn()
            .unwrap(),
        Duration::from_secs(90),
    );
    assert_eq!(outcome.status.code(), Some(6));
    let manifest = fixture.manifest().unwrap();
    assert_eq!(text(&manifest, "stage"), "kernel-certificatetokens");
    assert!(!stages(&manifest).iter().any(|stage| stage == "exporter"));
    assert!(!fixture.output.join("exporter").exists());
    assert_eq!(
        manifest
            .get("kernel_storage")
            .and_then(|storage| storage.get("state"))
            .and_then(Value::as_str),
        Some("retained-after-failure")
    );
    let retained = manifest
        .get("kernel_storage")
        .and_then(|storage| storage.get("retained_path"))
        .and_then(Value::as_str)
        .unwrap();
    assert!(retained.starts_with("/var/tmp/fang-kernel-"));
    fs::remove_dir_all(retained).unwrap();
}

#[test]
fn full_pipe_records_incomplete_solution_delivery() {
    let fixture = Fixture::new(true);
    let row = b"cnf('x',axiom,(p),file('input.p','a')).\n";
    let mut many: Vec<u8> = row.repeat(4096);
    many.extend_from_slice(LAST_ROW);
    fixture.set_exporter(
        &format!("cat {}/solution.bin", fixture.root.display()),
        &many,
    );
    fixture.configure(None);
    let mut child = fixture
        .command("compiled", "tstp", &["--wall-seconds", "8"])
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(40);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        assert!(
            Instant::now() < deadline,
            "the command did not give up on the full pipe"
        );
        std::thread::sleep(Duration::from_millis(20));
    };
    let outcome = finish(child, Duration::from_secs(5));
    assert_eq!(status.code(), Some(7));
    assert_eq!(outcome.stderr, b"");
    let manifest = fixture.manifest().unwrap();
    assert_eq!(text(&manifest, "status"), "Timeout");
    let delivery = manifest.get("output_delivery").unwrap();
    assert_eq!(text(delivery, "state"), "incomplete");
    assert_eq!(
        delivery
            .get("closing_marker_delivered")
            .and_then(Value::as_bool),
        Some(false)
    );
    assert!(!String::from_utf8_lossy(&outcome.stdout).contains("% SZS output end"));
}

#[test]
fn closed_output_pipe_records_error() {
    let fixture = Fixture::new(true);
    let (reader, writer) = std::io::pipe().unwrap();
    drop(reader);
    let mut command = fixture.command("compiled", "tstp", &[]);
    command.stdout(writer);
    let outcome = finish(command.spawn().unwrap(), Duration::from_secs(20));
    assert_eq!(
        outcome.status.code(),
        Some(6),
        "{}",
        String::from_utf8_lossy(&outcome.stderr)
    );
    let manifest = fixture.manifest().unwrap();
    let delivery = manifest.get("output_delivery").unwrap();
    assert_eq!(text(delivery, "state"), "incomplete");
    assert_eq!(
        delivery
            .get("closing_marker_delivered")
            .and_then(Value::as_bool),
        Some(false)
    );
}
