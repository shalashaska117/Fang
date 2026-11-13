// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Install the version-8 fang command into a fresh directory from a checked source snapshot. The specification
//! is tools/build-v8-local.py, with the launcher setup of tools/cli_setup.py and the older profiles'
//! provisioning of tools/fof_setup.py and tools/fang_szs/installation.py replaced as DESIGN.md describes.
//!
//! Steps: snapshot and check every source against its map, run the Rust workspace checks and the release build
//! of the producers, the launcher and the kernel package, build lean-v8 with fang-build-v8-lean (or take a
//! finished build of the same sources), run the kernel helper build and kernel install, copy the source maps
//! and build manifests as provenance, copy the launcher to bin/fang, write the older profiles' configuration
//! files, pin everything in v8-capability.json (schema v8), and write the receipt. Installation reads only the
//! files of the repository: the maps name the receipt every source came from, as data, and no receipt is read.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use fang_json::{Object, Value};
use fang_launcher::capability::{self as capability, Pin, Record};
use fang_supervisor::Supervisor;
use fang_supervisor::guard::Worker;

use crate::adapt::{self, StageCall};
use crate::common::{
    At, Error, Result, compact, copy2, copyfile, create_json, mkdir, mkdir_plain, object,
    read_json, require, resolve, run_captured, run_inherited, sha256_file, text_of, utc_now,
    write_bytes, write_manifest,
};
use crate::inventory::{self, installer_record, which};
use crate::report::{self, Report};

pub const INSTALLED: [&str; 9] = [
    "fang-v8-engine",
    "fang-v8-check",
    "fang-v8-tstp",
    "fang-bundle-producer",
    "fang-bundle-check",
    "fang-model-find",
    "fang-model-check",
    "fang-signed-producer",
    "fang-signed-check",
];
/// Built only when lean-v8 holds the bundle exporter or goal document gate, or when the kernel witness crate is staged.
pub const OPTIONAL: [&str; 8] = [
    "fang-bundle-tstp",
    "fang-goal-tstp",
    "fang-model-tstp",
    "fang-v8-witness",
    NAMED_SINGLE_EXPORTER,
    NAMED_GOAL_EXPORTER,
    SIGNED_SINGLE_PRODUCER,
    KERNEL_PRODUCER,
];
pub const SIGNED_SINGLE_PRODUCER: &str = "fang-signed-single-producer";
pub const KERNEL_PRODUCER: &str = "fang-kernel-producer";
/// Round two's named exporters (worker-product's route choice).
pub const NAMED_SINGLE_EXPORTER: &str = "fang-v8-tstp-named";
pub const NAMED_GOAL_EXPORTER: &str = "fang-goal-tstp-named";
/// SHA-256 prefixes of named conjecture exporter builds without the inputs mode, refused under that name.
pub const WITHOUT_INPUTS: [&str; 1] = ["308b5ea3"];
/// Provenance copied into the installation: the source maps, the audit list and the backend pins.
pub const PROVENANCE: [&str; 4] = [
    "tools/v8_szs/rust-sources.json",
    "tools/v8_szs/lean-sources.json",
    "lean-v8/audits.json",
    "tools/v8_szs/backend-pins.json",
];
/// Packages built beside the installed binaries, taken by fixed name until the map lists them.
pub const LAUNCHER_PACKAGE: &str = "fang-launcher";
pub const LAUNCHER_BINARY: &str = "fang-launcher";
pub const KERNEL_PACKAGE: &str = "fang-v8-kernel";
pub const KERNEL_CRATE: &str = "crates/v8-kernel";
const SCOPE: &str = "Version-8 command built from the repository alone: Rust producers, compiled Lean checkers and SZS status \
on the single-file, bundle and signed paths, and TSTP output on the single-file path. Kernel replay is not installed; \
--check kernel is refused before the input is read.";
const ENVIRONMENT_KEYS: [&str; 7] = [
    "PATH",
    "HOME",
    "RUSTUP_HOME",
    "CARGO_HOME",
    "RUSTUP_TOOLCHAIN",
    "LANG",
    "LC_ALL",
];
const HOUR: Duration = Duration::from_secs(3600);

pub struct Options {
    pub root: PathBuf,
    pub out: PathBuf,
    pub cargo: String,
    pub lean_toolchain: PathBuf,
    pub lean_build: Option<PathBuf>,
    pub backend: Option<PathBuf>,
    pub packages: Option<PathBuf>,
    pub aeneas_checkout: Option<PathBuf>,
    pub lean_work: Option<PathBuf>,
    pub older: Option<PathBuf>,
}

/// `shlex.quote`.
pub fn shell_quote(text: &str) -> String {
    let safe = !text.is_empty()
        && text
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || "@%+=:,./-_".contains(c));
    if safe {
        text.to_string()
    } else {
        format!("'{}'", text.replace('\'', "'\"'\"'"))
    }
}

fn record(path: &Path) -> Result<Value> {
    Ok(object(vec![
        ("path", text_of(path).into()),
        ("sha256", adapt::digest(path)?.into()),
    ]))
}

/// A binary's record: the plain SHA-256 and fang-hash's chunked digest in its tagged text form, which the launcher
/// checks on every run.
fn binary_record(path: &Path) -> Result<Value> {
    Ok(object(vec![
        ("path", text_of(path).into()),
        ("sha256", adapt::digest(path)?.into()),
        ("chunked_sha256", adapt::chunked(path)?.into()),
    ]))
}

fn pin(path: &Path) -> Result<Record> {
    Ok(Record {
        path: path.to_path_buf(),
        sha256: adapt::digest(path)?,
    })
}

fn binary_pin(path: &Path) -> Result<Pin> {
    Ok(Pin {
        path: path.to_path_buf(),
        sha256: adapt::digest(path)?,
        chunked_sha256: Some(adapt::chunked(path)?),
    })
}

fn checked_record(path: &Path, expected: Option<&Value>) -> Result<Record> {
    require(
        fs::symlink_metadata(path).is_ok_and(|metadata| metadata.is_file()),
        format!("Build artifact is not a regular file: {}", path.display()),
    )?;
    let record = pin(path)?;
    require(
        expected.and_then(Value::as_str) == Some(record.sha256.as_str()),
        format!(
            "Build artifact changed before provisioning: {}",
            path.display()
        ),
    )?;
    Ok(record)
}

fn checked_binaries(bin: &Path, receipt: &Value, names: &[&str]) -> Result<BTreeMap<String, Pin>> {
    let hashes = receipt
        .get("binaries_sha256")
        .and_then(Value::as_object)
        .ok_or_else(|| Error::Value("Missing binary inventory".into()))?;
    require(
        hashes.keys().collect::<BTreeSet<_>>() == names.iter().copied().collect(),
        "Build binary inventory differs from the expected set",
    )?;
    let mut pins = BTreeMap::new();
    for name in names {
        let path = bin.join(name);
        let checked = checked_record(&path, hashes.get(name))?;
        let binary = binary_pin(&fs::canonicalize(&path).at(&path)?)?;
        require(
            binary.sha256 == checked.sha256,
            "Binary changed while pinning",
        )?;
        pins.insert((*name).to_string(), binary);
    }
    Ok(pins)
}

/// The optional single-file route selects the named and cited protocols together.
fn final_signed_routes(produced: &Object, executables: &Object) -> Result<bool> {
    let binary = |name: &str, expected: &str| {
        produced.get(name).is_some_and(|entry| {
            entry.get("package").and_then(Value::as_str) == Some("fang-saturation")
                && entry.get("binary").and_then(Value::as_str) == Some(expected)
        })
    };
    let named = produced.contains_key(SIGNED_SINGLE_PRODUCER);
    let cited = binary("fang-signed-producer", "fang-v3-cited-bundle-final");
    let checker = executables.get("fang-signed-bundle-native-v6");
    if named || cited || checker.is_some() {
        require(
            binary(SIGNED_SINGLE_PRODUCER, "fang-v3-signed-named")
                && cited
                && executables
                    .values()
                    .filter(|entry| {
                        entry.get("installed_as").and_then(Value::as_str)
                            == Some("fang-signed-check")
                    })
                    .count()
                    == 1
                && checker.is_some_and(|entry| {
                    entry.get("root").and_then(Value::as_str) == Some("SignedBundleNativeV6Main")
                        && entry.get("installed_as").and_then(Value::as_str)
                            == Some("fang-signed-check")
                }),
            "Named signed routing requires both final producers and the role-v6 checker",
        )?;
    }
    Ok(named)
}

fn named_engine_route(produced: &Object, kernel_installed: bool) -> Result<bool> {
    let named = produced
        .get("fang-v8-engine")
        .and_then(|entry| entry.get("binary"))
        .and_then(Value::as_str)
        == Some("fang-v3-single-named");
    let kernel_producer = produced.get(KERNEL_PRODUCER);
    if let Some(entry) = kernel_producer {
        require(
            entry.get("package").and_then(Value::as_str) == Some("fang-saturation")
                && entry.get("binary").and_then(Value::as_str) == Some("fang-v3-single"),
            "Kernel replay requires the unnamed producer",
        )?;
    }
    require(
        !named || !kernel_installed || kernel_producer.is_some(),
        "Named engine with kernel replay requires a separate unnamed producer",
    )?;
    Ok(named)
}

fn text_field(value: &Value, key: &str) -> Result<String> {
    value
        .get(key)
        .and_then(Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| Error::Key(format!("'{key}'")))
}

/// Make a directory on a Windows drive case-sensitive, as lean-v8 holds FofInput and FOFInput.
fn case_sensitive(output: &Path) -> Result<String> {
    let fsutil = "/mnt/c/Windows/System32/fsutil.exe".to_string();
    let call = |command: Vec<String>| -> Result<String> {
        let done = run_captured(&command, None, None, Duration::MAX)?;
        if done.returncode != 0 {
            return Err(Error::Os {
                class: "CalledProcessError",
                message: format!(
                    "Command '{}' returned non-zero exit status {}.",
                    crate::common::py_repr_list(&command),
                    done.returncode
                ),
            });
        }
        Ok(String::from_utf8_lossy(&done.stdout).into_owned())
    };
    let windows = call(vec![
        "/usr/bin/wslpath".into(),
        "-w".into(),
        text_of(output),
    ])?
    .trim_matches(crate::scan::py_space)
    .to_string();
    call(vec![
        fsutil.clone(),
        "file".into(),
        "setCaseSensitiveInfo".into(),
        windows.clone(),
        "enable".into(),
    ])?;
    let query = call(vec![
        fsutil,
        "file".into(),
        "queryCaseSensitiveInfo".into(),
        windows.clone(),
    ])?
    .trim_matches(crate::scan::py_space)
    .to_string();
    require(
        query == format!("Case sensitive attribute on directory {windows} is enabled."),
        "Installation directory is not case sensitive",
    )?;
    Ok(query)
}

pub fn main(options: &Options, worker: Option<&Worker>) -> Result<i32> {
    require(
        cfg!(target_os = "linux"),
        "Installation requires Linux or WSL",
    )?;
    let root = resolve(&options.root)?;
    let output = resolve(&options.out)?;
    mkdir(&output, 0o700, true, false)?;
    let case_sensitivity = if output.starts_with("/mnt") {
        Value::from(case_sensitive(&output)?)
    } else {
        Value::Null
    };
    let mut supervisor = adapt::supervisor(7200.0, 8192, 64 << 20, 8 << 30)?;
    let report = Report::new(vec![
        ("schema", "fang-v8-installation-v1".into()),
        ("status", "building".into()),
        ("started_utc", utc_now().into()),
        ("scope", SCOPE.into()),
        ("case_sensitivity", case_sensitivity),
    ]);
    mkdir_plain(&output.join("stages"))?;
    let failure_path = output.join("setup-failure.json");
    report::on_cancel(worker, &report, failure_path.clone(), |_| {});
    report.set(
        "inherited_descriptors",
        supervisor.inherited_descriptors_json(),
    );
    match install(options, &root, &output, &report, &mut supervisor) {
        Ok(launcher) => {
            let add = format!(
                "export PATH={}:\"$PATH\"",
                shell_quote(&text_of(&output.join("bin")))
            );
            println!(
                "{}",
                compact(&object(vec![
                    ("status", "installed".into()),
                    ("command", text_of(&launcher).into()),
                    ("add_to_path", add.into())
                ]))
            );
            Ok(0)
        }
        Err(error) => {
            report.set("status", "failed");
            report.set("error", error.typed());
            report.set("stages", adapt::records(&supervisor));
            let mut written = Ok(());
            report::finish(worker, || {
                written = write_manifest(&failure_path, &report.value())
            });
            written?;
            eprintln!("Setup failed: {}", error.message());
            Ok(1)
        }
    }
}

/// build-v8-local.py `snapshot_files()`: build-local's inventory plus the lean-v8 files. The version-8 tools and
/// the kernel files the script added by name all lie under tools/, which that inventory already walks.
pub fn snapshot_files(root: &Path, supervisor: &Supervisor) -> Result<Vec<PathBuf>> {
    let mut files: BTreeSet<PathBuf> = inventory::source_files(root, supervisor, "adapter")?
        .into_iter()
        .collect();
    files.extend(adapt::lean_files(root, supervisor)?);
    let mut files: Vec<PathBuf> = files.into_iter().collect();
    files.sort_by_key(|path| inventory::path_key(path));
    Ok(files)
}

fn install(
    options: &Options,
    root: &Path,
    output: &Path,
    report: &Report,
    supervisor: &mut Supervisor,
) -> Result<PathBuf> {
    let installer = installer_record()?;
    report.set("installer", installer.clone());
    let frozen = output.join("source");
    let mut hashes = Object::new();
    for path in snapshot_files(root, supervisor)? {
        let inner = inventory::relative(&path, root);
        let data = fs::read(&path).at(&path)?;
        let target = frozen.join(&inner);
        if let Some(parent) = target.parent() {
            mkdir(parent, 0o777, true, true)?;
        }
        write_bytes(&target, &data)?;
        hashes.set(inner, fang_hash::sha256_hex(&data));
    }
    report.set("source_sha256", Value::Object(hashes.clone()));
    let source_check = fang_source_checks::check_tree(&frozen, false, false);
    let printed = compact(&source_check);
    if source_check.get("status").and_then(Value::as_str) != Some("passed") {
        let tail: String = {
            let all: Vec<char> = format!("{printed}\n").chars().collect();
            all[all.len().saturating_sub(500)..].iter().collect()
        };
        return Err(Error::Value(format!(
            "Snapshot source check failed: {tail}"
        )));
    }
    report.set("source_check", source_check);
    let cargo = which(&options.cargo)
        .ok_or_else(|| Error::Value("Install the pinned Rust toolchain first".to_string()))?;
    let mut environment: BTreeMap<String, String> = ENVIRONMENT_KEYS
        .iter()
        .filter_map(|key| {
            std::env::var(key)
                .ok()
                .map(|value| (key.to_string(), value))
        })
        .collect();
    environment.insert("CARGO_NET_OFFLINE".into(), "true".into());
    environment.insert("CARGO_BUILD_JOBS".into(), "2".into());
    environment.insert(
        "CARGO_TARGET_DIR".into(),
        text_of(&output.join("rust-target")),
    );
    environment.insert("TMPDIR".into(), text_of(&output.join("tmp")));
    mkdir_plain(&output.join("tmp"))?;
    report.set(
        "build_environment",
        Value::Object(
            environment
                .iter()
                .map(|(key, value)| (key.clone(), Value::from(value.as_str())))
                .collect(),
        ),
    );
    let stage_environment = adapt::environment(&environment)?;
    let stages = output.join("stages");
    let run = |supervisor: &mut Supervisor, stage: &str, command: Vec<String>| -> Result<String> {
        let result = adapt::run(
            supervisor,
            StageCall {
                name: stage,
                command,
                directory: stages.join(stage),
                run_root: &stages,
                environment: Some(&stage_environment),
                stdout_limit: None,
                cwd: Some(&frozen),
            },
        );
        report.set("stages", adapt::records(supervisor));
        let done = result?;
        require(adapt::completed(&done), format!("{stage} failed"))?;
        let mut both = done.stdout;
        both.extend_from_slice(&done.stderr);
        Ok(String::from_utf8_lossy(&both).into_owned())
    };
    let cargo_cmd = |extra: &[&str]| -> Vec<String> {
        std::iter::once(cargo.clone())
            .chain(extra.iter().map(|item| item.to_string()))
            .collect()
    };
    let cargo_version = run(supervisor, "cargo-version", cargo_cmd(&["--version"]))?
        .trim_matches(crate::scan::py_space)
        .to_string();
    report.set("cargo_version", cargo_version.as_str());
    require(
        cargo_version.starts_with("cargo 1.90.0 "),
        "Cargo differs from the pinned 1.90.0",
    )?;
    run(
        supervisor,
        "rust-fmt",
        cargo_cmd(&["fmt", "--all", "--", "--check"]),
    )?;
    run(
        supervisor,
        "rust-tests",
        cargo_cmd(&[
            "test",
            "--workspace",
            "--locked",
            "--offline",
            "--all-targets",
        ]),
    )?;
    run(
        supervisor,
        "rust-clippy",
        cargo_cmd(&[
            "clippy",
            "--workspace",
            "--locked",
            "--offline",
            "--all-targets",
            "--",
            "-D",
            "warnings",
        ]),
    )?;
    let rust_map = adapt::load_map(&frozen, adapt::RUST_MAP, adapt::RUST_SCHEMA, supervisor)?;
    let produced = rust_map
        .get("installed_binaries")
        .and_then(Value::as_object)
        .cloned()
        .unwrap_or_default();
    let mut packages: BTreeSet<String> = produced
        .values()
        .filter_map(|entry| entry.get("package").and_then(Value::as_str))
        .map(str::to_string)
        .collect();
    packages.insert(LAUNCHER_PACKAGE.to_string());
    let kernel_staged = frozen.join(KERNEL_CRATE).join("Cargo.toml").is_file();
    if kernel_staged {
        packages.insert(KERNEL_PACKAGE.to_string());
    }
    let mut build = cargo_cmd(&["build", "--release", "--locked", "--offline"]);
    for package in &packages {
        build.push("-p".into());
        build.push(package.clone());
    }
    run(supervisor, "rust-build", build)?;
    let release = output.join("rust-target/release");
    let toolchain = text_of(&options.lean_toolchain);
    let lean_build = match &options.lean_build {
        Some(finished) => resolve(finished)?,
        None => {
            let work = resolve(options.lean_work.as_ref().ok_or_else(|| {
                Error::Value("--backend and --packages need --lean-work".to_string())
            })?)?;
            let backend: Vec<String> = match (&options.backend, &options.packages) {
                (Some(backend), _) => {
                    let checkout = options.aeneas_checkout.as_ref().ok_or_else(|| {
                        Error::Value("--backend needs --aeneas-checkout".to_string())
                    })?;
                    vec![
                        "--backend".into(),
                        text_of(backend),
                        "--aeneas-checkout".into(),
                        text_of(checkout),
                    ]
                }
                (None, Some(fetched)) => vec!["--packages".into(), text_of(fetched)],
                (None, None) => {
                    return Err(Error::Value(
                        "one of --lean-build, --backend or --packages is required".to_string(),
                    ));
                }
            };
            let mut command = vec![
                text_of(&inventory::sibling("fang-build-v8-lean")?),
                "--root".into(),
                text_of(&frozen),
                "--out".into(),
                text_of(&work),
                "--lean-toolchain".into(),
                toolchain.clone(),
                "--memory-mib".into(),
                "7168".into(),
            ];
            command.extend(backend);
            let code = run_inherited(&command, Duration::from_secs(6000))?;
            require(
                code == 0,
                format!(
                    "lean-v8 build failed; see {}",
                    text_of(&work.join("manifest.json"))
                ),
            )?;
            work
        }
    };
    let lean_report = read_json(&lean_build.join("manifest.json"))?;
    require(
        lean_report.get("status").and_then(Value::as_str) == Some("built-and-audited"),
        "lean-v8 build did not pass",
    )?;
    require(
        lean_report.get("source_map_sha256") == hashes.get(adapt::LEAN_MAP),
        "lean-v8 build used other sources",
    )?;
    require(
        lean_report.get("backend_pins_sha256") == hashes.get(adapt::PINS),
        "Backend pins differ",
    )?;
    let lean_map = adapt::load_map(&frozen, adapt::LEAN_MAP, adapt::LEAN_SCHEMA, supervisor)?;
    let audit_list = read_json(
        &frozen
            .join(text_field(&lean_map, "project")?)
            .join("audits.json"),
    )?;
    let audit_count = audit_list
        .get("names")
        .and_then(Value::as_object)
        .map_or(0, Object::len) as u64;
    require(
        lean_report
            .get("axiom_audits")
            .and_then(|audits| audits.get("count"))
            .and_then(Value::as_u64)
            == Some(audit_count),
        "Fixed axiom audits are incomplete",
    )?;
    let sorted_strings = |value: Option<&Value>| -> Vec<String> {
        let mut items: Vec<String> = value
            .and_then(Value::as_array)
            .map(|items| {
                items
                    .iter()
                    .filter_map(|item| item.as_str().map(str::to_string))
                    .collect()
            })
            .unwrap_or_default();
        items.sort();
        items
    };
    let gate_names: Vec<String> = {
        let mut names: Vec<String> = lean_map
            .get("gates")
            .and_then(Value::as_object)
            .map(|gates| gates.keys().map(str::to_string).collect())
            .unwrap_or_else(|| sorted_strings(lean_map.get("gates")));
        names.sort();
        names
    };
    require(
        sorted_strings(
            lean_report
                .get("axiom_audits")
                .and_then(|audits| audits.get("gates")),
        ) == gate_names,
        "Not every gate was audited",
    )?;
    report.set(
        "lean_build",
        object(vec![
            ("path", text_of(&lean_build).into()),
            (
                "manifest_sha256",
                adapt::digest(&lean_build.join("manifest.json"))?.into(),
            ),
        ]),
    );
    let mut kernel: Option<(PathBuf, PathBuf)> = None;
    if kernel_staged {
        let helpers = output.join("kernel-helpers");
        let project = text_of(&lean_build.join("project"));
        let code = run_inherited(
            &[
                text_of(&release.join("fang-v8-kernel-helpers")),
                "--repository".into(),
                text_of(&frozen),
                "--project".into(),
                project.clone(),
                "--lean-toolchain".into(),
                toolchain.clone(),
                "--out".into(),
                text_of(&helpers),
            ],
            HOUR,
        )?;
        let helper_report = if helpers.join("manifest.json").is_file() {
            read_json(&helpers.join("manifest.json"))?
        } else {
            Value::Object(Object::new())
        };
        require(
            code == 0
                && helper_report.get("status").and_then(Value::as_str) == Some("built-and-audited"),
            format!(
                "Kernel helper build failed; see {}",
                text_of(&helpers.join("manifest.json"))
            ),
        )?;
        let kernel_root = output.join("kernel");
        let code = run_inherited(
            &[
                text_of(&release.join("fang-v8-kernel-install")),
                "--repository".into(),
                text_of(&frozen),
                "--root".into(),
                text_of(&kernel_root),
                "--project".into(),
                project,
                "--lean-build".into(),
                text_of(&lean_build),
                "--helpers".into(),
                text_of(&helpers),
                "--lean-toolchain".into(),
                toolchain.clone(),
            ],
            HOUR,
        )?;
        let installation = kernel_root.join("installation.json");
        require(
            code == 0 && installation.is_file(),
            "Kernel installation failed",
        )?;
        report.set(
            "kernel",
            object(vec![
                (
                    "helpers_manifest_sha256",
                    adapt::digest(&helpers.join("manifest.json"))?.into(),
                ),
                ("installation_sha256", adapt::digest(&installation)?.into()),
            ]),
        );
        kernel = Some((kernel_root, helpers));
    }
    let binaries = output.join("bin");
    mkdir_plain(&binaries)?;
    let mut built: BTreeMap<String, PathBuf> = BTreeMap::new();
    for (name, entry) in produced.iter() {
        built.insert(name.to_string(), release.join(text_field(entry, "binary")?));
    }
    let executables = lean_map
        .get("executables")
        .and_then(Value::as_object)
        .cloned()
        .unwrap_or_default();
    let final_signed = final_signed_routes(&produced, &executables)?;
    let named_engine = named_engine_route(&produced, kernel.is_some())?;
    for (exe, entry) in executables.iter() {
        let reported = lean_report
            .get("executables")
            .and_then(|table| table.get(exe))
            .cloned()
            .unwrap_or(Value::Null);
        let path = PathBuf::from(text_field(&reported, "path")?);
        require(
            reported.get("sha256").and_then(Value::as_str) == Some(adapt::digest(&path)?.as_str()),
            format!("Lean executable differs from its build: {exe}"),
        )?;
        built.insert(text_field(entry, "installed_as")?, path);
    }
    let required: BTreeSet<&str> = built
        .keys()
        .map(String::as_str)
        .filter(|name| !OPTIONAL.contains(name))
        .collect();
    require(
        required == INSTALLED.into_iter().collect::<BTreeSet<_>>(),
        format!(
            "Installed binary set differs: {}",
            built.keys().cloned().collect::<Vec<_>>().join(", ")
        ),
    )?;
    for (name, source) in &built {
        copy2(source, &binaries.join(name))?;
        require(
            adapt::digest(&binaries.join(name))? == adapt::digest(source)?,
            format!("Copied binary differs: {name}"),
        )?;
    }
    let provenance_dir = output.join("provenance");
    mkdir_plain(&provenance_dir)?;
    let mut provenance: Vec<Value> = Vec::new();
    for inner in PROVENANCE {
        let target = provenance_dir.join(Path::new(inner).file_name().expect("file name"));
        copyfile(&frozen.join(inner), &target)?;
        require(
            Some(adapt::digest(&target)?.as_str()) == hashes.get(inner).and_then(Value::as_str),
            format!("Copied provenance differs: {inner}"),
        )?;
        provenance.push(object(vec![
            ("path", text_of(&target).into()),
            ("sha256", hashes.get(inner).cloned().unwrap_or(Value::Null)),
        ]));
    }
    copyfile(
        &lean_build.join("manifest.json"),
        &provenance_dir.join("lean-v8-build.json"),
    )?;
    provenance.push(record(&provenance_dir.join("lean-v8-build.json"))?);
    let notices = output.join("LICENSES");
    mkdir_plain(&notices)?;
    let mut notice_names: Vec<&str> = hashes
        .keys()
        .filter(|name| *name == "LICENSE" || name.starts_with("LICENSES/"))
        .collect();
    notice_names.sort();
    for inner in notice_names {
        let target = notices.join(Path::new(inner).file_name().expect("file name"));
        copyfile(&frozen.join(inner), &target)?;
        require(
            Some(adapt::digest(&target)?.as_str()) == hashes.get(inner).and_then(Value::as_str),
            format!("Copied notice differs: {inner}"),
        )?;
        provenance.push(object(vec![
            ("path", text_of(&target).into()),
            ("sha256", hashes.get(inner).cloned().unwrap_or(Value::Null)),
        ]));
    }
    report.set("provenance", Value::Array(provenance.clone()));
    let pinned = |name: &str| binary_record(&binaries.join(name));
    let bundle = object(vec![
        ("producer", pinned("fang-bundle-producer")?),
        ("checker", pinned("fang-bundle-check")?),
    ]);
    let mut signed = object(vec![
        ("producer", pinned("fang-signed-producer")?),
        ("checker", pinned("fang-signed-check")?),
    ]);
    if final_signed {
        signed
            .as_object_mut()
            .expect("object")
            .set("single_producer", pinned(SIGNED_SINGLE_PRODUCER)?);
    }
    // Round two's named route, when installed: the single-file exporter moves to fang-v8-tstp-named, and the
    // conjecture exporter to fang-goal-tstp-named, which is pinned as both goal_exporter and inputs_exporter. The
    // unnamed builds stay as fallbacks the route does not pin. Without the named builds nothing moves.
    let single = if built.contains_key(NAMED_SINGLE_EXPORTER) {
        NAMED_SINGLE_EXPORTER
    } else {
        "fang-v8-tstp"
    };
    let mut tstp: Object = [("exporter", pinned(single)?)].into_iter().collect();
    if built.contains_key("fang-bundle-tstp") {
        tstp.set("bundle_exporter", pinned("fang-bundle-tstp")?);
    }
    if built.contains_key(NAMED_GOAL_EXPORTER) {
        // Only the build with the inputs mode may be installed under this name; its usage line in the Lean map,
        // which the Lean build's usage stage checks against the binary, must list --inputs.
        let usage = executables
            .values()
            .find(|entry| {
                entry.get("installed_as").and_then(Value::as_str) == Some(NAMED_GOAL_EXPORTER)
            })
            .and_then(|entry| entry.get("usage"))
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string();
        let inputs = usage
            .split([' ', '|', '(', ')'])
            .any(|word| word == "--inputs");
        let hash = adapt::digest(&binaries.join(NAMED_GOAL_EXPORTER))?;
        require(
            inputs && !WITHOUT_INPUTS.iter().any(|prefix| hash.starts_with(prefix)),
            format!("{NAMED_GOAL_EXPORTER} is a build without the --inputs mode"),
        )?;
        tstp.set("goal_exporter", pinned(NAMED_GOAL_EXPORTER)?);
        tstp.set("inputs_exporter", pinned(NAMED_GOAL_EXPORTER)?);
    } else if built.contains_key("fang-goal-tstp") {
        tstp.set("goal_exporter", pinned("fang-goal-tstp")?);
    }
    let kernel_section = match &kernel {
        Some((kernel_root, _)) => {
            require(
                built.contains_key("fang-v8-witness"),
                "Kernel mode needs the witness binary",
            )?;
            let mut section = object(vec![
                ("witness", pinned("fang-v8-witness")?),
                (
                    "entry",
                    binary_record(&kernel_root.join("bin/fang-v8-kernel"))?,
                ),
                (
                    "installation",
                    record(&kernel_root.join("installation.json"))?,
                ),
                ("output_root", text_of(&kernel_root.join("run")).into()),
            ]);
            if built.contains_key(KERNEL_PRODUCER) {
                section
                    .as_object_mut()
                    .expect("object")
                    .set("producer", pinned(KERNEL_PRODUCER)?);
            }
            section
        }
        None => Value::Null,
    };
    let mut model: Object = [
        ("producer", pinned("fang-model-find")?),
        ("checker", pinned("fang-model-check")?),
    ]
    .into_iter()
    .collect();
    if built.contains_key("fang-model-tstp") {
        model.set("exporter", pinned("fang-model-tstp")?);
    }
    let mut binaries_sha256 = Object::new();
    let mut listed: Vec<PathBuf> = fs::read_dir(&binaries)
        .at(&binaries)?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .collect();
    listed.sort();
    for path in &listed {
        binaries_sha256.set(
            path.file_name()
                .expect("file name")
                .to_string_lossy()
                .into_owned(),
            adapt::digest(path)?,
        );
    }
    report.edit(|manifest| {
        manifest.set("bundle", bundle.clone());
        manifest.set("signed", signed.clone());
        manifest.set("tstp", Value::Object(tstp.clone()));
        manifest.set("model", Value::Object(model.clone()));
        manifest.set("status", "built-and-checked");
        manifest.set("completed_utc", utc_now());
        manifest.set("binaries_sha256", Value::Object(binaries_sha256));
    });
    report.set("sampled_peak_rss_kib", supervisor.peak_kib);
    report.set("stages", adapt::records(supervisor));
    let build_manifest = output.join("build-manifest.json");
    write_manifest(&build_manifest, &report.value())?;
    // cli_setup.py created bin/fang at this point; the launcher binary takes its place.
    let launcher = binaries.join("fang");
    copy2(&release.join(LAUNCHER_BINARY), &launcher)?;
    require(
        adapt::digest(&launcher)? == adapt::digest(&release.join(LAUNCHER_BINARY))?,
        "Copied binary differs: fang",
    )?;
    let (cnf, ground_fof) = match &options.older {
        Some(older) => older_profiles(
            &resolve(older)?,
            output,
            &launcher,
            Path::new(&toolchain),
            supervisor,
        )?,
        None => (Value::Null, Value::Null),
    };
    let mut all_provenance = vec![record(&build_manifest)?];
    all_provenance.extend(provenance);
    let mut config: Object = [
        ("schema", Value::from(capability::SCHEMA)),
        ("language", capability::LANGUAGE.into()),
        ("certificate_version", 8u64.into()),
        ("max_input_bytes", capability::MAX_BYTES.into()),
        (
            "max_certificate_bytes",
            capability::MAX_CERTIFICATE_BYTES.into(),
        ),
        ("launcher", binary_record(&launcher)?),
        ("engine", pinned("fang-v8-engine")?),
        ("checker", pinned("fang-v8-check")?),
        ("provenance", Value::Array(all_provenance)),
        ("bundle", bundle),
        ("signed", signed),
        ("tstp", Value::Object(tstp)),
        ("kernel", kernel_section),
        ("model", Value::Object(model)),
        ("cnf", cnf),
        ("ground_fof", ground_fof),
        ("per_run_verification", capability::per_run_value()),
        ("default_check", capability::DEFAULT_CHECK.into()),
    ]
    .into_iter()
    .collect();
    if named_engine {
        config.set("engine_preparation", "named");
    }
    capability::check_fields(&config).map_err(Error::Value)?;
    let capability_path = output.join("v8-capability.json");
    create_json(&capability_path, &Value::Object(config))?;
    require(
        installer_record()? == installer,
        "Build installer executable changed",
    )?;
    write_manifest(
        &output.join("installation-receipt.json"),
        &object(vec![
            ("status", "installed".into()),
            ("finished_utc", utc_now().into()),
            (
                "build_manifest_sha256",
                adapt::digest(&build_manifest)?.into(),
            ),
            ("capability_sha256", adapt::digest(&capability_path)?.into()),
            ("command", text_of(&launcher).into()),
            ("command_sha256", adapt::digest(&launcher)?.into()),
        ]),
    )?;
    Ok(launcher)
}

/// installation.directory_inventory(root): relative path -> SHA-256 of every file, refusing links and
/// nonregular members.
fn directory_inventory(root: &Path) -> Result<BTreeMap<String, String>> {
    let real = fs::symlink_metadata(root).is_ok_and(|metadata| metadata.is_dir());
    require(real, "Installed library must be a real directory")?;
    let mut result = BTreeMap::new();
    let mut paths = inventory::rglob(root);
    paths.sort_by_key(|path| inventory::path_key(path));
    for path in paths {
        let kind = fs::symlink_metadata(&path).at(&path)?.file_type();
        require(!kind.is_symlink(), "Installation contains a symlink")?;
        if kind.is_file() {
            result.insert(inventory::relative(&path, root), adapt::digest(&path)?);
        } else {
            require(kind.is_dir(), "Installation contains a nonregular member")?;
        }
    }
    Ok(result)
}

/// installation.py's exporter checks for a TSTP installation: both exporter sources are in the inventory, and
/// lean/tstp-sources.json is in it with schema fang-tstp-source-link-v2 and exactly those two sources at the
/// inventory's hashes. The CNF builder copies the two hashes without reading the record, so the check stays here.
fn verify_exporter_sources(frozen: &Path, sources: &Object) -> Result<()> {
    const NAMES: [&str; 2] = ["lean/TstpExport.lean", "lean/TstpMain.lean"];
    require(
        NAMES.iter().all(|name| sources.contains_key(name)),
        "TSTP installation is missing exporter source",
    )?;
    require(
        sources.contains_key("lean/tstp-sources.json"),
        "New TSTP installation is missing its exporter source record",
    )?;
    let path = frozen.join("lean/tstp-sources.json");
    let data = fs::read(&path).at(&path)?;
    let record = fang_supervisor::strict_json(&data)?;
    let linked = record.get("sources").and_then(Value::as_object);
    let ok = record.get("schema").and_then(Value::as_str) == Some("fang-tstp-source-link-v2")
        && linked.is_some_and(|linked| {
            linked.keys().collect::<BTreeSet<_>>() == NAMES.into_iter().collect::<BTreeSet<_>>()
                && NAMES
                    .iter()
                    .all(|name| linked.get(name).is_some() && linked.get(name) == sources.get(name))
        });
    require(
        ok,
        "Exporter source record differs from the installed source bytes",
    )
}

/// The older profiles' configuration files, written with worker-roles' builders after the checks
/// fof_setup.provision and installation.make_installation made. Returns the capability's `cnf` and
/// `ground_fof` sections.
fn older_profiles(
    older: &Path,
    output: &Path,
    launcher: &Path,
    toolchain: &Path,
    supervisor: &Supervisor,
) -> Result<(Value, Value)> {
    use fang_launcher::profile_cnf::installation::{self as cnf_installation, CnfInputs, Library};
    use fang_launcher::profile_ground_fof::capability::{
        self as fof_capability, GroundFofExporter, GroundFofInputs, GroundFofKernel,
        GroundFofToolchain,
    };
    let build_manifest = older.join("build-manifest.json");
    let build = read_json(&build_manifest)?;
    require(
        build.get("status").and_then(Value::as_str) == Some("built-and-checked"),
        "Finalized build receipt differs",
    )?;
    let frozen = older.join("source");
    let sources = build
        .get("source_sha256")
        .and_then(Value::as_object)
        .cloned()
        .unwrap_or_default();
    for (inner, expected) in sources.iter() {
        let path = frozen.join(inner);
        let regular = fs::symlink_metadata(&path).is_ok_and(|metadata| metadata.is_file());
        require(
            regular && Some(adapt::digest(&path)?.as_str()) == expected.as_str(),
            format!("Installed source changed before provisioning: {inner}"),
        )?;
    }
    verify_exporter_sources(&frozen, &sources)?;
    let bin = older.join("bin");
    let cnf_binaries = checked_binaries(
        &bin,
        &build,
        &["fang-engine", "fang-check", "fang-tstp-export"],
    )?;
    let proof_suite = PathBuf::from(text_field(&build, "proof_suite")?);
    let proof_receipt = checked_record(
        &std::path::absolute(&proof_suite).at(&proof_suite)?,
        build.get("proof_suite_sha256"),
    )?;
    let lean = toolchain.join("bin/lean");
    require(
        Some(sha256_file(&lean)?.as_str()) == build.get("lean_sha256").and_then(Value::as_str),
        "Lean differs from the older build",
    )?;
    let library_path =
        fs::canonicalize(older.join("proof-library")).at(&older.join("proof-library"))?;
    let files = directory_inventory(&library_path)?;
    let library_pins: BTreeMap<String, String> = build
        .get("library_sha256")
        .and_then(Value::as_object)
        .map(|table| {
            table
                .iter()
                .map(|(key, value)| {
                    (
                        key.to_string(),
                        value.as_str().unwrap_or_default().to_string(),
                    )
                })
                .collect()
        })
        .unwrap_or_default();
    require(files == library_pins, "Checked proof library changed")?;
    let library = Library {
        path: library_path.clone(),
        files_sha256: files,
    };
    let launcher_pin = binary_pin(launcher)?;
    let source_inventory: BTreeMap<String, String> = sources
        .iter()
        .map(|(key, value)| {
            (
                key.to_string(),
                value.as_str().unwrap_or_default().to_string(),
            )
        })
        .collect();
    let cnf_inputs = CnfInputs {
        launcher: launcher_pin.clone(),
        engine: cnf_binaries["fang-engine"].clone(),
        checker: cnf_binaries["fang-check"].clone(),
        lean: binary_pin(&fs::canonicalize(&lean).at(&lean)?)?,
        exporter: Some(cnf_binaries["fang-tstp-export"].clone()),
        source_inventory,
        proof_library: library.clone(),
        provenance: vec![pin(&fs::canonicalize(&build_manifest).at(&build_manifest)?)?],
    };
    let cnf_value = cnf_installation::build(&cnf_inputs).map_err(Error::Value)?;
    let cnf_path = output.join("cnf-installation.json");
    create_json(&cnf_path, &cnf_value)?;
    let cnf = object(vec![("installation", record(&cnf_path)?)]);
    let Some(fof) = build.get("fof") else {
        return Ok((cnf, Value::Null));
    };
    let fof_binaries = checked_binaries(
        &bin,
        fof,
        &[
            "fang-ground-fof-driver",
            "fang-fof-check",
            "fang-fof-tstp-export",
        ],
    )?;
    let info = fof.get("toolchain").cloned().unwrap_or(Value::Null);
    let toolchain_root = PathBuf::from(text_field(&info, "path")?);
    let inventory_path = PathBuf::from(text_field(&info, "inventory")?);
    let captured = read_json(&inventory_path)?;
    adapt::toolchain::verify(&toolchain_root, &captured, supervisor, "fof-provisioning")?;
    let absolute = |path: &Path| -> Result<Record> { pin(&std::path::absolute(path).at(path)?) };
    let absolute_binary =
        |path: &Path| -> Result<Pin> { binary_pin(&std::path::absolute(path).at(path)?) };
    let inventory_record = absolute(&inventory_path)?;
    require(
        Some(inventory_record.sha256.as_str())
            == info.get("inventory_sha256").and_then(Value::as_str),
        "Captured toolchain inventory changed",
    )?;
    let receipt = absolute(&build_manifest)?;
    let inputs = GroundFofInputs {
        launcher: launcher_pin,
        engine: fof_binaries["fang-ground-fof-driver"].clone(),
        checker: fof_binaries["fang-fof-check"].clone(),
        proof_library: library.clone(),
        receipts: vec![receipt.clone()],
        kernel: Some(GroundFofKernel {
            lean: absolute_binary(&toolchain_root.join("bin/lean"))?,
            library,
            receipt: receipt.clone(),
            toolchain: GroundFofToolchain {
                path: toolchain_root.clone(),
                inventory: inventory_record,
                receipt: receipt.clone(),
            },
        }),
        exporter: Some(GroundFofExporter {
            exporter: fof_binaries["fang-fof-tstp-export"].clone(),
            proof_receipt,
            build_receipt: receipt,
        }),
    };
    let fof_value = fof_capability::build(&inputs).map_err(Error::Value)?;
    let fof_path = output.join("ground-fof-capability.json");
    create_json(&fof_path, &fof_value)?;
    Ok((cnf, object(vec![("capability", record(&fof_path)?)])))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn named_engine_requires_an_unnamed_kernel_producer() {
        let mut produced = Object::new();
        assert!(!named_engine_route(&produced, true).unwrap());
        let entry = |binary: &str| {
            object(vec![
                ("package", "fang-saturation".into()),
                ("binary", binary.into()),
            ])
        };
        produced.set("fang-v8-engine", entry("fang-v3-single-named"));
        assert!(named_engine_route(&produced, false).unwrap());
        assert!(named_engine_route(&produced, true).is_err());
        produced.set(KERNEL_PRODUCER, entry("fang-v3-single-named"));
        assert!(named_engine_route(&produced, true).is_err());
        produced.set(KERNEL_PRODUCER, entry("fang-v3-single"));
        assert!(named_engine_route(&produced, true).unwrap());
    }

    #[test]
    fn final_signed_protocols_must_be_installed_together() {
        let mut produced = Object::new();
        let mut executables = Object::new();
        assert!(!final_signed_routes(&produced, &executables).unwrap());
        let producer = |name: &str| {
            object(vec![
                ("package", "fang-saturation".into()),
                ("binary", name.into()),
            ])
        };
        let checker = object(vec![
            ("root", "SignedBundleNativeV6Main".into()),
            ("installed_as", "fang-signed-check".into()),
        ]);
        for mask in 1..8 {
            produced = Object::new();
            executables = Object::new();
            if mask & 1 != 0 {
                produced.set(SIGNED_SINGLE_PRODUCER, producer("fang-v3-signed-named"));
            }
            if mask & 2 != 0 {
                produced.set(
                    "fang-signed-producer",
                    producer("fang-v3-cited-bundle-final"),
                );
            }
            if mask & 4 != 0 {
                executables.set("fang-signed-bundle-native-v6", checker.clone());
            }
            assert_eq!(
                final_signed_routes(&produced, &executables).is_ok(),
                mask == 7
            );
        }
        produced.set(SIGNED_SINGLE_PRODUCER, producer("fang-v3-signed-bundle"));
        assert!(final_signed_routes(&produced, &executables).is_err());
        produced.set(SIGNED_SINGLE_PRODUCER, producer("fang-v3-signed-named"));
        executables.set("legacy-checker", checker);
        assert!(final_signed_routes(&produced, &executables).is_err());
    }

    #[test]
    fn provisioning_requires_complete_unchanged_binary_receipts() {
        let root = adapt::make_temp_dir(&std::env::temp_dir(), "fang-provision-binaries-").unwrap();
        for names in [
            ["fang-engine", "fang-check", "fang-tstp-export"],
            [
                "fang-ground-fof-driver",
                "fang-fof-check",
                "fang-fof-tstp-export",
            ],
        ] {
            let mut hashes = Object::new();
            for name in names {
                fs::write(root.join(name), b"original").unwrap();
                hashes.set(name, fang_hash::sha256_hex(b"original"));
            }
            let receipt = object(vec![("binaries_sha256", Value::Object(hashes.clone()))]);
            assert_eq!(checked_binaries(&root, &receipt, &names).unwrap().len(), 3);
            for invalid in [Value::Null, Value::Object(Object::new())] {
                assert!(checked_binaries(&root, &invalid, &names).is_err());
                let receipt = object(vec![("binaries_sha256", invalid)]);
                assert!(checked_binaries(&root, &receipt, &names).is_err());
            }
            for name in names {
                fs::write(root.join(name), b"modified").unwrap();
                assert!(checked_binaries(&root, &receipt, &names).is_err());
                fs::write(root.join(name), b"original").unwrap();
                let mut malformed = hashes.clone();
                malformed.set(name, "not-a-sha256");
                assert!(
                    checked_binaries(
                        &root,
                        &object(vec![("binaries_sha256", Value::Object(malformed))]),
                        &names
                    )
                    .is_err()
                );
            }
            hashes.set("unexpected", fang_hash::sha256_hex(b"original"));
            assert!(
                checked_binaries(
                    &root,
                    &object(vec![("binaries_sha256", Value::Object(hashes))]),
                    &names
                )
                .is_err()
            );
        }
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn provisioning_rejects_changed_or_unrecorded_proof_receipt() {
        let root = adapt::make_temp_dir(&std::env::temp_dir(), "fang-provision-proof-").unwrap();
        let path = root.join("proof-suite.json");
        fs::write(&path, b"original proof receipt").unwrap();
        let expected = Value::from(fang_hash::sha256_hex(b"original proof receipt"));
        assert!(checked_record(&path, Some(&expected)).is_ok());
        assert!(checked_record(&path, None).is_err());
        fs::write(&path, b"modified proof receipt").unwrap();
        assert!(checked_record(&path, Some(&expected)).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn installed_binary_pin_is_verified_and_rejects_changed_bytes() {
        use fang_launcher::v8::verify::{V8_MESSAGES, Verifier};

        let root = adapt::make_temp_dir(&std::env::temp_dir(), "fang-install-pin-").unwrap();
        let path = root.join("binary");
        fs::write(&path, b"installed binary").unwrap();
        let pin = binary_pin(&path).unwrap();
        assert_eq!(pin.sha256, fang_hash::sha256_hex(b"installed binary"));
        assert!(pin.chunked_sha256.is_some());
        let mut verifier = Verifier::new([pin.clone()], V8_MESSAGES);
        verifier.verify(&[&path]).unwrap();
        verifier.check_identities().unwrap();

        fs::write(&path, b"modified binary").unwrap();
        let mut verifier = Verifier::new([pin], V8_MESSAGES);
        assert!(verifier.verify(&[&path]).is_err());
        fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn shell_quote_follows_shlex() {
        assert_eq!(shell_quote("/var/tmp/x-1/bin"), "/var/tmp/x-1/bin");
        assert_eq!(shell_quote("a b"), "'a b'");
        assert_eq!(shell_quote("it's"), "'it'\"'\"'s'");
        assert_eq!(shell_quote(""), "''");
    }
}
