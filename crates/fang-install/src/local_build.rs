// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Build the older profiles from a fresh, checked source snapshot: the CNF command's engine, checker and TSTP
//! exporter, and with `--fof` the bounded ground-FOF driver, checker and exporter. The specification is
//! tools/build-local.py with tools/build-fof-local.py, and the build side of tools/fof_setup.py and
//! tools/fof_tstp_setup.py.
//!
//! The build ends at build-manifest.json. The configuration files of the two profiles are written later, by
//! fang-build-v8-local --older, because they pin the launcher, which exists only in the version-8
//! installation; so this build writes no installation.json, fof-capability.json, receipts or launchers.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use fang_json::{Object, Value};
use fang_supervisor::Supervisor;
use fang_supervisor::guard::Worker;

use crate::adapt::{self, StageCall, toolchain};
use crate::common::{
    At, Error, Result, compact, copy2, copyfile, mkdir, mkdir_plain, object, read_json, require,
    resolve, sha256_file, strings, text_of, utc_now, write_manifest,
};
use crate::inventory::{self, installer_record, which};
use crate::report::{self, Report};

pub const LEAVES: [&str; 4] = [
    "ground-fof-core",
    "ground-fof-frontend",
    "ground-fof-search",
    "ground-fof-versioned",
];
pub const AUDIT_MODULES: [&str; 5] = [
    "Fang.FOF.Audit",
    "Fang.FOF.GroundFormula",
    "Fang.FOF.FOFDiagnostics",
    "Fang.FOF.GrammarAudit",
    "Fang.FOF.CompletenessAudit",
];
pub const TEXT_THEOREM: &str = "Fang.FofTstpExport.RenderProof.decoded_render_checked_text";
pub const TEXT_MODULE: &str = "Fang.FOF.TSTP.Audit";
const ALLOWED_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];
const SCOPE: &str =
    "Local executable build and general independent Lean proof suite; no per-instance UNSAT claim";
const FOF_SCOPE: &str = "Bounded ground-FOF status and TSTP; original-byte checking; no general quantified FOF, equality or SAT acceptance";
const ALLOWED_ENVIRONMENT: [&str; 12] = [
    "PATH",
    "HOME",
    "USER",
    "RUSTUP_HOME",
    "CARGO_HOME",
    "TMPDIR",
    "TMP",
    "TEMP",
    "LANG",
    "LC_ALL",
    "LC_CTYPE",
    "XDG_CACHE_HOME",
];

pub struct Options {
    pub root: PathBuf,
    pub out: PathBuf,
    pub lean_tools: PathBuf,
    pub cargo: String,
    pub fof: bool,
}

fn strings_of(value: Option<&Value>) -> Vec<String> {
    value
        .and_then(Value::as_array)
        .map(|items| {
            items
                .iter()
                .filter_map(|item| item.as_str().map(str::to_string))
                .collect()
        })
        .unwrap_or_default()
}

/// fof_tstp_setup.read_inventory(frozen).
fn read_inventory(frozen: &Path) -> Result<Value> {
    let value = read_json(&frozen.join("tools/fof_proof_inventory.json"))?;
    let differs = || Error::Value("Required ground-FOF proof inventory differs".to_string());
    let object = value.as_object().ok_or_else(differs)?;
    let keys: BTreeSet<&str> = object.keys().collect();
    let modules = strings_of(object.get("modules"));
    let audits = object
        .get("audits")
        .and_then(Value::as_object)
        .ok_or_else(differs)?;
    let unique = |items: &[String]| items.iter().collect::<BTreeSet<_>>().len() == items.len();
    let ok = keys == BTreeSet::from(["schema", "modules", "audits"])
        && object.get("schema").and_then(Value::as_str)
            == Some("fang-ground-fof-proof-inventory-v1")
        && unique(&modules)
        && audits
            .keys()
            .all(|module| modules.iter().any(|known| known == module))
        && audits
            .values()
            .all(|names| unique(&strings_of(Some(names))))
        && strings_of(audits.get(TEXT_MODULE))
            .iter()
            .any(|name| name == TEXT_THEOREM);
    if ok { Ok(value) } else { Err(differs()) }
}

fn audit_rows(proof: &Value) -> Vec<(String, String, Vec<String>)> {
    proof
        .get("axiom_audits")
        .and_then(Value::as_array)
        .map(|rows| {
            rows.iter()
                .map(|row| {
                    (
                        row.get("module")
                            .and_then(Value::as_str)
                            .unwrap_or_default()
                            .to_string(),
                        row.get("declaration")
                            .and_then(Value::as_str)
                            .unwrap_or_default()
                            .to_string(),
                        strings_of(row.get("axioms")),
                    )
                })
                .collect()
        })
        .unwrap_or_default()
}

/// fof_tstp_setup.check_proofs(frozen, proof).
fn check_tstp_proofs(frozen: &Path, proof: &Value) -> Result<()> {
    let expected = read_inventory(frozen)?;
    let audits = expected
        .get("audits")
        .and_then(Value::as_object)
        .cloned()
        .unwrap_or_default();
    let wanted: BTreeSet<(String, String)> = audits
        .iter()
        .flat_map(|(module, names)| {
            strings_of(Some(names))
                .into_iter()
                .map(move |name| (module.to_string(), name))
        })
        .collect();
    let rows = audit_rows(proof);
    let actual: Vec<(String, String)> = rows
        .iter()
        .map(|(module, name, _)| (module.clone(), name.clone()))
        .collect();
    let mut completed = strings_of(proof.get("completed_modules"));
    completed.sort();
    let mut modules = strings_of(expected.get("modules"));
    modules.sort();
    let ok = proof.get("status").and_then(Value::as_str) == Some("passed")
        && completed == modules
        && actual.len() == wanted.len()
        && actual.iter().cloned().collect::<BTreeSet<_>>() == wanted
        && proof.get("declared_axiom_audits").and_then(Value::as_u64) == Some(wanted.len() as u64);
    require(
        ok,
        "Required combined proof inventory did not pass or an audit differs",
    )?;
    require(
        rows.iter().all(|(_, _, axioms)| {
            axioms
                .iter()
                .all(|axiom| ALLOWED_AXIOMS.contains(&axiom.as_str()))
        }),
        "Unexpected FOF theorem axiom",
    )
}

/// fof_setup.check_proofs(frozen, proof): returns the fixed audits of tools/fof_audits.json.
fn check_fof_proofs(frozen: &Path, proof: &Value) -> Result<Value> {
    check_tstp_proofs(frozen, proof)?;
    let expected = read_json(&frozen.join("tools/fof_audits.json"))?;
    let table = expected.as_object().cloned().unwrap_or_default();
    let modules: BTreeSet<&str> = table.keys().collect();
    let total: usize = table
        .values()
        .map(|names| strings_of(Some(names)).len())
        .sum();
    let unique = table.values().all(|names| {
        let names = strings_of(Some(names));
        names.iter().collect::<BTreeSet<_>>().len() == names.len()
    });
    require(
        modules == BTreeSet::from(AUDIT_MODULES)
            && total == 64
            && unique
            && proof.get("status").and_then(Value::as_str) == Some("passed"),
        "The required combined FOF proof inventory did not pass",
    )?;
    let rows = audit_rows(proof);
    for (module, names) in table.iter() {
        let names: BTreeSet<String> = strings_of(Some(names)).into_iter().collect();
        let selected: Vec<&(String, String, Vec<String>)> =
            rows.iter().filter(|row| row.0 == module).collect();
        let declared: BTreeSet<String> = selected.iter().map(|row| row.1.clone()).collect();
        require(
            selected.len() == names.len() && declared == names,
            format!("Required FOF theorem audit differs: {module}"),
        )?;
        require(
            selected.iter().all(|row| {
                row.2
                    .iter()
                    .all(|axiom| ALLOWED_AXIOMS.contains(&axiom.as_str()))
            }),
            "Unexpected FOF theorem axiom",
        )?;
    }
    Ok(expected)
}

/// fof_setup.capture_toolchain(root, check).
pub fn capture_toolchain(root: &Path, supervisor: &Supervisor, stage: &str) -> Result<Value> {
    let real = root.is_absolute() && !root.is_symlink() && root.is_dir();
    require(
        real,
        "Lean toolchain root must be an absolute real directory",
    )?;
    let before = toolchain::tree(root, supervisor, stage)?;
    let mut result = Object::new();
    for (inner, identity) in &before {
        adapt::check_stage(supervisor, stage)?;
        let path = root.join(inner);
        let kind = identity.mode & 0o170000;
        if kind == 0o040000 {
            continue;
        }
        let mut record = if kind == 0o120000 {
            let resolved = fs::canonicalize(&path).at(&path)?;
            require(
                resolved.starts_with(root) && resolved.is_file(),
                "Lean toolchain symlink escapes its root",
            )?;
            let target = fs::read_link(&path).at(&path)?;
            let mut record: Object = [
                ("kind", Value::from("symlink")),
                ("target", text_of(&target).into()),
                ("resolved", inventory::relative(&resolved, root).into()),
            ]
            .into_iter()
            .collect();
            if let Value::Object(file) = toolchain::stable_file(&resolved, supervisor, stage)? {
                for (key, value) in file.iter() {
                    record.set(key, value.clone());
                }
            }
            record
        } else if kind == 0o100000 {
            let mut record: Object = [("kind", Value::from("file"))].into_iter().collect();
            if let Value::Object(file) = toolchain::stable_file(&path, supervisor, stage)? {
                for (key, value) in file.iter() {
                    record.set(key, value.clone());
                }
            }
            record
        } else {
            return Err(Error::Value(
                "Nonregular Lean toolchain dependency".to_string(),
            ));
        };
        result.set(inner.as_str(), Value::Object(std::mem::take(&mut record)));
    }
    require(
        toolchain::tree(root, supervisor, stage)? == before,
        "Lean toolchain changed during capture",
    )?;
    let result = Value::Object(result);
    toolchain::verify(root, &result, supervisor, stage)?;
    Ok(result)
}

fn stable_sha256(path: &Path, supervisor: &Supervisor, stage: &str) -> Result<String> {
    Ok(toolchain::stable_file(path, supervisor, stage)?
        .get("sha256")
        .and_then(Value::as_str)
        .unwrap_or_default()
        .to_string())
}

pub fn main(options: &Options, worker: Option<&Worker>) -> Result<i32> {
    require(
        cfg!(target_os = "linux"),
        "Local setup currently requires Linux or WSL",
    )?;
    let root = resolve(&options.root)?;
    let output = resolve(&options.out)?;
    mkdir(&output, 0o700, true, false)?;
    let setup_seconds: u64 = if options.fof { 2400 } else { 1800 };
    let mut supervisor = adapt::supervisor(setup_seconds as f64, 4096, 16 << 20, 4 << 30)?;
    let report = Report::new(vec![
        ("status", "building".into()),
        ("started_utc", utc_now().into()),
        ("scope", SCOPE.into()),
        (
            "limits",
            object(vec![
                ("wall_seconds", setup_seconds.into()),
                ("sampled_tree_rss_mib", 4096u64.into()),
            ]),
        ),
        ("stages", Value::Array(Vec::new())),
    ]);
    mkdir_plain(&output.join("stages"))?;
    let failure_path = output.join("setup-failure.json");
    report::on_cancel(worker, &report, failure_path.clone(), |object| {
        object.set("reason", "External cancellation");
    });
    report.set(
        "inherited_descriptors",
        supervisor.inherited_descriptors_json(),
    );
    let result = build(options, &root, &output, &report, &mut supervisor);
    match result {
        Ok(manifest_path) => {
            println!(
                "{}",
                compact(&object(vec![
                    ("status", "built-and-checked".into()),
                    ("build_manifest", text_of(&manifest_path).into())
                ]))
            );
            Ok(0)
        }
        Err(error) => {
            let failure = object(vec![
                ("status", "failed".into()),
                ("reason", error.message().into()),
                ("stages", adapt::records(&supervisor)),
                ("sampled_peak_rss_kib", supervisor.peak_kib.into()),
            ]);
            let mut written = Ok(());
            report::finish(worker, || written = write_manifest(&failure_path, &failure));
            written?;
            eprintln!("Setup failed: {}", error.message());
            Ok(1)
        }
    }
}

fn build(
    options: &Options,
    root: &Path,
    output: &Path,
    report: &Report,
    supervisor: &mut Supervisor,
) -> Result<PathBuf> {
    let frozen = output.join("source");
    let mut environment: std::collections::BTreeMap<String, String> = ALLOWED_ENVIRONMENT
        .iter()
        .filter_map(|key| {
            std::env::var(key)
                .ok()
                .map(|value| (key.to_string(), value))
        })
        .collect();
    environment.insert("CARGO_NET_OFFLINE".into(), "true".into());
    environment.insert("CARGO_BUILD_JOBS".into(), "2".into());
    environment.insert("LEAN_NUM_THREADS".into(), "1".into());
    let tools = resolve(&options.lean_tools)?;
    let path = environment.get("PATH").cloned().unwrap_or_default();
    environment.insert("PATH".into(), format!("{}:{path}", text_of(&tools)));
    let lean = tools.join("lean");
    let lake = tools.join("lake");
    let cargo = which(&options.cargo);
    report.set(
        "declared_build_environment",
        Value::Object(
            environment
                .iter()
                .map(|(key, value)| (key.clone(), Value::from(value.as_str())))
                .collect(),
        ),
    );
    let stage_environment = adapt::environment(&environment)?;
    let stages = output.join("stages");
    let fof = options.fof;
    let run = |supervisor: &mut Supervisor, stage: &str, command: Vec<String>| -> Result<String> {
        let result = adapt::run(
            supervisor,
            StageCall {
                name: stage,
                command,
                directory: stages.join(stage),
                run_root: output,
                environment: Some(&stage_environment),
                stdout_limit: None,
                cwd: None,
            },
        );
        report.set("stages", adapt::records(supervisor));
        let done = result?;
        let classified = done
            .record
            .to_json()
            .get("classification")
            .and_then(Value::as_str)
            .map(str::to_string);
        if adapt::exit_code(&done) != Some(0) || (fof && classified.as_deref() != Some("completed"))
        {
            return Err(Error::Runtime(format!(
                "{stage} failed; see {}",
                text_of(&stages.join(stage))
            )));
        }
        let text = String::from_utf8(done.stdout)
            .map_err(|error| Error::Value(format!("UnicodeDecodeError: {error}")))?;
        Ok(text.trim_matches(crate::scan::py_space).to_string())
    };
    let cargo = match cargo {
        Some(cargo) if lean.is_file() && lake.is_file() => cargo,
        _ => {
            return Err(Error::Value(
                "Install the pinned Rust and Lean toolchains before setup".to_string(),
            ));
        }
    };
    let installer = installer_record()?;
    report.set("installer", installer.clone());
    let source_sha256 = inventory::snapshot(root, &frozen, supervisor)?;
    report.set("source_sha256", Value::Object(source_sha256.clone()));
    let link = read_json(&frozen.join("lean/tstp-sources.json"))?;
    require(
        link.get("schema").and_then(Value::as_str) == Some("fang-tstp-source-link-v2"),
        "Missing reviewed TSTP source-link record",
    )?;
    let linked = link
        .get("sources")
        .and_then(Value::as_object)
        .cloned()
        .unwrap_or_default();
    require(
        linked.keys().collect::<BTreeSet<_>>()
            == BTreeSet::from(["lean/TstpExport.lean", "lean/TstpMain.lean"]),
        "Incomplete TSTP source-link record",
    )?;
    for (source, expected) in linked.iter() {
        require(
            Some(sha256_file(&frozen.join(source))?.as_str()) == expected.as_str(),
            "Compiled exporter differs from the reviewed source bytes",
        )?;
    }
    report.set("tstp_source_link", link.clone());
    let toolchain_file = fs::read_to_string(frozen.join("rust-toolchain.toml"))
        .at(&frozen.join("rust-toolchain.toml"))?;
    let rust_toml =
        fang_toml::parse(&toolchain_file).map_err(|error| Error::Value(error.to_string()))?;
    let rust_version = rust_toml
        .get("toolchain")
        .and_then(|table| table.get("channel"))
        .and_then(Value::as_str)
        .ok_or_else(|| Error::Key("'channel'".to_string()))?
        .to_string();
    let lean_pin = fs::read_to_string(frozen.join("lean/lean-toolchain"))
        .at(&frozen.join("lean/lean-toolchain"))?;
    let lean_version = lean_pin
        .trim_matches(crate::scan::py_space)
        .rsplit_once(":v")
        .map(|(_, version)| version.to_string())
        .ok_or_else(|| Error::Os {
            class: "IndexError",
            message: "list index out of range".to_string(),
        })?;
    let cargo_prefix = vec![cargo.clone(), format!("+{rust_version}")];
    let with = |base: &[String], extra: &[&str]| -> Vec<String> {
        base.iter()
            .cloned()
            .chain(extra.iter().map(|item| item.to_string()))
            .collect()
    };
    let cargo_version = run(
        supervisor,
        "cargo-version",
        with(&cargo_prefix, &["--version"]),
    )?;
    report.set("cargo_version", cargo_version.as_str());
    let lean_text = text_of(&lean);
    let lean_reported = run(
        supervisor,
        "lean-version",
        vec![lean_text.clone(), "--version".into()],
    )?;
    report.set("lean_version", lean_reported.as_str());
    require(
        cargo_version.starts_with(&format!("cargo {rust_version} ")),
        "Cargo version differs from the pinned toolchain",
    )?;
    require(
        lean_reported.contains(&format!("version {lean_version},")),
        "Lean version differs from the pinned toolchain",
    )?;
    report.set("lean_sha256", sha256_file(&lean)?);
    let fof_context = if fof {
        let toolchain_root = tools
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| tools.clone());
        let captured = capture_toolchain(&toolchain_root, supervisor, "fof-toolchain-capture")?;
        let inventory_path = output.join("toolchain-inventory.json");
        write_manifest(&inventory_path, &captured)?;
        Some((
            toolchain_root,
            captured,
            inventory_path,
            stable_sha256(&lean, supervisor, "fof-toolchain-capture")?,
            stable_sha256(&lake, supervisor, "fof-toolchain-capture")?,
        ))
    } else {
        None
    };
    let manifest_path = text_of(&frozen.join("Cargo.toml"));
    let target = text_of(&output.join("rust-target"));
    let cargo_args = [
        "--manifest-path",
        &manifest_path,
        "--locked",
        "--offline",
        "--target-dir",
        &target,
    ];
    run(
        supervisor,
        "rust-tests",
        with(&with(&cargo_prefix, &["test"]), &cargo_args),
    )?;
    run(
        supervisor,
        "rust-build",
        with(&with(&cargo_prefix, &["build", "--release"]), &cargo_args),
    )?;
    let lake_text = text_of(&lake);
    let lean_project = text_of(&frozen.join("lean"));
    run(
        supervisor,
        "lean-checker-build",
        vec![
            lake_text.clone(),
            "-d".into(),
            lean_project.clone(),
            "build".into(),
            "fang-check".into(),
            "fang-tstp-export".into(),
        ],
    )?;
    if fof {
        let fof_target = text_of(&output.join("fof-rust-target"));
        for name in LEAVES {
            let crate_manifest = text_of(&frozen.join("crates").join(name).join("Cargo.toml"));
            let leaf = [
                "--manifest-path",
                crate_manifest.as_str(),
                "--locked",
                "--offline",
                "--target-dir",
                fof_target.as_str(),
            ];
            run(
                supervisor,
                &format!("{name}-tests"),
                with(&with(&cargo_prefix, &["test"]), &leaf),
            )?;
            if name == "ground-fof-versioned" {
                run(
                    supervisor,
                    "fof-driver-clippy",
                    with(
                        &with(&with(&cargo_prefix, &["clippy", "--all-targets"]), &leaf),
                        &["--", "-D", "warnings"],
                    ),
                )?;
                run(
                    supervisor,
                    "fof-driver-build",
                    with(
                        &with(
                            &cargo_prefix,
                            &["build", "--release", "--bin", "fang-ground-fof-driver"],
                        ),
                        &leaf,
                    ),
                )?;
            }
        }
        run(
            supervisor,
            "fof-checker-build",
            vec![
                lake_text.clone(),
                "-d".into(),
                lean_project.clone(),
                "build".into(),
                "fang-fof-check".into(),
                "fang-fof-tstp-export".into(),
            ],
        )?;
    }
    let proof_path = output.join("proof-suite").join("manifest.json");
    let mut suite = vec![
        text_of(&inventory::sibling("fang-check-suite")?),
        text_of(&frozen),
        lean_text.clone(),
        "--out".into(),
        text_of(&output.join("proof-suite")),
    ];
    if fof {
        suite.push("--with-tstp".into());
    }
    run(supervisor, "lean-proof-suite", suite)?;
    let proof = read_json(&proof_path)?;
    let completed = strings_of(proof.get("completed_modules"));
    require(
        proof.get("status").and_then(Value::as_str) == Some("passed")
            && completed
                .iter()
                .any(|name| name == "Fang.FrontendSoundness")
            && completed.iter().any(|name| name == "Fang.FrontendComplete"),
        "The required independent proof suite did not pass",
    )?;
    let fof_audits = if fof {
        Some(check_fof_proofs(&frozen, &proof)?)
    } else {
        None
    };
    let library = output.join("proof-library");
    let native = PathBuf::from(
        proof
            .get("native_project")
            .and_then(Value::as_str)
            .unwrap_or_default(),
    );
    let library_sha256 = proof
        .get("build_output_sha256")
        .and_then(Value::as_object)
        .cloned()
        .unwrap_or_default();
    for (inner, expected) in library_sha256.iter() {
        let source = native.join(inner);
        require(
            !source.is_symlink() && Some(sha256_file(&source)?.as_str()) == expected.as_str(),
            "Checked library changed",
        )?;
        let destination = library.join(inner);
        if let Some(parent) = destination.parent() {
            mkdir(parent, 0o777, true, true)?;
        }
        copyfile(&source, &destination)?;
        require(
            Some(sha256_file(&destination)?.as_str()) == expected.as_str(),
            "Copied checked library differs",
        )?;
    }
    let binaries = output.join("bin");
    mkdir_plain(&binaries)?;
    for (source, name) in [
        (output.join("rust-target/release/fang"), "fang-engine"),
        (frozen.join("lean/.lake/build/bin/fang-check"), "fang-check"),
        (
            frozen.join("lean/.lake/build/bin/fang-tstp-export"),
            "fang-tstp-export",
        ),
    ] {
        copy2(&source, &binaries.join(name))?;
    }
    if let (
        Some((toolchain_root, captured, inventory_path, lean_sha256, lake_sha256)),
        Some(fixed),
    ) = (&fof_context, &fof_audits)
    {
        let check = "fof-build-finalization";
        let mut fof_binaries = Object::new();
        for (original, name) in [
            (
                output.join("fof-rust-target/release/fang-ground-fof-driver"),
                "fang-ground-fof-driver",
            ),
            (
                frozen.join("lean/.lake/build/bin/fang-fof-check"),
                "fang-fof-check",
            ),
            (
                frozen.join("lean/.lake/build/bin/fang-fof-tstp-export"),
                "fang-fof-tstp-export",
            ),
        ] {
            let expected = stable_sha256(&original, supervisor, check)?;
            copy2(&original, &binaries.join(name))?;
            require(
                stable_sha256(&binaries.join(name), supervisor, check)? == expected,
                "Copied FOF binary differs",
            )?;
        }
        toolchain::verify(toolchain_root, captured, supervisor, check)?;
        require(
            stable_sha256(&toolchain_root.join("bin/lean"), supervisor, check)? == *lean_sha256
                && stable_sha256(&toolchain_root.join("bin/lake"), supervisor, check)?
                    == *lake_sha256,
            "Lean build executable changed",
        )?;
        for name in [
            "fang-ground-fof-driver",
            "fang-fof-check",
            "fang-fof-tstp-export",
        ] {
            fof_binaries.set(
                name,
                stable_sha256(&binaries.join(name), supervisor, check)?,
            );
        }
        let general = read_inventory(&frozen)?;
        let general_audits: usize = general
            .get("audits")
            .and_then(Value::as_object)
            .map(|audits| {
                audits
                    .values()
                    .map(|names| strings_of(Some(names)).len())
                    .sum()
            })
            .unwrap_or(0);
        let entries = captured.as_object().map_or(0, Object::len);
        report.set(
            "fof",
            object(vec![
                ("scope", FOF_SCOPE.into()),
                ("binaries_sha256", Value::Object(fof_binaries)),
                (
                    "toolchain",
                    object(vec![
                        ("path", text_of(toolchain_root).into()),
                        ("inventory", text_of(inventory_path).into()),
                        (
                            "inventory_sha256",
                            stable_sha256(inventory_path, supervisor, check)?.into(),
                        ),
                        ("entries", (entries as u64).into()),
                        ("verified_before_and_after", true.into()),
                        ("lean_sha256", lean_sha256.as_str().into()),
                        ("lake_sha256", lake_sha256.as_str().into()),
                    ]),
                ),
                ("fixed_audits", fixed.clone()),
                (
                    "general_modules",
                    (strings_of(general.get("modules")).len() as u64).into(),
                ),
                ("general_audits", (general_audits as u64).into()),
                (
                    "exporter",
                    object(vec![
                        ("theorem", TEXT_THEOREM.into()),
                        (
                            "inventory_sha256",
                            stable_sha256(
                                &frozen.join("tools/fof_proof_inventory.json"),
                                supervisor,
                                check,
                            )?
                            .into(),
                        ),
                    ]),
                ),
            ]),
        );
    }
    copy_licenses(&frozen.join("LICENSES"), &output.join("LICENSES"))?;
    copy2(&frozen.join("LICENSE"), &output.join("LICENSE"))?;
    let recorded: Vec<String> = {
        let mut names: Vec<String> = source_sha256.keys().map(str::to_string).collect();
        names.sort();
        names
    };
    for checked_root in [root, frozen.as_path()] {
        require(
            inventory::inventory_names(checked_root, supervisor, "final-source-inventory")?
                == recorded,
            "Source inventory changed while setup ran",
        )?;
    }
    for (inner, expected) in source_sha256.iter() {
        require(
            Some(sha256_file(&frozen.join(inner))?.as_str()) == expected.as_str()
                && Some(sha256_file(&root.join(inner))?.as_str()) == expected.as_str(),
            format!("Source changed while setup ran: {inner}"),
        )?;
    }
    require(
        installer_record()? == installer,
        "Build installer executable changed",
    )?;
    let mut binaries_sha256 = Object::new();
    for name in ["fang-engine", "fang-check", "fang-tstp-export"] {
        binaries_sha256.set(name, sha256_file(&binaries.join(name))?);
    }
    report.set("status", "built-and-checked");
    report.set("proof_suite", text_of(&proof_path));
    report.set("proof_suite_sha256", sha256_file(&proof_path)?);
    report.set("library_sha256", Value::Object(library_sha256));
    report.set("binaries_sha256", Value::Object(binaries_sha256));
    report.set("completed_utc", utc_now());
    report.set("sampled_peak_rss_kib", supervisor.peak_kib);
    report.set("stages", adapt::records(supervisor));
    let provenance = output.join("build-manifest.json");
    write_manifest(&provenance, &report.value())?;
    Ok(provenance)
}

/// `shutil.copytree(frozen / "LICENSES", output / "LICENSES")`: a new tree, files through copy2.
fn copy_licenses(source: &Path, target: &Path) -> Result<()> {
    mkdir(target, 0o777, true, false)?;
    let mut entries: Vec<PathBuf> = fs::read_dir(source)
        .at(source)?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .collect();
    entries.sort();
    for path in entries {
        let destination = target.join(path.file_name().expect("entry name"));
        if path.is_dir() {
            copy_licenses(&path, &destination)?
        } else {
            copy2(&path, &destination)?
        }
    }
    Ok(())
}

/// The fixed strings of tools/fof_tstp_setup.py and fof_setup.py the version-8 installer checks again.
pub fn fof_strings() -> Value {
    strings(&[TEXT_THEOREM.to_string(), TEXT_MODULE.to_string()])
}
