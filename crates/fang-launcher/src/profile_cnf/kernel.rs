// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The CNF profile's fresh kernel replay: a port of tools/fang_szs/kernel.py.
//!
//! The pinned checker exports the replay module, `protocol::fixed_replay` keeps only its constructor data, the
//! decomposition (`decompose`) runs as the launcher's internal stage `cnf-decompose` in a bounded child, and the
//! fixed audit is built here from the captured bytes. The source and the certificate cannot choose a proof
//! command. Without Python helpers there is no helper pin to check; the launcher pin covers the generator.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::fs;
use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
use std::path::Path;
use std::process::ExitCode;

use fang_json::{Object, Value};
use fang_supervisor::{Fault, Snapshot, Supervisor, child_environment};

use crate::older::{INTERNAL, error, python_utf8, run_stage};
use crate::profile_cnf::decompose::{self as generator, GENERATOR, MODULES};
use crate::profile_cnf::installation::{binary, digest_file};
use crate::profile_cnf::protocol::{completed_contract, exact_axioms, fixed_replay};
use fang_kernel_workspace::KernelWorkspace;

/// The internal stage that runs `decompose::decompose`.
pub const STAGE: &str = "cnf-decompose";
const SCOPE: &str = "Fresh original-byte kernel instance; no SAT or search-completeness proof";

fn check(supervisor: &Supervisor) -> impl FnMut() -> Result<(), fang_supervisor::Failure> + '_ {
    move || crate::older::check(supervisor)
}

fn verify_pair(
    supervisor: &Supervisor,
    source: &Snapshot,
    certificate: &Snapshot,
) -> Result<(), Fault> {
    source.verify(&mut check(supervisor))?;
    certificate.verify(&mut check(supervisor))
}

/// `verify`: export the replay, decompose it in a fresh native workspace, compile every module and the fixed
/// audit, and return the `kernel_check` record. `storage` is the run record's `kernel_storage` object.
pub fn verify(
    supervisor: &mut Supervisor,
    config: &Value,
    run_root: &Path,
    source: &Snapshot,
    certificate: &Snapshot,
    storage: &mut Object,
) -> Result<Value, Fault> {
    verify_pair(supervisor, source, certificate)?;
    let command: Vec<OsString> = vec![
        binary(config, "checker").into(),
        "--emit-replay".into(),
        source.argument().into(),
        certificate.argument().into(),
    ];
    let output = run_stage(
        supervisor,
        "export",
        &command,
        &run_root.join("export"),
        run_root,
        None,
        None,
        None,
    )?;
    if completed_contract(&output)? != 0 || !output.stderr.is_empty() {
        return Err(error("Replay exporter failed", "export"));
    }
    let replay = fixed_replay(&output.stdout, &source.data, &certificate.data)?;
    let mut workspace = KernelWorkspace::create(supervisor, run_root, storage)?;
    let result = replay_in(
        supervisor,
        config,
        &mut workspace,
        source,
        certificate,
        &replay,
        storage,
    );
    if let Err(fault) = &result {
        workspace.retain_failure(fault, storage);
    }
    result
}

fn replay_in(
    supervisor: &mut Supervisor,
    config: &Value,
    workspace: &mut KernelWorkspace,
    source: &Snapshot,
    certificate: &Snapshot,
    replay: &str,
    storage: &mut Object,
) -> Result<Value, Fault> {
    let Some(Value::Object(library)) = (match config {
        Value::Object(config) => config.get("proof_library"),
        _ => None,
    }) else {
        return Err(error("Shared proof-library inventory changed", "adapter"));
    };
    workspace.stage_library(supervisor, library, storage)?;
    let result = verify_native(supervisor, config, workspace, source, certificate, replay)?;
    workspace.verify_library(supervisor, storage)?;
    let mut expected = BTreeMap::new();
    if let Value::Object(record) = &result
        && let Some(Value::Object(hashes)) = record.get("module_source_sha256")
    {
        for (name, digest) in hashes.iter() {
            if let Value::String(digest) = digest {
                expected.insert(format!("kernel/decomposed/{name}.lean"), digest.clone());
            }
        }
    }
    expected.insert("kernel/input.p".to_string(), source.sha256.clone());
    expected.insert("kernel/proof.fang".to_string(), certificate.sha256.clone());
    workspace.archive(supervisor, &expected, storage)?;
    workspace.cleanup(supervisor, storage)?;
    supervisor.check("kernel-archived", 0.15)?;
    Ok(result)
}

fn source_hashes(
    supervisor: &Supervisor,
    modules_root: &Path,
) -> Result<Vec<(String, String)>, Fault> {
    let mut hashes = Vec::new();
    for name in MODULES.iter().copied().chain(["Audit"]) {
        hashes.push((
            name.to_string(),
            digest_file(
                &modules_root.join(format!("{name}.lean")),
                &mut check(supervisor),
            )?,
        ));
    }
    Ok(hashes)
}

/// `verify_native`.
fn verify_native(
    supervisor: &mut Supervisor,
    config: &Value,
    workspace: &KernelWorkspace,
    source: &Snapshot,
    certificate: &Snapshot,
    replay: &str,
) -> Result<Value, Fault> {
    let native = workspace.native().to_path_buf();
    let project = native.join("kernel");
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&project)
        .map_err(Fault::at(&project))?;
    let replay_path = project.join("Replay.lean");
    fs::write(&replay_path, replay).map_err(Fault::at(&replay_path))?;
    for (name, captured) in [("input.p", source), ("proof.fang", certificate)] {
        let path = project.join(name);
        fs::write(&path, &captured.data).map_err(Fault::at(&path))?;
        fs::set_permissions(&path, fs::Permissions::from_mode(0o400)).map_err(Fault::at(&path))?;
    }
    let modules_root = project.join("decomposed");
    let command: Vec<OsString> = vec![
        crate::older::launcher()?.into(),
        INTERNAL.into(),
        STAGE.into(),
        replay_path.into(),
        modules_root.clone().into(),
    ];
    let output = run_stage(
        supervisor,
        "decompose",
        &command,
        &native.join("decompose"),
        &native,
        None,
        None,
        None,
    )?;
    if completed_contract(&output)? != 0 || !output.stdout.is_empty() || !output.stderr.is_empty() {
        return Err(error("Fixed replay decomposition failed", "decompose"));
    }
    let emitted = fang_supervisor::read_regular(
        &modules_root.join("emitted.json"),
        4 << 20,
        &mut check(supervisor),
    )?;
    let emitted = fang_supervisor::strict_json(python_utf8(&emitted)?.as_bytes())?;
    let Value::Object(emitted) = emitted else {
        return Err(error("Unexpected generated module inventory", "decompose"));
    };
    let expected_modules = Value::Array(
        MODULES
            .iter()
            .map(|name| Value::String(name.to_string()))
            .collect(),
    );
    if !emitted
        .get("modules")
        .is_some_and(|modules| crate::older::json_equal(modules, &expected_modules))
    {
        return Err(error("Unexpected generated module inventory", "decompose"));
    }
    if !matches!(emitted.get("generator"), Some(Value::String(name)) if name == GENERATOR) {
        return Err(error(
            "Decomposition identity or endpoints differ",
            "decompose",
        ));
    }
    let mut present = BTreeSet::new();
    for entry in fs::read_dir(&modules_root).map_err(Fault::at(&modules_root))? {
        present.insert(
            entry
                .map_err(Fault::at(&modules_root))?
                .file_name()
                .to_string_lossy()
                .to_string(),
        );
    }
    let mut wanted: BTreeSet<String> = MODULES.iter().map(|name| format!("{name}.lean")).collect();
    wanted.insert("emitted.json".to_string());
    if present != wanted {
        return Err(error(
            "Decomposer emitted unexpected or precomputed files",
            "decompose",
        ));
    }
    for (name, captured) in [("input.p", source), ("proof.fang", certificate)] {
        let data = fang_supervisor::read_regular(
            &project.join(name),
            captured.data.len() as u64,
            &mut check(supervisor),
        )?;
        if data != captured.data {
            return Err(error("Decomposer changed captured bytes", "decompose"));
        }
    }
    let audit = generator::fixed_audit("CompleteReplay", &source.data, &certificate.data)
        .ok_or_else(|| error("Fixed replay decomposition failed", "decompose"))?;
    let audit_path = modules_root.join("Audit.lean");
    fs::write(&audit_path, audit).map_err(Fault::at(&audit_path))?;
    let mut environment = child_environment();
    environment.set(
        "LEAN_PATH",
        format!(
            "{}:{}",
            modules_root.display(),
            workspace.library().display()
        ),
    );
    let hashes = source_hashes(supervisor, &modules_root)?;
    let lean = binary(config, "lean");
    let memory = supervisor.limits.memory_mib.to_string();
    let mut results = Object::new();
    for name in MODULES.iter().copied().chain(["Audit"]) {
        let stage = format!("kernel-{}", name.to_lowercase());
        let command: Vec<OsString> = vec![
            lean.clone().into(),
            "-j1".into(),
            "-M".into(),
            memory.clone().into(),
            "--root".into(),
            modules_root.clone().into(),
            "-o".into(),
            modules_root.join(format!("{name}.olean")).into(),
            modules_root.join(format!("{name}.lean")).into(),
        ];
        let output = run_stage(
            supervisor,
            &stage,
            &command,
            &native.join(&stage),
            &native,
            Some(&environment),
            None,
            None,
        )?;
        if completed_contract(&output)? != 0 || !output.stderr.is_empty() {
            return Err(error("Kernel replay or fixed audit failed", stage));
        }
        if !modules_root.join(format!("{name}.olean")).is_file() {
            return Err(error("Kernel compiler did not write its module", stage));
        }
        if name == "Audit" {
            let text =
                python_utf8(&output.stdout).map_err(|fault| error(fault.python_str(), "audit"))?;
            results = exact_axioms(text)?;
        }
    }
    verify_pair(supervisor, source, certificate)?;
    if source_hashes(supervisor, &modules_root)? != hashes {
        return Err(error(
            "Generated proof source changed during compilation",
            "kernel",
        ));
    }
    let mut module_hashes = Object::new();
    for (name, digest) in &hashes {
        module_hashes.set(name.as_str(), digest.clone());
    }
    let audit_sha256 = hashes
        .iter()
        .find(|(name, _)| name == "Audit")
        .map(|(_, digest)| digest.clone())
        .unwrap_or_default();
    let mut record = Object::new();
    record.set("hook", "fixed-decomposed-v2");
    record.set("audited_theorems", Value::Object(results));
    record.set(
        "modules",
        Value::Array(
            MODULES
                .iter()
                .map(|name| Value::String(name.to_string()))
                .collect(),
        ),
    );
    record.set("module_source_sha256", Value::Object(module_hashes));
    record.set("fixed_audit_sha256", audit_sha256);
    record.set("scope", SCOPE);
    Ok(Value::Object(record))
}

/// The internal stage `cnf-decompose REPLAY DIRECTORY` (decomposed_replay_probe.py with `--grouped --full
/// --emit-only`): read REPLAY and the `input.p` and `proof.fang` beside it, create DIRECTORY and write the
/// modules and `emitted.json` into it. Exit 1 on any refusal. It never decides a status.
pub fn decompose(arguments: &[String]) -> ExitCode {
    let [replay, destination] = arguments else {
        eprintln!("fang: {STAGE} needs REPLAY DIRECTORY");
        return ExitCode::from(64);
    };
    let replay = Path::new(replay);
    let folder = replay.parent().unwrap_or(Path::new("."));
    let read = |path: &Path| {
        fs::read(path).map_err(|failure| format!("cannot read {}: {failure}", path.display()))
    };
    let outcome = (|| -> Result<(), String> {
        let original = String::from_utf8(read(replay)?)
            .map_err(|_| "the replay module is not UTF-8".to_string())?;
        let destination = Path::new(destination);
        if let Some(parent) = destination.parent() {
            fs::create_dir_all(parent).map_err(|failure| failure.to_string())?;
        }
        fs::create_dir(destination)
            .map_err(|failure| format!("cannot create {}: {failure}", destination.display()))?;
        let proof = read(&folder.join("proof.fang"))?;
        let source = read(&folder.join("input.p"))?;
        let modules = generator::decompose(&original, &proof, &source)?;
        for (name, contents) in &modules {
            fs::write(destination.join(format!("{name}.lean")), contents)
                .map_err(|failure| failure.to_string())?;
        }
        fs::write(
            destination.join("emitted.json"),
            generator::emitted_json(&modules),
        )
        .map_err(|failure| failure.to_string())
    })();
    match outcome {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("fang: {STAGE}: {message}");
            ExitCode::from(1)
        }
    }
}
