// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Fresh original-byte kernel replay under the run's deadline: a port of tools/fof_szs/kernel_replay.py.
//!
//! The generator is `replay`, run as the launcher's internal stage `ground-fof-replay` in a bounded child, in
//! place of the pinned Python helpers; the fixed audit module is built here from the captured pair, never read
//! from the child, and its report is read by fang-axiom-audit. Without helpers, the archive holds the generated
//! modules and the stage logs only.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::fs;
use std::io::Write;
use std::path::Path;
use std::process::ExitCode;

use fang_json::{Number, Object, Value};
use fang_supervisor::{Fault, Snapshot, Status, Supervisor, child_environment};

use crate::older::{INTERNAL, error, failure, json_equal, python_utf8, run_stage, value};
use crate::profile_ground_fof::{capability, protocol, replay};
use fang_kernel_workspace::KernelWorkspace;

/// The fixed audit module, compiled after the generated ones.
const AUDIT: &str = "FofInstanceAudit";
/// The internal stage that runs `replay::generate`.
pub const GENERATOR: &str = "ground-fof-replay";
const RESOURCE_LIMIT: &[u8] = b"ResourceLimit: kernel replay profile bound exceeded\n";
const SCOPE: &str = "Fresh exact-byte Lean kernel instance; compiled execution and direct Rust verification remain separate";

fn bound(name: &str) -> u64 {
    capability::KERNEL_LIMITS
        .iter()
        .find(|(key, _)| *key == name)
        .map_or(0, |(_, bound)| *bound as u64)
}

fn check(supervisor: &Supervisor) -> impl FnMut() -> Result<(), fang_supervisor::Failure> + '_ {
    move || crate::older::check(supervisor)
}

/// `exact_audits`: exactly the five fixed reports and nothing else, each with standard axioms only. Returns
/// theorem -> sorted axioms, in report order.
fn exact_audits(output: &[u8]) -> Result<Object, Fault> {
    let text = python_utf8(output)?;
    let reports = fang_axiom_audit::reports(text);
    if reports.len() != replay::AUDITS.len()
        || !fang_axiom_audit::python_strip(&fang_axiom_audit::strip_reports(text)).is_empty()
    {
        return Err(value("Fixed kernel audit report inventory differs"));
    }
    let required: Vec<String> = replay::AUDITS
        .iter()
        .map(|name| format!("Fang.FOFKernelAudit.{name}"))
        .collect();
    let names: Vec<&str> = required.iter().map(String::as_str).collect();
    let values =
        fang_axiom_audit::audit_axioms(text, &names).map_err(|failure| value(failure.0))?;
    let found: BTreeSet<&str> = values.iter().map(|(name, _)| name.as_str()).collect();
    if found != names.iter().copied().collect::<BTreeSet<&str>>() {
        return Err(value("Fixed kernel audit theorem set differs"));
    }
    let mut result = Object::new();
    for (name, axioms) in values {
        result.set(
            name.as_str(),
            Value::Array(axioms.into_iter().map(Value::String).collect()),
        );
    }
    Ok(result)
}

/// `verify`: replay the captured pair in a fresh native workspace and return the `kernel_check` record.
/// `storage` is the run record's `kernel_storage` object; on failure it records what was retained.
pub fn verify(
    supervisor: &mut Supervisor,
    config: &Object,
    root: &Path,
    source: &Snapshot,
    certificate: &Snapshot,
    storage: &mut Object,
) -> Result<Value, Fault> {
    let Some(Value::Object(kernel)) = config.get("kernel") else {
        return Err(value("Unsupported kernel capability"));
    };
    if source.data.len() as u64 > bound("input_bytes")
        || certificate.data.len() as u64 > bound("certificate_bytes")
    {
        return Err(failure(
            Status::ResourceOut,
            "Captured pair exceeds this kernel replay profile's byte cap",
            "kernel",
        ));
    }
    let mut workspace = KernelWorkspace::create(supervisor, root, storage)?;
    let result = replay_in(
        supervisor,
        kernel,
        &mut workspace,
        source,
        certificate,
        storage,
    );
    if let Err(fault) = &result {
        workspace.retain_failure(fault, storage);
    }
    result
}

fn verify_pair(
    supervisor: &Supervisor,
    source: &Snapshot,
    certificate: &Snapshot,
) -> Result<(), Fault> {
    source.verify(&mut check(supervisor))?;
    certificate.verify(&mut check(supervisor))
}

fn replay_in(
    supervisor: &mut Supervisor,
    kernel: &Object,
    workspace: &mut KernelWorkspace,
    source: &Snapshot,
    certificate: &Snapshot,
    storage: &mut Object,
) -> Result<Value, Fault> {
    let Some(Value::Object(library)) = kernel.get("library") else {
        return Err(value("Kernel library inventory changed"));
    };
    workspace.stage_library(supervisor, library, storage)?;
    let native = workspace.native().to_path_buf();
    let modules = native.join("modules");
    fs::create_dir(&modules).map_err(Fault::at(&modules))?;
    verify_pair(supervisor, source, certificate)?;
    let command: Vec<OsString> = vec![
        crate::older::launcher()?.into(),
        INTERNAL.into(),
        GENERATOR.into(),
        source.argument().into(),
        certificate.argument().into(),
        modules.clone().into(),
    ];
    let output = run_stage(
        supervisor,
        "kernel-generate",
        &command,
        &native.join("generate"),
        &native,
        None,
        None,
        None,
    )?;
    let code = protocol::normal_exit(&output)?;
    if code == 5 && output.stdout.is_empty() && output.stderr == RESOURCE_LIMIT {
        return Err(failure(
            Status::ResourceOut,
            "Kernel replay profile bound exceeded",
            "kernel-generate",
        ));
    }
    if code != 0 || !output.stdout.is_empty() || !output.stderr.is_empty() {
        return Err(error("Kernel witness generator failed", "kernel-generate"));
    }
    let emitted =
        fang_supervisor::read_regular(&modules.join("emitted.json"), 4096, &mut check(supervisor))?;
    let emitted = capability::strict_json(python_utf8(&emitted)?.as_bytes())?;
    let expected_modules = Value::Array(
        replay::MODULES
            .iter()
            .map(|name| Value::String(name.to_string()))
            .collect(),
    );
    let Value::Object(emitted) = emitted else {
        return Err(error(
            "Generated module inventory differs",
            "kernel-generate",
        ));
    };
    let keys: BTreeSet<&str> = emitted.iter().map(|(key, _)| key).collect();
    if keys
        != BTreeSet::from([
            "modules",
            "input_bytes",
            "certificate_bytes",
            "certificate_nodes",
        ])
        || !emitted
            .get("modules")
            .is_some_and(|modules| json_equal(modules, &expected_modules))
    {
        return Err(error(
            "Generated module inventory differs",
            "kernel-generate",
        ));
    }
    let nodes = match emitted.get("certificate_nodes") {
        Some(Value::Number(Number::Integer(nodes))) => nodes
            .as_i64()
            .filter(|nodes| (0..=bound("certificate_nodes") as i64).contains(nodes)),
        _ => None,
    };
    let same = |key: &str, length: usize| {
        emitted
            .get(key)
            .is_some_and(|value| json_equal(value, &Value::from(length as i64)))
    };
    let Some(nodes) = nodes.filter(|_| {
        same("input_bytes", source.data.len()) && same("certificate_bytes", certificate.data.len())
    }) else {
        return Err(error(
            "Generated replay metadata differs",
            "kernel-generate",
        ));
    };
    let mut present = BTreeSet::new();
    for entry in fs::read_dir(&modules).map_err(Fault::at(&modules))? {
        present.insert(
            entry
                .map_err(Fault::at(&modules))?
                .file_name()
                .to_string_lossy()
                .to_string(),
        );
    }
    let mut wanted: BTreeSet<String> = replay::MODULES
        .iter()
        .map(|name| format!("{name}.lean"))
        .collect();
    wanted.insert("emitted.json".to_string());
    if present != wanted {
        return Err(error("Unexpected generated artifact", "kernel-generate"));
    }
    // This audit is constructed separately from the captured pair, not read from child output or supplied with
    // the candidate certificate.
    let audit = modules.join(format!("{AUDIT}.lean"));
    fs::write(
        &audit,
        replay::audit_source(&source.data, &certificate.data),
    )
    .map_err(Fault::at(&audit))?;
    let mut source_hashes = Object::new();
    let mut expected = BTreeMap::new();
    let mut generated_bytes = 0u64;
    for name in replay::MODULES.iter().copied().chain([AUDIT]) {
        let data = fang_supervisor::read_regular(
            &modules.join(format!("{name}.lean")),
            bound("generated_bytes"),
            &mut check(supervisor),
        )?;
        generated_bytes += data.len() as u64;
        let digest = fang_hash::sha256_hex(&data);
        expected.insert(format!("modules/{name}.lean"), digest.clone());
        source_hashes.set(name, digest);
    }
    if generated_bytes > bound("generated_bytes") {
        return Err(failure(
            Status::ResourceOut,
            "Generated replay exceeds the profile byte cap",
            "kernel-generate",
        ));
    }
    let mut environment = child_environment();
    environment.set(
        "LEAN_PATH",
        format!("{}:{}", modules.display(), workspace.library().display()),
    );
    environment.set("LEAN_NUM_THREADS", "1");
    let lean = match kernel.get("lean") {
        Some(Value::Object(pin)) => match pin.get("path") {
            Some(Value::String(path)) => path.clone(),
            _ => return Err(value("Unsupported kernel capability")),
        },
        _ => return Err(value("Unsupported kernel capability")),
    };
    let memory = supervisor.limits.memory_mib.min(2048);
    let mut results = None;
    for name in replay::MODULES.iter().copied().chain([AUDIT]) {
        let stage = format!("kernel-{}", name.to_lowercase());
        let command: Vec<OsString> = vec![
            lean.clone().into(),
            "-j1".into(),
            format!("-M{memory}").into(),
            "-o".into(),
            modules.join(format!("{name}.olean")).into(),
            modules.join(format!("{name}.lean")).into(),
        ];
        let output = run_stage(
            supervisor,
            &stage,
            &command,
            &native.join(&stage),
            &native,
            Some(&environment),
            None,
            Some(&modules),
        )?;
        if protocol::normal_exit(&output)? != 0 || !output.stderr.is_empty() {
            return Err(error("Fresh kernel replay did not pass", stage));
        }
        if name == AUDIT {
            results = Some(exact_audits(&output.stdout)?);
        } else if !output.stdout.is_empty() {
            return Err(error("Unexpected kernel diagnostic", stage));
        }
        if !modules.join(format!("{name}.olean")).is_file() {
            return Err(error("Kernel module artifact missing", stage));
        }
    }
    verify_pair(supervisor, source, certificate)?;
    workspace.verify_library(supervisor, storage)?;
    workspace.archive(supervisor, &expected, storage)?;
    workspace.cleanup(supervisor, storage)?;
    supervisor.check("kernel-archived", 0.15)?;
    let mut record = Object::new();
    record.set("profile", capability::KERNEL_PROFILE);
    record.set(
        "audited_theorems",
        Value::Object(results.unwrap_or_default()),
    );
    record.set("module_source_sha256", Value::Object(source_hashes));
    record.set("certificate_nodes", Value::from(nodes));
    record.set("fresh_instance", true);
    record.set("source_sha256", source.sha256.clone());
    record.set("certificate_sha256", certificate.sha256.clone());
    record.set("scope", SCOPE);
    Ok(Value::Object(record))
}

/// The internal stage `ground-fof-replay SOURCE CERTIFICATE DIRECTORY` (emit_replay.py): write the generated
/// modules and `emitted.json` into DIRECTORY. Exit 5 with one fixed line when a profile bound is exceeded, 1
/// when the pair is outside what the generator reads or a file cannot be written. It never decides a status.
pub fn emit(arguments: &[String]) -> ExitCode {
    let [source, certificate, destination] = arguments else {
        eprintln!("fang: {GENERATOR} needs SOURCE CERTIFICATE DIRECTORY");
        return ExitCode::from(64);
    };
    let (source, certificate) = match (fs::read(source), fs::read(certificate)) {
        (Ok(source), Ok(certificate)) => (source, certificate),
        (Err(failure), _) | (_, Err(failure)) => {
            eprintln!("fang: {GENERATOR}: {failure}");
            return ExitCode::from(1);
        }
    };
    let generated = match replay::generate(&source, &certificate) {
        Ok(generated) => generated,
        Err(replay::Error::Limit(_)) => {
            let _ = std::io::stderr().write_all(RESOURCE_LIMIT);
            return ExitCode::from(5);
        }
        Err(replay::Error::Invalid(message)) => {
            eprintln!("fang: {GENERATOR}: {message}");
            return ExitCode::from(1);
        }
    };
    let destination = Path::new(destination);
    let files = generated
        .modules
        .iter()
        .map(|(name, contents)| (format!("{name}.lean"), contents.clone()))
        .chain([("emitted.json".to_string(), replay::emitted_json(&generated))]);
    for (name, contents) in files {
        if let Err(failure) = fs::write(destination.join(&name), contents) {
            eprintln!("fang: {GENERATOR}: cannot write {name}: {failure}");
            return ExitCode::from(1);
        }
    }
    ExitCode::SUCCESS
}

#[cfg(test)]
mod tests {
    use super::*;

    fn report(names: &[&str]) -> Vec<u8> {
        names
            .iter()
            .map(|name| {
                format!("'Fang.FOFKernelAudit.{name}' depends on axioms: [propext, Quot.sound]\n")
            })
            .collect::<String>()
            .into_bytes()
    }

    #[test]
    fn the_fixed_audit_needs_exactly_its_five_reports() {
        let all = exact_audits(&report(&replay::AUDITS)).unwrap();
        assert_eq!(all.len(), 5);
        assert!(exact_audits(&report(&replay::AUDITS[..4])).is_err());
        let mut extra = report(&replay::AUDITS);
        extra.extend_from_slice(b"warning: unused\n");
        assert_eq!(
            exact_audits(&extra).unwrap_err().python_str(),
            "Fixed kernel audit report inventory differs"
        );
        let mut renamed = report(&replay::AUDITS[..4]);
        renamed.extend_from_slice(b"'Fang.FOFKernelAudit.other' does not depend on any axioms\n");
        assert_eq!(
            exact_audits(&renamed).unwrap_err().python_str(),
            "Missing Lean theorem audits: ['Fang.FOFKernelAudit.exact_original_bytes_unsat']"
        );
    }

    #[test]
    fn invalid_utf8_gives_the_python_text() {
        assert_eq!(
            python_utf8(b"ok\xff").unwrap_err().python_str(),
            "'utf-8' codec can't decode byte 0xff in position 2: invalid start byte"
        );
        assert_eq!(
            python_utf8(b"\xe2\x82").unwrap_err().python_str(),
            "'utf-8' codec can't decode bytes in position 0-1: unexpected end of data"
        );
        assert_eq!(
            python_utf8(b"\xe2(").unwrap_err().python_str(),
            "'utf-8' codec can't decode byte 0xe2 in position 0: invalid continuation byte"
        );
    }
}
