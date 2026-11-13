// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Development builder, not the installer: writes a version-8 capability of schema v8 for the Rust launcher
//! from a capability of the Python adapter, pinning the given launcher. It is for development comparisons;
//! an installation writes its capability with the installer.
//!
//! usage: dev_capability --from CAPABILITY --launcher PATH --out PATH [--kernel-entry PATH] [--cnf PATH]
//!        [--ground-fof PATH]
//!
//! The pinned records of the binaries, the provenance and the optional sections are copied; the launcher, and
//! the kernel entry when given, are hashed here. The result must pass `check_fields`, and every pinned file
//! must still hash to its pin, or nothing is written.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use fang_json::{Object, Value};
use fang_launcher::capability::{
    self, DEFAULT_CHECK, LANGUAGE, MAX_BYTES, MAX_CERTIFICATE_BYTES, SCHEMA,
};

const USAGE: &str = "usage: dev_capability --from CAPABILITY --launcher PATH --out PATH [--kernel-entry PATH] \
                     [--cnf PATH] [--ground-fof PATH]";
const OPTIONS: [&str; 6] = [
    "--from",
    "--launcher",
    "--out",
    "--kernel-entry",
    "--cnf",
    "--ground-fof",
];

fn digest(path: &Path) -> Result<String, String> {
    let mut check = || Ok::<(), ()>(());
    fang_hash::hash_file(path, fang_hash::DEFAULT_FILE_LIMIT, &mut check)
        .map(|(digest, _)| digest)
        .map_err(|_| format!("cannot hash {}", path.display()))
}

fn chunked(path: &Path) -> Result<String, String> {
    let mut check = || Ok::<(), ()>(());
    fang_hash::hash_file_chunked(path, fang_hash::DEFAULT_FILE_LIMIT, 0, &mut check)
        .map(|(digest, _)| format!("{}{digest}", capability::CHUNKED_TAG))
        .map_err(|_| format!("cannot hash {}", path.display()))
}

fn record(path: &Path) -> Result<Value, String> {
    let mut object = Object::new();
    object.set("path", path.display().to_string());
    object.set("sha256", digest(path)?);
    Ok(Value::Object(object))
}

/// Add the chunked digest to a binary's record.
fn binary(value: &mut Value) -> Result<(), String> {
    let Value::Object(object) = value else {
        return Err("a pinned binary record is not an object".to_string());
    };
    let path = match object.get("path") {
        Some(Value::String(path)) => PathBuf::from(path),
        _ => return Err("a pinned binary record has no path".to_string()),
    };
    object.set("chunked_sha256", chunked(&path)?);
    Ok(())
}

fn build(options: &BTreeMap<String, PathBuf>) -> Result<(PathBuf, Object), String> {
    let required = |name: &str| options.get(name).ok_or_else(|| USAGE.to_string());
    let source = std::fs::read(required("--from")?).map_err(|error| error.to_string())?;
    let source = match fang_supervisor::strict_json(&source).map_err(|fault| fault.python_str())? {
        Value::Object(object) => object,
        _ => return Err("the source capability is not an object".to_string()),
    };
    let take = |name: &str| {
        source
            .get(name)
            .cloned()
            .ok_or_else(|| format!("the source capability has no {name}"))
    };
    let mut object = Object::new();
    object.set("schema", SCHEMA);
    object.set("language", LANGUAGE);
    object.set("certificate_version", Value::from(8u64));
    object.set("max_input_bytes", Value::from(MAX_BYTES));
    object.set("max_certificate_bytes", Value::from(MAX_CERTIFICATE_BYTES));
    object.set("default_check", DEFAULT_CHECK);
    object.set("per_run_verification", capability::per_run_value());
    for name in [
        "engine",
        "checker",
        "provenance",
        "bundle",
        "signed",
        "tstp",
        "model",
    ] {
        object.set(name, take(name)?);
    }
    let launcher =
        std::fs::canonicalize(required("--launcher")?).map_err(|error| error.to_string())?;
    object.set("launcher", record(&launcher)?);
    let mut kernel = take("kernel")?;
    if let Some(entry) = options.get("--kernel-entry") {
        match &mut kernel {
            Value::Object(section) => section.set("entry", record(entry)?),
            _ => return Err("--kernel-entry needs a kernel section".to_string()),
        }
    }
    object.set("kernel", kernel);
    for (option, section, field) in [
        ("--cnf", "cnf", "installation"),
        ("--ground-fof", "ground_fof", "capability"),
    ] {
        let value = match options.get(option) {
            Some(path) => {
                let mut inner = Object::new();
                inner.set(field, record(path)?);
                Value::Object(inner)
            }
            None => Value::Null,
        };
        object.set(section, value);
    }
    // Every binary's record also pins its chunked digest, which each run verifies.
    for name in ["launcher", "engine", "checker"] {
        if let Some(value) = object.get_mut(name) {
            binary(value)?;
        }
    }
    for name in ["bundle", "signed", "tstp", "model", "kernel"] {
        if let Some(Value::Object(section)) = object.get_mut(name) {
            let keys: Vec<String> = section.keys().map(|key| key.to_string()).collect();
            for key in keys {
                if (name == "kernel" && key != "witness" && key != "entry") || key == "output_root"
                {
                    continue;
                }
                if let Some(value) = section.get_mut(&key) {
                    binary(value)?;
                }
            }
        }
    }
    capability::check_fields(&object)?;
    Ok((required("--out")?.clone(), object))
}

/// Every pinned file of the written capability must still hash to its pins.
fn confirm(path: &Path) -> Result<usize, String> {
    let loaded = capability::Capability::load(path).map_err(|fault| fault.python_str())?;
    let pins = loaded.pins();
    for pin in &pins {
        let changed = digest(&pin.path)? != pin.sha256
            || pin
                .chunked_sha256
                .as_ref()
                .is_some_and(|expected| chunked(&pin.path).ok().as_ref() != Some(expected));
        if changed {
            return Err(format!("pinned file changed: {}", pin.path.display()));
        }
    }
    Ok(pins.len())
}

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let mut options = BTreeMap::new();
    for pair in arguments.chunks(2) {
        match pair {
            [name, value] if OPTIONS.contains(&name.as_str()) && !options.contains_key(name) => {
                options.insert(name.clone(), PathBuf::from(value));
            }
            _ => {
                eprintln!("{USAGE}");
                return ExitCode::from(64);
            }
        }
    }
    let (out, object) = match build(&options) {
        Ok(built) => built,
        Err(message) => {
            eprintln!("dev_capability: {message}");
            return ExitCode::from(1);
        }
    };
    let text = match fang_json::dumps_manifest(&Value::Object(object)) {
        Ok(text) => text + "\n",
        Err(error) => {
            eprintln!("dev_capability: {}", error.0);
            return ExitCode::from(1);
        }
    };
    let written = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&out)
        .and_then(|mut file| std::io::Write::write_all(&mut file, text.as_bytes()));
    if let Err(error) = written {
        eprintln!("dev_capability: {}: {error}", out.display());
        return ExitCode::from(1);
    }
    match confirm(&out) {
        Ok(count) => {
            println!(
                "{} {} ({count} pinned files)",
                fang_hash::sha256_hex(text.as_bytes()),
                out.display()
            );
            ExitCode::SUCCESS
        }
        Err(message) => {
            let _ = std::fs::remove_file(&out);
            eprintln!("dev_capability: {message}");
            ExitCode::from(1)
        }
    }
}
