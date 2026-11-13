// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The CNF installation file, schema `fang-local-installation-v3`: a port of tools/fang_szs/installation.py
//! `verify_installation` and `verify_running_adapter` without the Python pins.
//!
//! The launcher pin replaces the interpreter pin and the source snapshot, and the provenance records that carry
//! the source hashes are pinned. Each executed binary's pin also holds its chunked SHA-256 (`chunked_sha256`):
//! a run verifies the binaries it executes by that digest before their first execution and checks their identity
//! after the run (`binaries_of`), and rehashes the proof library and the provenance records before and after.
//! `exporter_sources` keeps the hashes of the two exporter Lean sources, which v2 read from its source
//! inventory. Every refusal is installation.py's Failure text, at stage "adapter".

use std::collections::BTreeMap;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};

use fang_json::{Object, Value};
use fang_supervisor::{Failure, Fault};

use crate::capability::{Pin, Record};
pub use crate::older::Library;
use crate::older::binaries::Binaries;
use crate::older::error;

pub const SCHEMA: &str = "fang-local-installation-v3";
/// The exporter's Lean sources whose hashes an installation with an exporter records.
pub const EXPORTER_SOURCES: [&str; 2] = ["lean/TstpExport.lean", "lean/TstpMain.lean"];
const REQUIRED_MODULES: [&str; 2] = [
    "Fang/FrontendSoundness.olean",
    "Fang/CertificateInput.olean",
];

type Check<'a> = &'a mut dyn FnMut() -> Result<(), Failure>;

fn failure(reason: &str) -> Fault {
    error(reason, "adapter")
}

fn get<'a>(object: &'a Object, key: &str) -> Option<&'a Value> {
    object.get(key)
}

fn text(value: Option<&Value>) -> Option<&str> {
    match value {
        Some(Value::String(text)) => Some(text),
        _ => None,
    }
}

fn object(value: Option<&Value>) -> Option<&Object> {
    match value {
        Some(Value::Object(object)) => Some(object),
        _ => None,
    }
}

fn hex64(value: Option<&Value>) -> bool {
    text(value).is_some_and(|text| {
        text.len() == 64
            && text
                .bytes()
                .all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
    })
}

fn same_keys(object: &Object, expected: &[&str]) -> bool {
    let mut actual: Vec<&str> = object.iter().map(|(key, _)| key).collect();
    let mut wanted = expected.to_vec();
    actual.sort_unstable();
    wanted.sort_unstable();
    actual == wanted
}

/// `digest_file`: the SHA-256 of a regular file, checking the deadline between blocks.
pub fn digest_file(path: &Path, check: Check) -> Result<String, Fault> {
    let regular = fs::symlink_metadata(path)
        .map_err(Fault::at(path))?
        .file_type()
        .is_file();
    if !regular {
        return Err(failure("Installation member must be a regular file"));
    }
    let mut stream = fs::File::open(path).map_err(Fault::at(path))?;
    let mut hasher = fang_hash::Hasher::new();
    let mut block = vec![0u8; 65536];
    loop {
        let read = stream.read(&mut block).map_err(Fault::at(path))?;
        if read == 0 {
            break;
        }
        check()?;
        hasher.update(&block[..read]);
    }
    Ok(fang_hash::hex(&hasher.finish()))
}

/// `directory_inventory`: relative POSIX path -> SHA-256 of every file under a real directory.
pub fn directory_inventory(root: &Path, check: Check) -> Result<BTreeMap<String, String>, Fault> {
    let real = fs::symlink_metadata(root).is_ok_and(|metadata| metadata.is_dir());
    if !real {
        return Err(failure("Installed library must be a real directory"));
    }
    let mut paths = Vec::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(directory) = pending.pop() {
        for entry in fs::read_dir(&directory).map_err(Fault::at(&directory))? {
            let path = entry.map_err(Fault::at(&directory))?.path();
            let metadata = fs::symlink_metadata(&path).map_err(Fault::at(&path))?;
            if metadata.is_dir() {
                pending.push(path.clone());
            }
            paths.push((path, metadata));
        }
    }
    paths.sort_by(|left, right| left.0.cmp(&right.0));
    let mut result = BTreeMap::new();
    for (path, metadata) in paths {
        if metadata.file_type().is_symlink() {
            return Err(failure("Installation contains a symlink"));
        }
        if metadata.is_file() {
            let relative = path
                .strip_prefix(root)
                .unwrap_or(&path)
                .to_string_lossy()
                .to_string();
            result.insert(relative, digest_file(&path, check)?);
        } else if !metadata.is_dir() {
            return Err(failure("Installation contains a nonregular member"));
        }
    }
    Ok(result)
}

fn library_matches(files: Option<&Value>, actual: &BTreeMap<String, String>) -> bool {
    object(files).is_some_and(|files| {
        files.len() == actual.len()
            && actual
                .iter()
                .all(|(name, digest)| text(files.get(name)) == Some(digest.as_str()))
    })
}

/// Whether this installation pins a TSTP exporter.
pub fn exporting(config: &Value) -> bool {
    object(Some(config)).is_some_and(|config| config.get("exporter").is_some())
}

fn binaries(config: &Object) -> Vec<&'static str> {
    let mut names = vec!["engine", "checker", "lean", "launcher"];
    if config.get("exporter").is_some() {
        names.push("exporter");
    }
    names
}

fn expected_keys(exporter: bool) -> Vec<&'static str> {
    let mut expected = vec![
        "schema",
        "platform",
        "proof_library",
        "provenance",
        "engine",
        "checker",
        "lean",
        "launcher",
    ];
    if exporter {
        expected.extend(["exporter", "exporter_sources"]);
    }
    expected
}

/// A `{path, sha256}` record: an absolute path and a SHA-256.
fn pin_shape(pin: Option<&Value>) -> bool {
    object(pin).is_some_and(|pin| {
        same_keys(pin, &["path", "sha256"])
            && text(get(pin, "path")).is_some_and(|path| Path::new(path).is_absolute())
            && hex64(get(pin, "sha256"))
    })
}

/// An executed binary's `{path, sha256, chunked_sha256}` pin.
fn binary_shape(pin: Option<&Value>) -> bool {
    object(pin).is_some_and(|pin| {
        same_keys(pin, &["path", "sha256", "chunked_sha256"])
            && text(get(pin, "path")).is_some_and(|path| Path::new(path).is_absolute())
            && hex64(get(pin, "sha256"))
            && text(get(pin, "chunked_sha256")).is_some_and(crate::capability::is_chunked)
    })
}

/// The schema check of an installation value, with no file read; the refusal is installation.py's text.
fn schema(config: &Value) -> Result<&Object, &'static str> {
    let config = object(Some(config)).ok_or("Unsupported installation schema")?;
    let exporter = config.get("exporter").is_some();
    if exporter {
        let sources = object(get(config, "exporter_sources"));
        if !sources.is_some_and(|sources| {
            EXPORTER_SOURCES
                .iter()
                .all(|name| sources.get(name).is_some())
        }) {
            return Err("TSTP installation is missing exporter source");
        }
    }
    if !same_keys(config, &expected_keys(exporter))
        || text(get(config, "schema")) != Some(SCHEMA)
        || text(get(config, "platform")) != Some("linux")
    {
        return Err("Unsupported installation schema");
    }
    if let Some(sources) = object(get(config, "exporter_sources"))
        && (!same_keys(sources, &EXPORTER_SOURCES)
            || !EXPORTER_SOURCES.iter().all(|name| hex64(sources.get(name))))
    {
        return Err("TSTP installation is missing exporter source");
    }
    if !binaries(config)
        .iter()
        .all(|name| binary_shape(get(config, name)))
    {
        return Err("Malformed executable pin");
    }
    let library = object(get(config, "proof_library"));
    let library_ok = library.is_some_and(|library| {
        same_keys(library, &["path", "files_sha256"])
            && text(get(library, "path")).is_some_and(|path| Path::new(path).is_absolute())
            && object(get(library, "files_sha256"))
                .is_some_and(|files| files.iter().all(|(_, digest)| hex64(Some(digest))))
    });
    if !library_ok {
        return Err("Shared proof-library inventory changed");
    }
    let files = library.and_then(|library| object(get(library, "files_sha256")));
    if !REQUIRED_MODULES
        .iter()
        .all(|name| files.is_some_and(|files| files.get(name).is_some()))
    {
        return Err("Required checked module is missing");
    }
    match get(config, "provenance") {
        Some(Value::Array(records)) if !records.is_empty() => {
            if !records.iter().all(|record| pin_shape(Some(record))) {
                return Err("Installation build/proof record changed");
            }
        }
        _ => return Err("Missing installation provenance"),
    }
    Ok(config)
}

/// The schema check of an installation value, with no file read.
pub fn check_section(config: &Value) -> Result<(), String> {
    schema(config).map(|_| ()).map_err(str::to_string)
}

fn pin_path(pin: Option<&Value>) -> PathBuf {
    PathBuf::from(
        object(pin)
            .and_then(|pin| text(get(pin, "path")))
            .unwrap_or_default(),
    )
}

fn pin_sha256(pin: Option<&Value>) -> &str {
    object(pin)
        .and_then(|pin| text(get(pin, "sha256")))
        .unwrap_or_default()
}

/// `verify_installation`: the schema, then the proof library and the provenance records rehashed. The binaries
/// are verified by `binaries_of` before their first execution.
pub fn verify_installation(config: &Value, check: Check) -> Result<(), Fault> {
    let config = schema(config).map_err(failure)?;
    let library = object(get(config, "proof_library"))
        .ok_or_else(|| failure("Shared proof-library inventory changed"))?;
    let actual = directory_inventory(
        Path::new(text(get(library, "path")).unwrap_or_default()),
        check,
    )?;
    if !library_matches(get(library, "files_sha256"), &actual) {
        return Err(failure("Shared proof-library inventory changed"));
    }
    if !REQUIRED_MODULES
        .iter()
        .all(|name| actual.contains_key(*name))
    {
        return Err(failure("Required checked module is missing"));
    }
    let Some(Value::Array(records)) = get(config, "provenance") else {
        return Err(failure("Missing installation provenance"));
    };
    for record in records {
        if digest_file(&pin_path(Some(record)), check)? != pin_sha256(Some(record)) {
            return Err(failure("Installation build/proof record changed"));
        }
    }
    Ok(())
}

/// installation.py's text for a binary whose hash or identity differs; the launcher is the running one.
fn refusal(name: &str) -> Fault {
    if name == "launcher" {
        failure("Running launcher differs from the installed launcher")
    } else {
        failure("Installed executable differs from its pin")
    }
}

/// The installation's binaries, for verification before their first execution: `engine`, `checker`, `lean`,
/// `launcher` and, when installed, `exporter`.
pub fn binaries_of(config: &Value) -> Result<Binaries, Fault> {
    let config = schema(config).map_err(failure)?;
    let pins = binaries(config)
        .into_iter()
        .map(|name| {
            let pin = get(config, name);
            let chunked = object(pin)
                .and_then(|pin| text(get(pin, "chunked_sha256")))
                .map(str::to_string);
            (
                name,
                Pin {
                    path: pin_path(pin),
                    sha256: pin_sha256(pin).to_string(),
                    chunked_sha256: chunked,
                },
            )
        })
        .collect();
    Binaries::new(pins, refusal)
}

/// The pinned path of `name` (`engine`, `checker`, `lean` or `exporter`).
pub fn binary(config: &Value, name: &str) -> PathBuf {
    pin_path(object(Some(config)).and_then(|config| config.get(name)))
}

/// What the installer gives the builder. The executed binaries carry their chunked SHA-256.
pub struct CnfInputs {
    pub launcher: Pin,
    pub engine: Pin,
    pub checker: Pin,
    pub lean: Pin,
    pub exporter: Option<Pin>,
    /// The built source inventory, relative path -> SHA-256; the exporter source hashes are taken from it.
    pub source_inventory: BTreeMap<String, String>,
    pub proof_library: Library,
    pub provenance: Vec<Record>,
}

fn record(record: &Record) -> Value {
    let mut pin = Object::new();
    pin.set("path", record.path.display().to_string());
    pin.set("sha256", record.sha256.clone());
    Value::Object(pin)
}

fn binary_pin(name: &str, pin: &Pin) -> Result<Value, String> {
    let chunked = pin
        .chunked_sha256
        .clone()
        .ok_or(format!("Missing chunked SHA-256 of the {name} pin"))?;
    let mut value = Object::new();
    value.set("path", pin.path.display().to_string());
    value.set("sha256", pin.sha256.clone());
    value.set("chunked_sha256", chunked);
    Ok(Value::Object(value))
}

/// Build the installation file's content for the installer (installation.py `make_installation`); the result
/// passes `check_section`.
pub fn build(inputs: &CnfInputs) -> Result<Value, String> {
    let mut config = Object::new();
    config.set("schema", SCHEMA);
    config.set("platform", "linux");
    let mut library = Object::new();
    library.set("path", inputs.proof_library.path.display().to_string());
    let mut files = Object::new();
    for (name, digest) in &inputs.proof_library.files_sha256 {
        files.set(name.as_str(), digest.clone());
    }
    library.set("files_sha256", Value::Object(files));
    config.set("proof_library", Value::Object(library));
    config.set(
        "provenance",
        Value::Array(inputs.provenance.iter().map(record).collect()),
    );
    config.set("engine", binary_pin("engine", &inputs.engine)?);
    config.set("checker", binary_pin("checker", &inputs.checker)?);
    config.set("lean", binary_pin("lean", &inputs.lean)?);
    config.set("launcher", binary_pin("launcher", &inputs.launcher)?);
    if let Some(exporter) = &inputs.exporter {
        config.set("exporter", binary_pin("exporter", exporter)?);
        let mut sources = Object::new();
        for name in EXPORTER_SOURCES {
            let digest = inputs
                .source_inventory
                .get(name)
                .ok_or("TSTP installation is missing exporter source")?;
            sources.set(name, digest.clone());
        }
        config.set("exporter_sources", Value::Object(sources));
    }
    if inputs.provenance.is_empty() {
        return Err("At least one reviewed build/proof provenance record is required".into());
    }
    for name in REQUIRED_MODULES {
        if !inputs.proof_library.files_sha256.contains_key(name) {
            return Err(format!("Installed proof library is missing {name}"));
        }
    }
    let config = Value::Object(config);
    check_section(&config)?;
    Ok(config)
}

/// `fang --self-check` on the installation file at `path`: load it, check the library and the provenance, and
/// verify every pinned binary, the running launcher included. Returns the number of pinned files checked.
pub fn self_check(path: &Path) -> Result<usize, String> {
    let loaded = crate::config::load(path, 32 << 20, None).map_err(|fault| fault.reason())?;
    let mut check = || Ok(());
    verify_installation(&loaded.value, &mut check).map_err(|fault| fault.reason())?;
    let config = object(Some(&loaded.value)).cloned().unwrap_or_default();
    let names = binaries(&config);
    let mut pinned = binaries_of(&loaded.value).map_err(|fault| fault.reason())?;
    pinned.start(&names);
    pinned.verify(&names).map_err(|fault| fault.reason())?;
    let library = object(get(&config, "proof_library"))
        .and_then(|library| object(get(library, "files_sha256")))
        .map_or(0, Object::len);
    let provenance = match get(&config, "provenance") {
        Some(Value::Array(records)) => records.len(),
        _ => 0,
    };
    Ok(names.len() + library + provenance)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pin(path: &str) -> Pin {
        Pin {
            path: PathBuf::from(path),
            sha256: "a".repeat(64),
            chunked_sha256: Some(fang_hash::chunked_text(&"d".repeat(64))),
        }
    }

    fn plain(path: &str) -> Record {
        Record {
            path: PathBuf::from(path),
            sha256: "a".repeat(64),
        }
    }

    fn inputs(exporter: bool) -> CnfInputs {
        let mut files = BTreeMap::new();
        for name in REQUIRED_MODULES {
            files.insert(name.to_string(), "b".repeat(64));
        }
        let mut sources = BTreeMap::new();
        for name in EXPORTER_SOURCES {
            sources.insert(name.to_string(), "c".repeat(64));
        }
        CnfInputs {
            launcher: pin("/i/bin/fang"),
            engine: pin("/i/bin/fang-engine"),
            checker: pin("/i/bin/fang-check"),
            lean: pin("/t/bin/lean"),
            exporter: exporter.then(|| pin("/i/bin/fang-tstp-export")),
            source_inventory: sources,
            proof_library: Library {
                path: PathBuf::from("/i/proof-library"),
                files_sha256: files,
            },
            provenance: vec![plain("/i/build-manifest.json")],
        }
    }

    #[test]
    fn the_builder_writes_what_the_schema_check_accepts() {
        for exporter in [false, true] {
            let value = build(&inputs(exporter)).unwrap();
            assert!(check_section(&value).is_ok());
            assert_eq!(exporting(&value), exporter);
        }
        let mut missing = inputs(true);
        missing.source_inventory.clear();
        assert_eq!(
            build(&missing).unwrap_err(),
            "TSTP installation is missing exporter source"
        );
        let mut bare = inputs(false);
        bare.provenance.clear();
        assert_eq!(
            build(&bare).unwrap_err(),
            "At least one reviewed build/proof provenance record is required"
        );
        let mut unchunked = inputs(false);
        unchunked.engine.chunked_sha256 = None;
        assert_eq!(
            build(&unchunked).unwrap_err(),
            "Missing chunked SHA-256 of the engine pin"
        );
    }

    #[test]
    fn the_schema_check_refuses_old_and_partial_files() {
        let Value::Object(mut value) = build(&inputs(true)).unwrap() else {
            unreachable!()
        };
        value.set("schema", "fang-local-installation-v2");
        assert_eq!(
            check_section(&Value::Object(value.clone())).unwrap_err(),
            "Unsupported installation schema"
        );
        value.set("schema", SCHEMA);
        let mut unchunked = value.clone();
        if let Some(Value::Object(engine)) = unchunked.get_mut("engine") {
            engine.remove("chunked_sha256");
        }
        assert_eq!(
            check_section(&Value::Object(unchunked)).unwrap_err(),
            "Malformed executable pin"
        );
        value.remove("exporter_sources");
        assert_eq!(
            check_section(&Value::Object(value)).unwrap_err(),
            "TSTP installation is missing exporter source"
        );
    }
}
