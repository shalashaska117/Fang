// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The ground-FOF capability file, schema `fang-ground-fof-capability-v3`: a port of
//! tools/fof_szs/capability.py `verify` without the Python pins. The launcher pin replaces the interpreter and
//! adapter-source pins; the build and proof receipts replace the per-run rehash of the source closure. Each
//! executed binary's pin (launcher, engine, checker, the kernel's Lean, the exporter) also holds its chunked
//! SHA-256: a run verifies the binaries it executes by that digest before their first execution and checks their
//! identity after the run (`binaries_of`); every other pin is rehashed by `verify`. Every refusal is
//! capability.py's ValueError text.

use std::collections::BTreeMap;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};

use fang_json::{Object, Value};
use fang_supervisor::{Failure, Fault};

use crate::capability::{Pin, Record};
pub use crate::older::Library;
use crate::older::binaries::Binaries;
use crate::older::{json_equal, value};
use crate::profile_ground_fof::toolchain;

pub const SCHEMA: &str = "fang-ground-fof-capability-v3";
pub const LANGUAGE: &str = "mixed-cnf-ground-fof-v1";
pub const ENVELOPE: &str = "fang-proof-2/ground-fof-distributive-v1";
pub const MAX_BYTES: i64 = 1 << 20;
pub const KERNEL_PROFILE: &str = "exact-v2-ground-fof-replay-v1";
/// input_bytes, certificate_bytes, certificate_nodes, generated_bytes.
pub const KERNEL_LIMITS: [(&str, i64); 4] = [
    ("input_bytes", 4096),
    ("certificate_bytes", 65536),
    ("certificate_nodes", 100),
    ("generated_bytes", 16 << 20),
];
const REQUIRED_THEOREM: &str = "Fang.FofTstpExport.RenderProof.decoded_render_checked_text";
const ALLOWED_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

type Check<'a> = &'a mut dyn FnMut() -> Result<(), Failure>;

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

fn strings(values: &[&str]) -> Value {
    Value::Array(
        values
            .iter()
            .map(|value| Value::String(value.to_string()))
            .collect(),
    )
}

fn keys(object: &Object) -> Vec<String> {
    let mut keys: Vec<String> = object.iter().map(|(key, _)| key.to_string()).collect();
    keys.sort();
    keys
}

fn same_keys(object: &Object, expected: &[&str]) -> bool {
    let mut wanted: Vec<String> = expected.iter().map(|key| key.to_string()).collect();
    wanted.sort();
    keys(object) == wanted
}

/// `digest` of capability.py: the SHA-256 of a regular file, checking the deadline between blocks.
pub fn digest(path: &Path, check: Check) -> Result<String, Fault> {
    check()?;
    let regular = fs::symlink_metadata(path)
        .map(|metadata| metadata.file_type().is_file())
        .map_err(Fault::at(path))?;
    if !regular {
        return Err(value(format!(
            "Pin must identify a regular file: {}",
            path.display()
        )));
    }
    let mut file = fs::File::open(path).map_err(Fault::at(path))?;
    let mut hasher = fang_hash::Hasher::new();
    let mut block = vec![0u8; 65536];
    loop {
        let read = file.read(&mut block).map_err(Fault::Os)?;
        if read == 0 {
            break;
        }
        check()?;
        hasher.update(&block[..read]);
    }
    Ok(fang_hash::hex(&hasher.finish()))
}

/// A `{path, sha256}` pin whose absolute path hashes to its value.
fn pin_holds(pin: Option<&Value>, check: Check) -> Result<bool, Fault> {
    let Some(pin) = object(pin) else {
        return Ok(false);
    };
    let (Some(path), Some(sha256)) = (text(get(pin, "path")), text(get(pin, "sha256"))) else {
        return Ok(false);
    };
    if !same_keys(pin, &["path", "sha256"]) || !Path::new(path).is_absolute() {
        return Ok(false);
    }
    Ok(digest(Path::new(path), check)? == sha256)
}

/// An executed binary's pin: `{path, sha256, chunked_sha256}` with an absolute path. Its file is verified by
/// `binaries_of` before its first execution, not here.
fn binary_shape(pin: Option<&Value>, extra: &[&str]) -> bool {
    let mut fields = vec!["path", "sha256", "chunked_sha256"];
    fields.extend_from_slice(extra);
    object(pin).is_some_and(|pin| {
        same_keys(pin, &fields)
            && text(get(pin, "path")).is_some_and(|path| Path::new(path).is_absolute())
            && text(get(pin, "sha256")).is_some_and(|sha256| sha256.len() == 64)
            && text(get(pin, "chunked_sha256")).is_some_and(crate::capability::is_chunked)
    })
}

/// `{path, sha256}` of a pin, without its chunked digest, for the comparisons with build records.
fn plain_pin(pin: Option<&Value>) -> Value {
    let mut plain = Object::new();
    if let Some(pin) = object(pin) {
        for field in ["path", "sha256"] {
            if let Some(value) = get(pin, field) {
                plain.set(field, value.clone());
            }
        }
    }
    Value::Object(plain)
}

/// capability.py's text for a binary whose hash or identity differs; the launcher is the running one.
fn refusal(name: &str) -> Fault {
    match name {
        "launcher" => value("Running launcher differs from capability"),
        "lean" => value("Kernel pin changed: lean"),
        "exporter" => value("Exporter executable changed"),
        other => value(format!("Executable pin changed: {other}")),
    }
}

/// The capability's binaries, for verification before their first execution: `launcher`, `engine`, `checker`
/// and, when installed, the kernel's `lean` and the `exporter`.
pub fn binaries_of(config: &Value) -> Result<Binaries, Fault> {
    let config = object(Some(config)).ok_or_else(|| value("Unsupported FOF capability schema"))?;
    let kernel = object(get(config, "kernel"));
    let mut pins: Vec<(&'static str, Option<&Value>)> = vec![
        ("launcher", get(config, "launcher")),
        ("engine", get(config, "engine")),
        ("checker", get(config, "checker")),
    ];
    if let Some(kernel) = kernel {
        pins.push(("lean", get(kernel, "lean")));
    }
    if let Some(exporter) = get(config, "exporter") {
        pins.push(("exporter", Some(exporter)));
    }
    let pins = pins
        .into_iter()
        .map(|(name, pin)| {
            let field = |key: &str| {
                object(pin)
                    .and_then(|pin| text(get(pin, key)))
                    .unwrap_or_default()
                    .to_string()
            };
            let chunked = Some(field("chunked_sha256")).filter(|text| !text.is_empty());
            (
                name,
                Pin {
                    path: PathBuf::from(field("path")),
                    sha256: field("sha256"),
                    chunked_sha256: chunked,
                },
            )
        })
        .collect();
    Binaries::new(pins, refusal)
}

/// `inventory` of capability.py: relative POSIX path -> SHA-256 of every file under a real directory.
pub fn inventory(root: &Path, check: Check) -> Result<Object, Fault> {
    let real = fs::symlink_metadata(root)
        .map(|metadata| metadata.is_dir())
        .unwrap_or(false);
    if !real {
        return Err(value("Library must be a real directory"));
    }
    let mut paths = Vec::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(directory) = pending.pop() {
        for entry in fs::read_dir(&directory).map_err(Fault::at(&directory))? {
            let path = entry.map_err(Fault::Os)?.path();
            let metadata = fs::symlink_metadata(&path).map_err(Fault::at(&path))?;
            if metadata.is_dir() {
                pending.push(path.clone());
            }
            paths.push((path, metadata));
        }
    }
    paths.sort_by(|left, right| left.0.cmp(&right.0));
    let mut result = Object::new();
    for (path, metadata) in paths {
        check()?;
        if metadata.file_type().is_symlink() {
            return Err(value("Library contains a symlink"));
        }
        if metadata.is_file() {
            let relative = path
                .strip_prefix(root)
                .unwrap_or(&path)
                .to_string_lossy()
                .to_string();
            result.set(relative.as_str(), digest(&path, check)?);
        } else if !metadata.is_dir() {
            return Err(value("Library contains a nonregular member"));
        }
    }
    Ok(result)
}

fn library_holds(library: Option<&Value>, check: Check) -> Result<bool, Fault> {
    let Some(library) = object(library) else {
        return Ok(false);
    };
    let Some(path) = text(get(library, "path")) else {
        return Ok(false);
    };
    if !same_keys(library, &["path", "files_sha256"]) || !Path::new(path).is_absolute() {
        return Ok(false);
    }
    let actual = inventory(Path::new(path), check)?;
    Ok(get(library, "files_sha256").is_some_and(|files| json_equal(&Value::Object(actual), files)))
}

fn has_files(library: &Value, names: &[&str]) -> bool {
    object(Some(library))
        .and_then(|library| object(get(library, "files_sha256")))
        .is_some_and(|files| names.iter().all(|name| files.get(name).is_some()))
}

/// `strict_json` of capability.py, with its own texts for a duplicate field and a non-finite constant.
pub fn strict_json(bytes: &[u8]) -> Result<Value, Fault> {
    let limits = fang_json::ParseLimits {
        max_bytes: usize::MAX,
        max_depth: 1 << 16,
    };
    fang_json::parse(bytes, &limits).map_err(|error| match error.kind {
        fang_json::ErrorKind::DuplicateKey => value("Duplicate capability field"),
        fang_json::ErrorKind::Nonfinite => value("Nonfinite JSON value"),
        _ => value(error.python_message(bytes)),
    })
}

fn read_json(path: &str, check: Check) -> Result<Value, Fault> {
    let bytes = fang_supervisor::read_regular(Path::new(path), 32 << 20, check)?;
    strict_json(&bytes)
}

/// The installed profiles and outputs this capability declares, after the schema check.
pub struct Declared {
    pub kernel: bool,
    pub exporting: bool,
}

/// The schema check of a capability value, with no file read: the field set, the fixed values and the shape
/// of every pin. Returns which profiles and outputs it declares.
pub fn check_section(config: &Value) -> Result<Declared, String> {
    let Some(config) = object(Some(config)) else {
        return Err("Unsupported FOF capability schema".into());
    };
    let compiled = strings(&["compiled"]);
    let both = strings(&["kernel", "compiled"]);
    let kernel = get(config, "profiles").is_some_and(|profiles| json_equal(profiles, &both));
    let exporting = get(config, "outputs")
        .is_some_and(|outputs| json_equal(outputs, &strings(&["status", "tstp"])));
    let mut expected = vec![
        "schema",
        "language",
        "certificate",
        "profiles",
        "outputs",
        "max_input_bytes",
        "max_certificate_bytes",
        "launcher",
        "engine",
        "checker",
        "proof_library",
        "receipts",
    ];
    if kernel {
        expected.push("kernel");
    }
    if exporting {
        expected.push("exporter");
    }
    if !same_keys(config, &expected)
        || text(get(config, "schema")) != Some(SCHEMA)
        || text(get(config, "language")) != Some(LANGUAGE)
        || text(get(config, "certificate")) != Some(ENVELOPE)
    {
        return Err("Unsupported FOF capability schema".into());
    }
    let profiles_ok =
        kernel || get(config, "profiles").is_some_and(|profiles| json_equal(profiles, &compiled));
    let outputs_ok = exporting
        || get(config, "outputs").is_some_and(|outputs| json_equal(outputs, &strings(&["status"])));
    if !profiles_ok || !outputs_ok || (exporting && !kernel) {
        return Err("Unimplemented checking/output capability".into());
    }
    for name in ["engine", "checker", "launcher"] {
        if !binary_shape(get(config, name), &[]) {
            return Err(format!("Executable pin changed: {name}"));
        }
    }
    if kernel
        && !binary_shape(
            object(get(config, "kernel")).and_then(|kernel| get(kernel, "lean")),
            &[],
        )
    {
        return Err("Kernel pin changed: lean".into());
    }
    if exporting && !binary_shape(get(config, "exporter"), &["proof_receipt", "build_receipt"]) {
        return Err("Exporter executable changed".into());
    }
    let cap = Value::from(MAX_BYTES);
    if !get(config, "max_input_bytes").is_some_and(|value| json_equal(value, &cap))
        || !get(config, "max_certificate_bytes").is_some_and(|value| json_equal(value, &cap))
    {
        return Err("Capability differs from the actual checker byte limits".into());
    }
    Ok(Declared { kernel, exporting })
}

/// `verify` of capability.py for schema v3: the binaries' pins are checked for their shape here and their files
/// by `binaries_of` before their first execution; every other pin is rehashed.
pub fn verify(config: &Value, check: Check) -> Result<Declared, Fault> {
    let declared = check_section(config).map_err(value)?;
    let config = object(Some(config)).ok_or_else(|| value("Unsupported FOF capability schema"))?;
    for name in ["engine", "checker", "launcher"] {
        if !binary_shape(get(config, name), &[]) {
            return Err(value(format!("Executable pin changed: {name}")));
        }
    }
    let library = get(config, "proof_library").cloned().unwrap_or(Value::Null);
    if !library_holds(Some(&library), check)? {
        return Err(value("Checked library inventory changed"));
    }
    for name in [
        "Fang/FOF/VersionedCheck.olean",
        "Fang/FOF/FOFByteSemantics.olean",
        "Fang/FOF/FofCertificateInput.olean",
    ] {
        if !has_files(&library, &[name]) {
            return Err(value(format!(
                "Required checked FOF module missing: {name}"
            )));
        }
    }
    let receipts = match get(config, "receipts") {
        Some(Value::Array(receipts)) if !receipts.is_empty() => receipts,
        _ => return Err(value("Missing build/proof receipt pins")),
    };
    for receipt in receipts {
        if !pin_holds(Some(receipt), check)? {
            return Err(value("Build/proof receipt changed"));
        }
    }
    if declared.kernel {
        verify_kernel(
            object(get(config, "kernel")).ok_or_else(|| value("Unsupported kernel capability"))?,
            check,
        )?;
    }
    if declared.exporting {
        let build = verify_exporter(
            object(get(config, "exporter"))
                .ok_or_else(|| value("Unsupported exporter capability"))?,
            check,
        )?;
        if !get(&build, "library_sha256").is_some_and(|files| {
            object(get(config, "proof_library"))
                .and_then(|library| get(library, "files_sha256"))
                .is_some_and(|ours| json_equal(ours, files))
        }) {
            return Err(value("Exporter and checker source/library linkage differs"));
        }
        verify_portable_links(config, &build)?;
    }
    Ok(declared)
}

fn verify_kernel(kernel: &Object, check: Check) -> Result<(), Fault> {
    if !same_keys(
        kernel,
        &[
            "profile",
            "lean",
            "library",
            "limits",
            "receipt",
            "toolchain",
        ],
    ) || text(get(kernel, "profile")) != Some(KERNEL_PROFILE)
    {
        return Err(value("Unsupported kernel capability"));
    }
    let mut limits = Object::new();
    for (name, bound) in KERNEL_LIMITS {
        limits.set(name, Value::from(bound));
    }
    if !get(kernel, "limits").is_some_and(|value| json_equal(value, &Value::Object(limits))) {
        return Err(value("Kernel replay bounds differ"));
    }
    if !binary_shape(get(kernel, "lean"), &[]) {
        return Err(value("Kernel pin changed: lean"));
    }
    if !pin_holds(get(kernel, "receipt"), check)? {
        return Err(value("Kernel pin changed: receipt"));
    }
    if !library_holds(get(kernel, "library"), check)? {
        return Err(value("Kernel library inventory changed"));
    }
    let library = get(kernel, "library").cloned().unwrap_or(Value::Null);
    if !has_files(
        &library,
        &[
            "Fang/FOF/Replay.olean",
            "Fang/FOF/VersionedCheck.olean",
            "Fang/FOF/FOFByteSemantics.olean",
        ],
    ) {
        return Err(value("Kernel library lacks the required checked modules"));
    }
    let tree = object(get(kernel, "toolchain"))
        .ok_or_else(|| value("Toolchain root differs from Lean's installed sysroot"))?;
    let lean = object(get(kernel, "lean"))
        .and_then(|lean| text(get(lean, "path")))
        .unwrap_or_default();
    let sysroot = Path::new(lean).parent().and_then(Path::parent);
    if !same_keys(tree, &["path", "inventory", "receipt"])
        || text(get(tree, "path")).map(Path::new) != sysroot
    {
        return Err(value(
            "Toolchain root differs from Lean's installed sysroot",
        ));
    }
    for name in ["inventory", "receipt"] {
        if !pin_holds(get(tree, name), check)? {
            return Err(value("Toolchain inventory/receipt pin changed"));
        }
    }
    let inventory_path = object(get(tree, "inventory"))
        .and_then(|pin| text(get(pin, "path")))
        .unwrap_or_default();
    let expected = read_json(inventory_path, check)?;
    toolchain::verify(
        Path::new(text(get(tree, "path")).unwrap_or_default()),
        &expected,
        check,
    )
}

fn verify_exporter(exporter: &Object, check: Check) -> Result<Object, Fault> {
    if !same_keys(
        exporter,
        &[
            "path",
            "sha256",
            "chunked_sha256",
            "proof_receipt",
            "build_receipt",
        ],
    ) {
        return Err(value("Unsupported exporter capability"));
    }
    let path = text(get(exporter, "path")).unwrap_or_default();
    let sha256 = text(get(exporter, "sha256")).unwrap_or_default();
    // The exporter's file is verified by `binaries_of` before it runs.
    if !binary_shape(
        Some(&Value::Object(exporter.clone())),
        &["proof_receipt", "build_receipt"],
    ) {
        return Err(value("Exporter executable changed"));
    }
    for name in ["proof_receipt", "build_receipt"] {
        if !pin_holds(get(exporter, name), check)? {
            return Err(value(format!("Exporter receipt changed: {name}")));
        }
    }
    let pin = |name: &str, field: &str| {
        object(get(exporter, name))
            .and_then(|pin| text(get(pin, field)))
            .unwrap_or_default()
            .to_string()
    };
    let Value::Object(proof) = read_json(&pin("proof_receipt", "path"), check)? else {
        return Err(value("Exporter source/build/proof linkage differs"));
    };
    let Value::Object(build) = read_json(&pin("build_receipt", "path"), check)? else {
        return Err(value("Exporter source/build/proof linkage differs"));
    };
    let installation = PathBuf::from(pin("build_receipt", "path"))
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_default();
    let fof = object(get(&build, "fof"));
    let exporter_sha = fof
        .and_then(|fof| object(get(fof, "binaries_sha256")))
        .and_then(|binaries| text(get(binaries, "fang-fof-tstp-export")));
    let linked = text(get(&proof, "status")) == Some("passed")
        && text(get(&build, "status")) == Some("built-and-checked")
        && text(get(&build, "proof_suite_sha256")) == Some(pin("proof_receipt", "sha256").as_str())
        && text(get(&build, "proof_suite")) == Some(pin("proof_receipt", "path").as_str())
        && Path::new(path) == installation.join("bin/fang-fof-tstp-export")
        && exporter_sha == Some(sha256)
        && match (
            get(&build, "library_sha256"),
            get(&proof, "build_output_sha256"),
        ) {
            (Some(left), Some(right)) => json_equal(left, right),
            _ => false,
        };
    if !linked {
        return Err(value("Exporter source/build/proof linkage differs"));
    }
    let rows: Vec<&Object> = match get(&proof, "axiom_audits") {
        Some(Value::Array(rows)) => rows.iter().filter_map(|row| object(Some(row))).collect(),
        _ => Vec::new(),
    };
    let matching: Vec<&&Object> = rows
        .iter()
        .filter(|row| {
            text(get(row, "module")) == Some("Fang.FOF.TSTP.Audit")
                && text(get(row, "declaration")) == Some(REQUIRED_THEOREM)
        })
        .collect();
    let allowed = |row: &Object| match get(row, "axioms") {
        Some(Value::Array(axioms)) => axioms.iter().all(
            |axiom| matches!(axiom, Value::String(name) if ALLOWED_AXIOMS.contains(&name.as_str())),
        ),
        _ => false,
    };
    let theorem = fof
        .and_then(|fof| object(get(fof, "exporter")))
        .and_then(|exporter| text(get(exporter, "theorem")));
    if matching.len() != 1 || !allowed(matching[0]) || theorem != Some(REQUIRED_THEOREM) {
        return Err(value("Exporter proof lacks its connected text theorem"));
    }
    let relative_sources = object(get(&build, "source_sha256"))
        .cloned()
        .unwrap_or_default();
    let unsafe_name = |name: &str| {
        let path = Path::new(name);
        path.is_absolute()
            || path
                .components()
                .any(|component| component == std::path::Component::ParentDir)
    };
    if relative_sources.is_empty() || relative_sources.iter().any(|(name, _)| unsafe_name(name)) {
        return Err(value("Invalid built source inventory"));
    }
    let required = [
        "lean/Fang/FOF/TstpExport.lean",
        "lean/FofTstpMain.lean",
        "lean/Fang/BoundedInput.lean",
        "proofs/fof-tstp/CheckedText.lean",
        "proofs/fof-tstp/Audit.lean",
        "tools/fof_proof_inventory.json",
    ];
    if required
        .iter()
        .any(|name| relative_sources.get(name).is_none())
    {
        return Err(value("Exporter source closure differs"));
    }
    // Every compiled Lean source must match the same captured source package.
    let mut checked: BTreeMap<String, Value> = BTreeMap::new();
    for (name, digest) in relative_sources.iter() {
        let target = if let Some(rest) = name.strip_prefix("lean/").filter(|_| {
            name.ends_with(".lean")
                || [
                    "lean/lean-toolchain",
                    "lean/lakefile.toml",
                    "lean/check-local.sh",
                ]
                .contains(&name)
        }) {
            rest.to_string()
        } else if let Some(rest) = name
            .strip_prefix("proofs/fof-tstp/")
            .filter(|_| name.ends_with(".lean"))
        {
            format!("Fang/FOF/TSTP/{rest}")
        } else if let Some(rest) = name
            .strip_prefix("proofs/tstp/")
            .filter(|_| name.ends_with(".lean"))
        {
            rest.to_string()
        } else {
            continue;
        };
        if checked.insert(target, digest.clone()).is_some() {
            return Err(value("Duplicate checked proof module"));
        }
    }
    let mut checked_object = Object::new();
    for (name, digest) in checked {
        checked_object.set(name.as_str(), digest);
    }
    if !get(&proof, "source_sha256")
        .is_some_and(|sources| json_equal(sources, &Value::Object(checked_object)))
    {
        return Err(value("Checked proof sources differ from the build"));
    }
    let inventory_pin = fof
        .and_then(|fof| object(get(fof, "exporter")))
        .and_then(|exporter| get(exporter, "inventory_sha256"));
    if !match (
        relative_sources.get("tools/fof_proof_inventory.json"),
        inventory_pin,
    ) {
        (Some(left), Some(right)) => json_equal(left, right),
        _ => false,
    } {
        return Err(value("Required exporter proof inventory changed"));
    }
    check_proofs(
        &installation.join("source"),
        &relative_sources,
        &proof,
        check,
    )?;
    Ok(build)
}

/// `fof_tstp_setup.check_proofs`, reading the proof inventory the build recorded (its bytes checked against the
/// build's hash) instead of trusting the source tree.
fn check_proofs(
    frozen: &Path,
    sources: &Object,
    proof: &Object,
    check: Check,
) -> Result<(), Fault> {
    let path = frozen.join("tools/fof_proof_inventory.json");
    let bytes = fang_supervisor::read_regular(&path, 32 << 20, check)?;
    if text(sources.get("tools/fof_proof_inventory.json"))
        != Some(fang_hash::sha256_hex(&bytes).as_str())
    {
        return Err(value("Required exporter proof inventory changed"));
    }
    let differs = || value("Required ground-FOF proof inventory differs");
    let Value::Object(inventory) = fang_supervisor::strict_json(&bytes)? else {
        return Err(differs());
    };
    let modules: Vec<String> = match get(&inventory, "modules") {
        Some(Value::Array(items)) => items
            .iter()
            .filter_map(|item| text(Some(item)).map(str::to_string))
            .collect(),
        _ => return Err(differs()),
    };
    let audits = object(get(&inventory, "audits")).ok_or_else(differs)?;
    let mut wanted: Vec<(String, String)> = Vec::new();
    for (module, names) in audits.iter() {
        let Value::Array(names) = names else {
            return Err(differs());
        };
        let names: Vec<String> = names
            .iter()
            .filter_map(|name| text(Some(name)).map(str::to_string))
            .collect();
        let mut unique = names.clone();
        unique.sort();
        unique.dedup();
        if unique.len() != names.len() || !modules.iter().any(|name| name == module) {
            return Err(differs());
        }
        wanted.extend(names.into_iter().map(|name| (module.to_string(), name)));
    }
    let mut unique_modules = modules.clone();
    unique_modules.sort();
    unique_modules.dedup();
    let text_theorem = audits.get("Fang.FOF.TSTP.Audit").is_some_and(|names| {
        matches!(names, Value::Array(names) if names.iter().any(|name| matches!(name, Value::String(n) if n == REQUIRED_THEOREM)))
    });
    if !same_keys(&inventory, &["schema", "modules", "audits"])
        || text(get(&inventory, "schema")) != Some("fang-ground-fof-proof-inventory-v1")
        || unique_modules.len() != modules.len()
        || !text_theorem
    {
        return Err(differs());
    }
    let rows: Vec<&Object> = match get(proof, "axiom_audits") {
        Some(Value::Array(rows)) => rows.iter().filter_map(|row| object(Some(row))).collect(),
        _ => Vec::new(),
    };
    let actual: Vec<(String, String)> = rows
        .iter()
        .map(|row| {
            (
                text(get(row, "module")).unwrap_or_default().to_string(),
                text(get(row, "declaration"))
                    .unwrap_or_default()
                    .to_string(),
            )
        })
        .collect();
    let mut completed: Vec<String> = match get(proof, "completed_modules") {
        Some(Value::Array(items)) => items
            .iter()
            .filter_map(|item| text(Some(item)).map(str::to_string))
            .collect(),
        _ => Vec::new(),
    };
    completed.sort();
    let mut expected_modules = modules.clone();
    expected_modules.sort();
    let mut wanted_set = wanted.clone();
    wanted_set.sort();
    wanted_set.dedup();
    let mut actual_set = actual.clone();
    actual_set.sort();
    actual_set.dedup();
    let declared = get(proof, "declared_axiom_audits")
        .is_some_and(|count| json_equal(count, &Value::from(wanted_set.len() as i64)));
    if text(get(proof, "status")) != Some("passed")
        || completed != expected_modules
        || actual.len() != wanted_set.len()
        || actual_set != wanted_set
        || !declared
    {
        return Err(value(
            "Required combined proof inventory did not pass or an audit differs",
        ));
    }
    let allowed = rows.iter().all(|row| match get(row, "axioms") {
        Some(Value::Array(axioms)) => axioms.iter().all(
            |axiom| matches!(axiom, Value::String(name) if ALLOWED_AXIOMS.contains(&name.as_str())),
        ),
        _ => false,
    });
    if !allowed {
        return Err(value("Unexpected FOF theorem axiom"));
    }
    Ok(())
}

fn pin_value(path: &Path, sha256: &str) -> Value {
    let mut pin = Object::new();
    pin.set("path", path.display().to_string());
    pin.set("sha256", sha256.to_string());
    Value::Object(pin)
}

fn verify_portable_links(config: &Object, build: &Object) -> Result<(), Fault> {
    let exporter = object(get(config, "exporter")).cloned().unwrap_or_default();
    let receipt = get(&exporter, "build_receipt")
        .cloned()
        .unwrap_or(Value::Null);
    let receipt_path = object(Some(&receipt))
        .and_then(|pin| text(get(pin, "path")))
        .unwrap_or_default();
    let installed = Path::new(receipt_path)
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_default();
    let fof = object(get(build, "fof")).cloned().unwrap_or_default();
    let binaries = object(get(&fof, "binaries_sha256"))
        .cloned()
        .unwrap_or_default();
    for (key, binary) in [
        ("engine", "fang-ground-fof-driver"),
        ("checker", "fang-fof-check"),
    ] {
        let expected = pin_value(
            &installed.join("bin").join(binary),
            text(get(&binaries, binary)).unwrap_or_default(),
        );
        if !json_equal(&plain_pin(get(config, key)), &expected) {
            return Err(value(format!(
                "Executing FOF binary differs from its build: {key}"
            )));
        }
    }
    let mut library = Object::new();
    library.set(
        "path",
        installed.join("proof-library").display().to_string(),
    );
    library.set(
        "files_sha256",
        get(build, "library_sha256").cloned().unwrap_or(Value::Null),
    );
    let library = Value::Object(library);
    let kernel = object(get(config, "kernel")).cloned().unwrap_or_default();
    let receipts = Value::Array(vec![receipt.clone()]);
    let same = |value: Option<&Value>, expected: &Value| {
        value.is_some_and(|value| json_equal(value, expected))
    };
    if !same(get(config, "proof_library"), &library)
        || !same(get(&kernel, "library"), &library)
        || !same(get(&kernel, "receipt"), &receipt)
        || !same(get(config, "receipts"), &receipts)
    {
        return Err(value("Kernel library/receipt differs from its build"));
    }
    let info = object(get(&fof, "toolchain")).cloned().unwrap_or_default();
    let root = text(get(&info, "path")).unwrap_or_default();
    let mut tree = Object::new();
    tree.set("path", root.to_string());
    tree.set(
        "inventory",
        pin_value(
            Path::new(text(get(&info, "inventory")).unwrap_or_default()),
            text(get(&info, "inventory_sha256")).unwrap_or_default(),
        ),
    );
    tree.set("receipt", receipt.clone());
    let lean = pin_value(
        &Path::new(root).join("bin/lean"),
        text(get(&info, "lean_sha256")).unwrap_or_default(),
    );
    if !same(get(&kernel, "toolchain"), &Value::Object(tree))
        || !json_equal(&plain_pin(get(&kernel, "lean")), &lean)
        || !matches!(
            get(&info, "verified_before_and_after"),
            Some(Value::Bool(true))
        )
    {
        return Err(value("Kernel helpers/toolchain differ from their build"));
    }
    Ok(())
}

/// What the installer gives the builder. The executed binaries carry their chunked SHA-256.
pub struct GroundFofInputs {
    pub launcher: Pin,
    pub engine: Pin,
    pub checker: Pin,
    pub proof_library: Library,
    pub receipts: Vec<Record>,
    pub kernel: Option<GroundFofKernel>,
    pub exporter: Option<GroundFofExporter>,
}

pub struct GroundFofKernel {
    pub lean: Pin,
    pub library: Library,
    pub receipt: Record,
    pub toolchain: GroundFofToolchain,
}

/// The installed Lean toolchain: its root, its reviewed inventory and the receipt that records it.
pub struct GroundFofToolchain {
    pub path: PathBuf,
    pub inventory: Record,
    pub receipt: Record,
}

pub struct GroundFofExporter {
    pub exporter: Pin,
    pub proof_receipt: Record,
    pub build_receipt: Record,
}

fn record(record: &Record) -> Value {
    pin_value(&record.path, &record.sha256)
}

fn binary_pin(name: &str, pin: &Pin) -> Result<Object, String> {
    let chunked = pin
        .chunked_sha256
        .clone()
        .ok_or(format!("Missing chunked SHA-256 of the {name} pin"))?;
    let mut value = Object::new();
    value.set("path", pin.path.display().to_string());
    value.set("sha256", pin.sha256.clone());
    value.set("chunked_sha256", chunked);
    Ok(value)
}

fn library(library: &Library) -> Value {
    let mut object = Object::new();
    object.set("path", library.path.display().to_string());
    let mut inventory = Object::new();
    for (name, digest) in &library.files_sha256 {
        inventory.set(name.as_str(), digest.clone());
    }
    object.set("files_sha256", Value::Object(inventory));
    Value::Object(object)
}

/// Build the capability file's content for the installer; the result passes `check_section`.
pub fn build(inputs: &GroundFofInputs) -> Result<Value, String> {
    let mut config = Object::new();
    config.set("schema", SCHEMA);
    config.set("language", LANGUAGE);
    config.set("certificate", ENVELOPE);
    config.set(
        "profiles",
        if inputs.kernel.is_some() {
            strings(&["kernel", "compiled"])
        } else {
            strings(&["compiled"])
        },
    );
    config.set(
        "outputs",
        if inputs.exporter.is_some() {
            strings(&["status", "tstp"])
        } else {
            strings(&["status"])
        },
    );
    config.set("max_input_bytes", Value::from(MAX_BYTES));
    config.set("max_certificate_bytes", Value::from(MAX_BYTES));
    config.set(
        "launcher",
        Value::Object(binary_pin("launcher", &inputs.launcher)?),
    );
    config.set(
        "engine",
        Value::Object(binary_pin("engine", &inputs.engine)?),
    );
    config.set(
        "checker",
        Value::Object(binary_pin("checker", &inputs.checker)?),
    );
    config.set("proof_library", library(&inputs.proof_library));
    config.set(
        "receipts",
        Value::Array(inputs.receipts.iter().map(record).collect()),
    );
    if let Some(kernel) = &inputs.kernel {
        let mut limits = Object::new();
        for (name, bound) in KERNEL_LIMITS {
            limits.set(name, Value::from(bound));
        }
        let mut tree = Object::new();
        tree.set("path", kernel.toolchain.path.display().to_string());
        tree.set("inventory", record(&kernel.toolchain.inventory));
        tree.set("receipt", record(&kernel.toolchain.receipt));
        let mut entry = Object::new();
        entry.set("profile", KERNEL_PROFILE);
        entry.set("lean", Value::Object(binary_pin("lean", &kernel.lean)?));
        entry.set("library", library(&kernel.library));
        entry.set("limits", Value::Object(limits));
        entry.set("receipt", record(&kernel.receipt));
        entry.set("toolchain", Value::Object(tree));
        config.set("kernel", Value::Object(entry));
    }
    if let Some(exporter) = &inputs.exporter {
        let mut entry = binary_pin("exporter", &exporter.exporter)?;
        entry.set("proof_receipt", record(&exporter.proof_receipt));
        entry.set("build_receipt", record(&exporter.build_receipt));
        config.set("exporter", Value::Object(entry));
    }
    let config = Value::Object(config);
    check_section(&config)?;
    Ok(config)
}

/// `fang --self-check` on the capability file at `path`: load it, rehash every pin and verify every binary, the
/// running launcher included. Returns the number of pinned files checked.
pub fn self_check(path: &Path) -> Result<usize, String> {
    let loaded = crate::config::load(path, 32 << 20, None).map_err(|fault| fault.reason())?;
    let mut check = || Ok(());
    let declared = verify(&loaded.value, &mut check).map_err(|fault| fault.python_str())?;
    let mut names = vec!["launcher", "engine", "checker"];
    if declared.kernel {
        names.push("lean");
    }
    if declared.exporting {
        names.push("exporter");
    }
    let mut binaries = binaries_of(&loaded.value).map_err(|fault| fault.python_str())?;
    binaries.start(&names);
    binaries
        .verify(&names)
        .map_err(|fault| fault.python_str())?;
    let config = object(Some(&loaded.value)).cloned().unwrap_or_default();
    let count = |value: Option<&Value>| {
        object(value)
            .and_then(|library| object(get(library, "files_sha256")))
            .map_or(0, Object::len)
    };
    let receipts = match get(&config, "receipts") {
        Some(Value::Array(receipts)) => receipts.len(),
        _ => 0,
    };
    let mut pins = 3 + receipts + count(get(&config, "proof_library"));
    if declared.kernel {
        let kernel = object(get(&config, "kernel")).cloned().unwrap_or_default();
        pins += 4 + count(get(&kernel, "library"));
    }
    if declared.exporting {
        pins += 3;
    }
    Ok(pins)
}
