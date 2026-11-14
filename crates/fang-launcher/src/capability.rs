// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The installed version-8 capability, schema v8: the launcher, the pinned binaries of every path, the older
//! profiles' pinned configuration files and the provenance records.
//!
//! An absent feature is a null section. The `bundle` section pins the bundle producer and checker for
//! axiom-only inputs with include directives, distinct objects or annotations; `signed` pins the signed
//! producer and checker for inputs with roles other than axiom; `tstp` pins the single-file exporter and,
//! when installed, the bundle exporter (`bundle_exporter`), the conjecture exporter (`goal_exporter`) and a
//! conjecture exporter with an inputs mode (`inputs_exporter`), for a signed single file with no conjecture to
//! prove. `cited_exporter` pins a build with both cited bundle modes, for goals and input refutations;
//! `model` pins the model producer, the model checker and, when installed, the model exporter; `kernel` pins
//! kernel mode. `cnf` and `ground_fof` pin the older profiles' own configuration files, whose schemas belong
//! to those profiles. Every record pins a file's SHA-256; a binary's record also pins its chunked SHA-256
//! (`chunked_sha256`, in fang-hash's tagged text form), which each run verifies. Verification is split by when
//! it runs; `PER_RUN` says how and is written into every capability.

use std::path::{Path, PathBuf};

use fang_json::{Number, Object, Value};
use fang_supervisor::Fault;

pub const SCHEMA: &str = "fang-v8-capability-v8";
pub const LANGUAGE: &str = "expanded-fof-equality-skolem-distributive-v1";
pub const MAX_BYTES: u64 = 1 << 20;
/// The final limits record's certificateLimit; the refutation checkers read a certificate up to it.
pub const MAX_CERTIFICATE_BYTES: u64 = 5_081_233;
/// The model checker reads a model certificate up to the byte limit.
pub const MAX_MODEL_BYTES: u64 = MAX_BYTES;
pub const DEFAULT_CHECK: &str = "compiled";
/// Limits that --check kernel needs: (option, minimum).
pub const KERNEL_MINIMUMS: [(&str, u64); 3] = [
    ("--wall-seconds", 600),
    ("--memory-mib", 4096),
    ("--max-artifact-bytes", 1 << 30),
];
/// Byte bound of the capability file itself.
pub const CAPABILITY_BYTES: u64 = 32 << 20;

const REQUIRED: [&str; 18] = [
    "bundle",
    "certificate_version",
    "checker",
    "cnf",
    "default_check",
    "engine",
    "ground_fof",
    "kernel",
    "language",
    "launcher",
    "max_certificate_bytes",
    "max_input_bytes",
    "model",
    "per_run_verification",
    "provenance",
    "schema",
    "signed",
    "tstp",
];
const KERNEL_FIELDS: [&str; 4] = ["entry", "installation", "output_root", "witness"];

/// The per-run verification policy, written into every capability as `per_run_verification`.
pub const PER_RUN: [(&str, &str); 5] = [
    (
        "after_execution",
        "Before a positive status, each file hashed before execution must keep its device, inode, size, mtime_ns \
      and ctime_ns. ctime cannot be set by a user, so an in-place rewrite that restores mtime is still seen.",
    ),
    (
        "before_execution",
        "SHA-256 of the launcher at start. Once the input is routed, the binaries the route may run are hashed \
      in background threads, each as the chunked SHA-256 its record pins (4 MiB chunks hashed in parallel), and \
      each must match before its first execution. Single file: engine and checker, plus the exporter when TSTP \
      is requested; with --check kernel, engine, witness, kernel entry and its installation record instead of \
      the checker. Bundle: bundle producer and checker, plus the bundle exporter when TSTP is requested. \
      Signed: signed producer and checker, plus the conjecture exporters when TSTP is requested. With --check \
      none, the producer of the path and, on the signed path, the checker that lists the conjectures. In \
      compiled mode, when the installation has them, the finite model producer and the model checker, plus the \
      model exporter when TSTP is requested.",
    ),
    (
        "full",
        "Install time and fang --self-check hash the launcher, every pinned file and the older profiles' pinned \
      configuration files, and check both digests of every binary.",
    ),
    (
        "not_per_run",
        "Provenance records and the binaries of other routes and modes. A change to them cannot affect the run's \
      result; it is found when a run executes them, by fang --self-check, or at install time.",
    ),
    (
        "why",
        "Hashes detect artifact changes; they do not prove correct execution, and artifact identity is trusted \
      (docs/DESIGN.md). The route's binaries are hashed at launch, each before it first runs, so every executed \
      byte is checked while the hashing overlaps the run.",
    ),
];

/// One pinned file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Record {
    pub path: PathBuf,
    pub sha256: String,
}

/// A loaded capability: the checked JSON value.
#[derive(Clone, Debug)]
pub struct Capability {
    value: Object,
    /// SHA-256 of the capability file's bytes.
    pub sha256: String,
    pub path: PathBuf,
}

impl Capability {
    /// Read, parse and check the capability at `path`; no pinned file is read. A schema mismatch is a
    /// `Fault::Value`, as the Python ValueError was.
    pub fn load(path: &Path) -> Result<Capability, Fault> {
        let mut check = || -> Result<(), fang_supervisor::Failure> { Ok(()) };
        let bytes = fang_supervisor::read_regular(path, CAPABILITY_BYTES, &mut check)?;
        let value = fang_supervisor::strict_json(&bytes)?;
        let Value::Object(object) = value else {
            return Err(Fault::Value(
                "Unexpected version-8 capability fields".to_string(),
            ));
        };
        check_fields(&object).map_err(Fault::Value)?;
        Ok(Capability {
            value: object,
            sha256: fang_hash::sha256_hex(&bytes),
            path: path.to_path_buf(),
        })
    }

    /// The JSON value, for the run record.
    pub fn value(&self) -> &Object {
        &self.value
    }

    pub fn section(&self, name: &str) -> Option<&Object> {
        match self.value.get(name) {
            Some(Value::Object(section)) => Some(section),
            _ => None,
        }
    }

    pub fn record(&self, name: &str) -> Record {
        record_of(self.value.get(name)).expect("checked by check_fields")
    }

    pub fn section_record(&self, section: &str, name: &str) -> Option<Record> {
        self.section(section)
            .and_then(|object| record_of(object.get(name)))
    }

    pub fn launcher(&self) -> Record {
        self.record("launcher")
    }

    /// The pinned configuration file of the CNF profile, when installed.
    pub fn cnf(&self) -> Option<Record> {
        self.section_record("cnf", "installation")
    }

    /// The pinned configuration file of the ground-FOF profile, when installed.
    pub fn ground_fof(&self) -> Option<Record> {
        self.section_record("ground_fof", "capability")
    }

    /// The JSON value of every pinned record, in the order install time and self-check report them.
    fn pinned_values(&self) -> Vec<&Value> {
        let mut values: Vec<&Value> = ["launcher", "engine", "checker"]
            .iter()
            .filter_map(|name| self.value.get(name))
            .collect();
        if let Some(Value::Array(items)) = self.value.get("provenance") {
            values.extend(items.iter());
        }
        for (section, names) in [
            ("bundle", &["producer", "checker"][..]),
            ("signed", &["producer", "checker", "single_producer"][..]),
            (
                "tstp",
                &[
                    "exporter",
                    "bundle_exporter",
                    "goal_exporter",
                    "inputs_exporter",
                    "cited_exporter",
                ][..],
            ),
            ("model", &["producer", "checker", "exporter"][..]),
            (
                "kernel",
                &["witness", "entry", "installation", "producer"][..],
            ),
            ("cnf", &["installation"][..]),
            ("ground_fof", &["capability"][..]),
        ] {
            for name in names {
                if let Some(value) = self.section(section).and_then(|object| object.get(name)) {
                    values.push(value);
                }
            }
        }
        values
    }

    /// Every pinned record, for install time and `fang --self-check`.
    pub fn pinned_records(&self) -> Vec<Record> {
        self.pinned_values()
            .into_iter()
            .filter_map(|value| record_of(Some(value)))
            .collect()
    }

    /// Every pinned file with both of its digests; only binaries have the chunked one.
    pub fn pins(&self) -> Vec<Pin> {
        self.pinned_values()
            .into_iter()
            .filter_map(|value| {
                let record = record_of(Some(value))?;
                Some(Pin {
                    path: record.path,
                    sha256: record.sha256,
                    chunked_sha256: chunked_of(Some(value)),
                })
            })
            .collect()
    }
}

/// A pinned file with the digests its record holds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pin {
    pub path: PathBuf,
    pub sha256: String,
    /// The chunked SHA-256 of a binary, in its tagged text form; None for other files.
    pub chunked_sha256: Option<String>,
}

/// The tag of the chunked SHA-256 the records hold, which names its chunk size; fang-hash defines it.
pub const CHUNKED_TAG: &str = fang_hash::CHUNKED_TAG;

/// Whether `text` is a chunked SHA-256 in the tagged form this launcher verifies.
pub fn is_chunked(text: &str) -> bool {
    fang_hash::parse_chunked(text).is_some()
}

fn record_of(value: Option<&Value>) -> Option<Record> {
    let Some(Value::Object(object)) = value else {
        return None;
    };
    let size = if object.contains_key("chunked_sha256") {
        3
    } else {
        2
    };
    match (object.get("path"), object.get("sha256")) {
        (Some(Value::String(path)), Some(Value::String(sha256))) if object.len() == size => {
            Some(Record {
                path: PathBuf::from(path),
                sha256: sha256.clone(),
            })
        }
        _ => None,
    }
}

fn chunked_of(value: Option<&Value>) -> Option<String> {
    match value {
        Some(Value::Object(object)) => text(object.get("chunked_sha256")).map(str::to_string),
        _ => None,
    }
}

/// A well-formed record: a binary's carries both digests, any other file's only the plain one.
fn is_record(value: Option<&Value>, binary: bool) -> bool {
    let plain = record_of(value).is_some_and(|record| {
        record.sha256.len() == 64 && fang_hash::parse_hex32(&record.sha256).is_some()
    });
    plain
        && match chunked_of(value) {
            Some(chunked) => binary && is_chunked(&chunked),
            None => !binary,
        }
}

fn keys(object: &Object) -> Vec<&str> {
    let mut names: Vec<&str> = object.iter().map(|(key, _)| key).collect();
    names.sort_unstable();
    names
}

fn integer(value: Option<&Value>) -> Option<u64> {
    match value {
        Some(Value::Number(Number::Integer(integer))) => integer.as_u64(),
        _ => None,
    }
}

fn text(value: Option<&Value>) -> Option<&str> {
    match value {
        Some(Value::String(text)) => Some(text.as_str()),
        _ => None,
    }
}

/// The `per_run_verification` value every capability carries.
pub fn per_run_value() -> Value {
    let mut object = Object::new();
    for (key, text) in PER_RUN {
        object.set(key, Value::String(text.to_string()));
    }
    Value::Object(object)
}

/// Schema and structure only; no file is read.
pub fn check_fields(object: &Object) -> Result<(), String> {
    let mut required = REQUIRED.to_vec();
    if let Some(preparation) = object.get("engine_preparation") {
        if preparation.as_str() != Some("named") {
            return Err("Unexpected engine preparation contract".to_string());
        }
        required.push("engine_preparation");
    }
    required.sort_unstable();
    if keys(object) != required {
        return Err("Unexpected version-8 capability fields".to_string());
    }
    if text(object.get("schema")) != Some(SCHEMA)
        || text(object.get("language")) != Some(LANGUAGE)
        || integer(object.get("certificate_version")) != Some(8)
        || integer(object.get("max_input_bytes")) != Some(MAX_BYTES)
        || integer(object.get("max_certificate_bytes")) != Some(MAX_CERTIFICATE_BYTES)
        || object.get("per_run_verification") != Some(&per_run_value())
        || text(object.get("default_check")) != Some(DEFAULT_CHECK)
    {
        return Err("Unsupported version-8 capability".to_string());
    }
    for name in ["launcher", "engine", "checker"] {
        if !is_record(object.get(name), true) {
            return Err("Unexpected pinned record fields".to_string());
        }
    }
    match object.get("provenance") {
        Some(Value::Array(items)) if items.iter().all(|item| is_record(Some(item), false)) => {}
        _ => return Err("Unexpected pinned record fields".to_string()),
    }
    let section = |name: &str| -> Result<Option<&Object>, String> {
        match object.get(name) {
            Some(Value::Null) => Ok(None),
            Some(Value::Object(section)) => Ok(Some(section)),
            _ => Err(format!("Unexpected {name} capability fields")),
        }
    };
    let exact = |section: &Object, allowed: &[&[&str]], name: &str| -> Result<(), String> {
        let present = keys(section);
        if !allowed.iter().any(|fields| {
            let mut fields = fields.to_vec();
            fields.sort_unstable();
            fields == present
        }) {
            return Err(format!("Unexpected {name} capability fields"));
        }
        // Every record of a section pins a binary except the configuration files of the kernel and the older
        // profiles.
        let binary = !matches!(name, "cnf" | "ground_fof");
        for (key, value) in section.iter() {
            if key != "output_root" && !is_record(Some(value), binary && key != "installation") {
                return Err("Unexpected pinned record fields".to_string());
            }
        }
        Ok(())
    };
    if let Some(kernel) = section("kernel")? {
        exact(
            kernel,
            &[
                &KERNEL_FIELDS,
                &[
                    "entry",
                    "installation",
                    "output_root",
                    "witness",
                    "producer",
                ],
            ],
            "kernel",
        )?;
        if text(kernel.get("output_root")).is_none() {
            return Err("Unexpected kernel capability fields".to_string());
        }
    }
    if let Some(value) = section("bundle")? {
        exact(value, &[&["producer", "checker"]], "bundle")?;
    }
    if let Some(value) = section("signed")? {
        exact(
            value,
            &[
                &["producer", "checker"],
                &["producer", "checker", "single_producer"],
            ],
            "signed",
        )?;
    }
    if let Some(model) = section("model")? {
        exact(
            model,
            &[
                &["producer", "checker"],
                &["producer", "checker", "exporter"],
            ],
            "model",
        )?;
    }
    if let Some(tstp) = section("tstp")? {
        // The single-file exporter, and any of the others.
        let optional = [
            "bundle_exporter",
            "goal_exporter",
            "inputs_exporter",
            "cited_exporter",
        ];
        let present = keys(tstp);
        if !present.contains(&"exporter")
            || present
                .iter()
                .any(|key| *key != "exporter" && !optional.contains(key))
        {
            return Err("Unexpected tstp capability fields".to_string());
        }
        exact(tstp, &[&present], "tstp")?;
    }
    if let Some(cnf) = section("cnf")? {
        exact(cnf, &[&["installation"]], "cnf")?;
    }
    if let Some(ground_fof) = section("ground_fof")? {
        exact(ground_fof, &[&["capability"]], "ground_fof")?;
    }
    Ok(())
}

/// The running launcher must be the pinned one. The executable's path comes from the /proc/self/exe link;
/// the file it names is hashed without following further links and compared with the pin.
pub fn check_launcher(capability: &Capability) -> Result<(), String> {
    let pinned = capability.launcher();
    let running =
        std::env::current_exe().map_err(|_| "Cannot locate the running launcher".to_string())?;
    let mut check = || Ok::<(), ()>(());
    match fang_hash::hash_file(&running, fang_hash::DEFAULT_FILE_LIMIT, &mut check) {
        Ok((digest, _)) if digest == pinned.sha256 => Ok(()),
        _ => Err("The running launcher differs from the installation".to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn per_run_keys_are_sorted_and_complete() {
        let names: Vec<&str> = PER_RUN.iter().map(|(key, _)| *key).collect();
        assert_eq!(
            names,
            [
                "after_execution",
                "before_execution",
                "full",
                "not_per_run",
                "why"
            ]
        );
        assert!(
            PER_RUN
                .iter()
                .all(|(_, text)| !text.contains("  ") && text.is_ascii())
        );
    }

    #[test]
    fn binaries_carry_both_digests_and_other_files_one() {
        let plain = "ab".repeat(32);
        let chunked = format!("{CHUNKED_TAG}{}", "cd".repeat(32));
        let mut binary = Object::new();
        binary.set("path", "/bin/x");
        binary.set("sha256", plain.as_str());
        let file = Value::Object(binary.clone());
        binary.set("chunked_sha256", chunked.as_str());
        let pinned = Value::Object(binary.clone());
        assert!(is_record(Some(&pinned), true));
        assert!(!is_record(Some(&pinned), false));
        assert!(is_record(Some(&file), false));
        assert!(!is_record(Some(&file), true));
        for tag in ["csha256-1m:", "csha256-4m:", "csha256-8m:"] {
            binary.set("chunked_sha256", format!("{tag}{}", "cd".repeat(32)));
            assert_eq!(
                is_record(Some(&Value::Object(binary.clone())), true),
                tag == CHUNKED_TAG
            );
        }
        binary.set("chunked_sha256", plain.as_str());
        assert!(!is_record(Some(&Value::Object(binary)), true));
        assert!(is_chunked(&chunked) && !is_chunked(&plain));
    }

    #[test]
    fn required_fields_are_unique() {
        let mut fields = REQUIRED.to_vec();
        fields.sort_unstable();
        fields.dedup();
        assert_eq!(fields.len(), REQUIRED.len());
    }
}
