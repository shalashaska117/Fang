// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Author-only policy capture for the version-8 entry, revision 8: the port of
//! provision-policy.py. Without an entry review the policy makes every run ReviewPending.
//!
//! The policy pins every repository source the three binaries are built from (each listed
//! crate's Cargo.toml and src/ tree, the lockfile and the toolchain file) and carries the reviews
//! as pin data, so an installation reads no receipt. The installer refuses a snapshot whose
//! sources differ from these pins. The endpoint review of the version-8 gate is recorded by its
//! hash and bindings. The Lean release is pinned by the hashes of its lean and lake binaries and
//! by the tree summary of its lib/ directory. With --entry-review, the entry review receipt is
//! read here, once: it must have passed and name the policy without the review slot, and its
//! hash, status and named policy become the policy's entry_review. Machine-specific values are
//! not in the policy; the installer writes them to installation.json.

use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};

use fang_json::{Object, ParseLimits, Value};

use crate::install::{POLICY, POLICY_SCHEMA};
use crate::util::{file_sha256, manifest_bytes};

const GATE_PIN: &str = "e8dbfe675733e2b708870349e4eed81d2ef5dea2f02f3c97b2a3a2214d75a5ea";
const LINK_PIN: &str = "c0f18bbe3457610f7972c49cd2b6ede5270727fa844c3d2b174bd748b94dac0c";
const REVIEW_SHA256: &str = "9454d117e63f255ad0ce3a461f3aa920c23e30cf185b0fd2dbb664540f2db438";
const REVIEW_PROVENANCE: &str =
    "evidence/verification/tptp-expanded-certificate-independent-review-v2-20261024/manifest.json";
const LEAN_RELEASE: &str = "v4.35.0";
const LEAN_SHA256: &str = "bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38";
const LAKE_SHA256: &str = "8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1";
const LIB_TREE_SHA256: &str = "0cf201fdce9c10d409d4e96e702b581d79248931f2318730d746a313822a08d1";

/// The crates compiled into the binaries, as repository directories.
pub const CRATES: [&str; 6] = [
    "crates/v8-kernel",
    "crates/fang-json",
    "crates/fang-hash",
    "crates/fang-supervisor",
    "crates/fang-axiom-audit",
    "crates/fang-kernel-workspace",
];
/// Repository files the build reads besides the crates.
pub const FILES: [&str; 3] = ["Cargo.toml", "Cargo.lock", "rust-toolchain.toml"];

type Fallible<T> = Result<T, String>;

fn walk(base: &Path, directory: &Path, found: &mut Vec<String>) -> Fallible<()> {
    let entries =
        fs::read_dir(directory).map_err(|error| format!("{}: {error}", directory.display()))?;
    for entry in entries {
        let entry = entry.map_err(|error| error.to_string())?;
        let path = entry.path();
        let kind = entry.file_type().map_err(|error| error.to_string())?;
        if kind.is_symlink() {
            return Err(format!(
                "Symbolic link among pinned sources: {}",
                path.display()
            ));
        }
        if kind.is_dir() {
            walk(base, &path, found)?;
        } else if kind.is_file() {
            let relative = path.strip_prefix(base).map_err(|error| error.to_string())?;
            found.push(relative.to_string_lossy().into_owned());
        }
    }
    Ok(())
}

/// The pinned repository paths, sorted.
pub fn pinned_paths(repository: &Path) -> Fallible<Vec<String>> {
    let mut paths: Vec<String> = FILES.iter().map(|path| (*path).to_owned()).collect();
    for directory in CRATES {
        paths.push(format!("{directory}/Cargo.toml"));
        walk(
            repository,
            &repository.join(directory).join("src"),
            &mut paths,
        )?;
    }
    paths.sort();
    paths.dedup();
    Ok(paths)
}

fn review() -> Value {
    let mut bindings = Object::new();
    bindings.set("pins.link_v2", LINK_PIN);
    bindings.set("pins.proof", GATE_PIN);
    let mut review = Object::new();
    review.set("sha256", REVIEW_SHA256);
    review.set("bindings", Value::Object(bindings));
    review.set("provenance", REVIEW_PROVENANCE);
    Value::Object(review)
}

/// The policy with an empty review slot.
pub fn unprovisioned(repository: &Path) -> Fallible<Object> {
    let mut files = Object::new();
    for path in pinned_paths(repository)? {
        files.set(path.as_str(), file_sha256(&repository.join(&path))?);
    }
    let mut toolchain = Object::new();
    toolchain.set("release", LEAN_RELEASE);
    toolchain.set("lean_sha256", LEAN_SHA256);
    toolchain.set("lake_sha256", LAKE_SHA256);
    toolchain.set("lib_tree_sha256", LIB_TREE_SHA256);
    let mut provenance = Object::new();
    provenance.set("gate_manifest_sha256", GATE_PIN);
    provenance.set("link_sha256", LINK_PIN);
    provenance.set(
        "note",
        "Receipts named here are provenance; the installation reads none of them.",
    );
    let mut policy = Object::new();
    policy.set("schema", POLICY_SCHEMA);
    policy.set("revision", 8u64);
    policy.set("files", Value::Object(files));
    policy.set("toolchain", Value::Object(toolchain));
    policy.set("batch_sha256", LINK_PIN);
    policy.set("independent_review", review());
    policy.set("entry_review", Value::Null);
    policy.set("provenance", Value::Object(provenance));
    Ok(policy)
}

/// `fang-v8-kernel-provision --repository R [--entry-review PATH --entry-review-sha256 HASH]`.
pub fn main(raw: &[OsString]) -> Fallible<Value> {
    let mut values: Vec<(String, String)> = Vec::new();
    let mut index = 1;
    while index < raw.len() {
        let flag = raw[index].to_string_lossy().into_owned();
        let Some(value) = raw.get(index + 1) else {
            return Err(format!("{flag} needs a value"));
        };
        if !["--repository", "--entry-review", "--entry-review-sha256"].contains(&flag.as_str())
            || values.iter().any(|(existing, _)| *existing == flag)
        {
            return Err(format!("unrecognized arguments: {flag}"));
        }
        values.push((flag, value.to_string_lossy().into_owned()));
        index += 2;
    }
    let get = |name: &str| {
        values
            .iter()
            .find(|(flag, _)| flag == name)
            .map(|(_, value)| value.clone())
    };
    let repository = PathBuf::from(
        get("--repository").ok_or("the following arguments are required: --repository")?,
    );
    let receipt_path = get("--entry-review");
    let receipt_sha256 = get("--entry-review-sha256");
    if receipt_path.is_some() != receipt_sha256.is_some() {
        return Err("Give the review receipt path and its SHA-256 together".to_owned());
    }
    let mut policy = unprovisioned(&repository)?;
    let files = policy
        .get("files")
        .and_then(Value::as_object)
        .map_or(0, Object::len);
    let unprovisioned_sha256 =
        fang_hash::sha256_hex(&manifest_bytes(&Value::Object(policy.clone()))?);
    if let (Some(path), Some(expected)) = (receipt_path, receipt_sha256) {
        let receipt =
            fs::read(repository.join(&path)).map_err(|error| format!("{path}: {error}"))?;
        if fang_hash::sha256_hex(&receipt) != expected {
            return Err("Entry review receipt differs from the given SHA-256".to_owned());
        }
        let reviewed = fang_json::parse(
            &receipt,
            &ParseLimits {
                max_bytes: 256 << 20,
                max_depth: 256,
            },
        )
        .map_err(|error| error.python_message(&receipt))?;
        if reviewed.get("status").and_then(Value::as_str) != Some("passed") {
            return Err("Entry review did not pass".to_owned());
        }
        let mut own = Object::new();
        own.set("policy.json", unprovisioned_sha256.as_str());
        let named = reviewed
            .get("inputs")
            .and_then(|inputs| inputs.get("entry_sources_sha256"));
        if named != Some(&Value::Object(own.clone())) {
            return Err("Entry review does not name this policy".to_owned());
        }
        let mut entry_review = Object::new();
        entry_review.set("sha256", expected.as_str());
        entry_review.set("status", "passed");
        entry_review.set("entry_sources_sha256", Value::Object(own));
        entry_review.set("provenance", path.as_str());
        policy.set("entry_review", Value::Object(entry_review));
    }
    let provisioned = !matches!(policy.get("entry_review"), Some(Value::Null) | None);
    let data = manifest_bytes(&Value::Object(policy))?;
    let target = repository.join(POLICY);
    fs::write(&target, &data).map_err(|error| format!("{}: {error}", target.display()))?;
    let mut summary = Object::new();
    summary.set(
        "status",
        if provisioned {
            "provisioned"
        } else {
            "review-pending"
        },
    );
    summary.set("files", files as u64);
    summary.set("policy_sha256", fang_hash::sha256_hex(&data));
    summary.set("unprovisioned_policy_sha256", unprovisioned_sha256);
    Ok(Value::Object(summary))
}
