// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Bundle path: inputs with include directives, distinct objects or annotations.
//!
//! The bundle producer reads the top-level file and its includes itself (relative to the input file, then the
//! TPTP root) and reports the bundle's files in order. The launcher then reads every listed file once, seals
//! it, hashes it into the run record and passes exactly those bytes to the bundle checker. Only the checker's
//! acceptance gives a result. The routing test is untrusted: both paths are sound for the inputs they accept.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use fang_json::{ParseLimits, Value};

use super::protocol::{self, ContractError, HEADER, RESOURCE, adapter_resources, input_pattern};
use super::signed;
use crate::pattern::{Pattern, group};

pub const ACCEPTED: &[u8] =
    b"accepted-original-bundle-equality (native checker; compiler/runtime trusted)\n";
pub const CANDIDATE: &[u8] = b"candidate-certificate: unchecked bundle input\n";
pub const FILE_BYTES: u64 = 1 << 20;
pub const TOTAL_BYTES: u64 = 4 << 20;
pub const NOT_INSTALLED: &str = "Inputs with include directives, distinct objects or annotations need the bundle \
                                 checker, which is not installed here. No other path was tried.";
pub const TSTP_UNAVAILABLE: &str = "TSTP output for bundles needs the bundle exporter, which is not installed here; \
                                    rerun with --output status. No fallback was performed.";

struct Compiled {
    capture: Pattern,
    input: Pattern,
    adapter: Vec<Pattern>,
    serialization: Pattern,
    unknown: Pattern,
    lines: Pattern,
    resource: Pattern,
}

fn compiled() -> &'static Compiled {
    static COMPILED: OnceLock<Compiled> = OnceLock::new();
    COMPILED.get_or_init(|| Compiled {
        capture: Pattern::of(concat!(
            r"capture: (InvalidInput|Unsupported|ResourceLimit) ([A-Za-z]+) file=(?:None|Some\([0-9]+\)) ",
            r"offset=(?:None|Some\([0-9]+\))\n"
        )),
        input: Pattern::of(&format!(r"adapter: Input\({}\)\n", input_pattern())),
        adapter: adapter_resources().iter().map(|pattern| Pattern::of(&format!(r"adapter: {pattern}\n"))).collect(),
        serialization: Pattern::of(&format!(r"serialization: {RESOURCE}\n")),
        unknown: Pattern::of(r"unknown: processed=[0-9]+ attempted=[0-9]+\n"),
        lines: Pattern::of(r"[ -~]+\n(?:  [ -~]+\n)*"),
        // Python's re.match: anchored at the start, any tail.
        resource: Pattern::of(concat!(
            r"(resource\.|replay\.(reservation|conversion)\.(predicate-limit|symbol-width|literal-limit)\n",
            r"|(certificate|replay\.(transport-input|preprocessing-input)): resource-exhaustion)(?:.|\n)*"
        )),
    })
}

/// Route by features of the input, before anything runs: a double quote or an include directive anywhere,
/// comments included, or a statement with an annotation (more than three arguments), which the single-file
/// decoder does not read and the bundle path does. The test is untrusted: a wrong route only gives the other
/// path's own checked answer or rejection, never a fallback.
pub fn needs_bundle(data: &[u8]) -> bool {
    if data.contains(&b'"') || has_include(data) {
        return true;
    }
    signed::statements(data).iter().any(|statement| {
        (statement.keyword == b"fof" || statement.keyword == b"cnf")
            && statement.arguments.len() > 3
    })
}

/// `(?<![A-Za-z0-9_$])include\s*\(` anywhere in the bytes.
fn has_include(data: &[u8]) -> bool {
    let word = b"include";
    let mut start = 0;
    while let Some(offset) = data[start..]
        .windows(word.len())
        .position(|window| window == word)
    {
        let at = start + offset;
        let before = at.checked_sub(1).map(|index| data[index]);
        let free = before
            .is_none_or(|byte| !(byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'$'));
        let mut after = at + word.len();
        while after < data.len() && b" \t\n\r\x0b\x0c".contains(&data[after]) {
            after += 1;
        }
        if free && data.get(after) == Some(&b'(') {
            return true;
        }
        start = at + 1;
    }
    false
}

/// A bundle path as the producer may report it: relative POSIX components, none empty, `.` or `..`, and no
/// backslash.
pub fn valid_path(text: &str) -> bool {
    !text.is_empty()
        && !text.starts_with('/')
        && !text.contains('\\')
        && text
            .split('/')
            .all(|part| !part.is_empty() && part != "." && part != "..")
}

/// The producer's first stderr line: the bundle's digest, files, declaration count and object count.
#[derive(Clone, Debug)]
pub struct Info {
    pub bundle_sha256: String,
    pub files: Vec<(String, String)>,
    pub declarations: Value,
    pub objects: Value,
}

fn bundle_info(line: &[u8]) -> Result<Info, ContractError> {
    let malformed = || ContractError("Malformed bundle producer file list".to_string());
    let value = fang_json::parse(line, &ParseLimits::default()).map_err(|_| malformed())?;
    let object = value.as_object().ok_or_else(malformed)?;
    let mut keys: Vec<&str> = object.keys().collect();
    keys.sort_unstable();
    if keys != ["bundle_sha256", "declarations", "files", "objects"] {
        return Err(malformed());
    }
    let digest = object
        .get("bundle_sha256")
        .and_then(Value::as_str)
        .unwrap_or_default();
    if digest.len() != 64
        || !digest
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(malformed());
    }
    let items = object
        .get("files")
        .and_then(Value::as_array)
        .ok_or_else(malformed)?;
    let mut files = Vec::new();
    for item in items {
        let pair = item.as_array().ok_or_else(malformed)?;
        let [root, path] = pair.as_slice() else {
            return Err(malformed());
        };
        let (Some(root), Some(path)) = (root.as_str(), path.as_str()) else {
            return Err(malformed());
        };
        if (root != "base" && root != "tptp") || !valid_path(path) {
            return Err(malformed());
        }
        files.push((root.to_string(), path.to_string()));
    }
    let mut unique = files.clone();
    unique.sort();
    unique.dedup();
    if files.is_empty()
        || files[0].0 != "base"
        || files[0].1.contains('/')
        || unique.len() != files.len()
    {
        return Err(malformed());
    }
    Ok(Info {
        bundle_sha256: digest.to_string(),
        files,
        declarations: object.get("declarations").cloned().unwrap_or(Value::Null),
        objects: object.get("objects").cloned().unwrap_or(Value::Null),
    })
}

/// What the bundle producer gives: a candidate with its file list, or a status with its reason.
#[derive(Clone, Debug)]
pub enum Outcome {
    Candidate(Info),
    Status(String, String),
}

fn status_of(kind: &[u8]) -> &'static str {
    match kind {
        b"InvalidInput" => "InputError",
        b"Unsupported" => "Inappropriate",
        _ => "ResourceOut",
    }
}

/// Map the bundle producer's streams; a candidate is never a result.
pub fn producer_outcome(
    record: &fang_json::Object,
    stdout: &[u8],
    stderr: &[u8],
) -> Result<Outcome, ContractError> {
    let code = protocol::normal(record)?;
    let patterns = compiled();
    if code == 0 || code == 2 {
        let (first, rest) = match stderr.iter().position(|&byte| byte == b'\n') {
            Some(at) => (&stderr[..at], &stderr[at + 1..]),
            None => (stderr, &b""[..]),
        };
        let info = bundle_info(first)?;
        if code == 0 && stdout.starts_with(HEADER) && rest == CANDIDATE {
            return Ok(Outcome::Candidate(info));
        }
        if code == 2 && stdout.is_empty() && patterns.unknown.is_full(rest) {
            return Ok(Outcome::Status(
                "GaveUp".to_string(),
                "Search stopped without a certified result".to_string(),
            ));
        }
        return Err(ContractError(
            "Malformed bundle producer outcome".to_string(),
        ));
    }
    if !stdout.is_empty() {
        return Err(ContractError(
            "Noncandidate bundle producer emitted certificate bytes".to_string(),
        ));
    }
    if code == 3 {
        if let Some(captures) = patterns.capture.fullmatch(stderr) {
            let kind = group(stderr, &captures, 1).unwrap_or_default();
            let reason = String::from_utf8_lossy(group(stderr, &captures, 2).unwrap_or_default())
                .into_owned();
            return Ok(Outcome::Status(
                status_of(kind).to_string(),
                format!("Bundle capture: {reason}"),
            ));
        }
        if let Some(captures) = patterns.input.fullmatch(stderr) {
            let kind = group(stderr, &captures, 1).unwrap_or_default();
            let message = group(stderr, &captures, 4).unwrap_or_default();
            let reason = fang_json::parse(message, &ParseLimits::default())
                .ok()
                .and_then(|value| value.as_str().map(str::to_string))
                .ok_or_else(|| ContractError("Malformed bundle producer diagnostic".to_string()))?;
            return Ok(Outcome::Status(status_of(kind).to_string(), reason));
        }
        if patterns
            .adapter
            .iter()
            .any(|pattern| pattern.is_full(stderr))
        {
            return Ok(Outcome::Status(
                "ResourceOut".to_string(),
                "Preprocessing or search reached a structural resource bound".to_string(),
            ));
        }
    }
    if code == 4 && patterns.serialization.is_full(stderr) {
        return Ok(Outcome::Status(
            "ResourceOut".to_string(),
            "Serialization reached a structural resource bound".to_string(),
        ));
    }
    Err(ContractError(
        "Unrecognized or failed bundle producer contract".to_string(),
    ))
}

/// Classify the native bundle checker; only `accepted` can lead to a result.
pub fn checker_outcome(
    record: &fang_json::Object,
    stdout: &[u8],
    stderr: &[u8],
) -> Result<&'static str, ContractError> {
    let code = protocol::normal(record)?;
    let patterns = compiled();
    if code == 0 && stdout == ACCEPTED && stderr.is_empty() {
        return Ok("accepted");
    }
    if !stdout.is_empty() || !patterns.lines.is_full(stderr) {
        return Err(ContractError(
            "Rejected or malformed bundle checker result".to_string(),
        ));
    }
    if code == 4 && patterns.resource.is_full(stderr) {
        return Ok("resource");
    }
    match code {
        1 => Ok("logical-rejection"),
        2 => Ok("input-or-bundle-rejection"),
        3 => Ok("certificate-rejection"),
        5 => Ok("internal-replay-failure"),
        6 => Ok("signature-rejection"),
        74 => Ok("io-failure"),
        _ => Err(ContractError(
            "Unrecognized or failed bundle checker contract".to_string(),
        )),
    }
}

/// The producer's bundle digest over (root, path, bytes) in bundle order.
pub fn digest(files: &[(&str, &str, &[u8])]) -> String {
    let mut data = b"fang-tptp-bundle-v1\0".to_vec();
    data.extend_from_slice(&(files.len() as u64).to_be_bytes());
    for (root, path, content) in files {
        data.push(if *root == "base" { 0 } else { 1 });
        let components: Vec<&str> = path.split('/').collect();
        data.extend_from_slice(&(components.len() as u64).to_be_bytes());
        for component in components {
            data.extend_from_slice(&(component.len() as u64).to_be_bytes());
            data.extend_from_slice(component.as_bytes());
        }
        data.extend_from_slice(&(content.len() as u64).to_be_bytes());
        data.extend_from_slice(content);
    }
    fang_hash::sha256_hex(&data)
}

/// Where each listed file is read from: the input's directory for `base`, the TPTP root for `tptp`.
pub fn locate(
    info: &Info,
    input: &Path,
    tptp_root: Option<&Path>,
) -> Result<Vec<(String, String, PathBuf)>, ContractError> {
    let input = std::path::absolute(input).map_err(|error| ContractError(error.to_string()))?;
    let name = input
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_default();
    if info.files.first() != Some(&("base".to_string(), name)) {
        return Err(ContractError(
            "Bundle producer did not start from the captured input".to_string(),
        ));
    }
    let mut places = Vec::new();
    for (root, path) in &info.files {
        let base = if root == "base" {
            input.parent().map(Path::to_path_buf).unwrap_or_default()
        } else {
            let Some(tptp) = tptp_root else {
                return Err(ContractError(
                    "Bundle needs a TPTP root that was not given".to_string(),
                ));
            };
            std::path::absolute(tptp).map_err(|error| ContractError(error.to_string()))?
        };
        places.push((root.clone(), path.clone(), base.join(path)));
    }
    Ok(places)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fang_json::Object;

    fn exited(code: i64) -> Object {
        let mut record = Object::new();
        record.set("exit_code", Value::from(code));
        record.set(
            "classification",
            Value::from(if code == 0 {
                "completed"
            } else {
                "nonzero-exit"
            }),
        );
        record
    }

    #[test]
    fn routing_test() {
        assert!(needs_bundle(b"fof(a,axiom,p(\"x\"))."));
        assert!(needs_bundle(b"include ('ax.ax')."));
        assert!(!needs_bundle(b"fof(a,axiom,p(x_include(a)))."));
        assert!(needs_bundle(b"fof(a,axiom,p,file('x.p',a))."));
        assert!(!needs_bundle(
            b"fof(a,axiom,![X,Y]:(p(X,Y) | q(f(X,Y)))). cnf(b,axiom,(p(a,b)))."
        ));
    }

    #[test]
    fn producer_contracts() {
        let info = format!(
            r#"{{"bundle_sha256": "{}", "files": [["base", "p.p"], ["base", "ax.ax"]], "declarations": 2, "objects": 1}}"#,
            "0".repeat(64)
        );
        let stderr = [info.as_bytes(), b"\n", CANDIDATE].concat();
        let certificate = [HEADER, b")\n"].concat();
        assert!(matches!(
            producer_outcome(&exited(0), &certificate, &stderr).unwrap(),
            Outcome::Candidate(_)
        ));
        let stderr = [info.as_bytes(), b"\nunknown: processed=1 attempted=2\n"].concat();
        assert!(
            matches!(producer_outcome(&exited(2), b"", &stderr).unwrap(), Outcome::Status(status, _) if status == "GaveUp")
        );
        let missing = b"capture: InvalidInput Missing file=Some(0) offset=Some(8)\n";
        assert!(
            matches!(producer_outcome(&exited(3), b"", missing).unwrap(),
                         Outcome::Status(status, reason) if status == "InputError" && reason == "Bundle capture: Missing")
        );
        let limit = b"capture: ResourceLimit Limit file=Some(0) offset=None\n";
        assert!(
            matches!(producer_outcome(&exited(3), b"", limit).unwrap(), Outcome::Status(status, _) if status == "ResourceOut")
        );
        assert!(
            matches!(producer_outcome(&exited(3), b"", b"adapter: Search(Search(Resource(\"time limit\")))\n").unwrap(),
                         Outcome::Status(status, _) if status == "ResourceOut")
        );
        let bad = format!(
            r#"{{"bundle_sha256": "{}", "files": [["base", "a/p.p"]], "declarations": 2, "objects": 1}}"#,
            "0".repeat(64)
        );
        assert!(
            producer_outcome(
                &exited(2),
                b"",
                format!("{bad}\nunknown: processed=1 attempted=2\n").as_bytes()
            )
            .is_err()
        );
    }

    #[test]
    fn checker_contracts() {
        assert_eq!(
            checker_outcome(&exited(0), ACCEPTED, b"").unwrap(),
            "accepted"
        );
        assert_eq!(
            checker_outcome(&exited(4), b"", b"resource.bytes.input\n").unwrap(),
            "resource"
        );
        assert_eq!(
            checker_outcome(&exited(2), b"", b"bundle.shape\n").unwrap(),
            "input-or-bundle-rejection"
        );
        assert!(checker_outcome(&exited(0), b"accepted\n", b"").is_err());
        assert!(checker_outcome(&exited(64), b"", b"usage\n").is_err());
    }

    #[test]
    fn digest_and_paths() {
        let files: [(&str, &str, &[u8]); 2] =
            [("base", "p.p", b"a"), ("tptp", "Axioms/x.ax", b"bc")];
        // The value Python's bundle.digest gives for the same files.
        assert_eq!(
            digest(&files),
            "7db26c87e760bfe1ae724b8ce39fc8bc1b8ee4308599b6d745c1b2a844a89407"
        );
        assert!(valid_path("Axioms/x.ax"));
        assert!(!valid_path("a//b"));
        assert!(!valid_path("./a"));
        assert!(!valid_path("a\\b"));
    }
}
