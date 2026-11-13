// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Signed path: inputs with any role other than axiom, over plain files or include bundles.
//!
//! The checker and the producer both take the bundle as ROOT PATH FILE triples, so the launcher finds the
//! include closure itself, in the order the bundle checker requires: depth-first first reach from the top-level
//! file, each include path resolved next to the including file within its root, then under the TPTP root. The
//! search for files and the routing test are untrusted: a wrong file list is rejected by the checker, and every
//! path is sound for the inputs it accepts.
//!
//! Status rules: docs/DESIGN.md, section "Status rules for conjectures". The checker's own `--goals` listing
//! decides; see `final_status`.

use std::collections::{HashMap, HashSet};
use std::os::unix::fs::FileTypeExt;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use fang_supervisor::Fault;

use super::protocol::{self, ContractError, HEADER};
use crate::pattern::{Pattern, group};

pub const FILE_BYTES: u64 = 1 << 20;
pub const TOTAL_BYTES: u64 = 4 << 20;
pub const INPUTS: &[u8] =
    b"accepted-inputs-unsatisfiable (native checker; compiler/runtime trusted)\n";
pub const CANDIDATE: &[u8] = b"candidate-certificate: unchecked signed bundle task\n";
pub const SINGLE_CANDIDATE: &[u8] = b"candidate-certificate: unchecked signed task\n";

/// The producer contract selected by the installed route. Only the checker decides acceptance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Producer {
    LegacyBundle,
    NamedSingle,
    CitedBundle,
}

/// Check the canonical premise-line envelope; the checker validates its citations and proof.
fn cited_header(bytes: &[u8]) -> bool {
    let Some(newline) = bytes.iter().position(|&byte| byte == b'\n') else {
        return false;
    };
    let Some(mut rest) = bytes[..newline].strip_prefix(b"(premises") else {
        return false;
    };
    while rest.starts_with(b" (item ") {
        rest = &rest[7..];
        for separator in [b' ', b')'] {
            let digits = rest.iter().take_while(|byte| byte.is_ascii_digit()).count();
            if digits == 0
                || (digits > 1 && rest[0] == b'0')
                || rest.get(digits) != Some(&separator)
            {
                return false;
            }
            rest = &rest[digits + 1..];
        }
    }
    rest == b")" && bytes[newline + 1..].starts_with(HEADER)
}
pub const NOT_INSTALLED: &str = "Inputs with roles other than axiom need the signed bundle checker, which is not \
                                 installed here. No other path was tried.";
pub const TSTP_UNAVAILABLE: &str = "TSTP output is not yet available for inputs with conjectures or other non-axiom \
                                    roles; rerun with --output status. No fallback was performed.";

struct Compiled {
    listing: Pattern,
    listed: Pattern,
    goal: Pattern,
    lines: Pattern,
    resource: Pattern,
    unsupported: Pattern,
    invalid: Pattern,
    unknown: Pattern,
    error_line: Pattern,
    limit_kind: Pattern,
}

fn compiled() -> &'static Compiled {
    static COMPILED: OnceLock<Compiled> = OnceLock::new();
    COMPILED.get_or_init(|| Compiled {
        listing: Pattern::of(r"goals ([0-9]+)\n((?:goal [0-9]+ item [0-9]+ [0-9]+\n)*)"),
        listed: Pattern::of(r"goal ([0-9]+) item ([0-9]+) ([0-9]+)\n"),
        goal: Pattern::of(
            r"accepted-goal ([0-9]+) item ([0-9]+) ([0-9]+) \(native checker; compiler/runtime trusted\)\n",
        ),
        lines: Pattern::of(r"[ -~]+\n(?:  [ -~]+\n)*"),
        // Python's re.match: anchored at the start, any tail.
        resource: Pattern::of(concat!(
            r"(resource\.|replay\.(reservation|conversion)\.(predicate-limit|symbol-width|literal-limit)\n",
            r"|(certificate|replay\.[a-z-]+): resource-exhaustion)(?:.|\n)*"
        )),
        unsupported: Pattern::of(r"(bundle\.frame|replay\.input)\.unsupported:[0-9]+\n"),
        invalid: Pattern::of(concat!(
            r"(bundle\.frame\.invalid:[0-9]+|bundle\.include\.(missing|cycle)|",
            r"bundle\.selection\.(missing|ambiguous)|replay\.input\.invalid:[0-9]+|",
            r"invalid-utf8\.input|(invalid-nul|unsupported-non-ascii)\.input:[0-9]+)\n"
        )),
        unknown: Pattern::of(r"unknown: processed=[0-9]+ attempted=[0-9]+\n"),
        error_line: Pattern::of(r"error: [a-z-]+ [ -~]*\n"),
        // The encoding and conversion limits, as the single-file contract reports them after `adapter: `.
        limit_kind: Pattern::of(r"(?:.)*(Encoding|Conversion)\((PredicateLimit|SymbolId|LiteralLimit)\)(?:.)*\n"),
    })
}

/// One top-level statement: its keyword and its arguments split at depth one.
#[derive(Clone, Debug)]
pub struct Statement {
    pub keyword: Vec<u8>,
    pub arguments: Vec<Vec<u8>>,
}

impl Statement {
    /// The role of an annotated formula, the second argument without surrounding whitespace.
    pub fn role(&self) -> Option<String> {
        if (self.keyword == b"fof" || self.keyword == b"cnf") && self.arguments.len() >= 2 {
            return Some(String::from_utf8_lossy(self.arguments[1].trim_ascii()).into_owned());
        }
        None
    }

    /// The single-quoted path of an include directive, unescaped.
    pub fn include(&self) -> Option<String> {
        if self.keyword != b"include" {
            return None;
        }
        let text = self.arguments.first()?.trim_ascii();
        if text.len() < 2 || text[0] != b'\'' || text[text.len() - 1] != b'\'' {
            return None;
        }
        let body = &text[1..text.len() - 1];
        let mut value = Vec::new();
        let mut index = 0;
        while index < body.len() {
            if body[index] == b'\\'
                && index + 1 < body.len()
                && (body[index + 1] == b'\\' || body[index + 1] == b'\'')
            {
                value.push(body[index + 1]);
                index += 2;
            } else {
                value.push(body[index]);
                index += 1;
            }
        }
        Some(String::from_utf8_lossy(&value).into_owned())
    }
}

fn skip_layout(data: &[u8], mut index: usize) -> usize {
    while index < data.len() {
        if b" \t\r\n\x0b\x0c".contains(&data[index]) {
            index += 1;
        } else if data[index] == b'%' {
            index = match data[index..].iter().position(|&byte| byte == b'\n') {
                Some(offset) => index + offset + 1,
                None => data.len(),
            };
        } else if data[index..].starts_with(b"/*") {
            index = match data[index + 2..]
                .windows(2)
                .position(|window| window == b"*/")
            {
                Some(offset) => index + 2 + offset + 2,
                None => data.len(),
            };
        } else {
            break;
        }
    }
    index
}

fn quoted(data: &[u8], mut index: usize) -> usize {
    let quote = data[index];
    index += 1;
    while index < data.len() {
        if data[index] == b'\\' {
            index += 2;
        } else if data[index] == quote {
            return index + 1;
        } else {
            index += 1;
        }
    }
    data.len()
}

/// Top-level statements with their arguments split at depth one; stops at the first unreadable byte.
pub fn statements(data: &[u8]) -> Vec<Statement> {
    let mut result = Vec::new();
    let mut index = 0;
    loop {
        index = skip_layout(data, index);
        if index >= data.len() || !data[index].is_ascii_lowercase() {
            return result;
        }
        let start = index;
        index += 1;
        while index < data.len() && (data[index].is_ascii_alphanumeric() || data[index] == b'_') {
            index += 1;
        }
        let keyword = data[start..index].to_vec();
        index = skip_layout(data, index);
        if data.get(index) != Some(&b'(') {
            return result;
        }
        let mut depth = 1;
        index += 1;
        let mut arguments = Vec::new();
        let mut current = Vec::new();
        while index < data.len() && depth > 0 {
            let byte = data[index];
            if byte == b'\'' || byte == b'"' {
                let end = quoted(data, index);
                current.extend_from_slice(&data[index..end.min(data.len())]);
                index = end;
                continue;
            }
            if byte == b'%' || data[index..].starts_with(b"/*") {
                index = skip_layout(data, index);
                current.push(b' ');
                continue;
            }
            if byte == b'(' || byte == b'[' {
                depth += 1;
            } else if byte == b')' || byte == b']' {
                depth -= 1;
                if depth == 0 {
                    arguments.push(std::mem::take(&mut current));
                    index += 1;
                    break;
                }
            } else if byte == b',' && depth == 1 {
                arguments.push(std::mem::take(&mut current));
                index += 1;
                continue;
            }
            current.push(byte);
            index += 1;
        }
        if depth > 0 {
            return result;
        }
        result.push(Statement { keyword, arguments });
        index = skip_layout(data, index);
        if data.get(index) != Some(&b'.') {
            return result;
        }
        index += 1;
    }
}

/// The bundle's include path rules: relative, 1 to 64 components, no `.`, `..`, empty component, backslash,
/// colon or NUL.
pub fn components(path: &str) -> Option<Vec<String>> {
    if path.is_empty()
        || path.chars().count() > 4096
        || path.starts_with('/')
        || path.contains(['\\', ':', '\0'])
    {
        return None;
    }
    let parts: Vec<String> = path.split('/').map(str::to_string).collect();
    if parts.len() > 64
        || parts
            .iter()
            .any(|part| part.is_empty() || part == "." || part == "..")
    {
        return None;
    }
    Some(parts)
}

/// A regular file reached through real directories, or None, as the bundle capture checks it.
fn location(root: Option<&Path>, parts: &[String]) -> Option<PathBuf> {
    let mut path = root?.to_path_buf();
    for (position, part) in parts.iter().enumerate() {
        path.push(part);
        let info = std::fs::symlink_metadata(&path).ok()?;
        let kind = info.file_type();
        if kind.is_symlink() {
            return None;
        }
        let last = position + 1 == parts.len();
        if (!last && !kind.is_dir()) || (last && !kind.is_file()) || kind.is_fifo() {
            return None;
        }
    }
    Some(path)
}

/// One file of a bundle: its root (`base` or `tptp`), its path in that root, where it was read (None for the
/// top-level input) and its bytes.
#[derive(Clone, Debug)]
pub struct BundleFile {
    pub root: String,
    pub path: String,
    pub location: Option<PathBuf>,
    pub data: Vec<u8>,
}

/// Bundle files in first-reach order; stops early on a problem the checker reports. `read` reads one located
/// file and may refuse it (for example past the bundle's total byte limit).
pub fn discover(
    top_name: &str,
    top_bytes: Vec<u8>,
    base_directory: &Path,
    tptp_root: Option<&Path>,
    read: &mut dyn FnMut(&Path) -> Result<Vec<u8>, Fault>,
) -> Result<Vec<BundleFile>, Fault> {
    /// Root, path components, where it was read, bytes.
    type Found = (String, Vec<String>, Option<PathBuf>, Vec<u8>);
    struct Search<'a> {
        files: Vec<Found>,
        index: HashMap<(String, Vec<String>), usize>,
        finished: HashSet<usize>,
        base: &'a Path,
        tptp: Option<&'a Path>,
    }
    fn visit(
        search: &mut Search,
        position: usize,
        stack: &[usize],
        read: &mut dyn FnMut(&Path) -> Result<Vec<u8>, Fault>,
    ) -> Result<bool, Fault> {
        let statements = statements(&search.files[position].3);
        for statement in statements {
            if statement.keyword != b"include" {
                continue;
            }
            let Some(parts) = statement.include().and_then(|path| components(&path)) else {
                return Ok(false);
            };
            let (root, key) = (
                search.files[position].0.clone(),
                search.files[position].1.clone(),
            );
            let mut sibling: Vec<String> = key[..key.len() - 1].to_vec();
            sibling.extend(parts.iter().cloned());
            let mut child = None;
            for candidate in [(root, sibling), ("tptp".to_string(), parts.clone())] {
                if let Some(&found) = search.index.get(&candidate) {
                    child = Some(found);
                    break;
                }
                let directory = if candidate.0 == "base" {
                    Some(search.base)
                } else {
                    search.tptp
                };
                if let Some(found) = location(directory, &candidate.1) {
                    let data = read(&found)?;
                    let next = search.files.len();
                    search.index.insert(candidate.clone(), next);
                    search
                        .files
                        .push((candidate.0, candidate.1, Some(found), data));
                    child = Some(next);
                    break;
                }
            }
            let Some(child) = child else { return Ok(false) };
            if stack.contains(&child) {
                return Ok(false);
            }
            if !search.finished.contains(&child) {
                let mut deeper = stack.to_vec();
                deeper.push(child);
                if !visit(search, child, &deeper, read)? {
                    return Ok(false);
                }
            }
        }
        search.finished.insert(position);
        Ok(true)
    }
    let top = vec![top_name.to_string()];
    let mut search = Search {
        files: vec![("base".to_string(), top.clone(), None, top_bytes)],
        index: HashMap::from([(("base".to_string(), top), 0)]),
        finished: HashSet::new(),
        base: base_directory,
        tptp: tptp_root,
    };
    visit(&mut search, 0, &[0], read)?;
    Ok(search
        .files
        .into_iter()
        .map(|(root, key, location, data)| BundleFile {
            root,
            path: key.join("/"),
            location,
            data,
        })
        .collect())
}

/// The roles of every annotated formula of the files, in order.
pub fn roles(files: &[BundleFile]) -> Vec<String> {
    files
        .iter()
        .flat_map(|file| statements(&file.data))
        .filter_map(|statement| statement.role())
        .collect()
}

/// `signed` for any role other than axiom; `bundle` for axiom-only inputs with includes or objects; else
/// `single`.
pub fn route(files: &[BundleFile], plain_bundle: bool) -> &'static str {
    if roles(files).iter().any(|role| role != "axiom") {
        "signed"
    } else if files.len() > 1 || plain_bundle {
        "bundle"
    } else {
        "single"
    }
}

/// A listed conjecture: its file index and statement index.
pub type Item = (u64, u64);

/// The checker's listing: the selected conjectures, or the status its rejection gives.
pub enum Listing {
    Listed(Vec<Item>),
    Rejected(String),
}

fn number(bytes: &[u8]) -> Option<u64> {
    std::str::from_utf8(bytes).ok()?.parse().ok()
}

/// The checker's own selected-conjecture listing, or the status its rejection gives.
pub fn listing(
    record: &fang_json::Object,
    stdout: &[u8],
    stderr: &[u8],
) -> Result<Listing, ContractError> {
    let code = protocol::normal(record)?;
    let patterns = compiled();
    if code == 0 && stderr.is_empty() {
        if let Some(captures) = patterns.listing.fullmatch(stdout) {
            let count = group(stdout, &captures, 1).and_then(number);
            let body = group(stdout, &captures, 2).unwrap_or_default();
            let mut items = Vec::new();
            for line in body.split_inclusive(|&byte| byte == b'\n') {
                if let Some(row) = patterns.listed.fullmatch(line) {
                    let values: Vec<Option<u64>> = (1..=3)
                        .map(|index| group(line, &row, index).and_then(number))
                        .collect();
                    if let [Some(index), Some(file), Some(statement)] = values[..] {
                        items.push((index, file, statement));
                    }
                }
            }
            let ordered = items
                .iter()
                .enumerate()
                .all(|(position, item)| item.0 == position as u64);
            if count == Some(items.len() as u64) && ordered {
                return Ok(Listing::Listed(
                    items
                        .into_iter()
                        .map(|(_, file, statement)| (file, statement))
                        .collect(),
                ));
            }
        }
        return Err(ContractError(
            "Malformed signed checker goal listing".to_string(),
        ));
    }
    Ok(Listing::Rejected(rejection(code, stdout, stderr, true)?))
}

/// The status of a checker rejection. Only input reading can give an input status; a task rejection is an
/// error.
pub fn rejection(
    code: i64,
    stdout: &[u8],
    stderr: &[u8],
    reading: bool,
) -> Result<String, ContractError> {
    let patterns = compiled();
    if !stdout.is_empty() || !patterns.lines.is_full(stderr) {
        return Err(ContractError(
            "Malformed signed checker rejection".to_string(),
        ));
    }
    if code == 4 && patterns.resource.is_full(stderr) {
        return Ok("ResourceOut".to_string());
    }
    if reading && code == 2 {
        if patterns.unsupported.is_full(stderr) || stderr == b"bundle.mixed-goal-modes\n" {
            return Ok("Inappropriate".to_string());
        }
        if patterns.invalid.is_full(stderr) {
            return Ok("InputError".to_string());
        }
    }
    if [1, 2, 3, 5, 6, 74].contains(&code) {
        return Ok("Error".to_string());
    }
    Err(ContractError(
        "Unrecognized signed checker contract".to_string(),
    ))
}

/// What one checker run on a task gives.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Checked {
    /// An accepted goal and the item it printed.
    Goal(Item),
    /// The accepted inputs task.
    Inputs,
    /// A rejection, with the status it gives.
    Rejected(String),
}

/// The checker's acceptance of a task (`None` for the inputs task), or `None` for a rejection the caller
/// classifies with `rejection`.
pub fn accepted(
    record: &fang_json::Object,
    stdout: &[u8],
    stderr: &[u8],
    task: Option<u64>,
) -> Result<Option<Checked>, ContractError> {
    let code = protocol::normal(record)?;
    if code == 0 && stderr.is_empty() {
        if task.is_none() && stdout == INPUTS {
            return Ok(Some(Checked::Inputs));
        }
        if let (Some(task), Some(captures)) = (task, compiled().goal.fullmatch(stdout)) {
            let values: Vec<Option<u64>> = (1..=3)
                .map(|index| group(stdout, &captures, index).and_then(number))
                .collect();
            if let [Some(index), Some(file), Some(statement)] = values[..]
                && index == task
            {
                return Ok(Some(Checked::Goal((file, statement))));
            }
        }
        return Err(ContractError(
            "Malformed signed checker acceptance".to_string(),
        ));
    }
    Ok(None)
}

/// The producer's outcome for one task: candidate, GaveUp, ResourceOut, Inappropriate or Error; never a
/// result. The encoding and conversion limits (PredicateLimit, SymbolId, LiteralLimit) are resource bounds, as
/// on the single-file path.
pub fn producer_outcome(
    record: &fang_json::Object,
    stdout: &[u8],
    stderr: &[u8],
) -> Result<&'static str, ContractError> {
    producer_outcome_for(record, stdout, stderr, Producer::LegacyBundle)
}

pub fn producer_outcome_for(
    record: &fang_json::Object,
    stdout: &[u8],
    stderr: &[u8],
    producer: Producer,
) -> Result<&'static str, ContractError> {
    let code = protocol::normal(record)?;
    let patterns = compiled();
    let (header, notice) = match producer {
        Producer::LegacyBundle => (stdout.starts_with(HEADER), CANDIDATE),
        Producer::NamedSingle => (stdout.starts_with(HEADER), SINGLE_CANDIDATE),
        Producer::CitedBundle => (cited_header(stdout), CANDIDATE),
    };
    if code == 0 && header && stderr == notice {
        return Ok("candidate");
    }
    if !stdout.is_empty() {
        return Err(ContractError(
            "Noncandidate signed producer emitted certificate bytes".to_string(),
        ));
    }
    if code == 2 && patterns.unknown.is_full(stderr) {
        return Ok("GaveUp");
    }
    if code == 1 && patterns.error_line.is_full(stderr) {
        let kind = stderr
            .split(|&byte| byte == b' ')
            .nth(1)
            .unwrap_or_default();
        if kind == b"modes" {
            // Mixed goal modes are unsupported (status rules above); the checker's listing refuses them first.
            return Ok("Inappropriate");
        }
        let contains = |needle: &[u8]| stderr.windows(needle.len()).any(|window| window == needle);
        if kind == b"resource"
            || kind == b"width"
            || contains(b"Resource(")
            || contains(b"ResourceLimit")
            || patterns.limit_kind.is_full(stderr)
        {
            return Ok("ResourceOut");
        }
        return Ok("Error");
    }
    Err(ContractError(
        "Unrecognized signed producer contract".to_string(),
    ))
}

/// docs/DESIGN.md, "Status rules for conjectures": Theorem only if the checker listed at least one selected
/// conjecture and every listed index was accepted printing its listed item; Unsatisfiable only if it listed
/// none and the inputs task was accepted. `outcomes` holds, per task in order, the acceptance or the first
/// non-accepting status, and stops at that status. A partial set of accepted goals is never reported.
pub fn final_status(listed: &[Item], outcomes: &[Checked]) -> String {
    if let Some(Checked::Rejected(status)) = outcomes.last() {
        return status.clone();
    }
    if !listed.is_empty() {
        let all = outcomes.len() == listed.len()
            && outcomes
                .iter()
                .zip(listed)
                .all(|(outcome, item)| *outcome == Checked::Goal(*item));
        return if all {
            protocol::task_status(listed.len(), outcomes.len())
        } else {
            "Error"
        }
        .to_string();
    }
    if outcomes == [Checked::Inputs] {
        return protocol::task_status(0, 1).to_string();
    }
    "Error".to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use fang_json::{Object, Value};

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
    fn statements_and_roles() {
        let data = b"% c\nfof(a, axiom, p). /* x */ cnf(b,negated_conjecture,(~p)). include('A\\'x.ax',[a]).";
        let found = statements(data);
        assert_eq!(found.len(), 3);
        assert_eq!(found[0].role().as_deref(), Some("axiom"));
        assert_eq!(found[1].role().as_deref(), Some("negated_conjecture"));
        assert_eq!(found[2].include().as_deref(), Some("A'x.ax"));
        assert_eq!(
            components("a/b.ax"),
            Some(vec!["a".to_string(), "b.ax".to_string()])
        );
        assert_eq!(components("../x"), None);
        assert_eq!(components("/abs"), None);
    }

    #[test]
    fn producer_contracts() {
        let candidate = [HEADER, b"  (final 0)\n)\n"].concat();
        assert_eq!(
            producer_outcome(&exited(0), &candidate, CANDIDATE).unwrap(),
            "candidate"
        );
        assert_eq!(
            producer_outcome(&exited(2), b"", b"unknown: processed=3 attempted=4\n").unwrap(),
            "GaveUp"
        );
        assert_eq!(
            producer_outcome(
                &exited(1),
                b"",
                b"error: internal Search(Search(Resource(\"time limit\")))\n"
            )
            .unwrap(),
            "ResourceOut"
        );
        // The tptp1000 differential's SWV421-1.460: an encoding limit is a resource bound, not an Error.
        assert_eq!(
            producer_outcome(
                &exited(1),
                b"",
                b"error: reservation Signed(Encoding(LiteralLimit))\n"
            )
            .unwrap(),
            "ResourceOut"
        );
        assert_eq!(
            producer_outcome(
                &exited(1),
                b"",
                b"error: conversion Signed(Conversion(PredicateLimit))\n"
            )
            .unwrap(),
            "ResourceOut"
        );
        assert_eq!(
            producer_outcome(&exited(1), b"", b"error: modes mixed goal modes\n").unwrap(),
            "Inappropriate"
        );
        assert_eq!(
            producer_outcome(&exited(1), b"", b"error: invalid bad thing\n").unwrap(),
            "Error"
        );
        assert!(producer_outcome(&exited(5), b"", b"panic\n").is_err());
    }

    #[test]
    fn named_and_cited_producer_envelopes_are_route_specific() {
        let proof = [HEADER, b"  (final 0)\n)\n"].concat();
        assert_eq!(
            producer_outcome_for(&exited(0), &proof, SINGLE_CANDIDATE, Producer::NamedSingle)
                .unwrap(),
            "candidate"
        );
        assert!(
            producer_outcome_for(&exited(0), &proof, CANDIDATE, Producer::NamedSingle).is_err()
        );
        for line in [
            b"(premises)\n".as_slice(),
            b"(premises (item 0 12) (item 1 7))\n",
        ] {
            let cited = [line, &proof].concat();
            assert_eq!(
                producer_outcome_for(&exited(0), &cited, CANDIDATE, Producer::CitedBundle).unwrap(),
                "candidate"
            );
            assert!(
                producer_outcome_for(&exited(0), &cited, SINGLE_CANDIDATE, Producer::NamedSingle)
                    .is_err()
            );
            assert!(producer_outcome(&exited(0), &cited, CANDIDATE).is_err());
        }
        for line in [
            b"(premises (item 0))\n".as_slice(),
            b"(premises (item 00 1))\n",
            b"(premises (item -1 0))\n",
            b"(premises) trailing\n",
            b"(premises)\r\n",
            b"(premises)\n(premises)\n",
        ] {
            assert!(
                producer_outcome_for(
                    &exited(0),
                    &[line, &proof].concat(),
                    CANDIDATE,
                    Producer::CitedBundle
                )
                .is_err()
            );
        }
        assert!(
            producer_outcome_for(&exited(0), &proof, CANDIDATE, Producer::CitedBundle).is_err()
        );
    }

    #[test]
    fn checker_contracts() {
        let listed = listing(
            &exited(0),
            b"goals 2\ngoal 0 item 0 1\ngoal 1 item 1 0\n",
            b"",
        )
        .unwrap();
        assert!(matches!(listed, Listing::Listed(items) if items == vec![(0, 1), (1, 0)]));
        assert!(listing(&exited(0), b"goals 2\ngoal 0 item 0 1\n", b"").is_err());
        assert!(
            matches!(listing(&exited(2), b"", b"bundle.frame.unsupported:12\n").unwrap(),
                         Listing::Rejected(status) if status == "Inappropriate")
        );
        assert!(
            matches!(listing(&exited(2), b"", b"bundle.selection.missing\n").unwrap(),
                         Listing::Rejected(status) if status == "InputError")
        );
        assert_eq!(
            rejection(4, b"", b"resource.bytes.certificate\n", false).unwrap(),
            "ResourceOut"
        );
        assert_eq!(
            rejection(1, b"", b"logical-rejection: x\n", false).unwrap(),
            "Error"
        );
        let goal = b"accepted-goal 1 item 1 0 (native checker; compiler/runtime trusted)\n";
        assert_eq!(
            accepted(&exited(0), goal, b"", Some(1)).unwrap(),
            Some(Checked::Goal((1, 0)))
        );
        assert!(accepted(&exited(0), goal, b"", Some(0)).is_err());
        assert_eq!(
            accepted(&exited(0), INPUTS, b"", None).unwrap(),
            Some(Checked::Inputs)
        );
        assert_eq!(accepted(&exited(1), b"", b"x\n", None).unwrap(), None);
    }

    #[test]
    fn final_status_rules() {
        let listed = [(0, 1), (1, 0)];
        assert_eq!(
            final_status(&listed, &[Checked::Goal((0, 1)), Checked::Goal((1, 0))]),
            "Theorem"
        );
        assert_eq!(final_status(&listed, &[Checked::Goal((0, 1))]), "Error");
        assert_eq!(
            final_status(
                &listed,
                &[Checked::Goal((0, 1)), Checked::Rejected("GaveUp".into())]
            ),
            "GaveUp"
        );
        assert_eq!(
            final_status(&listed, &[Checked::Goal((7, 1)), Checked::Goal((1, 0))]),
            "Error"
        );
        assert_eq!(final_status(&[], &[Checked::Inputs]), "Unsatisfiable");
        assert_eq!(final_status(&[], &[]), "Error");
    }
}
