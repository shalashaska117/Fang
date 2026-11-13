// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! tools/fang_szs/v8_dependencies.py: the version-8 crates and Lean modules against their
//! source maps, and, with receipts present, the maps against the receipt archives.

mod view;

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::{Path, PathBuf};

use fang_json::{Object, Value};

use crate::error::Error;
use crate::util::{
    self, Check, array, decode, display, entries, get, integer, listed_tree, lstat, object,
    optional, read_bytes, read_decoded, read_json, read_text, regular, sha256_hex, text,
};
pub use view::{Suffix, code_view, code_view_sha256};

pub const RUST_MAP: &str = "tools/v8_szs/rust-sources.json";
pub const LEAN_MAP: &str = "tools/v8_szs/lean-sources.json";
pub const RUST_SCHEMA: &str = "fang-v8-rust-source-map-v1";
pub const LEAN_SCHEMA: &str = "fang-v8-lean-source-map-v1";
pub const GROUND: [&str; 4] = [
    "crates/ground-fof-core",
    "crates/ground-fof-frontend",
    "crates/ground-fof-search",
    "crates/ground-fof-versioned",
];
/// Trees whose crates must not resolve to the root workspace.
pub const OUTSIDE: [&str; 4] = [".local", "evidence", "experiments", "verification"];

fn fail<T>(message: impl Into<String>) -> Result<T, Error> {
    Err(Error::value(message))
}

/// `digest(path, check)`.
pub fn digest(path: &Path, check: Check<'_>) -> Result<String, Error> {
    util::digest(path, check)
}

/// `load_map(root, relative, schema, check)`.
pub fn load_map(
    root: &Path,
    relative: &str,
    schema: &str,
    check: Check<'_>,
) -> Result<Value, Error> {
    let path = root.join(relative);
    regular(&path, check)?;
    let value = read_json(&path)?;
    if optional(&value, "schema").and_then(Value::as_str) != Some(schema) {
        return fail(format!("Unexpected source map schema: {relative}"));
    }
    Ok(value)
}

/// `crate_names(root, check)`: directory names under crates/ of the version-8 workspace.
pub fn crate_names(root: &Path, check: Check<'_>) -> Result<BTreeSet<String>, Error> {
    let map = load_map(root, RUST_MAP, RUST_SCHEMA, check)?;
    Ok(object(get(&map, "crates")?)?
        .keys()
        .map(|name| name.rsplit('/').next().unwrap_or(name).to_owned())
        .collect())
}

fn line_of(entry: &Value) -> Result<usize, Error> {
    Ok(integer(get(entry, "line")?)? as usize)
}

/// `apply_rewrites(original, rewrites, edits, includes)`.
pub fn apply_rewrites(
    original: &[u8],
    rewrites: &[Value],
    edits: &[Value],
    includes: &[Value],
) -> Result<Vec<u8>, Error> {
    let source = decode(original)?;
    let mut lines: Vec<String> = source.split('\n').map(str::to_owned).collect();
    let line = |lines: &Vec<String>, number: usize| -> Result<String, Error> {
        number
            .checked_sub(1)
            .and_then(|index| lines.get(index))
            .cloned()
            .ok_or_else(|| Error::value("list index out of range"))
    };
    for edit in edits {
        let number = line_of(edit)?;
        if line(&lines, number)? != text(get(edit, "from")?)? {
            return fail("Recorded line edit does not match the receipt bytes");
        }
        lines[number - 1] = text(get(edit, "to")?)?.to_owned();
    }
    for (rewrites, macro_name, message) in [
        (
            rewrites,
            "path = \"",
            "Recorded path rewrite does not match the receipt bytes",
        ),
        (
            includes,
            "include_str!(\"",
            "Recorded include rewrite does not match the receipt bytes",
        ),
    ] {
        for rewrite in rewrites {
            let number = line_of(rewrite)?;
            let current = line(&lines, number)?;
            let closing = if macro_name.starts_with("path") {
                "\""
            } else {
                "\")"
            };
            let needle = format!("{macro_name}{}{closing}", text(get(rewrite, "from")?)?);
            if current.matches(&needle).count() != 1 {
                return fail(message);
            }
            let replacement = format!("{macro_name}{}{closing}", text(get(rewrite, "to")?)?);
            lines[number - 1] = current.replace(&needle, &replacement);
        }
    }
    Ok(lines.join("\n").into_bytes())
}

/// `apply_comment_rewrite(original, rewrite, suffix)`: the development check.
pub fn apply_comment_rewrite(
    original: &[u8],
    rewrite: &Value,
    suffix: Suffix,
) -> Result<Vec<u8>, Error> {
    let source = decode(original)?;
    if code_view_sha256(source, suffix)? != text(get(rewrite, "code_view_sha256")?)? {
        return fail("Recorded code view differs from the reviewed bytes");
    }
    let mut lines: Vec<String> = source.split('\n').map(str::to_owned).collect();
    for edit in array(get(rewrite, "edits")?)? {
        let number = line_of(edit)?;
        let to = text(get(edit, "to")?)?;
        if !(1..=lines.len()).contains(&number)
            || to.contains('\n')
            || sha256_hex(lines[number - 1].as_bytes()) != text(get(edit, "from_sha256")?)?
        {
            return fail("Recorded comment edit does not match the reviewed bytes");
        }
        lines[number - 1] = to.to_owned();
    }
    Ok(lines.join("\n").into_bytes())
}

/// `check_comment_rewrite(current, rewrite, suffix)`: the install-time check.
pub fn check_comment_rewrite(current: &[u8], rewrite: &Value, suffix: Suffix) -> Result<(), Error> {
    let source = decode(current)?;
    let (view, spans) = view::view_and_spans(source, suffix)?;
    if sha256_hex(view.as_bytes()) != text(get(rewrite, "code_view_sha256")?)? {
        return fail("Code differs from the reviewed file beyond comment text");
    }
    let edits = array(get(rewrite, "edits")?)?;
    let numbers: Vec<i64> = edits
        .iter()
        .map(|edit| integer(get(edit, "line")?))
        .collect::<Result<_, _>>()?;
    if edits.is_empty() || numbers.iter().collect::<HashSet<_>>().len() != numbers.len() {
        return fail("Comment edits must name distinct lines");
    }
    let lines: Vec<&str> = source.split('\n').collect();
    let mut offsets = vec![0usize];
    for line in &lines {
        offsets.push(offsets.last().copied().unwrap_or(0) + line.chars().count() + 1);
    }
    let starts: Vec<usize> = spans.iter().map(|span| span.0).collect();
    for edit in edits {
        let number = line_of(edit)?;
        let to = text(get(edit, "to")?)?;
        if !(1..=lines.len()).contains(&number)
            || lines[number - 1] != to
            || sha256_hex(to.as_bytes()) == text(get(edit, "from_sha256")?)?
        {
            return fail("Recorded comment edit does not match the file");
        }
        for (offset, character) in (offsets[number - 1]..).zip(to.chars()) {
            // bisect_right(starts, offset) - 1
            let index = starts.partition_point(|start| *start <= offset) as isize - 1;
            if !fang_json_isspace(character) && (index < 0 || offset >= spans[index as usize].1) {
                return fail("Recorded comment edit lies outside comments");
            }
        }
    }
    Ok(())
}

/// Python's `str.isspace` for one character.
fn fang_json_isspace(character: char) -> bool {
    matches!(
        character,
        '\t'..='\r'
            | '\u{1c}'..='\u{20}'
            | '\u{85}'
            | '\u{a0}'
            | '\u{1680}'
            | '\u{2000}'..='\u{200a}'
            | '\u{2028}'
            | '\u{2029}'
            | '\u{202f}'
            | '\u{205f}'
            | '\u{3000}'
    )
}

fn strings(value: &Value) -> Result<Vec<String>, Error> {
    array(value)?
        .iter()
        .map(|item| text(item).map(str::to_owned))
        .collect()
}

/// `check_workspace(root, manifest, source_map, check)`.
pub fn check_workspace(
    root: &Path,
    manifest: &Value,
    source_map: &Value,
    check: Check<'_>,
) -> Result<(), Error> {
    let expected = get(source_map, "workspace")?;
    let members = get(expected, "members")?;
    let exclude = get(expected, "exclude")?;
    let mut table = Object::new();
    table.set("members", members.clone());
    table.set("exclude", exclude.clone());
    if optional(manifest, "workspace") != Some(&Value::Object(table)) {
        return fail("Unreviewed root workspace table");
    }
    let crates = object(get(source_map, "crates")?)?;
    let mut ours: Vec<String> = vec!["crates/fang-predicate-index".to_owned()];
    let mut excluded: Vec<String> = GROUND.iter().map(|name| (*name).to_owned()).collect();
    for (name, entry) in crates.iter() {
        if optional(entry, "workspace").and_then(Value::as_str) == Some("member") {
            ours.push(name.to_owned());
        } else {
            excluded.push(name.to_owned());
        }
    }
    excluded.extend(OUTSIDE.iter().map(|name| (*name).to_owned()));
    let (mut members, mut exclude) = (strings(members)?, strings(exclude)?);
    ours.sort();
    members.sort();
    excluded.sort();
    exclude.sort();
    if ours != members || excluded != exclude {
        return fail("Workspace roles differ from the source map");
    }
    if digest(&root.join("Cargo.lock"), check)? != text(get(expected, "lock_sha256")?)? {
        return fail("Unreviewed workspace lockfile");
    }
    Ok(())
}

/// `Path(name).suffix`: the extension of the last component, with its dot.
fn python_suffix(name: &str) -> String {
    let file = name.rsplit('/').next().unwrap_or(name);
    match file.rfind('.') {
        Some(index) if index > 0 && index + 1 < file.len() => file[index..].to_owned(),
        _ => String::new(),
    }
}

fn suffix_of(path: &Path) -> Option<Suffix> {
    Suffix::of(&display(path))
}

fn check_recorded_comments(path: &Path, entry: &Value, check: Check<'_>) -> Result<(), Error> {
    check()?;
    let Some(suffix) = suffix_of(path) else {
        return Err(Error::Key(python_suffix(&display(path))));
    };
    check_comment_rewrite(&read_bytes(path)?, get(entry, "comment_rewrite")?, suffix)
}

/// `check_rust_include(root, path, rewrite, check)`: a rewritten include must read the recorded lean-v8 file itself.
pub fn check_rust_include(
    root: &Path,
    path: &Path,
    rewrite: &Value,
    check: Check<'_>,
) -> Result<(), Error> {
    check()?;
    let source = read_text(path)?;
    let number = line_of(rewrite)?;
    let line = number
        .checked_sub(1)
        .and_then(|index| source.split('\n').nth(index))
        .ok_or_else(|| Error::value("list index out of range"))?;
    let to = text(get(rewrite, "to")?)?;
    let target_field = text(get(rewrite, "target")?)?;
    let relative = util::relative_posix(path, root);
    let target = util::normpath(&util::join(util::dirname(&relative), to));
    if line.matches(&format!("include_str!(\"{to}\")")).count() != 1
        || target != target_field
        || !target_field.starts_with("lean-v8/")
    {
        return fail(format!(
            "Include does not read its recorded lean-v8 file: {}",
            display(path)
        ));
    }
    regular(&root.join(target_field), check)
}

/// `rust_files(root, check)`: every moved crate file after checking the exact inventory and hashes.
pub fn rust_files(root: &Path, check: Check<'_>) -> Result<Vec<PathBuf>, Error> {
    let source_map = load_map(root, RUST_MAP, RUST_SCHEMA, check)?;
    let crates = object(get(&source_map, "crates")?)?;
    let files = object(get(&source_map, "files")?)?;
    let mut listed: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (name, _) in files.iter() {
        let Some(crate_name) = crates
            .keys()
            .find(|crate_name| name.starts_with(&format!("{crate_name}/")))
        else {
            return fail(format!("Source map file outside its crates: {name}"));
        };
        listed
            .entry(crate_name.to_owned())
            .or_default()
            .insert(name[crate_name.len() + 1..].to_owned());
    }
    let mut result = Vec::new();
    for crate_name in crates.keys() {
        let directory = root.join(crate_name);
        if !lstat(&directory)?.file_type().is_dir() {
            return fail(format!("Missing moved crate: {crate_name}"));
        }
        let expected = listed.get(crate_name).cloned().unwrap_or_default();
        if listed_tree(&directory, check, &["target"])? != expected {
            return fail(format!(
                "Moved crate inventory differs from the source map: {crate_name}"
            ));
        }
        let Some(names) = listed.get(crate_name) else {
            return Err(Error::Key(crate_name.to_owned()));
        };
        for relative in names {
            let path = directory.join(relative);
            let entry = get(&source_map, "files")
                .and_then(|files| get(files, &format!("{crate_name}/{relative}")))?;
            if digest(&path, check)? != text(get(entry, "sha256")?)? {
                return fail(format!(
                    "Moved file differs from its receipt: {crate_name}/{relative}"
                ));
            }
            if optional(entry, "comment_rewrite").is_some() {
                check_recorded_comments(&path, entry, check)?;
            }
            for rewrite in optional(entry, "include_rewrites")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
            {
                check_rust_include(root, &path, rewrite, check)?;
            }
            result.push(path);
        }
    }
    for (name, entry) in object(get(&source_map, "path_targets")?)?.iter() {
        if digest(&root.join(name), check)? != text(get(entry, "sha256")?)? {
            return fail(format!(
                "Path target differs from the receipt the crates were built with: {name}"
            ));
        }
        if optional(entry, "comment_rewrite").is_some() {
            check_recorded_comments(&root.join(name), entry, check)?;
        }
    }
    for (name, entry) in entries(&source_map, "data_files") {
        let sha = text(get(entry, "sha256")?)?;
        if digest(&root.join(name), check)? != sha {
            return fail(format!(
                "Crate data file differs from the source map: {name}"
            ));
        }
        if let Some(same) = optional(entry, "same_as").and_then(Value::as_str)
            && digest(&root.join(same), check)? != sha
        {
            return fail(format!("Crate data file differs from {same}: {name}"));
        }
        if optional(entry, "comment_rewrite").is_some() {
            check_recorded_comments(&root.join(name), entry, check)?;
        }
        result.push(root.join(name));
    }
    let mut targets = BTreeSet::new();
    for (_, entry) in files.iter() {
        for rewrite in optional(entry, "include_rewrites")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            targets.insert(text(get(rewrite, "target")?)?.to_owned());
        }
    }
    result.extend(targets.into_iter().map(|target| root.join(target)));
    Ok(result)
}

fn source_table<'v>(manifest: &'v Value, receipt: &Value) -> Result<&'v Value, Error> {
    let table = optional(receipt, "source_table")
        .and_then(Value::as_str)
        .unwrap_or("source_sha256");
    get(manifest, table)
}

fn archived_path(root: &Path, receipt: &Value, original: &str) -> Result<PathBuf, Error> {
    let manifest = text(get(receipt, "manifest")?)?;
    let archive = optional(receipt, "archive")
        .and_then(Value::as_str)
        .unwrap_or("run/source");
    let parent = root
        .join(manifest)
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| root.to_path_buf());
    Ok(parent.join(archive).join(original))
}

fn str_or(value: Option<&Value>) -> Option<&str> {
    value.and_then(Value::as_str)
}

/// `check_rust_receipts(root, check)`: the map agrees with the receipt archives.
pub fn check_rust_receipts(root: &Path, check: Check<'_>) -> Result<u64, Error> {
    let source_map = load_map(root, RUST_MAP, RUST_SCHEMA, check)?;
    let receipts = object(get(&source_map, "receipts")?)?;
    let mut manifests: BTreeMap<String, Value> = BTreeMap::new();
    for (name, receipt) in receipts.iter() {
        let path = root.join(text(get(receipt, "manifest")?)?);
        if digest(&path, check)? != text(get(receipt, "sha256")?)? {
            return fail(format!("Receipt pin differs: {name}"));
        }
        let manifest = read_json(&path)?;
        if get(&manifest, "status")?.as_str() != Some("passed") {
            return fail(format!("Receipt did not pass: {name}"));
        }
        manifests.insert(name.to_owned(), manifest);
    }
    let lean_map = load_map(root, LEAN_MAP, LEAN_SCHEMA, check)?;
    let mut listed: Vec<(&str, &Value)> = object(get(&source_map, "files")?)?.iter().collect();
    listed.extend(object(get(&source_map, "path_targets")?)?.iter());
    let selected: Vec<(&str, &Value)> = listed
        .into_iter()
        .filter(|(_, entry)| str_or(optional(entry, "origin")) != Some("product"))
        .collect();
    for (name, entry) in &selected {
        let receipt_name = text(get(entry, "receipt")?)?;
        let manifest = manifests
            .get(receipt_name)
            .ok_or_else(|| Error::Key(receipt_name.to_owned()))?;
        let receipt = get(get(&source_map, "receipts")?, receipt_name)?;
        let original = text(get(entry, "original")?)?;
        let archived = archived_path(root, receipt, original)?;
        let expected = str_or(optional(entry, "original_sha256"))
            .map_or_else(|| text(get(entry, "sha256")?), Ok)?;
        let table_value = str_or(object(source_table(manifest, receipt)?)?.get(original));
        let artifact_value = str_or(optional(
            get(manifest, "artifacts_sha256")?,
            &format!("source/{original}"),
        ));
        if table_value != Some(expected)
            || artifact_value != Some(expected)
            || digest(&archived, check)? != expected
        {
            return fail(format!("Source map differs from the receipt: {name}"));
        }
        let empty = Vec::new();
        let list = |key: &str| {
            optional(entry, key)
                .and_then(Value::as_array)
                .unwrap_or(&empty)
        };
        let mut rebuilt = apply_rewrites(
            &read_bytes(&archived)?,
            list("path_rewrites"),
            list("line_edits"),
            list("include_rewrites"),
        )?;
        for rewrite in list("include_rewrites") {
            let from = text(get(rewrite, "from")?)?;
            let source = util::normpath(&util::join(util::dirname(original), from));
            let tested = str_or(object(source_table(manifest, receipt)?)?.get(&source));
            let target = text(get(rewrite, "target")?)?;
            let tail: String = target.chars().skip("lean-v8/".len()).collect();
            let reviewed = optional(get(&lean_map, "files")?, &tail);
            let reviewed_original = reviewed.and_then(|value| {
                str_or(optional(value, "original_sha256"))
                    .or_else(|| str_or(optional(value, "sha256")))
            });
            let reviewed_sha = reviewed.and_then(|value| str_or(optional(value, "sha256")));
            match tested {
                Some(tested)
                    if Some(tested) == reviewed_original || Some(tested) == reviewed_sha => {}
                _ => {
                    return fail(format!(
                        "Rewritten include reads other bytes than the receipt tested: {name}"
                    ));
                }
            }
        }
        if let Some(rewrite) = optional(entry, "comment_rewrite") {
            let suffix = Suffix::of(name).ok_or_else(|| Error::Key(python_suffix(name)))?;
            rebuilt = apply_comment_rewrite(&rebuilt, rewrite, suffix)?;
        }
        if sha256_hex(&rebuilt) != text(get(entry, "sha256")?)? {
            return fail(format!(
                "Moved file is not the receipt bytes with the recorded path strings: {name}"
            ));
        }
    }
    for (name, entry) in entries(&source_map, "data_files") {
        let receipt_name = text(get(entry, "receipt")?)?;
        let manifest = manifests
            .get(receipt_name)
            .ok_or_else(|| Error::Key(receipt_name.to_owned()))?;
        let receipt = get(get(&source_map, "receipts")?, receipt_name)?;
        let original = text(get(entry, "original")?)?;
        let archived = archived_path(root, receipt, original)?;
        let expected = str_or(optional(entry, "original_sha256"))
            .map_or_else(|| text(get(entry, "sha256")?), Ok)?;
        let mut rebuilt = read_bytes(&archived)?;
        if let Some(rewrite) = optional(entry, "comment_rewrite") {
            let suffix = Suffix::of(name).ok_or_else(|| Error::Key(python_suffix(name)))?;
            rebuilt = apply_comment_rewrite(&rebuilt, rewrite, suffix)?;
        }
        if str_or(object(source_table(manifest, receipt)?)?.get(original)) != Some(expected)
            || digest(&archived, check)? != expected
            || sha256_hex(&rebuilt) != text(get(entry, "sha256")?)?
        {
            return fail(format!("Crate data file differs from its receipt: {name}"));
        }
    }
    for (name, entry) in object(get(&source_map, "not_moved")?)?.iter() {
        let receipt_name = text(get(entry, "receipt")?)?;
        let receipt = get(get(&source_map, "receipts")?, receipt_name)?;
        let manifest = manifests
            .get(receipt_name)
            .ok_or_else(|| Error::Key(receipt_name.to_owned()))?;
        if str_or(object(source_table(manifest, receipt)?)?.get(name))
            != Some(text(get(entry, "sha256")?)?)
        {
            return fail(format!("Unmoved receipt file differs: {name}"));
        }
    }
    Ok(selected.len() as u64)
}

/// `gate_table(manifest)`: a gate's module table by lean-v8 path.
pub fn gate_table(manifest: &Value) -> Result<BTreeMap<String, String>, Error> {
    let mut table = BTreeMap::new();
    if let Some(sources) = optional(manifest, "source_sha256") {
        let sources = object(sources)?;
        let by_path = sources.keys().any(|name| name.ends_with(".lean"));
        for (name, value) in sources.iter() {
            let key = if by_path {
                name.to_owned()
            } else {
                format!("{}.lean", name.replace('.', "/"))
            };
            table.insert(key, text(value)?.to_owned());
        }
        return Ok(table);
    }
    for (name, value) in object(get(manifest, "artifacts_sha256")?)?.iter() {
        if let Some(relative) = name.strip_prefix("source/")
            && relative.ends_with(".lean")
        {
            table.insert(relative.to_owned(), text(value)?.to_owned());
        }
    }
    Ok(table)
}

/// REPORT of v8_dependencies: a whole line `'name'\s+(depends on axioms:\s*[...]|does not depend on any axioms)\s*`.
fn line_reports(text: &str) -> Vec<(String, Option<String>)> {
    let space = |character: char| fang_json_isspace(character);
    let mut found = Vec::new();
    let mut position = 0;
    let bytes_len = text.len();
    // re.M with ^ and $: try at the start of the text and after each newline; `\s+`, `\s*` and the
    // trailing `\s*` may cross newlines, and `$` then matches before a newline or at the end.
    let mut starts = vec![0usize];
    starts.extend(text.match_indices('\n').map(|(index, _)| index + 1));
    let mut consumed_until = 0;
    for start in starts {
        if start < consumed_until || start > bytes_len {
            continue;
        }
        let rest = &text[start..];
        let Some(after_quote) = rest.strip_prefix('\'') else {
            continue;
        };
        let Some(close) = after_quote.find('\'') else {
            continue;
        };
        let name = &after_quote[..close];
        if name.is_empty() || name.contains('\n') {
            continue;
        }
        let mut index = start + 1 + close + 1;
        let gap_start = index;
        while let Some(character) = text[index..]
            .chars()
            .next()
            .filter(|character| space(*character))
        {
            index += character.len_utf8();
        }
        if index == gap_start {
            continue;
        }
        let mut axioms = None;
        let mut end = None;
        if text[index..].starts_with("depends on axioms:") {
            let mut inner = index + "depends on axioms:".len();
            while let Some(character) = text[inner..]
                .chars()
                .next()
                .filter(|character| space(*character))
            {
                inner += character.len_utf8();
            }
            if text[inner..].starts_with('[')
                && let Some(close) = text[inner + 1..].find(']')
            {
                axioms = Some(text[inner + 1..inner + 1 + close].to_owned());
                end = Some(inner + 1 + close + 1);
            }
        }
        if end.is_none() && text[index..].starts_with("does not depend on any axioms") {
            end = Some(index + "does not depend on any axioms".len());
        }
        let Some(mut end) = end else { continue };
        // Trailing \s* (greedy, may cross lines), then $ (end of text or before a newline).
        let mut last_valid = None;
        let mut scan = end;
        loop {
            if scan == bytes_len || text[scan..].starts_with('\n') {
                last_valid = Some(scan);
            }
            match text[scan..].chars().next() {
                Some(character) if space(character) => scan += character.len_utf8(),
                _ => break,
            }
        }
        let Some(stop) = last_valid else { continue };
        end = stop;
        found.push((name.to_owned(), axioms));
        consumed_until = end.max(start + 1);
        position = end;
    }
    let _ = position;
    found
}

/// `stage_reports(directory, manifest, modules, check)`.
pub fn stage_reports(
    directory: &Path,
    manifest: &Value,
    modules: &BTreeSet<String>,
    check: Check<'_>,
) -> Result<BTreeMap<String, Vec<String>>, Error> {
    let mut reports: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for module in modules {
        check()?;
        let relative = format!("stages/{module}/stdout");
        let path = directory.join("run").join(&relative);
        let recorded = str_or(optional(get(manifest, "artifacts_sha256")?, &relative));
        if Some(digest(&path, check)?.as_str()) != recorded {
            return fail(format!("Stage output differs from its receipt: {module}"));
        }
        // Path.read_text(errors="replace") decodes and translates line endings.
        let text = String::from_utf8_lossy(&read_bytes(&path)?)
            .replace("\r\n", "\n")
            .replace('\r', "\n");
        for (name, axioms) in line_reports(&text) {
            let mut items: Vec<String> = axioms
                .unwrap_or_default()
                .split(',')
                .map(|item| item.trim_matches(fang_json_isspace).to_owned())
                .filter(|item| !item.is_empty())
                .collect();
            items.sort();
            items.dedup();
            match reports.get(&name) {
                Some(existing) if *existing != items => {
                    return fail(format!("Stage outputs disagree on the axioms of {name}"));
                }
                Some(_) => {}
                None => {
                    reports.insert(name, items);
                }
            }
        }
    }
    Ok(reports)
}

fn import_line(text: &str) -> bool {
    // IMPORT_LINE.fullmatch: "public import [A-Za-z0-9_.]+"
    text.strip_prefix("public import ").is_some_and(|rest| {
        !rest.is_empty()
            && rest
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.')
    })
}

/// `remove_imports(data, additions)`.
pub fn remove_imports(data: &[u8], additions: &[Value]) -> Result<Vec<u8>, Error> {
    let source = decode(data)?;
    let mut lines: Vec<&str> = source.split('\n').collect();
    let mut rows: Vec<&Value> = additions.iter().collect();
    rows.sort_by_key(|row| {
        std::cmp::Reverse(integer(get(row, "line").unwrap_or(&Value::Null)).unwrap_or(0))
    });
    for addition in rows {
        let number = line_of(addition)?;
        let wanted = text(get(addition, "text")?)?;
        if !import_line(wanted) || number == 0 || lines.get(number - 1) != Some(&wanted) {
            return fail("Recorded import addition does not match the file");
        }
        lines.remove(number - 1);
    }
    Ok(lines.join("\n").into_bytes())
}

/// `add_imports(data, additions)`.
pub fn add_imports(data: &[u8], additions: &[Value]) -> Result<Vec<u8>, Error> {
    let source = decode(data)?;
    let mut lines: Vec<String> = source.split('\n').map(str::to_owned).collect();
    let mut rows: Vec<&Value> = additions.iter().collect();
    rows.sort_by_key(|row| integer(get(row, "line").unwrap_or(&Value::Null)).unwrap_or(0));
    for addition in rows {
        let wanted = text(get(addition, "text")?)?;
        if !import_line(wanted) {
            return fail("Recorded import addition is not an import line");
        }
        let index = (line_of(addition)?).saturating_sub(1).min(lines.len());
        lines.insert(index, wanted.to_owned());
    }
    Ok(lines.join("\n").into_bytes())
}

/// IMPORT.fullmatch on each line: "(?:public )?import ([A-Za-z0-9_. ]+)" with the line number,
/// the tokens text and its character start.
fn imports(source: &str) -> Vec<(usize, String, usize)> {
    let mut found = Vec::new();
    for (number, line) in source.split('\n').enumerate() {
        let (prefix, rest) = if let Some(rest) = line.strip_prefix("public import ") {
            ("public import ", rest)
        } else if let Some(rest) = line.strip_prefix("import ") {
            ("import ", rest)
        } else {
            continue;
        };
        if !rest.is_empty()
            && rest
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == ' ')
        {
            found.push((number + 1, rest.to_owned(), prefix.chars().count()));
        }
    }
    found
}

fn imported_tokens(source: &str) -> HashSet<String> {
    imports(source)
        .into_iter()
        .flat_map(|(_, tokens, _)| {
            tokens
                .split_whitespace()
                .map(str::to_owned)
                .collect::<Vec<_>>()
        })
        .collect()
}

/// `lean_files(root, check)`: every lean-v8 source after checking the exact inventory and hashes.
pub fn lean_files(root: &Path, check: Check<'_>) -> Result<Vec<PathBuf>, Error> {
    let source_map = load_map(root, LEAN_MAP, LEAN_SCHEMA, check)?;
    let project = root.join(text(get(&source_map, "project")?)?);
    let files = object(get(&source_map, "files")?)?;
    let expected: BTreeSet<String> = files.keys().map(str::to_owned).collect();
    if listed_tree(&project, check, &[".lake", "build"])? != expected {
        return fail("lean-v8 inventory differs from the source map");
    }
    for relative in &expected {
        let entry = files.get(relative).expect("listed");
        if digest(&project.join(relative), check)? != text(get(entry, "sha256")?)? {
            return fail(format!(
                "lean-v8 file differs from the source map: {relative}"
            ));
        }
    }
    check_adaptations(&project, &source_map, check)?;
    check_left_out(&project, &source_map, check)?;
    Ok(expected
        .into_iter()
        .map(|relative| project.join(relative))
        .collect())
}

/// `check_left_out(project, source_map, check)`.
pub fn check_left_out(project: &Path, source_map: &Value, check: Check<'_>) -> Result<(), Error> {
    let mut left_out: BTreeMap<String, String> = BTreeMap::new();
    for (_, gate) in object(get(source_map, "gates")?)?.iter() {
        for (relative, reason) in entries(gate, "left_out") {
            if !truthy(reason) || !relative.ends_with(".lean") {
                return fail(format!("Left-out module without a reason: {relative}"));
            }
            left_out.insert(
                relative[..relative.len() - 5].replace('/', "."),
                relative.to_owned(),
            );
        }
    }
    let files = object(get(source_map, "files")?)?;
    let staged: HashSet<String> = files
        .keys()
        .filter(|relative| relative.ends_with(".lean"))
        .map(|relative| relative[..relative.len() - 5].replace('/', "."))
        .collect();
    if left_out.keys().any(|module| staged.contains(module))
        || left_out
            .values()
            .any(|relative| project.join(relative).exists())
    {
        return fail("A left-out module is staged in lean-v8");
    }
    let mut names: Vec<&str> = files.keys().collect();
    names.sort();
    for relative in names {
        check()?;
        if relative.ends_with(".lean") {
            let source = read_text(&project.join(relative))?;
            if imported_tokens(&source)
                .iter()
                .any(|token| left_out.contains_key(token))
            {
                return fail(format!("Module imports a left-out module: {relative}"));
            }
        }
    }
    Ok(())
}

fn renames_of(value: Option<&Value>) -> BTreeMap<String, String> {
    value
        .and_then(Value::as_object)
        .map(|object| {
            object
                .iter()
                .filter_map(|(old, new)| new.as_str().map(|new| (old.to_owned(), new.to_owned())))
                .collect()
        })
        .unwrap_or_default()
}

/// `check_adaptations(project, source_map, check)`.
pub fn check_adaptations(
    project: &Path,
    source_map: &Value,
    check: Check<'_>,
) -> Result<(), Error> {
    let renames = renames_of(optional(source_map, "module_renames"));
    // In map order, as Python iterates the gates.
    let scoped: Vec<(String, BTreeMap<String, String>)> = entries(source_map, "gates")
        .into_iter()
        .map(|(name, gate)| {
            (
                name.to_owned(),
                renames_of(optional(gate, "module_renames")),
            )
        })
        .collect();
    let files = object(get(source_map, "files")?)?;
    let lowered: Vec<String> = files.keys().map(str::to_lowercase).collect();
    if lowered.iter().collect::<HashSet<_>>().len() != lowered.len() {
        return fail("lean-v8 has paths that differ only in letter case");
    }
    let mut names: Vec<&str> = files.keys().collect();
    names.sort();
    for relative in names {
        let entry = files.get(relative).expect("listed");
        check()?;
        if !relative.ends_with(".lean") {
            continue;
        }
        let adaptation = optional(entry, "adaptation");
        let mut current = read_bytes(&project.join(relative))?;
        let imports_added = optional(entry, "imports_added")
            .and_then(Value::as_array)
            .filter(|items| !items.is_empty());
        if let Some(additions) = imports_added {
            current = remove_imports(&current, additions)?;
            if Some(sha256_hex(&current).as_str()) != str_or(optional(entry, "pre_import_sha256")) {
                return fail(format!(
                    "Module differs from its bytes before the recorded imports: {relative}"
                ));
            }
        }
        let source = read_decoded(&project.join(relative))?;
        let imported = imported_tokens(&source);
        if imported.iter().any(|token| renames.contains_key(token)) {
            return fail(format!("Import of a renamed module remains: {relative}"));
        }
        let receipt = str_or(optional(entry, "receipt"));
        let also: Vec<String> = optional(entry, "also_in")
            .and_then(Value::as_array)
            .map(|items| {
                items
                    .iter()
                    .filter_map(|item| item.as_str().map(str::to_owned))
                    .collect()
            })
            .unwrap_or_default();
        let owners: HashSet<Option<String>> = std::iter::once(receipt.map(str::to_owned))
            .chain(also.iter().cloned().map(Some))
            .collect();
        for (gate, gate_renames) in &scoped {
            let owned = owners.contains(&Some(gate.clone()));
            if owned
                && imported
                    .iter()
                    .any(|token| gate_renames.contains_key(token))
            {
                return fail(format!(
                    "Import of a module renamed in {gate} remains: {relative}"
                ));
            }
            if !owned
                && imported
                    .iter()
                    .any(|token| gate_renames.values().any(|new| new == token))
            {
                return fail(format!(
                    "Import of a module renamed only in {gate}: {relative}"
                ));
            }
        }
        let mut own = renames.clone();
        if let Some(receipt) = receipt
            && also.is_empty()
            && let Some((_, gate_renames)) = scoped.iter().find(|(gate, _)| gate == receipt)
        {
            own.extend(gate_renames.clone());
        }
        if let Some(adaptation) = adaptation
            && text(get(adaptation, "kind")?)? == "comment-rewrite"
        {
            if relative != text(get(entry, "original")?)? {
                return fail(format!("Comment rewrite of a moved module: {relative}"));
            }
            check_comment_rewrite(&current, adaptation, Suffix::Lean)?;
            continue;
        }
        let Some(adaptation) = adaptation else {
            let original = str_or(optional(entry, "original")).unwrap_or(relative);
            let moved =
                relative != original && str_or(optional(entry, "origin")) != Some("pinned-source");
            if moved
                || optional(entry, "original_sha256").is_some()
                || imported
                    .iter()
                    .any(|token| own.values().any(|new| new == token))
                || imports_added.is_some()
            {
                return fail(format!("Unrecorded adaptation: {relative}"));
            }
            continue;
        };
        let old = text(get(adaptation, "from")?)?;
        let new = text(get(adaptation, "to")?)?;
        if own.get(old).map(String::as_str) != Some(new) {
            return fail(format!("Adaptation names an unrecorded rename: {relative}"));
        }
        match text(get(adaptation, "kind")?)? {
            "module-rename" => {
                if relative != format!("{}.lean", new.replace('.', "/"))
                    || text(get(entry, "original")?)? != format!("{}.lean", old.replace('.', "/"))
                    || optional(entry, "original_sha256").is_some()
                {
                    return fail(format!(
                        "Renamed module is not a path-only move: {relative}"
                    ));
                }
            }
            "import-rename" => {
                let lines_field: Vec<i64> = array(get(adaptation, "lines")?)?
                    .iter()
                    .map(integer)
                    .collect::<Result<_, _>>()?;
                let mut lines: Vec<String> = source.split('\n').map(str::to_owned).collect();
                for (number, tokens, start) in imports(&source) {
                    let split: Vec<&str> = tokens.split(' ').collect();
                    let has_new = split.contains(&new);
                    if has_new != lines_field.contains(&(number as i64)) {
                        return fail(format!(
                            "Import lines differ from the recorded adaptation: {relative}"
                        ));
                    }
                    if has_new {
                        let replaced: Vec<&str> = split
                            .iter()
                            .map(|token| if *token == new { old } else { token })
                            .collect();
                        let line: String = lines[number - 1].chars().take(start).collect();
                        lines[number - 1] = format!("{line}{}", replaced.join(" "));
                    }
                }
                if relative != text(get(entry, "original")?)?
                    || sha256_hex(lines.join("\n").as_bytes())
                        != text(get(entry, "original_sha256")?)?
                {
                    return fail(format!(
                        "Module differs from the gate beyond the recorded import lines: {relative}"
                    ));
                }
            }
            _ => return fail(format!("Unknown adaptation kind: {relative}")),
        }
    }
    Ok(())
}

/// `check_lean_receipts(root, check)`: every module equals its gate's source table and archive,
/// and the audit list its gates.
pub fn check_lean_receipts(root: &Path, check: Check<'_>) -> Result<u64, Error> {
    let source_map = load_map(root, LEAN_MAP, LEAN_SCHEMA, check)?;
    let mut checked = 0u64;
    let mut manifests: BTreeMap<String, Value> = BTreeMap::new();
    for (name, receipt) in object(get(&source_map, "receipts")?)?.iter() {
        let path = root.join(text(get(receipt, "manifest")?)?);
        if digest(&path, check)? != text(get(receipt, "sha256")?)? {
            return fail(format!("Receipt pin differs: {name}"));
        }
        manifests.insert(name.to_owned(), read_json(&path)?);
    }
    let gate_entries = object(get(&source_map, "gates")?)?;
    let files = object(get(&source_map, "files")?)?;
    let executables = object(get(&source_map, "executables")?)?;
    // The gates in map order, as Python iterates them.
    let mut gates: Vec<(String, &Value)> = Vec::new();
    for (name, _) in gate_entries.iter() {
        gates.push((
            name.to_owned(),
            manifests
                .get(name)
                .ok_or_else(|| Error::Key(name.to_owned()))?,
        ));
    }
    let gate_of = |name: &str| -> Result<&Value, Error> {
        gates
            .iter()
            .find(|(other, _)| other == name)
            .map(|(_, gate)| *gate)
            .ok_or_else(|| Error::Key(name.to_owned()))
    };
    let receipt_of = |entry: &Value| str_or(optional(entry, "receipt")).map(str::to_owned);
    let also_of = |entry: &Value| -> Vec<String> {
        optional(entry, "also_in")
            .and_then(Value::as_array)
            .map(|items| {
                items
                    .iter()
                    .filter_map(|item| item.as_str().map(str::to_owned))
                    .collect()
            })
            .unwrap_or_default()
    };
    for (name, gate) in &gates {
        let gate_entry = gate_entries.get(name).expect("listed");
        if optional(gate_entry, "over_tree").is_some_and(truthy) {
            let owned: BTreeSet<&str> = files
                .iter()
                .filter(|(_, entry)| receipt_of(entry).as_deref() == Some(name.as_str()))
                .map(|(relative, _)| relative)
                .collect();
            let table = object(get(gate, "source_sha256")?)?;
            let mismatch = table
                .iter()
                .any(|(relative, value)| match files.get(relative) {
                    None => true,
                    Some(entry) => {
                        !owned.contains(relative)
                            && str_or(optional(entry, "pre_import_sha256"))
                                .or_else(|| str_or(optional(entry, "sha256")))
                                != value.as_str()
                    }
                });
            if !owned.iter().all(|relative| table.contains_key(relative)) || mismatch {
                return fail(format!(
                    "lean-v8 differs from the tree {name} was gated over"
                ));
            }
            continue;
        }
        let covered: BTreeSet<String> = files
            .iter()
            .filter(|(_, entry)| {
                (str_or(optional(entry, "origin")).is_some_and(|origin| origin.ends_with("-gate"))
                    && receipt_of(entry).as_deref() == Some(name.as_str()))
                    || also_of(entry).contains(name)
            })
            .filter_map(|(_, entry)| str_or(optional(entry, "original")).map(str::to_owned))
            .collect();
        let left_out: BTreeSet<String> = entries(gate_entry, "left_out")
            .into_iter()
            .map(|(relative, _)| relative.to_owned())
            .collect();
        let replaced: Vec<(&str, &Value)> = entries(gate_entry, "replaced");
        for (relative, owner) in &replaced {
            let owner = owner.as_str().unwrap_or_default();
            let entry = files.get(relative);
            let built = executables.get(owner);
            let by_build = built.is_some_and(|built| {
                optional(built, "build_receipt").is_some()
                    && str_or(optional(built, "root"))
                        .map(|root| format!("{}.lean", root.replace('.', "/")))
                        .as_deref()
                        == Some(relative)
            });
            let by_gate = gate_entries
                .get(owner)
                .is_some_and(|owner_gate| optional(owner_gate, "over_tree").is_some_and(truthy))
                && owner != name
                && entry.is_some_and(|entry| receipt_of(entry).as_deref() == Some(owner));
            let empty =
                entry.is_none_or(|entry| entry.as_object().is_none_or(|object| object.is_empty()));
            if empty
                || entry.is_some_and(|entry| {
                    receipt_of(entry).as_deref() == Some(name.as_str())
                        || also_of(entry).contains(name)
                })
                || !(by_build || by_gate)
            {
                return fail(format!(
                    "Replaced module has no main with a native build or owning gate: {relative}"
                ));
            }
        }
        let replaced_set: BTreeSet<String> = replaced
            .iter()
            .map(|(relative, _)| (*relative).to_owned())
            .collect();
        let table: BTreeSet<String> = gate_table(gate)?.into_keys().collect();
        let union: BTreeSet<String> = covered
            .iter()
            .chain(left_out.iter())
            .chain(replaced_set.iter())
            .cloned()
            .collect();
        if covered.intersection(&left_out).next().is_some()
            || covered.intersection(&replaced_set).next().is_some()
            || left_out.intersection(&replaced_set).next().is_some()
            || union != table
        {
            return fail(format!(
                "lean-v8 modules are not exactly the module set of {name}"
            ));
        }
    }
    for (relative, entry) in files.iter() {
        let origin = text(get(entry, "origin")?)?;
        if origin == "product" {
            continue;
        }
        let original = str_or(optional(entry, "original_sha256"))
            .map_or_else(|| text(get(entry, "sha256")?), Ok)?;
        let original_path = text(get(entry, "original")?)?;
        if origin == "pinned-source" {
            let path = root.join(original_path);
            if path.exists() && digest(&path, check)? != original {
                return fail(format!(
                    "Pinned source changed in the working tree: {relative}"
                ));
            }
            checked += 1;
            continue;
        }
        let receipt_name = text(get(entry, "receipt")?)?;
        let manifest = manifests
            .get(receipt_name)
            .ok_or_else(|| Error::Key(receipt_name.to_owned()))?;
        let receipt = get(get(&source_map, "receipts")?, receipt_name)?;
        let archived = root
            .join(text(get(receipt, "manifest")?)?)
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_default()
            .join("run/source")
            .join(original_path);
        let recorded = if origin.ends_with("-gate") {
            gate_table(manifest)?.get(original_path).cloned()
        } else {
            str_or(optional(
                get(manifest, "capture_sha256")?,
                &format!("source/{original_path}"),
            ))
            .map(str::to_owned)
        };
        let adaptation_kind =
            optional(entry, "adaptation").and_then(|value| str_or(optional(value, "kind")));
        let moved = adaptation_kind == Some("module-rename");
        let differs = (relative != original_path && !moved) || {
            // original == recorded == digest(archived) == artifacts[...], evaluated left to right.
            let same = recorded.as_deref() == Some(original)
                && digest(&archived, check)? == original
                && text(get(
                    get(manifest, "artifacts_sha256")?,
                    &format!("source/{original_path}"),
                )?)? == original;
            !same
        };
        if differs {
            return fail(format!("Lean source differs from its receipt: {relative}"));
        }
        let mut rebuilt = read_bytes(&archived)?;
        if adaptation_kind == Some("comment-rewrite") {
            rebuilt = apply_comment_rewrite(&rebuilt, get(entry, "adaptation")?, Suffix::Lean)?;
        }
        let imports_added = optional(entry, "imports_added")
            .and_then(Value::as_array)
            .filter(|items| !items.is_empty());
        if let Some(additions) = imports_added {
            rebuilt = add_imports(&rebuilt, additions)?;
        }
        if (adaptation_kind == Some("comment-rewrite") || imports_added.is_some())
            && sha256_hex(&rebuilt) != text(get(entry, "sha256")?)?
        {
            return fail(format!(
                "Module is not its receipt bytes with the recorded comment edits and imports: {relative}"
            ));
        }
        for gate_name in also_of(entry) {
            let gate = gate_of(&gate_name)?;
            if gate_table(gate)?.get(original_path).map(String::as_str) != Some(original) {
                return fail(format!("Shared module differs in {gate_name}: {relative}"));
            }
        }
        checked += 1;
    }
    let audits = read_json(
        &root
            .join(text(get(&source_map, "project")?)?)
            .join("audits.json"),
    )?;
    let mut expected: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (name, gate) in &gates {
        let gate_entry = gate_entries.get(name).expect("listed");
        let key = str_or(optional(gate_entry, "audit_key")).unwrap_or("fixed_audit_set");
        if key == "stage_reports" {
            let modules: BTreeSet<String> = files
                .iter()
                .filter_map(|(_, entry)| {
                    let original = str_or(optional(entry, "original"))?;
                    (original.ends_with(".lean")
                        && (receipt_of(entry).as_deref() == Some(name.as_str())
                            || also_of(entry).contains(name)))
                    .then(|| original[..original.len() - 5].replace('/', "."))
                })
                .collect();
            let receipt = get(get(&source_map, "receipts")?, name)?;
            let directory = root
                .join(text(get(receipt, "manifest")?)?)
                .parent()
                .map(Path::to_path_buf)
                .unwrap_or_default();
            for (theorem, axioms) in stage_reports(&directory, gate, &modules, check)? {
                match expected.get(&theorem) {
                    Some(existing) if *existing != axioms => {
                        return fail(format!("Gates disagree on the axioms of {theorem}"));
                    }
                    Some(_) => {}
                    None => {
                        expected.insert(theorem, axioms);
                    }
                }
            }
            continue;
        }
        let audits_table = get(gate, "axiom_audits")?;
        for theorem in array(get(gate, key)?)? {
            let theorem = text(theorem)?;
            if !expected.contains_key(theorem) {
                let mut axioms = strings(get(audits_table, theorem)?)?;
                axioms.sort();
                expected.insert(theorem.to_owned(), axioms);
            }
        }
    }
    let mut listed: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (theorem, row) in object(get(&audits, "names")?)?.iter() {
        listed.insert(theorem.to_owned(), strings(get(row, "axioms")?)?);
    }
    if listed != expected {
        return fail("Fixed audit list differs from the gates");
    }
    let roots = get(&audits, "roots")?;
    for (name, entry) in gate_entries.iter() {
        if get(roots, name)? != get(entry, "library_roots")? {
            return fail("Audit roots differ from the gate roots");
        }
    }
    for (name, executable) in executables.iter() {
        let gate_name = str_or(optional(executable, "gate"));
        let gate_entry = gate_name.and_then(|gate| gate_entries.get(gate));
        let mut renames = renames_of(optional(&source_map, "module_renames"));
        renames.extend(renames_of(
            gate_entry.and_then(|entry| optional(entry, "module_renames")),
        ));
        let mut renamed: BTreeMap<String, String> =
            renames.into_iter().map(|(old, new)| (new, old)).collect();
        if gate_entry.is_some_and(|entry| optional(entry, "over_tree").is_some_and(truthy)) {
            renamed.clear();
        }
        let additions: BTreeSet<String> = optional(executable, "closure_additions")
            .and_then(Value::as_array)
            .map(|items| {
                items
                    .iter()
                    .filter_map(|item| item.as_str().map(str::to_owned))
                    .collect()
            })
            .unwrap_or_default();
        let mut closure: Vec<String> = array(get(executable, "closure")?)?
            .iter()
            .filter_map(Value::as_str)
            .filter(|module| !additions.contains(*module))
            .map(|module| {
                renamed
                    .get(module)
                    .cloned()
                    .unwrap_or_else(|| module.to_owned())
            })
            .collect();
        closure.sort();
        if let Some(build_receipt) = str_or(optional(executable, "build_receipt")) {
            let receipt = manifests
                .get(build_receipt)
                .ok_or_else(|| Error::Key(build_receipt.to_owned()))?;
            let built = optional(receipt, "executables")
                .and_then(|executables| optional(executables, name));
            if let Some(built) = built
                && optional(built, "root") != Some(get(executable, "root")?)
            {
                return fail(format!("{name} has another root in its native build"));
            }
            match built {
                Some(built) if optional(built, "module_order").is_none() => {
                    let order: BTreeSet<String> = strings(get(receipt, "module_order")?)?
                        .into_iter()
                        .collect();
                    if closure.len() as i64 != integer(get(built, "closure_modules")?)?
                        || !closure.iter().all(|module| order.contains(module))
                    {
                        return fail(format!("{name} closure differs from its native build"));
                    }
                }
                _ => {
                    let source = built.unwrap_or(receipt);
                    let mut order = strings(get(source, "module_order")?)?;
                    order.sort();
                    if closure != order {
                        return fail(format!("{name} closure differs from its native build"));
                    }
                }
            }
        } else if str_or(optional(executable, "closure_source")) == Some("gate") {
            let gate_name = gate_name.ok_or_else(|| Error::Key("gate".to_owned()))?;
            let gate = gate_of(gate_name)?;
            let table = gate_table(gate)?;
            if !closure
                .iter()
                .all(|module| table.contains_key(&format!("{}.lean", module.replace('.', "/"))))
            {
                return fail(format!("{name} closure leaves its gate"));
            }
        }
    }
    Ok(checked)
}

/// Python truthiness of a JSON value.
fn truthy(value: &Value) -> bool {
    match value {
        Value::Null => false,
        Value::Bool(value) => *value,
        Value::Number(fang_json::Number::Integer(integer)) => integer.magnitude() != 0,
        Value::Number(fang_json::Number::Float(float)) => *float != 0.0,
        Value::String(text) => !text.is_empty(),
        Value::Array(items) => !items.is_empty(),
        Value::Object(object) => !object.is_empty(),
    }
}
