// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Lean axiom audits: every parser of `#print axioms` reports the Fang tools use, in one place.
//!
//! - `audit_axioms`, `reports` and `strip_reports`: tools/replay/axiom_audit.py, and through it
//!   protocol.exact_axioms and kernel_replay.exact_audits.
//! - `parse_build_audit`: parse_audit of tools/build-v8-lean.py.
//! - `check_suite_audit`: the audit of tools/replay/check-suite.py.
//!
//! Each regular expression is a hand-written scanner with Python's `finditer` semantics;
//! Python's `\s` and `str.strip()` use the whitespace set of `str.isspace`, written out below.
//! Error texts are Python's.
#![forbid(unsafe_code)]

use fang_json::{python_repr_list, python_repr_str};

pub const ALLOWED_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuditError(pub String);

impl std::fmt::Display for AuditError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for AuditError {}

fn fail<T>(message: impl Into<String>) -> Result<T, AuditError> {
    Err(AuditError(message.into()))
}

/// Python's `str.isspace` (and `\s` in a str pattern).
pub fn is_python_space(character: char) -> bool {
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

/// `text.strip()`.
pub fn python_strip(text: &str) -> &str {
    text.trim_matches(is_python_space)
}

/// One report: its name, the text between the brackets (`None` for "does not depend on any
/// axioms"), and its byte span in the output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Report {
    pub name: String,
    pub axioms: Option<String>,
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Copy)]
enum Gap {
    /// `\s+` before the alternatives and `\s*` after "axioms:".
    Whitespace,
    /// One literal space in both places.
    Space,
}

#[derive(Clone, Copy)]
struct Pattern {
    name_spans_lines: bool,
    gap: Gap,
    depends: bool,
    none: bool,
    newline: bool,
}

/// axiom_audit.REPORT
const AUDIT: Pattern = Pattern {
    name_spans_lines: false,
    gap: Gap::Whitespace,
    depends: true,
    none: true,
    newline: false,
};
/// build-v8-lean.REPORT
const BUILD: Pattern = Pattern {
    name_spans_lines: false,
    gap: Gap::Space,
    depends: true,
    none: true,
    newline: true,
};
/// check-suite.py's two findall patterns.
const SUITE_DEPENDS: Pattern = Pattern {
    name_spans_lines: true,
    gap: Gap::Space,
    depends: true,
    none: false,
    newline: false,
};
const SUITE_NONE: Pattern = Pattern {
    name_spans_lines: true,
    gap: Gap::Space,
    depends: false,
    none: true,
    newline: false,
};

fn match_at(text: &str, start: usize, pattern: Pattern) -> Option<Report> {
    let rest = &text[start..];
    let mut characters = rest.char_indices();
    if characters.next()?.1 != '\'' {
        return None;
    }
    let mut name_end = None;
    for (offset, character) in characters {
        if character == '\'' {
            name_end = Some(offset);
            break;
        }
        if character == '\n' && !pattern.name_spans_lines {
            return None;
        }
    }
    let name_end = name_end?;
    if name_end == 1 {
        return None;
    }
    let name = rest[1..name_end].to_owned();
    let mut position = start + name_end + 1;
    let skip_gap = |position: &mut usize, at_least_one: bool| -> bool {
        match pattern.gap {
            Gap::Space => {
                if text[*position..].starts_with(' ') {
                    *position += 1;
                    true
                } else {
                    false
                }
            }
            Gap::Whitespace => {
                let mut count = 0;
                for character in text[*position..].chars() {
                    if !is_python_space(character) {
                        break;
                    }
                    *position += character.len_utf8();
                    count += 1;
                }
                count > 0 || !at_least_one
            }
        }
    };
    if !skip_gap(&mut position, true) {
        return None;
    }
    let finish = |end: usize, axioms: Option<String>| -> Option<Report> {
        let mut end = end;
        if pattern.newline {
            if !text[end..].starts_with('\n') {
                return None;
            }
            end += 1;
        }
        Some(Report {
            name: name.clone(),
            axioms,
            start,
            end,
        })
    };
    if pattern.depends && text[position..].starts_with("depends on axioms:") {
        let mut inner = position + "depends on axioms:".len();
        if skip_gap(&mut inner, false) && text[inner..].starts_with('[') {
            inner += 1;
            if let Some(close) = text[inner..].find(']')
                && let Some(report) = finish(
                    inner + close + 1,
                    Some(text[inner..inner + close].to_owned()),
                )
            {
                return Some(report);
            }
        }
    }
    if pattern.none && text[position..].starts_with("does not depend on any axioms") {
        return finish(position + "does not depend on any axioms".len(), None);
    }
    None
}

fn finditer(text: &str, pattern: Pattern) -> Vec<Report> {
    let mut found = Vec::new();
    let mut position = 0;
    while position < text.len() {
        match match_at(text, position, pattern) {
            Some(report) => {
                position = report.end;
                found.push(report);
            }
            None => position += text[position..].chars().next().map_or(1, char::len_utf8),
        }
    }
    found
}

/// `axiom_audit.REPORT.finditer(output)`.
pub fn reports(output: &str) -> Vec<Report> {
    finditer(output, AUDIT)
}

/// `axiom_audit.REPORT.sub("", output)`.
pub fn strip_reports(output: &str) -> String {
    let mut kept = String::new();
    let mut end = 0;
    for report in reports(output) {
        kept.push_str(&output[end..report.start]);
        end = report.end;
    }
    kept.push_str(&output[end..]);
    kept
}

fn allowed(axiom: &str) -> bool {
    ALLOWED_AXIOMS.contains(&axiom)
}

/// axiom_audit.audit_axioms: fail closed on missing reports or any axiom outside the allowlist.
/// The result keeps the order of first reports, each with its sorted axioms.
pub fn audit_axioms(
    output: &str,
    required: &[&str],
) -> Result<Vec<(String, Vec<String>)>, AuditError> {
    if required.is_empty() {
        return fail("At least one theorem must be required by the audit");
    }
    if output.contains("sorryAx") {
        return fail("Lean audit contains sorryAx");
    }
    let mut found: Vec<(String, Vec<String>)> = Vec::new();
    for report in reports(output) {
        let mut names: Vec<String> = match &report.axioms {
            None => Vec::new(),
            Some(text) => text
                .split(',')
                .map(python_strip)
                .filter(|name| !name.is_empty())
                .map(str::to_owned)
                .collect(),
        };
        names.sort();
        names.dedup();
        let mut unexpected: Vec<&str> = names
            .iter()
            .map(String::as_str)
            .filter(|name| !allowed(name))
            .collect();
        if !unexpected.is_empty() {
            unexpected.sort();
            return fail(format!(
                "Unexpected axioms for {}: {}",
                report.name,
                python_repr_list(unexpected)
            ));
        }
        match found.iter_mut().find(|(name, _)| *name == report.name) {
            Some((_, value)) if *value != names => {
                return fail(format!("Conflicting axiom reports for {}", report.name));
            }
            Some((_, value)) => *value = names,
            None => found.push((report.name, names)),
        }
    }
    let mut missing: Vec<&str> = required
        .iter()
        .copied()
        .filter(|name| !found.iter().any(|(other, _)| other == name))
        .collect();
    if !missing.is_empty() {
        missing.sort();
        missing.dedup();
        return fail(format!(
            "Missing Lean theorem audits: {}",
            python_repr_list(missing)
        ));
    }
    Ok(found)
}

/// build-v8-lean.parse_audit: reports and nothing else, each name once, standard axioms only,
/// the names equal to `names`, and each equal to its gate record.
pub fn parse_build_audit(
    text: &str,
    names: &[&str],
    recorded: &[(&str, Vec<String>)],
) -> Result<Vec<(String, Vec<String>)>, AuditError> {
    if text.contains("sorryAx") {
        return fail("Audit output mentions sorryAx");
    }
    let mut found: Vec<(String, Vec<String>)> = Vec::new();
    let mut end = 0;
    for report in finditer(text, BUILD) {
        if report.start != end {
            return fail("Unexpected audit output");
        }
        end = report.end;
        if found.iter().any(|(name, _)| *name == report.name) {
            return fail(format!("Duplicate audit report: {}", report.name));
        }
        let mut axioms: Vec<String> = match &report.axioms {
            None => Vec::new(),
            Some(text) => text
                .split(',')
                .map(|item| python_strip(item).to_owned())
                .collect(),
        };
        axioms.sort();
        if !axioms.iter().all(|axiom| allowed(axiom)) {
            return fail(format!(
                "Nonstandard axiom in {}: {}",
                report.name,
                python_repr_list(axioms.iter().map(String::as_str))
            ));
        }
        found.push((report.name, axioms));
    }
    if end != text.len() {
        return fail("Unexpected trailing audit output");
    }
    let mut reported: Vec<&str> = found.iter().map(|(name, _)| name.as_str()).collect();
    reported.sort();
    let mut expected: Vec<&str> = names.to_vec();
    expected.sort();
    if reported != expected {
        return fail("Audit reports differ from the fixed audit list");
    }
    for name in names {
        let reported = &found
            .iter()
            .find(|(other, _)| other == name)
            .expect("checked above")
            .1;
        let mut record: Vec<String> = recorded
            .iter()
            .find(|(other, _)| other == name)
            .map(|(_, axioms)| axioms.clone())
            .unwrap_or_default();
        record.sort();
        if *reported != record {
            return fail(format!("Axioms differ from the gate record: {name}"));
        }
    }
    Ok(found)
}

/// check-suite.py: the "depends" reports, then the "does not depend" reports, each with its
/// sorted, deduplicated axioms; an axiom outside the three standard ones is an error.
/// Python prints the unexpected axioms as a set, in hash order; here they are sorted.
pub fn check_suite_audit(
    text: &str,
    module: &str,
) -> Result<Vec<(String, Vec<String>)>, AuditError> {
    if text.contains("sorryAx") {
        return fail(format!("Unexpected sorryAx in {module}"));
    }
    let mut audits: Vec<(String, String)> = finditer(text, SUITE_DEPENDS)
        .into_iter()
        .map(|report| (report.name, report.axioms.unwrap_or_default()))
        .collect();
    audits.extend(
        finditer(text, SUITE_NONE)
            .into_iter()
            .map(|report| (report.name, String::new())),
    );
    let mut result = Vec::new();
    for (name, raw) in audits {
        let mut axioms: Vec<String> = raw
            .split(',')
            .map(python_strip)
            .filter(|item| !item.is_empty())
            .map(str::to_owned)
            .collect();
        axioms.sort();
        axioms.dedup();
        let unexpected: Vec<String> = axioms
            .iter()
            .filter(|axiom| !allowed(axiom))
            .map(|axiom| python_repr_str(axiom))
            .collect();
        if !unexpected.is_empty() {
            return fail(format!(
                "Unexpected assumptions for {name}: {{{}}}",
                unexpected.join(", ")
            ));
        }
        result.push((name, axioms));
    }
    Ok(result)
}

/// axiom_audit.self_test: the nine controls of the Python module.
pub fn self_test() -> Result<fang_json::Value, AuditError> {
    let cases: [(&str, &[&str], bool); 9] = [
        (
            "'T' depends on axioms: [propext,\n Classical.choice, Quot.sound]",
            &["T"],
            true,
        ),
        ("'T' does not depend on any axioms", &["T"], true),
        ("'T' depends on axioms: []", &["T"], true),
        ("'T' depends on axioms: [Trusted.unsound]", &["T"], false),
        ("'T' depends on axioms: [sorryAx]", &["T"], false),
        ("'Other' does not depend on any axioms", &["T"], false),
        (
            "'T' depends on axioms: [propext]\n'T' depends on axioms: []",
            &["T"],
            false,
        ),
        ("'T' depends on axioms: [propext", &["T"], false),
        ("", &[], false),
    ];
    for (index, (output, required, expected)) in cases.iter().enumerate() {
        if audit_axioms(output, required).is_ok() != *expected {
            return fail(format!("Axiom audit control {index} failed"));
        }
    }
    let mut result = fang_json::Object::new();
    result.set("controls", cases.len());
    result.set("status", "passed");
    result.set("scope", "report parser only");
    Ok(fang_json::Value::Object(result))
}
