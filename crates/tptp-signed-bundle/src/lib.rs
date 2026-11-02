// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Shared Fang components retain LICENSES/Vampire.txt and Vampire.ORIGIN.
#![forbid(unsafe_code)]

//! Signed role tasks over a sealed include bundle. The coverage candidate frames and expands the bundle with every record role read as `axiom`; the original roles are restored by statement position. The expansion is written as one flat TPTP text, and the accepted signed producer of crates/tptp-signed-roles runs on it unchanged.
//!
//! The flat text lists the selected records in expansion order with their roles and with distinct objects renamed to fresh constants, then one disequality per pair of objects in the order of the Lean `distinctItems`: objects by their position in the function table, each pair once with the earlier object on the left. Output is a candidate certificate or Unknown, never a checked result.

use fang_tptp_coverage_candidate::{Body, Bundle, BundleFile, Expanded, Key, Reason, Root, Source};
use fang_tptp_signed_roles::{Limits, Prepared, Produced, Selection};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug)]
pub enum Error {
    /// A `fof` or `cnf` record whose role word could not be read before framing.
    Role {
        file: usize,
        offset: usize,
    },
    Expansion(fang_tptp_coverage_candidate::Error),
    Render(&'static str),
    /// The flat text was rejected by the role parser.
    Flat(fang::Error),
    /// A selected conjecture together with a selected negated conjecture, refused before parsing as the Lean read refuses it.
    Modes,
    Signed(fang_tptp_signed_roles::Error),
}

/// One bundle file as the checker receives it: root, slash-separated path, bytes.
pub fn sealed(files: Vec<(Root, String, Vec<u8>)>) -> Bundle {
    Bundle {
        files: files
            .into_iter()
            .map(|(root, path, bytes)| BundleFile {
                key: Key {
                    root,
                    path: path.split('/').map(str::to_owned).collect(),
                },
                bytes,
            })
            .collect(),
    }
}

fn copy_quoted(bytes: &[u8], start: usize, output: &mut Vec<u8>) -> Option<usize> {
    let quote = bytes[start];
    let mut position = start + 1;
    loop {
        match *bytes.get(position)? {
            b'\\' => position += 2,
            byte if byte == quote => {
                output.extend_from_slice(&bytes[start..=position]);
                return Some(position + 1);
            }
            _ => position += 1,
        }
    }
}

/// Copy whitespace and comments; return the next position.
fn copy_layout(bytes: &[u8], mut position: usize, output: &mut Vec<u8>) -> Option<usize> {
    loop {
        match bytes.get(position) {
            Some(b' ' | b'\t' | b'\r' | b'\n') => {
                output.push(bytes[position]);
                position += 1;
            }
            Some(b'%') => {
                while position < bytes.len() && bytes[position] != b'\n' {
                    output.push(bytes[position]);
                    position += 1;
                }
            }
            Some(b'/') if bytes.get(position + 1) == Some(&b'*') => {
                let end = bytes[position + 2..]
                    .windows(2)
                    .position(|pair| pair == b"*/")?;
                output.extend_from_slice(&bytes[position..position + 2 + end + 2]);
                position += 2 + end + 2;
            }
            _ => return Some(position),
        }
    }
}

fn word_end(bytes: &[u8], mut position: usize) -> usize {
    while bytes
        .get(position)
        .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
    {
        position += 1;
    }
    position
}

/// The file with every `fof` and `cnf` role word replaced by `axiom`, and the original role words by statement index, include directives counted.
pub fn neutral_roles(
    bytes: &[u8],
    file: usize,
) -> Result<(Vec<u8>, BTreeMap<usize, String>), Error> {
    let fail = |offset| Error::Role { file, offset };
    let mut output = Vec::with_capacity(bytes.len());
    let mut roles = BTreeMap::new();
    let mut position = 0;
    let mut depth = 0usize;
    let mut statement = 0;
    let mut at_start = true;
    while position < bytes.len() {
        let next = copy_layout(bytes, position, &mut output).ok_or(fail(position))?;
        if next != position {
            position = next;
            continue;
        }
        match bytes[position] {
            b'\'' | b'"' => {
                position = copy_quoted(bytes, position, &mut output).ok_or(fail(position))?;
                at_start = false;
            }
            b'(' => {
                depth += 1;
                output.push(b'(');
                position += 1;
            }
            b')' => {
                depth = depth.checked_sub(1).ok_or(fail(position))?;
                output.push(b')');
                position += 1;
            }
            b'.' if depth == 0 => {
                statement += 1;
                at_start = true;
                output.push(b'.');
                position += 1;
            }
            b'a'..=b'z' if depth == 0 && at_start => {
                let end = word_end(bytes, position);
                let keyword = &bytes[position..end];
                output.extend_from_slice(keyword);
                position = end;
                at_start = false;
                if keyword != b"fof" && keyword != b"cnf" {
                    continue;
                }
                position = copy_layout(bytes, position, &mut output).ok_or(fail(position))?;
                if bytes.get(position) != Some(&b'(') {
                    continue;
                }
                depth += 1;
                output.push(b'(');
                position = copy_layout(bytes, position + 1, &mut output).ok_or(fail(position))?;
                position = match bytes.get(position) {
                    Some(b'\'') => {
                        copy_quoted(bytes, position, &mut output).ok_or(fail(position))?
                    }
                    Some(byte) if byte.is_ascii_alphanumeric() => {
                        let end = word_end(bytes, position);
                        output.extend_from_slice(&bytes[position..end]);
                        end
                    }
                    _ => return Err(fail(position)),
                };
                position = copy_layout(bytes, position, &mut output).ok_or(fail(position))?;
                if bytes.get(position) != Some(&b',') {
                    return Err(fail(position));
                }
                output.push(b',');
                position = copy_layout(bytes, position + 1, &mut output).ok_or(fail(position))?;
                let end = word_end(bytes, position);
                let role =
                    std::str::from_utf8(&bytes[position..end]).map_err(|_| fail(position))?;
                if role.is_empty() || !role.as_bytes()[0].is_ascii_lowercase() {
                    return Err(fail(position));
                }
                roles.insert(statement, role.to_owned());
                output.extend_from_slice(b"axiom");
                position = end;
            }
            byte => {
                at_start = false;
                output.push(byte);
                position += 1;
            }
        }
    }
    Ok((output, roles))
}

/// The coverage expansion of the bundle with roles read as `axiom`, and each file's original roles.
pub fn expand(bundle: &Bundle) -> Result<(Expanded, Vec<BTreeMap<usize, String>>), Error> {
    let mut neutral = bundle.clone();
    let mut roles = Vec::new();
    for (index, file) in neutral.files.iter_mut().enumerate() {
        let (bytes, found) = neutral_roles(&file.bytes, index)?;
        file.bytes = bytes;
        roles.push(found);
    }
    let limits = fang_tptp_coverage_candidate::Limits {
        max_bundle_bytes: BUNDLE_BYTES,
        ..Default::default()
    };
    let expanded =
        fang_tptp_coverage_candidate::expand(&neutral, &limits).map_err(Error::Expansion)?;
    Ok((expanded, roles))
}

/// Bytes of all files of one bundle, as the bundle checker caps them (`bundleLimit`).
pub const BUNDLE_BYTES: usize = 4 << 20;

/// Parser limits for the flat text of a bundle with `files` files. The expansion already holds the bundle to `BUNDLE_BYTES`, and the flat text renames records and objects, which can lengthen it, so the text's own length is its byte cap. The declaration, term node, formula node and binder counts of one file are multiplied by the number of files, and the declaration count also admits the `generated` disequalities.
fn flat_limits(limits: &Limits, files: usize, bytes: usize, generated: usize) -> Limits {
    let mut flat = limits.clone();
    let scale = |value: usize| value.saturating_mul(files);
    flat.input.input.max_input_bytes = bytes;
    flat.input.input.max_clauses = scale(limits.input.input.max_clauses).saturating_add(generated);
    flat.input.input.max_term_nodes = scale(limits.input.input.max_term_nodes);
    flat.input.max_formula_nodes = scale(limits.input.max_formula_nodes);
    flat.input.max_binders = scale(limits.input.max_binders);
    flat
}

/// A fresh lower word per distinct object, never equal to an ordinary function name of the expansion.
fn object_names(expanded: &Expanded) -> Vec<String> {
    let objects: BTreeSet<u32> = expanded
        .distinct_objects
        .iter()
        .map(|(id, _)| *id)
        .collect();
    let ordinary: BTreeSet<&str> = expanded
        .parsed
        .functions
        .iter()
        .enumerate()
        .filter(|(index, _)| !objects.contains(&(*index as u32)))
        .map(|(_, symbol)| symbol.name.as_str())
        .collect();
    let mut prefix = String::from("fang_object_");
    while (0..expanded.distinct_objects.len())
        .any(|index| ordinary.contains(format!("{prefix}{index}").as_str()))
    {
        prefix.insert(0, 'x');
    }
    (0..expanded.distinct_objects.len())
        .map(|index| format!("{prefix}{index}"))
        .collect()
}

/// Formula bytes with each distinct object replaced by its fresh name; comments and quoted atoms are copied.
fn body_text(bytes: &[u8], contents: &[String], names: &[String]) -> Result<String, Error> {
    let mut output = Vec::with_capacity(bytes.len());
    let mut position = 0;
    while position < bytes.len() {
        let next = copy_layout(bytes, position, &mut output)
            .ok_or(Error::Render("unterminated comment"))?;
        if next != position {
            position = next;
            continue;
        }
        match bytes[position] {
            b'\'' => {
                position = copy_quoted(bytes, position, &mut output)
                    .ok_or(Error::Render("unterminated quoted atom"))?;
            }
            b'"' => {
                let mut quoted = Vec::new();
                let end = copy_quoted(bytes, position, &mut quoted)
                    .ok_or(Error::Render("unterminated object"))?;
                let mut content = Vec::new();
                let mut inner = 1;
                while inner + 1 < quoted.len() {
                    if quoted[inner] == b'\\' {
                        inner += 1;
                    }
                    content.push(quoted[inner]);
                    inner += 1;
                }
                let content =
                    String::from_utf8(content).map_err(|_| Error::Render("non-ASCII object"))?;
                let index = contents
                    .iter()
                    .position(|value| *value == content)
                    .ok_or(Error::Render("object outside the inventory"))?;
                output.extend_from_slice(names[index].as_bytes());
                position = end;
            }
            byte => {
                output.push(byte);
                position += 1;
            }
        }
    }
    String::from_utf8(output).map_err(|_| Error::Render("non-ASCII formula"))
}

#[derive(Debug)]
pub struct Flat {
    /// Selected records in expansion order, then the generated disequalities.
    pub text: String,
    /// Bundle item (file, statement) of each selected conjecture, in expansion order.
    pub goals: Vec<(usize, usize)>,
    /// Generated disequalities.
    pub distinct_clauses: usize,
}

/// Write the expansion as one flat text whose signed tasks are the Lean bundle tasks.
pub fn flatten(bundle: &Bundle, limits: &Limits) -> Result<Flat, Error> {
    let (expanded, roles) = expand(bundle)?;
    let names = object_names(&expanded);
    let contents: Vec<String> = expanded
        .distinct_objects
        .iter()
        .map(|(_, value)| value.clone())
        .collect();
    let mut text = String::new();
    let mut goals = Vec::new();
    let mut negated = false;
    for (index, (declaration, source)) in expanded
        .parsed
        .declarations
        .iter()
        .zip(&expanded.sources)
        .enumerate()
    {
        let Source::File {
            file, statement, ..
        } = source
        else {
            continue;
        };
        let role = roles
            .get(*file)
            .and_then(|found| found.get(statement))
            .ok_or(Error::Render("record without a role"))?;
        if role == "conjecture" {
            goals.push((*file, *statement));
        }
        negated |= role == "negated_conjecture";
        let bytes = &expanded.bundle.files[*file].bytes;
        let body = bytes
            .get(declaration.body_bytes.clone())
            .ok_or(Error::Render("body outside its file"))?;
        let kind = match declaration.body {
            Body::Cnf(_) => "cnf",
            Body::Fof(_) => "fof",
        };
        text.push_str(&format!(
            "{kind}(fang_bundle_{index},{role},{}).\n",
            body_text(body, &contents, &names)?
        ));
    }
    if !goals.is_empty() && negated {
        return Err(Error::Modes);
    }
    // Lean orders the objects as the complete function table does; the role parser builds that table from the same records.
    let parsed = fang_tptp_full_frontend_candidate::parse(
        text.as_bytes(),
        &flat_limits(limits, bundle.files.len(), text.len(), 0).input,
    )
    .map_err(Error::Flat)?;
    let mut ordered: Vec<(usize, &String)> = names
        .iter()
        .map(|name| {
            parsed
                .functions
                .iter()
                .position(|symbol| symbol.name == *name && symbol.arity == 0)
                .map(|position| (position, name))
                .ok_or(Error::Render("object missing from the function table"))
        })
        .collect::<Result<_, _>>()?;
    ordered.sort();
    let mut distinct_clauses = 0;
    for (left, (_, first)) in ordered.iter().enumerate() {
        for (right, (_, second)) in ordered.iter().enumerate().skip(left + 1) {
            text.push_str(&format!(
                "cnf(fang_distinct_{left}_{right},axiom,{first} != {second}).\n"
            ));
            distinct_clauses += 1;
        }
    }
    Ok(Flat {
        text,
        goals,
        distinct_clauses,
    })
}

/// The bundle item of the selected goal, if any, and the prepared task.
pub fn prepare_bundle_task(
    bundle: &Bundle,
    selection: Selection,
    limits: &Limits,
) -> Result<(Flat, Prepared), Error> {
    let flat = flatten(bundle, limits)?;
    let limits = flat_limits(
        limits,
        bundle.files.len(),
        flat.text.len(),
        flat.distinct_clauses,
    );
    let prepared = fang_tptp_signed_roles::prepare_task(flat.text.as_bytes(), selection, &limits)
        .map_err(Error::Signed)?;
    Ok((flat, prepared))
}

/// Prepare one task, then run the accepted prepared ordered search and serializer on it.
pub fn produce_bundle_task(
    bundle: &Bundle,
    selection: Selection,
    limits: &Limits,
) -> Result<(Flat, Produced), Error> {
    let flat = flatten(bundle, limits)?;
    let limits = flat_limits(
        limits,
        bundle.files.len(),
        flat.text.len(),
        flat.distinct_clauses,
    );
    let produced = fang_tptp_signed_roles::produce_task(flat.text.as_bytes(), selection, &limits)
        .map_err(Error::Signed)?;
    Ok((flat, produced))
}

/// The rejection kind printed by the agreement campaign; the Lean probe maps `BundleError` to the same names.
pub fn error_kind(error: &Error) -> &'static str {
    match error {
        Error::Expansion(error) => match error.reason {
            Reason::Missing => "missing",
            Reason::Cycle => "cycle",
            Reason::SelectionMissing => "selection-missing",
            Reason::SelectionAmbiguous => "selection-ambiguous",
            Reason::BundleShape => "shape",
            Reason::Limit => "resource",
            _ => "frame",
        },
        Error::Role { .. } => "frame",
        Error::Modes => "modes",
        Error::Flat(_) | Error::Render(_) => "internal",
        Error::Signed(fang_tptp_signed_roles::Error::Encoding(
            fang_fof_equality_bridge::Error::SymbolId,
        )) => "width",
        Error::Signed(error) => fang_tptp_signed_roles::error_kind(error),
    }
}
