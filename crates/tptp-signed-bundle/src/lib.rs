// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Shared Fang components retain LICENSES/Vampire.txt and Vampire.ORIGIN.
#![forbid(unsafe_code)]

//! Signed role tasks over a sealed include bundle. The coverage candidate frames and expands the bundle with every record role read as `axiom`; the original roles are restored by statement position. The expansion is written as one flat TPTP text, and the accepted signed producer of roles/signed runs on it unchanged.
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
    /// A cited item that is not an expanded premise (goal task) or positive input (inputs task); the checker refuses it too.
    Citation((usize, usize)),
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

/// The coverage expansion of the bundle with roles read as `axiom`, and each file's original roles, reading formulas to the coverage candidate's default height.
pub fn expand(bundle: &Bundle) -> Result<(Expanded, Vec<BTreeMap<usize, String>>), Error> {
    expand_to_depth(
        bundle,
        fang_tptp_coverage_candidate::Limits::default().max_formula_depth,
    )
}

/// `expand`, reading formulas to height `depth`. The flat text is written from this expansion, so a task's formula height must be read here as well as when the flat text is parsed.
pub fn expand_to_depth(
    bundle: &Bundle,
    depth: usize,
) -> Result<(Expanded, Vec<BTreeMap<usize, String>>), Error> {
    let mut neutral = bundle.clone();
    let mut roles = Vec::new();
    for (index, file) in neutral.files.iter_mut().enumerate() {
        let (bytes, found) = neutral_roles(&file.bytes, index)?;
        file.bytes = bytes;
        roles.push(found);
    }
    let limits = fang_tptp_coverage_candidate::Limits {
        max_bundle_bytes: BUNDLE_BYTES,
        max_formula_depth: depth,
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
    /// Bundle item of each record of the text, in order; the generated disequalities have none.
    pub items: Vec<(usize, usize)>,
    /// The original role word of each record, beside `items`.
    pub roles: Vec<String>,
    /// Generated disequalities.
    pub distinct_clauses: usize,
}

/// Write the expansion as one flat text whose signed tasks are the Lean bundle tasks.
pub fn flatten(bundle: &Bundle, limits: &Limits) -> Result<Flat, Error> {
    write_flat(bundle, limits, |_| true, true)
}

/// The flat text of the kept part of the expansion: the records whose items are cited, and `extra`, in expansion order, with the disequalities over their own objects only. Its tasks are the Lean cited tasks.
pub fn flatten_kept(
    bundle: &Bundle,
    limits: &Limits,
    cited: &[(usize, usize)],
    extra: Option<(usize, usize)>,
) -> Result<Flat, Error> {
    let cited: BTreeSet<_> = cited.iter().copied().collect();
    write_flat(
        bundle,
        limits,
        |item| cited.contains(&item) || extra == Some(item),
        false,
    )
}

/// The records `keep` accepts, in expansion order, with the disequalities over the distinct objects they use. Record names keep their position in the whole expansion. Mixed goal modes are checked over the whole expansion, as the Lean read checks them. With `whole`, every distinct object must occur in the text.
fn write_flat(
    bundle: &Bundle,
    limits: &Limits,
    keep: impl Fn((usize, usize)) -> bool,
    whole: bool,
) -> Result<Flat, Error> {
    let (expanded, roles) = expand_to_depth(bundle, limits.input.max_formula_depth)?;
    let names = object_names(&expanded);
    let contents: Vec<String> = expanded
        .distinct_objects
        .iter()
        .map(|(_, value)| value.clone())
        .collect();
    let mut text = String::new();
    let mut goals = Vec::new();
    let mut items = Vec::new();
    let mut kept_roles = Vec::new();
    let mut any_goal = false;
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
        any_goal |= role == "conjecture";
        negated |= role == "negated_conjecture";
        let item = (*file, *statement);
        if !keep(item) {
            continue;
        }
        if role == "conjecture" {
            goals.push(item);
        }
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
        items.push(item);
        kept_roles.push(role.clone());
    }
    if any_goal && negated {
        return Err(Error::Modes);
    }
    // Lean orders the objects as the complete function table does; the role parser builds that table from the same records.
    let parsed = fang_tptp_full_frontend_candidate::parse(
        text.as_bytes(),
        &flat_limits(limits, bundle.files.len(), text.len(), 0).input,
    )
    .map_err(Error::Flat)?;
    let mut ordered: Vec<(usize, &String)> = Vec::new();
    for name in &names {
        match parsed
            .functions
            .iter()
            .position(|symbol| symbol.name == *name && symbol.arity == 0)
        {
            Some(position) => ordered.push((position, name)),
            None if whole => return Err(Error::Render("object missing from the function table")),
            None => {}
        }
    }
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
        items,
        roles: kept_roles,
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

/// Canonical premise references in expansion order.
pub type Citations = Vec<(usize, usize)>;
/// Cited items, the kept source text, and its prepared task.
pub type CitedPrepared = (Citations, Flat, Prepared);
/// Cited items, the kept source text, and its produced candidate.
pub type CitedProduced = (Citations, Flat, Produced);
type KeptTask = (Citations, Flat, Selection);

/// Role words of the premises of a goal task.
const PREMISE_ROLES: &[&str] = &[
    "axiom",
    "hypothesis",
    "definition",
    "lemma",
    "theorem",
    "corollary",
];
/// Role words of the positive inputs of the satisfiability task.
const INPUT_ROLES: &[&str] = &[
    "axiom",
    "hypothesis",
    "definition",
    "lemma",
    "theorem",
    "corollary",
    "negated_conjecture",
];

/// The premise line a cited certificate begins with, in canonical form: `(premises (item F S) ...)`.
pub fn premise_line(cited: &[(usize, usize)]) -> String {
    let mut line = String::from("(premises");
    for (file, statement) in cited {
        line.push_str(&format!(" (item {file} {statement})"));
    }
    line.push(')');
    line
}

/// The cited items in expansion order without repeats, the kept flat text and the selection within it. The checks and their order follow the Lean cited entries: the whole expansion is read first, then every citation must be an expanded premise (goal task) or positive input (inputs task), then the goal is chosen among the conjectures of the whole expansion. The kept text holds no other conjecture, so the goal is its first.
fn kept_task(
    bundle: &Bundle,
    selection: Selection,
    cited: &[(usize, usize)],
    limits: &Limits,
) -> Result<KeptTask, Error> {
    let whole = flatten(bundle, limits)?;
    let allowed = match selection {
        Selection::Goal(_) => PREMISE_ROLES,
        Selection::Inputs => INPUT_ROLES,
    };
    let mut roles = BTreeMap::new();
    for (item, role) in whole.items.iter().zip(&whole.roles) {
        roles.entry(*item).or_insert(role.as_str());
    }
    for item in cited {
        if !roles.get(item).is_some_and(|role| allowed.contains(role)) {
            return Err(Error::Citation(*item));
        }
    }
    let extra = match selection {
        Selection::Goal(index) => Some(
            *whole
                .goals
                .get(index)
                .ok_or(Error::Signed(fang_tptp_signed_roles::Error::NoGoal))?,
        ),
        Selection::Inputs if whole.goals.is_empty() => None,
        Selection::Inputs => {
            return Err(Error::Signed(fang_tptp_signed_roles::Error::GoalsPresent));
        }
    };
    let kept = flatten_kept(bundle, limits, cited, extra)?;
    let mut citations = Vec::new();
    let mut seen = BTreeSet::new();
    for item in &kept.items {
        if Some(*item) != extra && seen.insert(*item) {
            citations.push(*item);
        }
    }
    let selection = match selection {
        Selection::Goal(_) => Selection::Goal(0),
        Selection::Inputs => Selection::Inputs,
    };
    Ok((citations, kept, selection))
}

/// The cited task: the cited items and, for a goal task, the selected goal of the whole expansion. Returns the cited items in expansion order, the kept flat text and the prepared task.
pub fn prepare_cited_task(
    bundle: &Bundle,
    selection: Selection,
    cited: &[(usize, usize)],
    limits: &Limits,
) -> Result<CitedPrepared, Error> {
    let (citations, kept, selection) = kept_task(bundle, selection, cited, limits)?;
    let limits = flat_limits(
        limits,
        bundle.files.len(),
        kept.text.len(),
        kept.distinct_clauses,
    );
    let prepared = fang_tptp_signed_roles::prepare_task(kept.text.as_bytes(), selection, &limits)
        .map_err(Error::Signed)?;
    Ok((citations, kept, prepared))
}

/// Prepare the cited task, then run the accepted prepared ordered search and serializer on it. A candidate is printed after `premise_line` of the returned items.
pub fn produce_cited_task(
    bundle: &Bundle,
    selection: Selection,
    cited: &[(usize, usize)],
    limits: &Limits,
) -> Result<CitedProduced, Error> {
    let (citations, kept, selection) = kept_task(bundle, selection, cited, limits)?;
    let limits = flat_limits(
        limits,
        bundle.files.len(),
        kept.text.len(),
        kept.distinct_clauses,
    );
    let produced = fang_tptp_signed_roles::produce_task(kept.text.as_bytes(), selection, &limits)
        .map_err(Error::Signed)?;
    Ok((citations, kept, produced))
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
        Error::Citation(_) => "citation",
        Error::Flat(_) | Error::Render(_) => "internal",
        Error::Signed(fang_tptp_signed_roles::Error::Encoding(
            fang_fof_equality_bridge::Error::SymbolId,
        )) => "width",
        Error::Signed(error) => fang_tptp_signed_roles::error_kind(error),
    }
}

mod named_prepare;
pub use named_prepare::{prepare_bundle_task_named, prepare_cited_task_named};

mod cited_inputs;
pub use cited_inputs::{InputOriginError, cited_inputs};
