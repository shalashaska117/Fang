// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
#![forbid(unsafe_code)]

//! Version-8 candidate producer for a sealed bundle. The coverage candidate
//! captures and expands the bundle; the expansion is written as one flat TPTP
//! text from the original formula bytes, and the accepted version-8 producer
//! runs on that text unchanged. No preprocessing, search or serialization code
//! lives here. Only the independent bundle checker can accept the result.

use fang_tptp_coverage_candidate::{Body, Expanded, Source, capture};
use fang_tptp_expanded_integration::Limits;
use fang_tptp_expanded_v8::{Produced, produce};
use std::collections::BTreeSet;
use std::path::Path;

#[derive(Debug)]
pub enum Error {
    Capture(fang_tptp_coverage_candidate::Error),
    Render(&'static str),
    Producer(fang_tptp_expanded_v8::Error),
}

/// A fresh lower word per distinct object, never equal to an ordinary function
/// name of the expansion. Objects keep their inventory order.
pub fn object_names(expanded: &Expanded) -> Vec<String> {
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

/// Copy formula bytes, replacing each distinct object by its fresh name.
/// Comments and quoted atoms are copied unchanged.
fn body_text(bytes: &[u8], contents: &[String], names: &[String]) -> Result<String, Error> {
    let mut output = Vec::with_capacity(bytes.len());
    let mut position = 0;
    while position < bytes.len() {
        let byte = bytes[position];
        if byte == b'%' {
            while position < bytes.len() && bytes[position] != b'\n' {
                output.push(bytes[position]);
                position += 1;
            }
        } else if byte == b'/' && bytes.get(position + 1) == Some(&b'*') {
            let end = bytes[position + 2..]
                .windows(2)
                .position(|pair| pair == b"*/")
                .ok_or(Error::Render("unterminated block comment"))?;
            output.extend_from_slice(&bytes[position..position + 2 + end + 2]);
            position += 2 + end + 2;
        } else if byte == b'\'' || byte == b'"' {
            let mut cursor = position + 1;
            let mut content = Vec::new();
            loop {
                let next = *bytes
                    .get(cursor)
                    .ok_or(Error::Render("unterminated quoted token"))?;
                if next == b'\\' {
                    content.push(
                        *bytes
                            .get(cursor + 1)
                            .ok_or(Error::Render("unfinished escape"))?,
                    );
                    cursor += 2;
                } else if next == byte {
                    cursor += 1;
                    break;
                } else {
                    content.push(next);
                    cursor += 1;
                }
            }
            if byte == b'\'' {
                output.extend_from_slice(&bytes[position..cursor]);
            } else {
                let content =
                    String::from_utf8(content).map_err(|_| Error::Render("non-ASCII object"))?;
                let index = contents
                    .iter()
                    .position(|value| *value == content)
                    .ok_or(Error::Render("object outside the inventory"))?;
                output.extend_from_slice(names[index].as_bytes());
            }
            position = cursor;
        } else {
            output.push(byte);
            position += 1;
        }
    }
    String::from_utf8(output).map_err(|_| Error::Render("non-ASCII formula"))
}

/// One flat text whose accepted version-8 preparation is the bundle's numeric
/// input: expanded records in order, objects renamed, generated clauses last.
pub fn render(expanded: &Expanded) -> Result<String, Error> {
    let names = object_names(expanded);
    let contents: Vec<String> = expanded
        .distinct_objects
        .iter()
        .map(|(_, value)| value.clone())
        .collect();
    let mut text = String::new();
    for (index, (declaration, source)) in expanded
        .parsed
        .declarations
        .iter()
        .zip(&expanded.sources)
        .enumerate()
    {
        match source {
            Source::File { file, .. } => {
                let bytes = &expanded.bundle.files[*file].bytes;
                let body = bytes
                    .get(declaration.body_bytes.clone())
                    .ok_or(Error::Render("body outside its file"))?;
                let kind = match declaration.body {
                    Body::Cnf(_) => "cnf",
                    Body::Fof(_) => "fof",
                };
                text.push_str(&format!(
                    "{kind}(fang_bundle_{index},axiom,{}).\n",
                    body_text(body, &contents, &names)?
                ));
            }
            Source::DistinctPair { left, right } => {
                text.push_str(&format!(
                    "cnf(fang_distinct_{left}_{right},axiom,{} != {}).\n",
                    names[*left], names[*right]
                ));
            }
        }
    }
    Ok(text)
}

pub struct BundleRun {
    pub expanded: Expanded,
    pub flat: String,
    pub produced: Produced,
}

/// The version-8 producer's limits for the flat text of an expansion. The text is rendered
/// from a bundle the coverage candidate already holds to the checker's limits, and renaming can
/// lengthen it, so its byte cap is its own length. The per-file declaration, term node, formula
/// node and binder counts are multiplied by the number of bundle files, and the declaration
/// count also admits the generated disequalities.
pub fn flat_limits(limits: &Limits, expanded: &Expanded, flat: &str) -> Limits {
    let mut widened = limits.clone();
    let files = expanded.bundle.files.len();
    let objects = expanded.distinct_objects.len();
    let pairs = objects * objects.saturating_sub(1) / 2;
    let input = &mut widened.input;
    input.input.max_input_bytes = input.input.max_input_bytes.max(flat.len());
    input.input.max_clauses = input
        .input
        .max_clauses
        .saturating_mul(files)
        .saturating_add(pairs);
    input.input.max_term_nodes = input.input.max_term_nodes.saturating_mul(files);
    input.max_formula_nodes = input.max_formula_nodes.saturating_mul(files);
    input.max_binders = input.max_binders.saturating_mul(files);
    widened
}

/// Capture, expand, render and run the accepted version-8 producer on the flat text, with
/// `limits` widened by `flat_limits`.
pub fn produce_bundle(
    top: &Path,
    tptp_root: Option<&Path>,
    limits: &Limits,
) -> Result<BundleRun, Error> {
    let coverage_limits = fang_tptp_coverage_candidate::Limits::default();
    let expanded = capture(top, tptp_root, &coverage_limits).map_err(Error::Capture)?;
    let flat = render(&expanded)?;
    let produced = produce(flat.as_bytes(), &flat_limits(limits, &expanded, &flat))
        .map_err(Error::Producer)?;
    Ok(BundleRun {
        expanded,
        flat,
        produced,
    })
}
