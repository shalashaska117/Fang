// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The producer's default limits equal the values of the Lean record `NativeLimits.lean`.

use fang_tptp_signed_roles::Limits;

const RECORD: &str = include_str!("../../../lean-v8/NativeLimits.lean");

/// The literal after `field := ` at its first occurrence in `text`.
fn literal(text: &str, field: &str) -> usize {
    let pattern = format!("{field} := ");
    let start = text
        .find(&pattern)
        .unwrap_or_else(|| panic!("{field} missing from NativeLimits.lean"))
        + pattern.len();
    let digits: String = text[start..]
        .chars()
        .take_while(char::is_ascii_digit)
        .collect();
    digits
        .parse()
        .unwrap_or_else(|_| panic!("{field} is not a literal"))
}

/// The text of the brace block that opens with `opening`, up to its first closing brace.
fn block(opening: &str) -> &'static str {
    let start = RECORD
        .find(opening)
        .unwrap_or_else(|| panic!("{opening} missing from NativeLimits.lean"));
    let rest = &RECORD[start + opening.len()..];
    let end = rest
        .find('}')
        .unwrap_or_else(|| panic!("{opening} is not closed"));
    &rest[..end]
}

/// Compares every field of one block, so that a field added to the record fails the test.
fn compare(opening: &str, fields: &[(&str, usize)]) {
    let text = block(opening);
    assert_eq!(text.matches(" := ").count(), fields.len(), "{opening}");
    for &(field, value) in fields {
        assert_eq!(value, literal(text, field), "{opening} {field}");
    }
}

#[test]
fn default_limits_match_the_lean_record() {
    let limits = Limits::default();
    assert!(RECORD.contains("def byteLimit : Nat := 1024 * 1024"));
    assert_eq!(limits.input.input.max_input_bytes, 1024 * 1024);
    assert_eq!(
        limits.input.input.max_clauses,
        literal(RECORD, "def declarationLimit : Nat")
    );
    assert_eq!(
        limits.max_predicates,
        literal(RECORD, "def maximumPredicates : Usize")
    );
    assert_eq!(
        limits.max_bridge_literals,
        literal(RECORD, "def maximumLiterals : Usize")
    );
    let skolem = &limits.skolem;
    let core = &skolem.core;
    compare(
        "core := {",
        &[
            ("max_formula_depth", core.max_formula_depth),
            ("max_formula_nodes", core.max_formula_nodes),
            ("max_term_depth", core.max_term_depth),
            ("max_input_term_nodes", core.max_input_term_nodes),
            ("max_clauses", core.max_clauses),
            ("max_literals_per_clause", core.max_literals_per_clause),
            ("max_literals", core.max_literals),
            ("max_stored_nodes", core.max_stored_nodes),
            ("max_operations", core.max_operations),
            ("max_binders", core.max_binders),
        ],
    );
    // These three follow the core block and occur nowhere else in the record.
    assert_eq!(skolem.max_declarations, literal(RECORD, "max_declarations"));
    assert_eq!(skolem.max_functions, literal(RECORD, "max_functions"));
    assert_eq!(
        skolem.max_skolem_symbols,
        literal(RECORD, "max_skolem_symbols")
    );
    let removal = &limits.removal;
    compare(
        "removal := {",
        &[
            ("max_formula_depth", removal.max_formula_depth),
            ("max_operations", removal.max_operations),
            ("max_output_nodes", removal.max_output_nodes),
        ],
    );
    let clausification = &limits.clausification;
    compare(
        "clausification := {",
        &[
            ("max_formula_depth", clausification.max_formula_depth),
            ("max_formula_nodes", clausification.max_formula_nodes),
            ("max_term_depth", clausification.max_term_depth),
            ("max_input_term_nodes", clausification.max_input_term_nodes),
            ("max_clauses", clausification.max_clauses),
            (
                "max_literals_per_clause",
                clausification.max_literals_per_clause,
            ),
            ("max_literals", clausification.max_literals),
            ("max_stored_nodes", clausification.max_stored_nodes),
            ("max_operations", clausification.max_operations),
        ],
    );
    // No counterpart in the record. The parser's whole-file counts of term nodes, formula nodes and binders take the input byte bound; its term depth, literals per clause and the other `fang::Limits` counts, its formula depth and every search limit keep their earlier values.
    let bytes = limits.input.input.max_input_bytes;
    assert_eq!(limits.input.input.max_term_nodes, bytes);
    assert_eq!(limits.input.max_formula_nodes, bytes);
    assert_eq!(limits.input.max_binders, bytes);
}
