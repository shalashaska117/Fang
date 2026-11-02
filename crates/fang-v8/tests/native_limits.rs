// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The producer's native limits equal the values of the Lean record `NativeLimits.lean`.

use fang_tptp_expanded_v8::native_limits;

const RECORD: &str = include_str!("../../../lean-v8/NativeLimits.lean");

/// The literal after `field := ` at its first occurrence in the Lean record.
fn record(field: &str) -> usize {
    let pattern = format!("{field} := ");
    let start = RECORD
        .find(&pattern)
        .unwrap_or_else(|| panic!("{field} missing from NativeLimits.lean"))
        + pattern.len();
    let digits: String = RECORD[start..]
        .chars()
        .take_while(char::is_ascii_digit)
        .collect();
    digits
        .parse()
        .unwrap_or_else(|_| panic!("{field} is not a literal"))
}

#[test]
fn native_limits_match_the_lean_record() {
    let limits = native_limits();
    let skolem = &limits.preprocessing;
    assert!(RECORD.contains("def byteLimit : Nat := 1024 * 1024"));
    assert_eq!(limits.input.input.max_input_bytes, 1024 * 1024);
    assert_eq!(
        limits.input.input.max_clauses,
        record("def declarationLimit : Nat")
    );
    assert_eq!(skolem.max_declarations, record("max_declarations"));
    assert_eq!(skolem.max_functions, record("max_functions"));
    assert_eq!(skolem.max_skolem_symbols, record("max_skolem_symbols"));
    assert_eq!(
        limits.max_predicates,
        record("def maximumPredicates : Usize")
    );
    assert_eq!(
        limits.max_bridge_literals,
        record("def maximumLiterals : Usize")
    );
    // The Skolem core block comes first in the record, so each field's first occurrence is its own.
    // The clause and literal counts are the pipeline's whole-problem output caps, which the
    // checker does not have; they take the stored-node bound.
    assert_eq!(skolem.core.max_clauses, record("max_stored_nodes"));
    assert_eq!(skolem.core.max_literals, record("max_stored_nodes"));
    let core = [
        ("max_formula_depth", skolem.core.max_formula_depth),
        ("max_formula_nodes", skolem.core.max_formula_nodes),
        ("max_term_depth", skolem.core.max_term_depth),
        ("max_input_term_nodes", skolem.core.max_input_term_nodes),
        (
            "max_literals_per_clause",
            skolem.core.max_literals_per_clause,
        ),
        ("max_stored_nodes", skolem.core.max_stored_nodes),
        ("max_operations", skolem.core.max_operations),
        ("max_binders", skolem.core.max_binders),
    ];
    for (field, value) in core {
        assert_eq!(value, record(field), "{field}");
    }
    // The record's removal and clausification blocks have no producer counterpart here: the
    // producer's pipeline spends one budget on every declaration, so they are not compared.
}
