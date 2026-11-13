// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Experimental binding of the approved final record; product defaults are unchanged.
use fang_tptp_signed_roles::Limits;

pub const CERTIFICATE_BYTES: usize = 5_081_233;
pub const NAMING_THRESHOLD: usize = 8;

pub fn replay_limits() -> Limits {
    let mut limits = Limits {
        max_predicates: 74_339,
        max_bridge_literals: 256,
        ..Limits::default()
    };
    limits.input.input.max_input_bytes = 1_048_576;
    limits.input.input.max_clauses = 65_536;
    limits.input.input.max_term_nodes = 1_048_576;
    limits.input.max_formula_nodes = 1_048_576;
    limits.input.max_binders = 1_048_576;
    limits.input.max_formula_depth = 2_984;
    limits.skolem.core.max_formula_depth = 2_984;
    limits.skolem.core.max_formula_nodes = 10_000;
    limits.skolem.core.max_term_depth = 64;
    limits.skolem.core.max_input_term_nodes = 100_000;
    limits.skolem.core.max_clauses = 1_000;
    limits.skolem.core.max_literals_per_clause = 256;
    limits.skolem.core.max_literals = 100_000;
    limits.skolem.core.max_stored_nodes = 7_943_814;
    limits.skolem.core.max_operations = 16_000_000;
    limits.skolem.core.max_binders = 10_000;
    limits.removal.max_formula_depth = 2_984;
    limits.removal.max_operations = 5_000_000;
    limits.removal.max_output_nodes = 1_000_000;
    limits.clausification.max_formula_depth = 2_984;
    limits.clausification.max_formula_nodes = 10_000;
    limits.clausification.max_term_depth = 64;
    limits.clausification.max_input_term_nodes = 100_000;
    limits.clausification.max_clauses = 36_045;
    limits.clausification.max_literals_per_clause = 256;
    limits.clausification.max_literals = 423_500;
    limits.clausification.max_stored_nodes = 6_657_931;
    limits.clausification.max_operations = 6_657_983;
    limits.skolem.max_declarations = 65_536;
    limits.skolem.max_functions = 83_412;
    limits.skolem.max_skolem_symbols = 30_675;
    limits
}

#[cfg(test)]
mod tests {
    use super::*;
    const RECORD: &str = include_str!("../../../../lean-v8/NativeLimits.lean");
    fn literal(text: &str, field: &str) -> usize {
        let start = text.find(&format!("{field} := ")).expect("record field") + field.len() + 4;
        text[start..]
            .chars()
            .take_while(char::is_ascii_digit)
            .collect::<String>()
            .parse()
            .expect("record literal")
    }
    #[test]
    fn final_limits_match_every_record_field() {
        let limits = replay_limits();
        assert!(RECORD.contains("def byteLimit : Nat := 1024 * 1024"));
        assert_eq!(limits.input.input.max_input_bytes, 1_048_576);
        assert_eq!(
            CERTIFICATE_BYTES,
            literal(RECORD, "def certificateLimit : Nat")
        );
        assert_eq!(
            NAMING_THRESHOLD,
            literal(RECORD, "def namingThreshold : Nat")
        );
        assert_eq!(
            limits.input.input.max_clauses,
            literal(RECORD, "def declarationLimit : Nat")
        );
        assert_eq!(
            limits.input.max_formula_depth,
            literal(RECORD, "def formulaDepthLimit : Nat")
        );
        assert_eq!(
            limits.max_predicates,
            literal(RECORD, "def maximumPredicates : Usize")
        );
        assert_eq!(
            limits.max_bridge_literals,
            literal(RECORD, "def maximumLiterals : Usize")
        );
        let block = RECORD
            .split_once("core := {")
            .unwrap()
            .1
            .split_once('}')
            .unwrap()
            .0;
        assert_eq!(block.matches(" := ").count(), 10);
        assert_eq!(
            limits.skolem.core.max_formula_depth,
            literal(block, "max_formula_depth")
        );
        assert_eq!(
            limits.skolem.core.max_formula_nodes,
            literal(block, "max_formula_nodes")
        );
        assert_eq!(
            limits.skolem.core.max_term_depth,
            literal(block, "max_term_depth")
        );
        assert_eq!(
            limits.skolem.core.max_input_term_nodes,
            literal(block, "max_input_term_nodes")
        );
        assert_eq!(
            limits.skolem.core.max_clauses,
            literal(block, "max_clauses")
        );
        assert_eq!(
            limits.skolem.core.max_literals_per_clause,
            literal(block, "max_literals_per_clause")
        );
        assert_eq!(
            limits.skolem.core.max_literals,
            literal(block, "max_literals")
        );
        assert_eq!(
            limits.skolem.core.max_stored_nodes,
            literal(block, "max_stored_nodes")
        );
        assert_eq!(
            limits.skolem.core.max_operations,
            literal(block, "max_operations")
        );
        assert_eq!(
            limits.skolem.core.max_binders,
            literal(block, "max_binders")
        );
        let block = RECORD
            .split_once("removal := {")
            .unwrap()
            .1
            .split_once('}')
            .unwrap()
            .0;
        assert_eq!(block.matches(" := ").count(), 3);
        assert_eq!(
            limits.removal.max_formula_depth,
            literal(block, "max_formula_depth")
        );
        assert_eq!(
            limits.removal.max_operations,
            literal(block, "max_operations")
        );
        assert_eq!(
            limits.removal.max_output_nodes,
            literal(block, "max_output_nodes")
        );
        let block = RECORD
            .split_once("clausification := {")
            .unwrap()
            .1
            .split_once('}')
            .unwrap()
            .0;
        assert_eq!(block.matches(" := ").count(), 9);
        assert_eq!(
            limits.clausification.max_formula_depth,
            literal(block, "max_formula_depth")
        );
        assert_eq!(
            limits.clausification.max_formula_nodes,
            literal(block, "max_formula_nodes")
        );
        assert_eq!(
            limits.clausification.max_term_depth,
            literal(block, "max_term_depth")
        );
        assert_eq!(
            limits.clausification.max_input_term_nodes,
            literal(block, "max_input_term_nodes")
        );
        assert_eq!(
            limits.clausification.max_clauses,
            literal(block, "max_clauses")
        );
        assert_eq!(
            limits.clausification.max_literals_per_clause,
            literal(block, "max_literals_per_clause")
        );
        assert_eq!(
            limits.clausification.max_literals,
            literal(block, "max_literals")
        );
        assert_eq!(
            limits.clausification.max_stored_nodes,
            literal(block, "max_stored_nodes")
        );
        assert_eq!(
            limits.clausification.max_operations,
            literal(block, "max_operations")
        );
        assert_eq!(
            limits.skolem.max_declarations,
            literal(RECORD, "max_declarations")
        );
        assert_eq!(
            limits.skolem.max_functions,
            literal(RECORD, "max_functions")
        );
        assert_eq!(
            limits.skolem.max_skolem_symbols,
            literal(RECORD, "max_skolem_symbols")
        );
    }
}
