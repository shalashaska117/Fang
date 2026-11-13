// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The expanded producer's limits under the final limits record. Experimental binding; the product
//! defaults are unchanged. The shared preprocessing charges removal and clausification against the
//! Skolem core caps over the whole input, so those caps are the record's storage bound for every stage.

use super::Limits;

pub const CERTIFICATE_BYTES: usize = 5_081_233;
pub const NAMING_THRESHOLD: usize = 8;

pub fn final_limits() -> Limits {
    let mut limits = Limits::default();
    limits.input.input.max_input_bytes = 1_048_576;
    let bytes = limits.input.input.max_input_bytes;
    limits.input.input.max_clauses = 65_536;
    limits.input.input.max_term_nodes = bytes;
    limits.input.max_formula_nodes = bytes;
    limits.input.max_binders = bytes;
    limits.input.max_formula_depth = 2_984;
    limits.preprocessing.max_declarations = 65_536;
    limits.preprocessing.max_functions = 83_412;
    limits.preprocessing.max_skolem_symbols = 30_675;
    limits.preprocessing.core.max_formula_depth = 2_984;
    limits.preprocessing.core.max_term_depth = 64;
    let stored = 7_943_814;
    limits.preprocessing.core.max_stored_nodes = stored;
    limits.preprocessing.core.max_operations = 16_000_000;
    limits.preprocessing.core.max_clauses = stored;
    limits.preprocessing.core.max_literals = stored;
    limits.max_predicates = 74_339;
    limits.max_bridge_literals = 256;
    limits
}

#[cfg(test)]
mod tests {
    use super::*;
    const RECORD: &str = include_str!("../../../lean-v8/NativeLimits.lean");

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
    fn final_limits_match_the_record() {
        let limits = final_limits();
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
        let declarations = literal(RECORD, "def declarationLimit : Nat");
        assert_eq!(limits.input.input.max_clauses, declarations);
        assert_eq!(limits.preprocessing.max_declarations, declarations);
        let depth = literal(RECORD, "def formulaDepthLimit : Nat");
        assert_eq!(limits.input.max_formula_depth, depth);
        assert_eq!(limits.preprocessing.core.max_formula_depth, depth);
        assert_eq!(
            limits.max_predicates,
            literal(RECORD, "def maximumPredicates : Usize")
        );
        assert_eq!(
            limits.max_bridge_literals,
            literal(RECORD, "def maximumLiterals : Usize")
        );
        let core = RECORD
            .split_once("core := {")
            .unwrap()
            .1
            .split_once('}')
            .unwrap()
            .0;
        assert_eq!(
            limits.preprocessing.core.max_term_depth,
            literal(core, "max_term_depth")
        );
        assert_eq!(
            limits.preprocessing.core.max_stored_nodes,
            literal(core, "max_stored_nodes")
        );
        assert_eq!(
            limits.preprocessing.core.max_operations,
            literal(core, "max_operations")
        );
        let skolem = RECORD.split_once("max_declarations := ").unwrap().1;
        assert_eq!(
            limits.preprocessing.max_functions,
            literal(skolem, "max_functions")
        );
        assert_eq!(
            limits.preprocessing.max_skolem_symbols,
            literal(skolem, "max_skolem_symbols")
        );
    }
}
