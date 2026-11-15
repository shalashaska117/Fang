// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use super::*;
use fang_equality_inference_core::{Atom as InputAtom, Literal};

fn input(positive: bool, symbol: u32) -> Literal {
    Literal {
        positive,
        atom: InputAtom::Predicate(symbol, vec![]),
    }
}

#[test]
fn stored_limit_counts_inputs_and_never_reports_saturation_after_refusal() {
    let clauses = vec![vec![input(true, 0)], vec![input(false, 0)]];
    for limit in 0..=2 {
        let mut options = Options::preset("step1").unwrap();
        options.max_stored = Some(limit);
        let mut search = Search::new(&clauses, &[], &[0], &options, Limits::default()).unwrap();
        assert_eq!(search.run(), Stop::StoredLimit);
        assert_eq!(search.clauses.len() as u64, limit);
        assert_eq!(search.stats.clauses_stored, limit);
        // Resource refusal remains sticky even when run is called again.
        assert_eq!(search.run(), Stop::StoredLimit);
    }
}

#[test]
fn a_proof_at_the_exact_storage_boundary_remains_replayable() {
    let clauses = vec![vec![input(true, 0)], vec![input(false, 0)]];
    let mut options = Options::preset("step1").unwrap();
    options.max_stored = Some(3);
    let mut search = Search::new(&clauses, &[], &[0], &options, Limits::default()).unwrap();
    let Stop::Proof(id) = search.run() else {
        panic!("expected boundary proof")
    };
    assert_eq!(search.clauses.len(), 3);
    assert!(search.certificate(id, 1 << 20).is_ok());
}

#[test]
fn simplification_records_share_the_storage_limit() {
    let clauses = vec![vec![input(true, 0), input(true, 0)]];
    let mut options = Options::preset("step5").unwrap();
    options.max_stored = Some(1);
    let mut search = Search::new(&clauses, &[], &[0], &options, Limits::default()).unwrap();
    assert_eq!(search.run(), Stop::StoredLimit);
    assert_eq!(search.clauses.len(), 1);
    assert!(search.found.is_none());
}

#[test]
fn generated_limit_counts_dropped_conclusions_and_stops_within_one_given_clause() {
    let mut options = Options::preset("step1").unwrap();
    options.max_generated = Some(1);
    options.max_literals = 0;
    let mut search = Search::new(&[], &[], &[0], &options, Limits::default()).unwrap();
    let literal = Lit {
        positive: true,
        atom: Atom::Pred(search.bank.app(0, &[])),
    };
    let rule = || Rule::Input {
        index: 0,
        original: vec![],
    };
    assert!(!search.derived(vec![literal], rule()));
    assert_eq!(search.stats.generated, 1);
    assert_eq!(search.stats.dropped_literals, 1);
    assert!(!search.derived(vec![], rule()));
    assert_eq!(search.stats.generated, 1);
    assert!(search.tick());
    assert_eq!(search.run(), Stop::GeneratedLimit);
    assert!(search.clauses.is_empty());
}

#[test]
fn generated_boundary_allows_the_last_conclusion_but_zero_refuses_generation() {
    let clauses = vec![vec![input(true, 0)], vec![input(false, 0)]];
    for limit in 0..=1 {
        let mut options = Options::preset("step1").unwrap();
        options.max_generated = Some(limit);
        let mut search = Search::new(&clauses, &[], &[0], &options, Limits::default()).unwrap();
        let result = search.run();
        assert_eq!(search.stats.generated, limit);
        if limit == 0 {
            assert_eq!(result, Stop::GeneratedLimit);
        } else {
            assert!(matches!(result, Stop::Proof(_)));
        }
    }
}

#[test]
fn empty_input_needs_storage_but_no_generation_budget() {
    let mut options = Options::preset("step5").unwrap();
    options.max_generated = Some(0);
    options.max_stored = Some(1);
    let mut search = Search::new(&[vec![]], &[], &[], &options, Limits::default()).unwrap();
    assert_eq!(search.run(), Stop::Proof(0));
    assert_eq!(search.stats.generated, 0);
    assert!(search.certificate(0, 1 << 20).is_ok());
}

#[test]
fn count_options_accept_u64_and_reject_invalid_values() {
    for key in ["max_stored", "max_generated"] {
        for value in ["0", "1", "18446744073709551615"] {
            assert!(Options::from_settings(&[(key.into(), value.into())]).is_ok());
        }
        for value in ["-1", "1.0", "18446744073709551616", "off"] {
            assert!(Options::from_settings(&[(key.into(), value.into())]).is_err());
        }
    }
}
