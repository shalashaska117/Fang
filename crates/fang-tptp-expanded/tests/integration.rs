// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::ErrorKind;
use fang_equality_inference_core::Atom;
use fang_equality_search::Outcome;
use fang_tptp_expanded_integration::{Error, Limits, prepare, prove_bytes};
use fang_tptp_full_frontend_candidate::NameKind;

fn snapshot(outcome: Outcome) -> (Option<String>, [usize; 4]) {
    let (certificate, s) = match outcome {
        Outcome::CandidateRefutation {
            certificate,
            statistics,
        } => (Some(certificate.to_text(1 << 20).unwrap()), statistics),
        Outcome::Unknown(statistics) => (None, statistics),
    };
    (
        certificate,
        [
            s.processed_clauses,
            s.attempted_inferences,
            s.derived_clauses,
            s.stored_term_nodes,
        ],
    )
}

#[test]
fn omitted_rows_before_between_after_keep_original_intervals() {
    let source = b"cnf(z,axiom,$true).cnf(a,axiom,p).cnf(y,axiom,~$false).fof(b,axiom,q).fof(t,axiom,$true).cnf(x,axiom,$true).cnf(c,axiom,r).cnf(w,axiom,$true).";
    let result = prepare(source, &Limits::default()).unwrap();
    assert_eq!(result.sources.len(), 8);
    assert_eq!(
        result
            .sources
            .iter()
            .map(|s| s.clauses.clone())
            .collect::<Vec<_>>(),
        [0..0, 0..1, 1..1, 1..2, 2..2, 2..2, 2..3, 3..3]
    );
    assert_eq!(
        result
            .origins
            .iter()
            .map(|o| (o.declaration, o.local_clause))
            .collect::<Vec<_>>(),
        [(1, 0), (3, 0), (6, 0)]
    );
    for row in &result.sources {
        assert!(row.bytes.start <= row.body_bytes.start && row.body_bytes.end <= row.bytes.end);
        assert_eq!(source[row.bytes.end - 1], b'.');
    }
}

#[test]
fn omitted_symbols_reserve_function_ids_before_skolemization() {
    let result = prepare(b"cnf(z,axiom,$true|hidden(f(a))).fof(e,axiom,![Unused,U]:?[X]:(X=U & q(X))).cnf(t,axiom,$true|late(fang_skolem_3)).", &Limits::default()).unwrap();
    assert_eq!(
        result.functions[..3]
            .iter()
            .map(|s| (s.name.as_str(), s.arity))
            .collect::<Vec<_>>(),
        [("f", 1), ("a", 0), ("fang_skolem_3", 0)]
    );
    assert_eq!(result.functions[3].name, "fang_skolem_3_");
    assert_eq!(
        result
            .predicates
            .iter()
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>(),
        ["hidden", "q", "late"]
    );
    assert_eq!(result.introduced.len(), 1);
    let fresh = &result.introduced[0];
    assert_eq!((fresh.declaration, fresh.function, fresh.binder), (1, 3, 2));
    assert_eq!(fresh.universals, [0, 1]);
    assert_eq!(result.sources[1].variables, ["Unused", "U", "X"]);
}

#[test]
fn tagged_names_and_internal_labels_cannot_collide() {
    let result = prepare(
        b"cnf(1,axiom,$true).cnf('1',axiom,p).fof(fang_source_1,axiom,q).",
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(
        (result.sources[0].name.as_str(), result.sources[0].name_kind),
        ("1", NameKind::Integer)
    );
    assert_eq!(
        (result.sources[1].name.as_str(), result.sources[1].name_kind),
        ("1", NameKind::Atom)
    );
    assert_eq!(
        result
            .sources
            .iter()
            .map(|s| s.internal_name.as_str())
            .collect::<Vec<_>>(),
        ["fang_source_0", "fang_source_1", "fang_source_2"]
    );
    assert_ne!(result.clause_names[0], result.clause_names[1]);
}

#[test]
fn arity_overloads_and_separate_namespaces_keep_numeric_positions() {
    let result = prepare(
        b"cnf(a,axiom,p(f(a))|p(f(a,b),b)|f(a)).",
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(
        result
            .functions
            .iter()
            .map(|s| (s.name.as_str(), s.arity))
            .collect::<Vec<_>>(),
        [("f", 1), ("a", 0), ("f", 2), ("b", 0)]
    );
    assert_eq!(
        result
            .predicates
            .iter()
            .map(|s| (s.name.as_str(), s.arity))
            .collect::<Vec<_>>(),
        [("p", 1), ("p", 2), ("f", 1)]
    );
    assert!(matches!(result.clauses[0][0].atom, Atom::Predicate(0, _)));
    assert!(matches!(result.clauses[0][1].atom, Atom::Predicate(1, _)));
    assert!(matches!(result.clauses[0][2].atom, Atom::Predicate(2, _)));
}

#[test]
fn signed_constants_preserve_zero_versus_empty_and_stable_dedup() {
    let result = prepare(
        b"cnf(t,axiom,~$false).cnf(f,axiom,~$true).cnf(p,axiom,$false|p|p|~$true).",
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(
        result
            .sources
            .iter()
            .map(|s| s.cnf_clauses)
            .collect::<Vec<_>>(),
        [Some(0), Some(1), Some(1)]
    );
    assert_eq!(result.clauses.len(), 2);
    assert!(result.clauses[0].is_empty());
    assert_eq!(result.clauses[1].len(), 1);
    assert_eq!(result.statistics.raw_output_literals, 2);
}

#[test]
fn compatible_prepared_problem_and_counters_match_old_adapter() {
    for source in [
        "",
        "cnf(a,axiom,(p(a)|p(a))).",
        "fof(a,axiom,![X]:p(X)).fof(b,axiom,?[Y]:~p(Y)).",
        "fof(e,axiom,?[X]:(X=a & p(X))).cnf(n,axiom,(~p(a))).",
    ] {
        let new = prepare(source.as_bytes(), &Limits::default()).unwrap();
        let old =
            fang_quantified_equality_pipeline::prepare(source.as_bytes(), &Default::default())
                .unwrap();
        assert_eq!(new.clauses, old.clauses, "{source}");
        assert_eq!(new.functions, old.functions);
        assert_eq!(new.predicates, old.predicates);
        assert_eq!(new.origins, old.origins);
        assert_eq!(new.introduced, old.introduced);
        assert_eq!(
            new.statistics.preprocessing_operations,
            old.statistics.preprocessing_operations
        );
        assert_eq!(new.statistics.stored_nodes, old.statistics.stored_nodes);
    }
}

#[test]
fn compatible_search_certificates_and_four_counters_remain_exact() {
    for source in [
        "",
        "cnf(a,axiom,($false)).",
        "cnf(a,axiom,(X!=X)).",
        "cnf(e,axiom,(a=b)).cnf(p,axiom,(p(a))).cnf(n,axiom,(~p(b))).",
    ] {
        let new = prove_bytes(source.as_bytes(), &Limits::default()).unwrap();
        let old =
            fang_quantified_equality_pipeline::prove_bytes(source.as_bytes(), &Default::default())
                .unwrap();
        assert_eq!(snapshot(new.outcome), snapshot(old.outcome), "{source}");
    }
}

#[test]
fn expanded_connectives_and_nested_shadowing_reach_actual_calls() {
    for source in [
        "fof(a,axiom,p<=q).cnf(b,axiom,q).cnf(c,axiom,~p).",
        "fof(a,axiom,p~&q).cnf(b,axiom,p).cnf(c,axiom,q).",
        "fof(a,axiom,p~|q).cnf(b,axiom,p).",
        "fof(a,axiom,p<=>q).cnf(b,axiom,p).cnf(c,axiom,~q).",
        "fof(a,axiom,p<~>q).cnf(b,axiom,p).cnf(c,axiom,q).",
    ] {
        assert!(
            matches!(
                prove_bytes(source.as_bytes(), &Limits::default())
                    .unwrap()
                    .outcome,
                Outcome::CandidateRefutation { .. }
            ),
            "{source}"
        );
    }
    let result = prepare(
        b"cnf(z,axiom,$true).fof(a,axiom,![X]:?[X]:![Y]:?[Z]:(X=Z)).",
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(
        result
            .introduced
            .iter()
            .map(|i| (i.declaration, i.binder, i.universals.clone()))
            .collect::<Vec<_>>(),
        [(1, 1, vec![0]), (1, 3, vec![0, 2])]
    );
}

#[test]
fn complete_source_and_output_caps_are_not_bypassed_by_omission() {
    let mut limits = Limits::default();
    limits.preprocessing.max_declarations = 1;
    assert!(matches!(
        prepare(b"cnf(a,axiom,$true).cnf(b,axiom,$true).", &limits),
        Err(Error::Resource("total source declaration cap"))
    ));
    limits = Limits::default();
    limits.max_adapter_operations = 0;
    assert!(matches!(
        prepare(b"cnf(a,axiom,$true).", &limits),
        Err(Error::Resource(_))
    ));
    limits = Limits::default();
    limits.preprocessing.core.max_literals_per_clause = 1;
    assert!(matches!(
        prepare(b"cnf(a,axiom,$true).cnf(b,axiom,p|q).", &limits),
        Err(Error::Preprocessing(_))
    ));
    limits = Limits::default();
    limits.max_bridge_literals = 1;
    assert!(matches!(
        prepare(b"cnf(a,axiom,$true|p).", &limits),
        Err(Error::Encoding(_))
    ));
}

#[test]
fn unsupported_roles_and_late_invalid_inputs_remain_typed() {
    for source in ["fof(a,conjecture,p).", "include('a.p').", "thf(a,axiom,p)."] {
        assert!(
            matches!(prepare(source.as_bytes(), &Limits::default()), Err(Error::Input(e)) if e.kind == ErrorKind::Unsupported)
        );
    }
    for source in [
        "cnf(a,axiom,$false).fof(b,axiom,p(X)).",
        "cnf(a,axiom,$true).cnf(a,axiom,p).",
    ] {
        assert!(
            matches!(prepare(source.as_bytes(), &Limits::default()), Err(Error::Input(e)) if e.kind == ErrorKind::InvalidInput)
        );
    }
}

#[test]
fn satisfiable_inputs_are_unknown_without_a_sat_claim() {
    for source in [
        "cnf(a,axiom,$true).",
        "cnf(a,axiom,$true|p(f(a))).cnf(b,axiom,q).",
        "fof(a,axiom,p<=>p).",
    ] {
        assert!(matches!(
            prove_bytes(source.as_bytes(), &Limits::default())
                .unwrap()
                .outcome,
            Outcome::Unknown(_)
        ));
    }
}
