// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::ErrorKind;
use fang::syntax::Term;
use fang_equality_inference_core::Atom;
use fang_equality_search::Outcome;
use fang_fof_equality_bridge::Error as BridgeError;
use fang_quantified_equality_pipeline::{Error, Limits, prepare, prove_bytes};

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

fn candidate(source: &str) {
    assert!(matches!(
        prove_bytes(source.as_bytes(), &Limits::default())
            .unwrap()
            .outcome,
        Outcome::CandidateRefutation { .. }
    ));
}

#[test]
fn duplicate_free_cnf_matches_old_byte_search_exactly() {
    for source in [
        "",
        "cnf(a,axiom,($false)).",
        "cnf(a,axiom,(X!=X)).",
        "cnf(a,axiom,(a=b)).",
        "cnf(e,axiom,(a=b)).cnf(p,axiom,(p(a))).cnf(n,axiom,(~p(b))).",
        "cnf(p,axiom,(p(X)|q(X))).cnf(n,axiom,(~p(a))).cnf(m,axiom,(~q(a))).",
    ] {
        let limits = Limits::default();
        let new = prove_bytes(source.as_bytes(), &limits).unwrap();
        let old =
            fang_equality_search::prove_bytes_ordered(source.as_bytes(), &limits.search).unwrap();
        assert_eq!(snapshot(new.outcome), snapshot(old), "{source}");
    }
}

#[test]
fn existing_stable_deduplication_is_explicit() {
    let output = prepare(b"cnf(a,axiom,(X!=X|X!=X|p(X)|p(X))).", &Limits::default()).unwrap();
    assert_eq!(output.clauses[0].len(), 2);
    assert!(matches!(
        output.clauses[0][0].atom,
        Atom::Equal(Term::Var(0), Term::Var(0))
    ));
    assert!(matches!(output.clauses[0][1].atom, Atom::Predicate(0, _)));
    assert!(!output.clauses[0][0].positive);
    assert_eq!(output.statistics.raw_output_literals, 4);
}

#[test]
fn universal_equality_and_congruence_produce_candidates() {
    candidate("fof(e,axiom,![X]:(f(X)=X)).cnf(p,axiom,(p(f(a)))).cnf(n,axiom,(~p(a))).");
    candidate("fof(e,axiom,![X]:(X=f(X))).cnf(p,axiom,(p(a))).cnf(n,axiom,(~p(f(a)))).");
}

#[test]
fn existential_witnesses_and_negative_reflexivity_produce_candidates() {
    candidate("fof(e,axiom,?[X]:(X=a & p(f(X)))).fof(n,axiom,~p(f(a))).");
    candidate("fof(e,axiom,?[X]:(X!=X)).");
    candidate("fof(e,axiom,~(![X]:(X=X))).");
    candidate("fof(a,axiom,![X]:p(X)).fof(b,axiom,?[Y]:~p(Y)).");
}

#[test]
fn complete_mixed_sources_and_unused_dependencies_keep_order() {
    let input = b"fof(t,axiom,$true).cnf(c,axiom,(p(a)|p(a))).fof(e,axiom,![Unused,U]:?[X]:((X=U)&q(X))).fof(z,axiom,$true).cnf(n,axiom,(r)).";
    let output = prepare(input, &Limits::default()).unwrap();
    assert_eq!(
        output
            .sources
            .iter()
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>(),
        ["t", "c", "e", "z", "n"]
    );
    assert_eq!(
        output
            .sources
            .iter()
            .map(|s| s.clauses.clone())
            .collect::<Vec<_>>(),
        [0..0, 0..1, 1..3, 3..3, 3..4]
    );
    assert_eq!(
        output
            .origins
            .iter()
            .map(|o| (o.declaration, o.local_clause))
            .collect::<Vec<_>>(),
        [(1, 0), (2, 0), (2, 1), (4, 0)]
    );
    assert_eq!(output.clause_names, ["c_1_0", "e_2_0", "e_2_1", "n_4_0"]);
    assert_eq!(output.introduced.len(), 1);
    let fresh = &output.introduced[0];
    assert_eq!(
        (
            fresh.declaration,
            fresh.binder,
            fresh.function,
            &fresh.universals
        ),
        (2, 2, 1, &vec![0, 1])
    );
    assert_eq!(output.functions[1].arity, 2);
    assert_eq!(output.sources[2].variables, ["Unused", "U", "X"]);
    for source in &output.sources {
        assert!(
            source.bytes.start <= source.body_bytes.start
                && source.body_bytes.end <= source.bytes.end
        );
        assert_eq!(&input[source.bytes.end - 1..source.bytes.end], b".");
    }
}

#[test]
fn shadowing_retains_rectified_dependency_positions() {
    let output = prepare(
        b"fof(a,axiom,![X]:?[X]:![Y]:?[Z]:(X=Z)).",
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(
        output
            .introduced
            .iter()
            .map(|i| (i.binder, i.universals.clone()))
            .collect::<Vec<_>>(),
        [(1, vec![0]), (3, vec![0, 2])]
    );
    assert_eq!(output.sources[0].variables, ["X", "Y", "Z"]);
}

#[test]
fn late_symbols_and_display_name_collisions_do_not_capture_equality() {
    let output = prepare(
        b"fof(e,axiom,?[X]:(X=a)).cnf(l,axiom,(fang_equality(fang_skolem_2)|p(b))).",
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(
        output
            .predicates
            .iter()
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>(),
        ["fang_equality", "p"]
    );
    assert_eq!(
        output.functions[..3]
            .iter()
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>(),
        ["a", "fang_skolem_2", "b"]
    );
    assert_eq!(output.introduced[0].function, 3);
    assert!(matches!(output.clauses[0][0].atom, Atom::Equal(_, _)));
    assert!(matches!(output.clauses[1][0].atom, Atom::Predicate(0, _)));
    assert!(output.predicates.iter().all(|s| !s.name.contains('\0')));
    let collision = prepare(
        b"fof(e,axiom,?[X]:p(X)).cnf(c,axiom,(q(fang_skolem_1))).",
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(collision.functions[1].name, "fang_skolem_1_");
}

#[test]
fn unsupported_and_invalid_inputs_remain_distinct_before_search() {
    for source in ["thf(a,axiom,p).", "fof(a,conjecture,p).", "include('a.p')."] {
        assert!(
            matches!(prove_bytes(source.as_bytes(), &Limits::default()), Err(Error::Input(error)) if error.kind == ErrorKind::Unsupported)
        );
    }
    for source in [
        "fof(a,axiom,p(X)).",
        "cnf(e,axiom,($false)).fof(a,axiom,(X=X)).",
    ] {
        assert!(
            matches!(prove_bytes(source.as_bytes(), &Limits::default()), Err(Error::Input(error)) if error.kind == ErrorKind::InvalidInput)
        );
    }
    assert!(matches!(
        prepare(b"cnf(a,axiom,(\0fang_equality)).", &Limits::default()),
        Err(Error::Input(_))
    ));
}

#[test]
fn reservation_and_conversion_limits_are_typed() {
    let mut limits = Limits {
        max_predicates: 1,
        ..Limits::default()
    };
    assert!(matches!(
        prepare(b"cnf(a,axiom,(p)).", &limits),
        Err(Error::Encoding(BridgeError::PredicateLimit))
    ));
    limits.max_predicates = 2;
    assert!(prepare(b"cnf(a,axiom,(p)).", &limits).is_ok());
    limits.max_bridge_literals = 1;
    assert!(matches!(
        prepare(b"fof(a,axiom,(a=b|c=d)).", &limits),
        Err(Error::Conversion(BridgeError::LiteralLimit))
    ));
    assert!(matches!(
        prepare(b"cnf(a,axiom,(a=b|c=d)).", &limits),
        Err(Error::Encoding(BridgeError::LiteralLimit))
    ));
}

#[test]
fn exact_adapter_budget_has_no_partial_output() {
    let input = b"fof(a,axiom,?[X]:(X=a&p(X))).cnf(b,axiom,(q)).";
    let output = prepare(input, &Limits::default()).unwrap();
    let mut limits = Limits {
        max_adapter_operations: output.adapter_operations,
        ..Limits::default()
    };
    assert!(prepare(input, &limits).is_ok());
    limits.max_adapter_operations -= 1;
    assert!(matches!(prepare(input, &limits), Err(Error::Resource(_))));
}

#[test]
fn parser_preprocessing_and_search_resources_stay_separate() {
    let input = b"fof(e,axiom,?[X]:(X!=X)).";
    let mut limits = Limits::default();
    limits.input.input.max_input_bytes = 1;
    assert!(
        matches!(prove_bytes(input, &limits), Err(Error::Input(error)) if error.kind == ErrorKind::ResourceLimit)
    );
    limits = Limits::default();
    limits.preprocessing.core.max_operations = 0;
    assert!(matches!(
        prove_bytes(input, &limits),
        Err(Error::Preprocessing(_))
    ));
    limits = Limits::default();
    limits.search.input.max_operations = 0;
    assert!(matches!(
        prove_bytes(input, &limits),
        Err(Error::Search(
            fang_equality_search::PreparedError::Resource(_)
        ))
    ));
}

#[test]
fn satisfiable_looking_inputs_return_only_unknown() {
    for input in [
        "fof(a,axiom,$true).",
        "fof(a,axiom,?[X]:(X=a)).",
        "fof(a,axiom,![X]:(X=X)).",
    ] {
        assert!(matches!(
            prove_bytes(input.as_bytes(), &Limits::default())
                .unwrap()
                .outcome,
            Outcome::Unknown(_)
        ));
    }
}

#[test]
fn generated_congruence_candidates_preserve_complete_tables() {
    for index in 0..24 {
        let (left, right) = if index % 2 == 0 {
            ("X", "a")
        } else {
            ("a", "X")
        };
        let mut term = "X".to_owned();
        let mut ground = "a".to_owned();
        for depth in 0..index % 3 {
            term = format!("f{depth}({term})");
            ground = format!("f{depth}({ground})");
        }
        let source = format!(
            "fof(e,axiom,?[X]:({left}={right}&p{index}({term}))).fof(n,axiom,~p{index}({ground}))."
        );
        let result = prove_bytes(source.as_bytes(), &Limits::default()).unwrap();
        assert!(matches!(
            result.outcome,
            Outcome::CandidateRefutation { .. }
        ));
        assert_eq!(result.prepared.predicates.len(), 1);
        assert_eq!(result.prepared.predicates[0].name, format!("p{index}"));
        assert_eq!(result.prepared.introduced.len(), 1);
    }
}
