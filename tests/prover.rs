// Copyright (c) 2026 Pietro Pellegrino.
use fang::{
    ErrorKind, Limits,
    parser::parse,
    search::{Outcome, prove},
    syntax::{Substitution, Term, apply},
    unify::Unifier,
};

fn constant(id: u32) -> Term {
    Term::Fun(id, vec![])
}
fn function(id: u32, arg: Term) -> Term {
    Term::Fun(id, vec![arg])
}
fn parse_ok(text: &str) -> fang::syntax::Problem {
    parse(text.as_bytes(), &Limits::default()).unwrap()
}

#[test]
fn substitution_insertion_handles_empty_append_interior_and_replacement() {
    let mut substitution = Substitution::new();
    assert_eq!(substitution.insert(2, constant(0)), None);
    assert_eq!(substitution.insert(4, constant(1)), None);
    assert_eq!(substitution.insert(1, constant(2)), None);
    assert_eq!(substitution.insert(3, constant(3)), None);
    assert_eq!(substitution.insert(2, constant(4)), Some(constant(0)));
    assert_eq!(substitution.len(), 4);
    assert_eq!(
        substitution.iter().cloned().collect::<Vec<_>>(),
        vec![
            (1, constant(2)),
            (2, constant(4)),
            (3, constant(3)),
            (4, constant(1))
        ]
    );
}

#[test]
fn acyclic_variable_chain_can_exceed_the_normalization_depth_cap() {
    let limits = Limits {
        max_term_depth: usize::MAX,
        max_term_nodes: usize::MAX,
        max_operations: usize::MAX,
        ..Limits::default()
    };
    for length in [64, 65] {
        let pairs: Vec<_> = (1..=length)
            .rev()
            .map(|variable| (Term::Var(variable), Term::Var(variable - 1)))
            .collect();
        let mut unifier = Unifier::default();
        assert_eq!(unifier.unify(&pairs, &limits), Ok(true));
        if length == 64 {
            let witness = unifier.substitution(&limits).unwrap();
            for variable in 1..=length {
                assert_eq!(witness.get(&variable), Some(&Term::Var(0)));
            }
        } else {
            let error = unifier.substitution(&limits).unwrap_err();
            assert_eq!(error.kind, ErrorKind::ResourceLimit);
            assert_eq!(error.message, "unifier expansion depth limit exceeded");
            // A solution exists. Increasing the configured limits cannot remove
            // the hard 64-frame expansion cap or justify reporting a mismatch.
            let solution: Substitution = (1..=length)
                .map(|variable| (variable, Term::Var(0)))
                .collect();
            for (left, right) in &pairs {
                assert_eq!(apply(left, &solution), apply(right, &solution));
            }
        }
    }
}

#[test]
fn parser_preserves_first_occurrence_and_clause_local_names() {
    let problem = parse_ok(
        "cnf(first,axiom,(p(f(g(a)),X,X0,X)|q)).\ncnf(second,axiom,(q|p(f(g(a)),X,X0,X))).",
    );
    assert_eq!(
        problem
            .functions
            .iter()
            .map(|s| (&*s.name, s.arity))
            .collect::<Vec<_>>(),
        vec![("f", 1), ("g", 1), ("a", 0)]
    );
    assert_eq!(
        problem
            .predicates
            .iter()
            .map(|s| (&*s.name, s.arity))
            .collect::<Vec<_>>(),
        vec![("p", 4), ("q", 0)]
    );
    assert_eq!(
        problem.clauses[0][0].arguments[1..],
        [Term::Var(0), Term::Var(1), Term::Var(0)]
    );
    assert_eq!(
        problem.clauses[1][1].arguments[1..],
        [Term::Var(0), Term::Var(1), Term::Var(0)]
    );
}

#[test]
fn parser_preserves_underscores_and_mixed_case_variable_names() {
    let problem = parse_ok(concat!(
        "cnf(c_0,axiom,(p_0(f_1(a_2),Xlower_1,XLower_1,Xlower_1))).",
        "cnf(c_1,axiom,(p_0(f_1(a_2),XLower_1,Xlower_1,XLower_1))).",
    ));
    assert_eq!(problem.clause_names, ["c_0", "c_1"]);
    assert_eq!(
        problem
            .functions
            .iter()
            .map(|s| (&*s.name, s.arity))
            .collect::<Vec<_>>(),
        [("f_1", 1), ("a_2", 0)]
    );
    assert_eq!(
        problem
            .predicates
            .iter()
            .map(|s| (&*s.name, s.arity))
            .collect::<Vec<_>>(),
        [("p_0", 4)]
    );
    for clause in &problem.clauses {
        assert_eq!(clause[0].arguments[0], function(0, constant(1)));
        assert_eq!(
            clause[0].arguments[1..],
            [Term::Var(0), Term::Var(1), Term::Var(0)]
        );
    }
}

#[test]
fn parser_accepts_whitespace_nullary_symbols_empty_file_and_false() {
    let empty = parse_ok("");
    assert!(empty.clauses.is_empty());
    assert!(empty.clause_names.is_empty());
    assert!(empty.functions.is_empty());
    assert!(empty.predicates.is_empty());
    assert!(parse_ok(" \t\n\u{b}\u{c}\r").clauses.is_empty());
    assert!(parse_ok("cnf(c,axiom,($false)).").clauses[0].is_empty());
    let p = parse_ok("\tcnf ( c , axiom , ( p | ~ p | p ) ) .\r\n");
    assert_eq!(p.clauses[0].len(), 2);
    assert!(p.clauses[0][0].positive);
    assert!(!p.clauses[0][1].positive);
    assert_eq!(parse_ok("cnf(c,axiom,(p(p))).").functions[0].name, "p");
}

#[test]
fn parser_rejects_invalid_syntax_arity_and_names() {
    for text in [
        "cnfx(c,axiom,(p)).",
        "cnf(c,axiom,(p)).garbage",
        "cnf(c,axiom,(p())).",
        "cnf(c,axiom,(p(a()))).",
        "cnf(c,axiom,(p)).cnf(c,axiom,(q)).",
        "cnf(c,axiom,(p|p(a))).",
        "cnf(c,axiom,(p(f(f)))).",
        "cnf(c,axiom,(p(a)|q(a(a)))).",
        "cnf(c,axiom,($false|p)).",
        "cnf(c,axiom,(~$false)).",
        "cnf(c,axiom,(p)).)",
        "cnf(c,axiom,(p))",
        "cnf(c,axiom,(p(aB))).",
        "cnf(c,axiom,()).",
        "cnf(c,axiom,(p(A)(a))).",
        "cnf(c,axiom,(p)).\u{feff}",
        "cnf(c,axiom,(p(é))).",
    ] {
        let error = parse(text.as_bytes(), &Limits::default()).unwrap_err();
        assert_eq!(error.kind, ErrorKind::InvalidInput, "{text}: {error}");
        assert!(error.offset.is_some(), "missing source offset for {text}");
    }
}

#[test]
fn parser_classifies_supported_tptp_extensions_as_unsupported() {
    for text in [
        "fof(c,axiom,(p)).",
        "tff(c,axiom,(p)).",
        "thf(c,axiom,(p)).",
        "include(x).",
        "cnf(c,conjecture,(p)).",
        "cnf(c,axiom,(a=b)).",
        "cnf(c,axiom,(a!=b)).",
        "cnf(c,axiom,(p(12))).",
        "cnf(c,axiom,(p(_X))).",
        "cnf(c,axiom,($true)).",
        "cnf(c,axiom,(p($sum(a,b)))).",
        "% comment\ncnf(c,axiom,(p)).",
        "cnf(c,axiom,(p),'annotation').",
        "cnf(c,axiom,(![X]:p(X))).",
        "cnf(c,axiom,('p')).",
    ] {
        assert_eq!(
            parse(text.as_bytes(), &Limits::default()).unwrap_err().kind,
            ErrorKind::Unsupported,
            "{text}"
        );
    }
}

#[test]
fn parser_rejects_escapes_quoted_names_and_existential_syntax() {
    for text in [
        r"cnf(c,axiom,(p(a\n))).",
        r"cnf(c,axiom,(p(a\u0062))).",
        r"cnf(c,axiom,(p(\X))).",
        r#"cnf(c,axiom,("p"))."#,
        r"cnf(c,axiom,('p\'q')).",
        "cnf(c,axiom,(?[X]:p(X))).",
    ] {
        let error = parse(text.as_bytes(), &Limits::default()).unwrap_err();
        // The public grammar promises rejection. It does not require every
        // escaped token to share the same invalid/unsupported diagnostic.
        assert!(matches!(
            error.kind,
            ErrorKind::InvalidInput | ErrorKind::Unsupported
        ));
        assert!(error.offset.is_some(), "missing byte offset: {text}");
        assert!(
            !error.message.is_empty(),
            "missing rejection reason: {text}"
        );
    }
}

#[test]
fn parser_limits_are_resource_results() {
    let deep = format!("cnf(c,axiom,(p({}a{}))).", "f(".repeat(65), ")".repeat(65));
    assert_eq!(
        parse(deep.as_bytes(), &Limits::default()).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    let limits = Limits {
        max_input_bytes: 5,
        ..Limits::default()
    };
    assert_eq!(
        parse(b"cnf(c,axiom,(p)).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    let limits = Limits {
        max_clauses: 0,
        ..Limits::default()
    };
    assert_eq!(
        parse(b"cnf(c,axiom,(p)).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
}

#[test]
fn simultaneous_application_does_not_expand_images() {
    let substitution = Substitution::from([(0, Term::Var(1)), (1, constant(0))]);
    assert_eq!(apply(&Term::Var(0), &substitution), Term::Var(1));
}

#[test]
fn occurs_check_direct_indirect_and_rollback() {
    let limits = Limits::default();
    let mut u = Unifier::default();
    assert!(
        !u.unify(&[(Term::Var(0), function(0, Term::Var(0)))], &limits)
            .unwrap()
    );
    assert!(u.substitution(&limits).unwrap().is_empty());
    assert!(
        u.unify(&[(Term::Var(0), function(0, Term::Var(1)))], &limits)
            .unwrap()
    );
    let before = u.clone();
    assert!(
        !u.unify(&[(Term::Var(1), function(1, Term::Var(0)))], &limits)
            .unwrap()
    );
    assert_eq!(u, before);
    assert!(
        !u.unify(
            &[(Term::Var(2), constant(1)), (constant(2), constant(3))],
            &limits
        )
        .unwrap()
    );
    assert_eq!(u, before);
    let limited = Limits {
        max_operations: 1,
        ..limits.clone()
    };
    assert_eq!(
        u.unify(&[(Term::Var(3), constant(0))], &limited)
            .unwrap_err()
            .kind,
        ErrorKind::ResourceLimit
    );
    assert_eq!(u, before);
}

#[test]
fn normalized_witness_unifies_transitive_bindings() {
    let limits = Limits::default();
    let pairs = [
        (Term::Var(0), function(0, Term::Var(1))),
        (Term::Var(1), constant(1)),
    ];
    let mut u = Unifier::default();
    assert!(u.unify(&pairs, &limits).unwrap());
    let witness = u.substitution(&limits).unwrap();
    assert_eq!(witness[&0], function(0, constant(1)));
    for (left, right) in pairs {
        assert_eq!(apply(&left, &witness), apply(&right, &witness));
    }
}

#[test]
fn failed_normalization_preserves_state_and_can_be_retried() {
    let limits = Limits::default();
    let pairs = [
        (Term::Var(0), function(0, Term::Var(1))),
        (Term::Var(1), constant(1)),
    ];
    let mut unifier = Unifier::default();
    assert!(unifier.unify(&pairs, &limits).unwrap());
    let before = unifier.clone();
    let limited = Limits {
        max_term_nodes: 1,
        ..limits.clone()
    };
    let error = unifier.substitution(&limited).unwrap_err();
    assert_eq!(error.kind, ErrorKind::ResourceLimit);
    assert_eq!(error.offset, None);
    assert_eq!(error.message, "unifier expansion node limit exceeded");
    assert_eq!(unifier, before);

    let witness = unifier.substitution(&limits).unwrap();
    for (left, right) in &pairs {
        assert_eq!(apply(left, &witness), apply(right, &witness));
    }
    assert_eq!(unifier, before);
}

#[test]
fn empty_unification_revalidates_stored_bindings_under_new_limits() {
    let limits = Limits::default();
    let mut unifier = Unifier::default();
    assert!(
        unifier
            .unify(&[(Term::Var(0), function(0, constant(1)))], &limits)
            .unwrap()
    );
    let before = unifier.clone();
    let limited = Limits {
        max_term_depth: 1,
        ..limits.clone()
    };
    let error = unifier.unify(&[], &limited).unwrap_err();
    assert_eq!(error.kind, ErrorKind::ResourceLimit);
    assert_eq!(error.offset, None);
    assert_eq!(error.message, "unifier input depth limit exceeded");
    assert_eq!(unifier, before);
    assert!(unifier.unify(&[], &limits).unwrap());
    assert_eq!(unifier, before);
}

#[test]
fn unification_mismatch_and_expansion_limits_are_separate() {
    let limits = Limits::default();
    let mut u = Unifier::default();
    assert!(!u.unify(&[(constant(0), constant(1))], &limits).unwrap());
    assert!(
        !u.unify(&[(constant(0), function(0, constant(1)))], &limits)
            .unwrap()
    );
    let limits = Limits {
        max_term_depth: 2,
        ..limits
    };
    assert_eq!(
        u.unify(
            &[(function(0, function(0, constant(1))), Term::Var(0))],
            &limits
        )
        .unwrap_err()
        .kind,
        ErrorKind::ResourceLimit
    );
}

#[test]
fn public_unifier_validates_depth_before_recursive_copy() {
    let limits = Limits::default();
    let mut deep = constant(0);
    for _ in 0..128 {
        deep = function(1, deep);
    }
    let mut unifier = Unifier::default();
    assert_eq!(
        unifier
            .unify(&[(deep, Term::Var(0))], &limits)
            .unwrap_err()
            .kind,
        ErrorKind::ResourceLimit
    );
    assert_eq!(unifier, Unifier::default());
}

#[test]
fn resource_failure_after_a_local_binding_rolls_back() {
    let limits = Limits {
        max_operations: 16,
        ..Limits::default()
    };
    let mut deep = constant(1);
    for _ in 0..5 {
        deep = function(2, deep);
    }
    let pairs = [(Term::Var(0), constant(0)), (Term::Var(1), deep)];
    // The first equation fits by itself. In the batch, expansion of the second
    // equation exhausts the budget after the first local binding was made.
    assert!(Unifier::default().unify(&pairs[..1], &limits).unwrap());
    let mut unifier = Unifier::default();
    assert_eq!(
        unifier.unify(&pairs, &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    assert_eq!(unifier, Unifier::default());
    assert!(
        unifier
            .unify(&[(Term::Var(0), constant(1))], &Limits::default())
            .unwrap()
    );
}

fn certificate(input: &str) -> String {
    let limits = Limits::default();
    match prove(&parse_ok(input), &limits).unwrap() {
        Outcome::CandidateRefutation(proof) => proof.to_text(limits.max_proof_bytes).unwrap(),
        other => panic!("expected a candidate refutation, got {other:?}"),
    }
}

#[test]
fn search_produces_factoring_and_resolution_witnesses() {
    let text = certificate("cnf(c0,axiom,(p(X)|p(Y)|p(X))).cnf(c1,axiom,(~p(a))).");
    assert!(
        text.contains("(factor 2 0 0 1 (subst (1 (v 0))) (clause (pos 0 (v 0))))"),
        "{text}"
    );
    assert!(text.contains("(resolve "));
    assert!(text.contains("(clause))"));
    assert_eq!(
        text,
        certificate("cnf(c0,axiom,(p(X)|p(Y)|p(X))).cnf(c1,axiom,(~p(a))).")
    );
}

#[test]
fn search_handles_empty_nullary_ground_and_nonground_inputs() {
    assert!(certificate("cnf(c,axiom,($false)).").contains("(final 0)"));
    for input in [
        "cnf(c0,axiom,(p)).cnf(c1,axiom,(~p)).",
        "cnf(c0,axiom,(p(a))).cnf(c1,axiom,(~p(a))).",
        "cnf(c0,axiom,(p(f(X)))).cnf(c1,axiom,(~p(f(a)))).",
        "cnf(c0,axiom,(p(X)|q(X))).cnf(c1,axiom,(~p(a))).cnf(c2,axiom,(~q(a))).",
    ] {
        assert!(certificate(input).contains("(final "));
    }
}

#[test]
fn input_empty_clause_finishes_the_certificate_before_later_inputs() {
    let proof = certificate("cnf(c0,axiom,($false)).cnf(c1,axiom,(p)).");
    assert_eq!(proof, "(fang-proof 1\n  (input 0 0)\n  (final 0))\n");
}

#[test]
fn public_search_api_rejects_malformed_signatures_and_unprocessed_inputs() {
    let original = parse_ok("cnf(c0,axiom,(p(a))).cnf(c1,axiom,(~p(a))).");
    let mut bad = original.clone();
    bad.clauses[1][0].arguments.clear();
    assert_eq!(
        prove(&bad, &Limits::default()).unwrap_err().kind,
        ErrorKind::InvalidInput
    );
    let mut bad = original.clone();
    bad.clauses[0][0].predicate = 42;
    assert_eq!(
        prove(&bad, &Limits::default()).unwrap_err().kind,
        ErrorKind::InvalidInput
    );
    let mut bad = original.clone();
    bad.clauses[0][0].arguments[0] = constant(42);
    assert_eq!(
        prove(&bad, &Limits::default()).unwrap_err().kind,
        ErrorKind::InvalidInput
    );
    let mut bad = original.clone();
    bad.clauses[0][0].arguments[0] = function(0, constant(0));
    assert_eq!(
        prove(&bad, &Limits::default()).unwrap_err().kind,
        ErrorKind::InvalidInput
    );
    let mut bad = original.clone();
    let duplicate = bad.clauses[0][0].clone();
    bad.clauses[0].push(duplicate);
    assert_eq!(
        prove(&bad, &Limits::default()).unwrap_err().kind,
        ErrorKind::InvalidInput
    );
    let mut bad = original;
    bad.clause_names.clear();
    assert_eq!(
        prove(&bad, &Limits::default()).unwrap_err().kind,
        ErrorKind::InvalidInput
    );
}

#[test]
fn search_exhaustion_is_unknown_never_sat() {
    for input in [
        "",
        "cnf(c,axiom,(p(a))).",
        "cnf(c,axiom,(p(X)|~p(X))).",
        "cnf(c0,axiom,(p(X,X))).cnf(c1,axiom,(~p(Y,f(Y)))).",
    ] {
        assert!(matches!(
            prove(&parse_ok(input), &Limits::default()).unwrap(),
            Outcome::Unknown { .. }
        ));
    }
}

#[test]
fn search_and_serialization_limits_do_not_report_logical_results() {
    let problem = parse_ok("cnf(c0,axiom,(p)).cnf(c1,axiom,(~p)).");
    let limits = Limits {
        max_steps: 0,
        ..Limits::default()
    };
    assert_eq!(
        prove(&problem, &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    if let Outcome::CandidateRefutation(proof) = prove(&problem, &Limits::default()).unwrap() {
        assert_eq!(proof.to_text(4).unwrap_err().kind, ErrorKind::ResourceLimit);
    } else {
        panic!("missing candidate");
    }
}

// Fixed xorshift64 generator, deterministic on every supported platform.
fn random(state: &mut u64) -> u32 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    (*state >> 16) as u32
}
fn generated_term(state: &mut u64, depth: usize) -> Term {
    let choice = random(state) % 5;
    if choice < 2 {
        Term::Var(random(state) % 4)
    } else if depth == 0 || choice == 2 {
        constant(random(state) % 3)
    } else {
        function(random(state) % 3, generated_term(state, depth - 1))
    }
}

#[test]
fn generated_successful_unifiers_satisfy_all_original_equations() {
    let limits = Limits::default();
    let mut successes = 0;
    for seed in 1..=10 {
        let mut state = seed;
        for _ in 0..1000 {
            let pairs = vec![
                (generated_term(&mut state, 3), generated_term(&mut state, 3)),
                (generated_term(&mut state, 3), generated_term(&mut state, 3)),
            ];
            let mut u = Unifier::default();
            if u.unify(&pairs, &limits).unwrap() {
                successes += 1;
                let substitution = u.substitution(&limits).unwrap();
                for (left, right) in &pairs {
                    assert_eq!(apply(left, &substitution), apply(right, &substitution));
                }
                for term in substitution.values() {
                    assert_eq!(
                        apply(term, &substitution),
                        *term,
                        "normalized witness must be idempotent"
                    );
                }
            } else {
                assert!(u.substitution(&limits).unwrap().is_empty());
            }
        }
    }
    assert!(successes > 100);
}

#[test]
fn bounded_arbitrary_byte_inputs_never_panic() {
    let mut state = 0x4641_4e47;
    let limits = Limits::default();
    for _ in 0..5000 {
        let length = (random(&mut state) % 128) as usize;
        let bytes: Vec<u8> = (0..length).map(|_| random(&mut state) as u8).collect();
        let _ = parse(&bytes, &limits);
    }
}

#[test]
fn finite_ground_assignments_factor_through_generated_unifiers() {
    // This checks a finite sample of the MGU contract. It is not a completeness proof.
    let limits = Limits::default();
    let candidates = [constant(0), constant(1), function(0, constant(0))];
    let mut state = 0x4d47_5553;
    let mut solved_ground_instances = 0;
    for _ in 0..250 {
        let pairs = [(generated_term(&mut state, 2), generated_term(&mut state, 2))];
        let mut unifier = Unifier::default();
        let success = unifier.unify(&pairs, &limits).unwrap();
        let witness = unifier.substitution(&limits).unwrap();
        for a in &candidates {
            for b in &candidates {
                for c in &candidates {
                    for d in &candidates {
                        let assignment = Substitution::from([
                            (0, a.clone()),
                            (1, b.clone()),
                            (2, c.clone()),
                            (3, d.clone()),
                        ]);
                        if pairs.iter().all(|(left, right)| {
                            apply(left, &assignment) == apply(right, &assignment)
                        }) {
                            solved_ground_instances += 1;
                            assert!(success, "a ground solution refutes the reported mismatch");
                            for variable in 0..4 {
                                assert_eq!(
                                    apply(&apply(&Term::Var(variable), &witness), &assignment),
                                    assignment[&variable],
                                    "the supplied unifier must preserve every tested ground solution"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(solved_ground_instances > 50);
}
