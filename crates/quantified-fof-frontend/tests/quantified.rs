// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::{ErrorKind, syntax::Term};
use fang_quantified_fof_core::{
    Formula, Signature, rectify_closed, rectify_normalize_closed, validate,
};
use fang_quantified_fof_frontend::{Body, Limits, Parsed, parse};

fn parsed(source: &str) -> Parsed {
    parse(source.as_bytes(), &Limits::default()).unwrap()
}

fn signature(value: &Parsed) -> Signature {
    Signature {
        functions: value.functions.iter().map(|s| s.arity).collect(),
        predicates: value.predicates.iter().map(|s| s.arity).collect(),
    }
}

fn formula(value: &Parsed, index: usize) -> &Formula {
    let Body::Fof(formula) = &value.declarations[index].body else {
        panic!("expected FOF")
    };
    formula
}

#[test]
fn nested_shadowing_restores_outer_scope_and_rectifies_occurrences() {
    let value = parsed("fof(a,axiom,![X]:((?[X]:p(X)) & p(X))).");
    assert_eq!(value.declarations[0].variables, ["X"]);
    assert_eq!(value.statistics.binders, 2);
    let actual =
        rectify_closed(formula(&value, 0), &signature(&value), &Default::default()).unwrap();
    assert_eq!(actual.binder_count, 2);
    assert_eq!(
        actual.formula,
        Formula::Forall(
            0,
            Box::new(Formula::And(
                Box::new(Formula::Exists(
                    1,
                    Box::new(Formula::Atom(0, vec![Term::Var(1)]))
                )),
                Box::new(Formula::Atom(0, vec![Term::Var(0)])),
            ))
        )
    );
}

#[test]
fn unused_and_repeated_list_binders_remain_in_source_order() {
    let value = parsed("fof(a,axiom,?[Unused,X,X]:![Y]:p(X,Y)).");
    assert_eq!(value.declarations[0].variables, ["Unused", "X", "Y"]);
    assert_eq!(value.statistics.binders, 4);
    let actual =
        rectify_closed(formula(&value, 0), &signature(&value), &Default::default()).unwrap();
    assert_eq!(actual.binder_count, 4);
    assert_eq!(
        actual.formula,
        Formula::Exists(
            0,
            Box::new(Formula::Exists(
                1,
                Box::new(Formula::Exists(
                    2,
                    Box::new(Formula::Forall(
                        3,
                        Box::new(Formula::Atom(0, vec![Term::Var(2), Term::Var(3)]))
                    ))
                ))
            ))
        )
    );
}

#[test]
fn siblings_and_declarations_do_not_leak_bindings() {
    for source in [
        "fof(a,axiom,((![X]:p(X)) & p(X))).",
        "fof(a,axiom,((?[X]:p(X)) => p(X))).",
        "fof(a,axiom,![X]:p(Y)).",
        "fof(a,axiom,![X]:(p(X) | ?[Y]:p(Z))).",
        "fof(a,axiom,![X]:p(X)).fof(b,axiom,p(X)).",
        "cnf(a,axiom,(p(X))).fof(b,axiom,p(X)).",
        "fof(a,axiom,((![X]:p(X)) | ?[Y]:p(X))).",
    ] {
        assert_eq!(
            parse(source.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::InvalidInput,
            "{source}"
        );
    }
    let value = parsed("fof(a,axiom,((![X]:p(X)) & ?[X]:p(X))).");
    assert_eq!(value.declarations[0].variables, ["X"]);
    assert_eq!(
        rectify_closed(formula(&value, 0), &signature(&value), &Default::default())
            .unwrap()
            .binder_count,
        2
    );
}

#[test]
fn mixed_declarations_keep_original_bytes_names_and_raw_clauses() {
    let source = " \tcnf(c,axiom,(p(X)|p(X))).\nfof(a,axiom, ![Unused,X]: ?[Y]:(p(f(X)) | p(Y)) ).\ncnf(d,axiom,(p(Y))).";
    let value = parsed(source);
    assert_eq!(
        value
            .declarations
            .iter()
            .map(|d| d.variables.clone())
            .collect::<Vec<_>>(),
        [vec!["X"], vec!["Unused", "X", "Y"], vec!["Y"]]
    );
    assert_eq!(
        &source[value.declarations[1].bytes.clone()],
        "fof(a,axiom, ![Unused,X]: ?[Y]:(p(f(X)) | p(Y)) )."
    );
    assert_eq!(
        &source[value.declarations[1].body_bytes.clone()],
        "![Unused,X]: ?[Y]:(p(f(X)) | p(Y))"
    );
    let Body::Cnf(clause) = &value.declarations[0].body else {
        panic!()
    };
    assert_eq!(clause.len(), 2);
    assert_eq!(clause[0], clause[1]);
    assert_eq!(clause[0].arguments, [Term::Var(0)]);
    let Body::Cnf(clause) = &value.declarations[2].body else {
        panic!()
    };
    assert_eq!(clause[0].arguments, [Term::Var(0)]);
}

#[test]
fn all_original_symbols_are_reserved_before_any_future_skolemization() {
    let value = parsed("fof(a,axiom,?[X]:f(g(f(X)))).fof(b,axiom,p(sk0(a))).");
    assert_eq!(
        value
            .functions
            .iter()
            .map(|s| (s.name.as_str(), s.arity))
            .collect::<Vec<_>>(),
        [("g", 1), ("f", 1), ("sk0", 1), ("a", 0)]
    );
    assert_eq!(
        value
            .predicates
            .iter()
            .map(|s| (s.name.as_str(), s.arity))
            .collect::<Vec<_>>(),
        [("f", 1), ("p", 1)]
    );
    for declaration in &value.declarations {
        let Body::Fof(f) = &declaration.body else {
            panic!()
        };
        validate(f, &signature(&value), &Default::default()).unwrap();
    }
    for source in [
        "fof(a,axiom,?[X]:p(X)).fof(b,axiom,p(a,b)).",
        "fof(a,axiom,?[X]:p(f(X))).fof(b,axiom,p(f)).",
        "fof(a,axiom,?[X]:p(X)).fof(a,axiom,$true).",
    ] {
        assert_eq!(
            parse(source.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::InvalidInput
        );
    }
}

#[test]
fn quantifiers_under_negation_and_in_either_binary_operand_reach_core() {
    for body in [
        "~![X]:p(X)",
        "~?[X]:p(X)",
        "(?[X]:p(X))",
        "((![X]:p(X)) => ?[Y]:p(Y))",
        "![X]:?[Y]:![Z]:p(f(X,Y,Z))",
        "((?[X]:$true) | ![X]:$false)",
    ] {
        let value = parsed(&format!("fof(a,axiom,{body})."));
        for positive in [false, true] {
            rectify_normalize_closed(
                formula(&value, 0),
                positive,
                &signature(&value),
                &Default::default(),
            )
            .unwrap();
        }
    }
}

#[test]
fn malformed_and_unsupported_input_remain_distinct() {
    for source in [
        "fof(a,axiom,?[]:p).",
        "fof(a,axiom,![x]:p).",
        "fof(a,axiom,?[X,]:p).",
        "fof(a,axiom,?[X Y]:p).",
        "fof(a,axiom,?[X]p).",
        "fof(a,axiom,![X]:).",
        "fof(a,axiom,![X]:X).",
        "fof(a,axiom,?[X]:p(X)). junk",
        "fof(a,axiom,(p & q | r)).",
    ] {
        assert_eq!(
            parse(source.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::InvalidInput,
            "{source}"
        );
    }
    for source in [
        "fof(a,axiom,?[X]:X=a).",
        "fof(a,axiom,![X:$i]:p(X)).",
        "fof(a,conjecture,![X]:p(X)).",
        "fof(a,hypothesis,p).",
        "fof(a,axiom,(p <=> q)).",
        "fof(a,axiom,'p').",
        "% comment\nfof(a,axiom,p).",
        "cnf(a,axiom,(![X]:p(X))).",
        "cnf(a,axiom,(~?[X]:p(X))).",
        "fof(a,axiom,?[X]:p(X),source).",
        "tff(a,axiom,p).",
        "include('a.p').",
    ] {
        assert_eq!(
            parse(source.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::Unsupported,
            "{source}"
        );
    }
    assert_eq!(
        parse(b"fof(a,axiom,p).\xff", &Limits::default())
            .unwrap_err()
            .kind,
        ErrorKind::InvalidInput
    );
}

#[test]
fn binder_and_formula_budgets_count_unused_shadowed_and_later_declarations() {
    let input = b"fof(a,axiom,![X,X]:?[X]:$true).fof(b,axiom,![Y]:$true).";
    for limit in 0..=4 {
        let limits = Limits {
            max_binders: limit,
            ..Default::default()
        };
        let result = parse(input, &limits);
        if limit == 4 {
            assert_eq!(result.unwrap().statistics.binders, 4);
        } else {
            assert_eq!(result.unwrap_err().kind, ErrorKind::ResourceLimit);
        }
    }
    let limits = Limits {
        max_formula_nodes: 5,
        ..Default::default()
    };
    assert_eq!(
        parse(input, &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    let limits = Limits {
        max_formula_nodes: 6,
        ..Default::default()
    };
    assert_eq!(parse(input, &limits).unwrap().statistics.formula_nodes, 6);
}

#[test]
fn expanded_prefix_and_recursive_grouping_cannot_bypass_depth_limit() {
    let names = (0..64).map(|i| format!("V{i}")).collect::<Vec<_>>();
    let at_limit = format!("fof(a,axiom,![{}]:$true).", names[..63].join(","));
    let over_limit = format!("fof(a,axiom,![{}]:$true).", names.join(","));
    assert_eq!(parsed(&at_limit).statistics.formula_nodes, 64);
    assert_eq!(
        parse(over_limit.as_bytes(), &Limits::default())
            .unwrap_err()
            .kind,
        ErrorKind::ResourceLimit
    );
    let limits = Limits {
        max_formula_depth: usize::MAX,
        ..Default::default()
    };
    assert_eq!(
        parse(over_limit.as_bytes(), &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    for body in ["![X,Y]:$true", "((p))", "~![X]:p(X)"] {
        let limits = Limits {
            max_formula_depth: 2,
            ..Default::default()
        };
        assert_eq!(
            parse(format!("fof(a,axiom,{body}).").as_bytes(), &limits)
                .unwrap_err()
                .kind,
            ErrorKind::ResourceLimit
        );
    }
}

#[test]
fn resource_errors_publish_no_partial_input() {
    let input = b"fof(a,axiom,![X]:p(f(X))).fof(b,axiom,?[Y]:p(a)).";
    let cases = [
        fang::Limits {
            max_input_bytes: input.len() - 1,
            ..Default::default()
        },
        fang::Limits {
            max_operations: 0,
            ..Default::default()
        },
        fang::Limits {
            max_term_nodes: 1,
            ..Default::default()
        },
        fang::Limits {
            max_term_depth: 1,
            ..Default::default()
        },
        fang::Limits {
            max_clauses: 1,
            ..Default::default()
        },
    ];
    for input_limits in cases {
        let limits = Limits {
            input: input_limits,
            ..Default::default()
        };
        assert_eq!(
            parse(input, &limits).unwrap_err().kind,
            ErrorKind::ResourceLimit
        );
    }
}

fn lift(f: universal_core_reference::Formula) -> Formula {
    use universal_core_reference::Formula as F;
    match f {
        F::Atom(p, ts) => Formula::Atom(p, ts),
        F::True => Formula::True,
        F::False => Formula::False,
        F::Not(a) => Formula::Not(Box::new(lift(*a))),
        F::And(a, b) => Formula::And(Box::new(lift(*a)), Box::new(lift(*b))),
        F::Or(a, b) => Formula::Or(Box::new(lift(*a)), Box::new(lift(*b))),
        F::Implies(a, b) => Formula::Implies(Box::new(lift(*a)), Box::new(lift(*b))),
    }
}

#[test]
fn accepted_universal_fragment_preserves_exact_tables_clauses_and_formula() {
    let atoms = ["p(X)", "p(f(Y))", "$true", "$false", "~p(X)", "p(a)"];
    let mut count = 0;
    for prefix in ["X,Y", "Y,X", "Unused,Y,X"] {
        for left in atoms {
            for right in atoms {
                for connective in ["&", "|", "=>"] {
                    let source = format!(
                        "cnf(c,axiom,(p(Z)|p(Z))).fof(f,axiom,![{prefix}]:({left}{connective}{right})).fof(g,axiom,p(a))."
                    );
                    let old =
                        universal_reference::parse(source.as_bytes(), &Default::default()).unwrap();
                    let new = parsed(&source);
                    assert_eq!(old.functions, new.functions);
                    assert_eq!(old.predicates, new.predicates);
                    for (old, new) in old.declarations.into_iter().zip(new.declarations) {
                        assert_eq!(old.name, new.name);
                        assert_eq!(old.bytes, new.bytes);
                        assert_eq!(old.variables, new.variables);
                        match (old.body, new.body) {
                            (universal_reference::Body::Cnf(a), Body::Cnf(b)) => assert_eq!(a, b),
                            (universal_reference::Body::Fof(a), Body::Fof(b)) => {
                                assert_eq!(lift(a), b)
                            }
                            (universal_reference::Body::Universal(a), Body::Fof(b)) => {
                                let mut expected = lift(a);
                                for id in (0..old.variables.len()).rev() {
                                    expected = Formula::Forall(id as u32, Box::new(expected));
                                }
                                assert_eq!(expected, b);
                            }
                            _ => panic!("declaration kind changed"),
                        }
                    }
                    count += 1;
                }
            }
        }
    }
    assert_eq!(count, 324);
}

#[test]
fn deterministic_byte_mutations_never_return_a_free_or_ill_formed_fof_ast() {
    let seed = b"fof(a,axiom,![X]:(p(X) => ?[Y]:(p(Y) & p(f(X))))).";
    let mut state = 0x5f31_93a7_u32;
    let mut accepted = 0;
    for _ in 0..10_000 {
        state = state.wrapping_mul(1664525).wrapping_add(1013904223);
        let mut bytes = seed.to_vec();
        let at = state as usize % bytes.len();
        match state >> 30 {
            0 => {
                bytes.remove(at);
            }
            1 => bytes.insert(at, (state >> 16) as u8),
            2 => bytes[at] = (state >> 8) as u8,
            _ => bytes.insert(at, b' '),
        }
        if let Ok(value) = parse(&bytes, &Limits::default()) {
            accepted += 1;
            for declaration in &value.declarations {
                assert!(declaration.bytes.end <= bytes.len());
                assert!(declaration.body_bytes.start >= declaration.bytes.start);
                assert!(declaration.body_bytes.end < declaration.bytes.end);
                if let Body::Fof(f) = &declaration.body {
                    validate(f, &signature(&value), &Default::default()).unwrap();
                }
            }
        }
    }
    assert!(
        accepted > 100,
        "mutation corpus must exercise successful parsing too"
    );
}
