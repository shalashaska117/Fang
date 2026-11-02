// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::syntax::{Clause, Literal, Term};
use fang_fof_core::{
    Error, Formula, Invalid, Limits, Nnf, Resource, Signature, normalize, preprocess, validate,
};

fn signature() -> Signature {
    Signature {
        functions: vec![],
        predicates: vec![0, 0, 0, 0, 0],
    }
}

fn atom(predicate: u32) -> Formula {
    Formula::Atom(predicate, vec![])
}

fn literal(predicate: u32, positive: bool) -> Literal {
    Literal {
        positive,
        predicate,
        arguments: vec![],
    }
}

fn duplicate(formula: &Formula) -> Formula {
    match formula {
        Formula::Atom(predicate, terms) => Formula::Atom(*predicate, terms.clone()),
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Not(inner) => Formula::Not(Box::new(duplicate(inner))),
        Formula::And(left, right) => {
            Formula::And(Box::new(duplicate(left)), Box::new(duplicate(right)))
        }
        Formula::Or(left, right) => {
            Formula::Or(Box::new(duplicate(left)), Box::new(duplicate(right)))
        }
        Formula::Implies(left, right) => {
            Formula::Implies(Box::new(duplicate(left)), Box::new(duplicate(right)))
        }
    }
}

// Test specification: clauses are interpreted under a Boolean atom assignment.
// Term-bearing tests below separately check exact term preservation.
fn truth(formula: &Formula, assignment: &[bool]) -> bool {
    match formula {
        Formula::Atom(predicate, _) => assignment[*predicate as usize],
        Formula::True => true,
        Formula::False => false,
        Formula::Not(inner) => !truth(inner, assignment),
        Formula::And(left, right) => truth(left, assignment) && truth(right, assignment),
        Formula::Or(left, right) => truth(left, assignment) || truth(right, assignment),
        Formula::Implies(left, right) => !truth(left, assignment) || truth(right, assignment),
    }
}

fn nnf_truth(formula: &Nnf, assignment: &[bool]) -> bool {
    match formula {
        Nnf::Literal(value) => assignment[value.predicate as usize] == value.positive,
        Nnf::True => true,
        Nnf::False => false,
        Nnf::And(left, right) => nnf_truth(left, assignment) && nnf_truth(right, assignment),
        Nnf::Or(left, right) => nnf_truth(left, assignment) || nnf_truth(right, assignment),
    }
}

fn cnf_truth(clauses: &[Clause], assignment: &[bool]) -> bool {
    clauses.iter().all(|clause| {
        clause
            .iter()
            .any(|value| assignment[value.predicate as usize] == value.positive)
    })
}

// Direct formula-to-clause specification, separate from the implementation's
// NNF conversion, metadata, storage preflight and copying loops.
fn expected_cnf(formula: &Formula, positive: bool) -> Vec<Clause> {
    let append = |mut left: Vec<Clause>, right: Vec<Clause>| {
        left.extend(right);
        left
    };
    let product = |left: Vec<Clause>, right: Vec<Clause>| {
        left.iter()
            .flat_map(|first| {
                right.iter().map(move |second| {
                    first
                        .iter()
                        .chain(second.iter())
                        .cloned()
                        .collect::<Clause>()
                })
            })
            .collect()
    };
    match formula {
        Formula::Atom(predicate, arguments) => vec![vec![Literal {
            predicate: *predicate,
            positive,
            arguments: arguments.clone(),
        }]],
        Formula::True => {
            if positive {
                vec![]
            } else {
                vec![vec![]]
            }
        }
        Formula::False => {
            if positive {
                vec![vec![]]
            } else {
                vec![]
            }
        }
        Formula::Not(inner) => expected_cnf(inner, !positive),
        Formula::And(left, right) => {
            let left = expected_cnf(left, positive);
            let right = expected_cnf(right, positive);
            if positive {
                append(left, right)
            } else {
                product(left, right)
            }
        }
        Formula::Or(left, right) => {
            let left = expected_cnf(left, positive);
            let right = expected_cnf(right, positive);
            if positive {
                product(left, right)
            } else {
                append(left, right)
            }
        }
        Formula::Implies(left, right) => {
            let left = expected_cnf(left, !positive);
            let right = expected_cnf(right, positive);
            if positive {
                product(left, right)
            } else {
                append(left, right)
            }
        }
    }
}

fn formulas_by_size(maximum: usize) -> Vec<Vec<Formula>> {
    let mut sizes = vec![
        vec![],
        vec![atom(0), atom(1), Formula::True, Formula::False],
    ];
    for size in 2..=maximum {
        let mut formulas = sizes[size - 1]
            .iter()
            .map(|formula| Formula::Not(Box::new(duplicate(formula))))
            .collect::<Vec<_>>();
        for left_size in 1..size - 1 {
            let right_size = size - 1 - left_size;
            for left in &sizes[left_size] {
                for right in &sizes[right_size] {
                    formulas.push(Formula::And(
                        Box::new(duplicate(left)),
                        Box::new(duplicate(right)),
                    ));
                    formulas.push(Formula::Or(
                        Box::new(duplicate(left)),
                        Box::new(duplicate(right)),
                    ));
                    formulas.push(Formula::Implies(
                        Box::new(duplicate(left)),
                        Box::new(duplicate(right)),
                    ));
                }
            }
        }
        sizes.push(formulas);
    }
    sizes
}

#[test]
fn all_1652_small_formulas_preserve_truth_and_exact_order() {
    let sizes = formulas_by_size(5);
    assert_eq!(sizes.iter().map(Vec::len).sum::<usize>(), 1652);
    let mut evaluations = 0;
    for formula in sizes.iter().flatten() {
        let cnf = preprocess(formula, &signature(), &Limits::default()).unwrap();
        assert_eq!(cnf.clauses, expected_cnf(formula, true), "{formula:?}");
        let positive = normalize(formula, true, &signature(), &Limits::default()).unwrap();
        let negative = normalize(formula, false, &signature(), &Limits::default()).unwrap();
        for assignment in [[false, false], [false, true], [true, false], [true, true]] {
            let expected = truth(formula, &assignment);
            assert_eq!(nnf_truth(&positive.formula, &assignment), expected);
            assert_eq!(nnf_truth(&negative.formula, &assignment), !expected);
            assert_eq!(cnf_truth(&cnf.clauses, &assignment), expected);
            evaluations += 1;
        }
    }
    assert_eq!(evaluations, 6608);
}

#[test]
fn distribution_is_left_major_and_preserves_repeated_literals() {
    let left = Formula::And(Box::new(atom(0)), Box::new(atom(1)));
    let right = Formula::And(
        Box::new(atom(2)),
        Box::new(Formula::And(Box::new(atom(3)), Box::new(atom(4)))),
    );
    let result = preprocess(
        &Formula::Or(Box::new(left), Box::new(right)),
        &signature(),
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(
        result.clauses,
        vec![
            vec![literal(0, true), literal(2, true)],
            vec![literal(0, true), literal(3, true)],
            vec![literal(0, true), literal(4, true)],
            vec![literal(1, true), literal(2, true)],
            vec![literal(1, true), literal(3, true)],
            vec![literal(1, true), literal(4, true)],
        ]
    );
    let repeated = Formula::Or(
        Box::new(atom(0)),
        Box::new(Formula::Or(
            Box::new(atom(0)),
            Box::new(Formula::Not(Box::new(atom(0)))),
        )),
    );
    assert_eq!(
        preprocess(&repeated, &signature(), &Limits::default())
            .unwrap()
            .clauses,
        vec![vec![literal(0, true), literal(0, true), literal(0, false)]]
    );
}

#[test]
fn implication_polarity_and_constants_have_the_declared_encodings() {
    let implication = Formula::Implies(Box::new(atom(0)), Box::new(atom(1)));
    assert_eq!(
        normalize(&implication, false, &signature(), &Limits::default())
            .unwrap()
            .formula,
        Nnf::And(
            Box::new(Nnf::Literal(literal(0, true))),
            Box::new(Nnf::Literal(literal(1, false)))
        )
    );
    assert!(
        preprocess(&Formula::True, &signature(), &Limits::default())
            .unwrap()
            .clauses
            .is_empty()
    );
    assert_eq!(
        preprocess(&Formula::False, &signature(), &Limits::default())
            .unwrap()
            .clauses,
        vec![vec![]]
    );
    for formula in [
        Formula::Or(Box::new(Formula::True), Box::new(Formula::False)),
        Formula::Or(Box::new(Formula::False), Box::new(Formula::True)),
    ] {
        assert!(
            preprocess(&formula, &signature(), &Limits::default())
                .unwrap()
                .clauses
                .is_empty()
        );
    }
}

#[test]
fn ground_terms_are_preserved_and_counted_after_distribution() {
    let signature = Signature {
        functions: vec![0, 1, 2],
        predicates: vec![2],
    };
    let terms = vec![
        Term::Fun(1, vec![Term::Fun(0, vec![])]),
        Term::Fun(2, vec![Term::Fun(0, vec![]), Term::Fun(0, vec![])]),
    ];
    let formula = Formula::And(
        Box::new(Formula::Atom(0, terms.clone())),
        Box::new(Formula::Not(Box::new(Formula::Atom(0, terms.clone())))),
    );
    let before = duplicate(&formula);
    let result = preprocess(&formula, &signature, &Limits::default()).unwrap();
    assert_eq!(formula, before);
    assert_eq!(result.clauses, expected_cnf(&formula, true));
    assert_eq!(result.statistics.input_term_nodes, 10);
    assert_eq!(result.statistics.output_term_nodes, 10);
    assert_eq!(result.statistics.output_clauses, 2);
    assert_eq!(result.statistics.output_literals, 2);
}

#[test]
fn malformed_numeric_atoms_are_rejected_before_rewriting() {
    let signature = Signature {
        functions: vec![0, 1],
        predicates: vec![1],
    };
    let cases = [
        (Formula::Atom(0, vec![Term::Var(0)]), Invalid::FreeVariable),
        (
            Formula::Atom(0, vec![Term::Fun(2, vec![])]),
            Invalid::UnknownFunction(2),
        ),
        (
            Formula::Atom(0, vec![Term::Fun(1, vec![])]),
            Invalid::FunctionArity(1),
        ),
        (Formula::Atom(1, vec![]), Invalid::UnknownPredicate(1)),
        (Formula::Atom(0, vec![]), Invalid::PredicateArity(0)),
    ];
    for (bad, expected) in cases {
        // Even a branch that is true after distribution must be validated.
        let formula = Formula::Or(Box::new(Formula::True), Box::new(bad));
        assert_eq!(
            preprocess(&formula, &signature, &Limits::default()),
            Err(Error::Invalid(expected))
        );
    }
}

#[test]
fn clause_and_literal_limits_reject_the_complete_product() {
    let formula = Formula::Or(
        Box::new(Formula::And(Box::new(atom(0)), Box::new(atom(1)))),
        Box::new(Formula::And(Box::new(atom(2)), Box::new(atom(3)))),
    );
    let before = duplicate(&formula);
    for (limits, expected) in [
        (
            Limits {
                max_clauses: 3,
                ..Limits::default()
            },
            Resource::Clauses,
        ),
        (
            Limits {
                max_literals_per_clause: 1,
                ..Limits::default()
            },
            Resource::LiteralsPerClause,
        ),
        (
            Limits {
                max_literals: 7,
                ..Limits::default()
            },
            Resource::Literals,
        ),
    ] {
        assert_eq!(
            preprocess(&formula, &signature(), &limits),
            Err(Error::Resource(expected))
        );
        assert_eq!(formula, before);
    }
    let limits = Limits {
        max_clauses: 4,
        max_literals_per_clause: 2,
        max_literals: 8,
        ..Limits::default()
    };
    assert_eq!(
        preprocess(&formula, &signature(), &limits).unwrap().clauses,
        expected_cnf(&formula, true)
    );
}

#[test]
fn every_operation_and_storage_boundary_returns_only_error_or_full_result() {
    let formula = Formula::Or(
        Box::new(Formula::And(Box::new(atom(0)), Box::new(atom(1)))),
        Box::new(Formula::Implies(Box::new(atom(2)), Box::new(atom(3)))),
    );
    let before = duplicate(&formula);
    let complete = preprocess(&formula, &signature(), &Limits::default()).unwrap();
    for operations in 0..=complete.statistics.operations {
        let limits = Limits {
            max_operations: operations,
            ..Limits::default()
        };
        let result = preprocess(&formula, &signature(), &limits);
        if operations == complete.statistics.operations {
            assert_eq!(result.unwrap(), complete);
        } else {
            assert_eq!(result, Err(Error::Resource(Resource::Operations)));
        }
        assert_eq!(formula, before);
    }
    for stored in 0..=complete.statistics.allocated_nodes {
        let limits = Limits {
            max_stored_nodes: stored,
            ..Limits::default()
        };
        let result = preprocess(&formula, &signature(), &limits);
        if stored == complete.statistics.allocated_nodes {
            assert_eq!(result.unwrap(), complete);
        } else {
            assert_eq!(result, Err(Error::Resource(Resource::StoredNodes)));
        }
        assert_eq!(formula, before);
    }
}

#[test]
fn formula_term_and_zero_output_caps_are_separate() {
    let formula = Formula::Not(Box::new(atom(0)));
    assert_eq!(
        validate(
            &formula,
            &signature(),
            &Limits {
                max_formula_depth: 1,
                ..Limits::default()
            },
        ),
        Err(Error::Resource(Resource::FormulaDepth))
    );
    assert_eq!(
        validate(
            &formula,
            &signature(),
            &Limits {
                max_formula_nodes: 1,
                ..Limits::default()
            },
        ),
        Err(Error::Resource(Resource::FormulaNodes))
    );
    let term_formula = Formula::Atom(0, vec![Term::Fun(1, vec![Term::Fun(0, vec![])])]);
    let term_signature = Signature {
        functions: vec![0, 1],
        predicates: vec![1],
    };
    for (limits, expected) in [
        (
            Limits {
                max_term_depth: 1,
                ..Limits::default()
            },
            Resource::TermDepth,
        ),
        (
            Limits {
                max_input_term_nodes: 1,
                ..Limits::default()
            },
            Resource::InputTermNodes,
        ),
    ] {
        assert_eq!(
            preprocess(&term_formula, &term_signature, &limits),
            Err(Error::Resource(expected))
        );
    }
    let no_clauses = Limits {
        max_clauses: 0,
        max_literals: 0,
        max_literals_per_clause: 0,
        ..Limits::default()
    };
    assert!(preprocess(&Formula::True, &signature(), &no_clauses).is_ok());
    assert_eq!(
        preprocess(&Formula::False, &signature(), &no_clauses),
        Err(Error::Resource(Resource::Clauses))
    );
    let empty_clause = Limits {
        max_clauses: 1,
        ..no_clauses
    };
    assert!(preprocess(&Formula::False, &signature(), &empty_clause).is_ok());
    assert_eq!(
        preprocess(&atom(0), &signature(), &empty_clause),
        Err(Error::Resource(Resource::LiteralsPerClause))
    );
}

#[test]
fn fixed_recursion_caps_cannot_be_disabled_by_large_configuration() {
    let mut formula = atom(0);
    for _ in 0..64 {
        formula = Formula::Not(Box::new(formula));
    }
    let limits = Limits {
        max_formula_depth: usize::MAX,
        max_term_depth: usize::MAX,
        ..Limits::default()
    };
    assert_eq!(
        preprocess(&formula, &signature(), &limits),
        Err(Error::Resource(Resource::FormulaDepth))
    );
    let mut term = Term::Fun(0, vec![]);
    for _ in 0..64 {
        term = Term::Fun(1, vec![term]);
    }
    assert_eq!(
        preprocess(
            &Formula::Atom(0, vec![term]),
            &Signature {
                functions: vec![0, 1],
                predicates: vec![1],
            },
            &limits,
        ),
        Err(Error::Resource(Resource::TermDepth))
    );
}

fn reference_formula(formula: &Formula) -> ground_reference::Formula {
    use ground_reference::Formula as Old;
    match formula {
        Formula::Atom(id, terms) => Old::Atom(*id, terms.clone()),
        Formula::True => Old::True,
        Formula::False => Old::False,
        Formula::Not(body) => Old::Not(Box::new(reference_formula(body))),
        Formula::And(left, right) => Old::And(
            Box::new(reference_formula(left)),
            Box::new(reference_formula(right)),
        ),
        Formula::Or(left, right) => Old::Or(
            Box::new(reference_formula(left)),
            Box::new(reference_formula(right)),
        ),
        Formula::Implies(left, right) => Old::Implies(
            Box::new(reference_formula(left)),
            Box::new(reference_formula(right)),
        ),
    }
}

fn reference_error(error: ground_reference::Error) -> Error {
    use ground_reference::{Error as Old, Invalid as I, Resource as R};
    match error {
        Old::Invalid(invalid) => Error::Invalid(match invalid {
            I::FreeVariable => Invalid::FreeVariable,
            I::UnknownFunction(id) => Invalid::UnknownFunction(id),
            I::FunctionArity(id) => Invalid::FunctionArity(id),
            I::UnknownPredicate(id) => Invalid::UnknownPredicate(id),
            I::PredicateArity(id) => Invalid::PredicateArity(id),
        }),
        Old::Resource(resource) => Error::Resource(match resource {
            R::FormulaDepth => Resource::FormulaDepth,
            R::FormulaNodes => Resource::FormulaNodes,
            R::TermDepth => Resource::TermDepth,
            R::InputTermNodes => Resource::InputTermNodes,
            R::Clauses => Resource::Clauses,
            R::LiteralsPerClause => Resource::LiteralsPerClause,
            R::Literals => Resource::Literals,
            R::StoredNodes => Resource::StoredNodes,
            R::Operations => Resource::Operations,
            R::Arithmetic => Resource::Arithmetic,
        }),
    }
}

fn reference_statistics(value: ground_reference::Statistics) -> fang_fof_core::Statistics {
    fang_fof_core::Statistics {
        operations: value.operations,
        input_formula_nodes: value.input_formula_nodes,
        input_term_nodes: value.input_term_nodes,
        allocated_nodes: value.allocated_nodes,
        output_clauses: value.output_clauses,
        output_literals: value.output_literals,
        output_term_nodes: value.output_term_nodes,
    }
}

#[test]
fn ground_wrapper_matches_the_actual_frozen_reference() {
    let mut formulas = formulas_by_size(5)
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    // Ground, invalid-variable and malformed-signature cases exercise validation
    // order, including failures hidden under a tautological disjunct.
    formulas.extend([
        Formula::Atom(2, vec![Term::Fun(1, vec![Term::Fun(0, vec![])])]),
        Formula::Atom(2, vec![Term::Var(0)]),
        Formula::Atom(2, vec![Term::Fun(3, vec![])]),
        Formula::Atom(2, vec![Term::Fun(1, vec![])]),
        Formula::Atom(3, vec![]),
        Formula::Atom(2, vec![]),
        Formula::Or(
            Box::new(Formula::True),
            Box::new(Formula::Atom(2, vec![Term::Var(0)])),
        ),
    ]);
    let signature = Signature {
        functions: vec![0, 1],
        predicates: vec![0, 0, 1],
    };
    let old_signature = ground_reference::Signature {
        functions: signature.functions.clone(),
        predicates: signature.predicates.clone(),
    };
    let limits = [
        Limits::default(),
        Limits {
            max_operations: 0,
            ..Limits::default()
        },
        Limits {
            max_operations: 12,
            ..Limits::default()
        },
        Limits {
            max_stored_nodes: 0,
            ..Limits::default()
        },
        Limits {
            max_stored_nodes: 5,
            ..Limits::default()
        },
        Limits {
            max_formula_depth: 1,
            ..Limits::default()
        },
        Limits {
            max_formula_nodes: 2,
            ..Limits::default()
        },
        Limits {
            max_term_depth: 1,
            ..Limits::default()
        },
        Limits {
            max_input_term_nodes: 0,
            ..Limits::default()
        },
        Limits {
            max_clauses: 0,
            ..Limits::default()
        },
        Limits {
            max_literals: 0,
            ..Limits::default()
        },
        Limits {
            max_literals_per_clause: 0,
            ..Limits::default()
        },
    ];
    let mut comparisons = 0;
    for formula in &formulas {
        let old_formula = reference_formula(formula);
        for cap in &limits {
            let old_cap = ground_reference::Limits {
                max_formula_depth: cap.max_formula_depth,
                max_formula_nodes: cap.max_formula_nodes,
                max_term_depth: cap.max_term_depth,
                max_input_term_nodes: cap.max_input_term_nodes,
                max_clauses: cap.max_clauses,
                max_literals_per_clause: cap.max_literals_per_clause,
                max_literals: cap.max_literals,
                max_stored_nodes: cap.max_stored_nodes,
                max_operations: cap.max_operations,
            };
            let expected = ground_reference::preprocess(&old_formula, &old_signature, &old_cap)
                .map(|value| fang_fof_core::Preprocessed {
                    clauses: value.clauses,
                    statistics: reference_statistics(value.statistics),
                })
                .map_err(reference_error);
            assert_eq!(
                preprocess(formula, &signature, cap),
                expected,
                "{formula:?}, {cap:?}"
            );
            assert_eq!(
                validate(formula, &signature, cap),
                ground_reference::validate(&old_formula, &old_signature, &old_cap)
                    .map(reference_statistics)
                    .map_err(reference_error)
            );
            comparisons += 1;
        }
    }
    assert_eq!(comparisons, 19_908);
}
