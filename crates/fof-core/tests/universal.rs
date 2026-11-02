use fang::syntax::{Clause, Literal, Term};
use fang_fof_core::{
    Error, Formula, Invalid, Limits, Nnf, Resource, Signature, VariableScope, normalize,
    normalize_with_scope, preprocess, preprocess_with_scope, validate, validate_with_scope,
};

fn signature() -> Signature {
    Signature {
        functions: vec![0, 1, 2],
        predicates: vec![1, 2],
    }
}

fn atom(id: u32) -> Formula {
    Formula::Atom(0, vec![Term::Var(id)])
}

#[test]
fn scope_boundaries_reject_unbound_ids_before_rewriting() {
    for (id, count, accepted) in [
        (0, 0, false),
        (0, 1, true),
        (1, 1, false),
        (3, 4, true),
        (4, 4, false),
        (u32::MAX - 1, u32::MAX, true),
        (u32::MAX, u32::MAX, false),
    ] {
        // A true disjunct must not hide an invalid ID in a nested term.
        let formula = Formula::Or(
            Box::new(Formula::True),
            Box::new(Formula::Atom(0, vec![Term::Fun(1, vec![Term::Var(id)])])),
        );
        let result = preprocess_with_scope(
            &formula,
            &signature(),
            VariableScope::Bound(count),
            &Limits::default(),
        );
        if accepted {
            assert!(result.unwrap().clauses.is_empty());
        } else {
            assert_eq!(result, Err(Error::Invalid(Invalid::FreeVariable)));
        }
    }
}

#[test]
fn unused_prefix_positions_and_repeated_variables_keep_exact_ids() {
    let args = vec![Term::Var(3), Term::Fun(2, vec![Term::Var(1), Term::Var(3)])];
    let formula = Formula::Implies(Box::new(Formula::Atom(1, args.clone())), Box::new(atom(3)));
    let result = preprocess_with_scope(
        &formula,
        &signature(),
        VariableScope::Bound(4),
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(
        result.clauses,
        vec![vec![
            Literal {
                positive: false,
                predicate: 1,
                arguments: args,
            },
            Literal {
                positive: true,
                predicate: 0,
                arguments: vec![Term::Var(3)],
            },
        ]]
    );
    assert_eq!(result.statistics.input_term_nodes, 5);
    assert_eq!(result.statistics.output_term_nodes, 5);
}

#[test]
fn bound_zero_is_exactly_the_ground_wrappers() {
    let formulas = [
        Formula::True,
        Formula::False,
        Formula::Atom(0, vec![Term::Fun(0, vec![])]),
        atom(0),
        Formula::Not(Box::new(atom(1))),
        Formula::Or(Box::new(Formula::True), Box::new(atom(u32::MAX))),
    ];
    for formula in formulas {
        for operations in [0, 1, 2, 5, 100] {
            let limits = Limits {
                max_operations: operations,
                ..Limits::default()
            };
            assert_eq!(
                validate(&formula, &signature(), &limits),
                validate_with_scope(&formula, &signature(), VariableScope::Bound(0), &limits)
            );
            assert_eq!(
                preprocess(&formula, &signature(), &limits),
                preprocess_with_scope(&formula, &signature(), VariableScope::Bound(0), &limits)
            );
            for positive in [false, true] {
                assert_eq!(
                    normalize(&formula, positive, &signature(), &limits),
                    normalize_with_scope(
                        &formula,
                        positive,
                        &signature(),
                        VariableScope::Bound(0),
                        &limits
                    )
                );
            }
        }
    }
}

#[test]
fn variable_copies_obey_every_work_and_storage_boundary() {
    let formula = Formula::Or(
        Box::new(Formula::And(Box::new(atom(0)), Box::new(atom(1)))),
        Box::new(Formula::And(Box::new(atom(2)), Box::new(atom(3)))),
    );
    let full = preprocess_with_scope(
        &formula,
        &signature(),
        VariableScope::Bound(4),
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(full.clauses.len(), 4);
    assert_eq!(full.statistics.output_term_nodes, 8);
    for work in 0..=full.statistics.operations {
        let result = preprocess_with_scope(
            &formula,
            &signature(),
            VariableScope::Bound(4),
            &Limits {
                max_operations: work,
                ..Limits::default()
            },
        );
        if work == full.statistics.operations {
            assert_eq!(result.unwrap(), full);
        } else {
            assert_eq!(result, Err(Error::Resource(Resource::Operations)));
        }
    }
    for nodes in 0..=full.statistics.allocated_nodes {
        let result = preprocess_with_scope(
            &formula,
            &signature(),
            VariableScope::Bound(4),
            &Limits {
                max_stored_nodes: nodes,
                ..Limits::default()
            },
        );
        if nodes == full.statistics.allocated_nodes {
            assert_eq!(result.unwrap(), full);
        } else {
            assert_eq!(result, Err(Error::Resource(Resource::StoredNodes)));
        }
    }
    assert_eq!(
        preprocess_with_scope(
            &formula,
            &signature(),
            VariableScope::Bound(4),
            &Limits {
                max_clauses: 3,
                ..Limits::default()
            }
        ),
        Err(Error::Resource(Resource::Clauses))
    );
}

fn next(seed: &mut u32) -> u32 {
    *seed = seed.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
    *seed
}

fn term(seed: &mut u32, depth: usize) -> Term {
    let value = next(seed);
    if depth == 0 || value.is_multiple_of(3) {
        Term::Var((value >> 8) % 4)
    } else if value % 3 == 1 {
        Term::Fun(0, vec![])
    } else if value & 16 == 0 {
        Term::Fun(1, vec![term(seed, depth - 1)])
    } else {
        Term::Fun(2, vec![term(seed, depth - 1), term(seed, depth - 1)])
    }
}

fn formula(seed: &mut u32, depth: usize) -> Formula {
    let value = next(seed);
    if depth == 0 || value.is_multiple_of(7) {
        if value & 32 == 0 {
            Formula::Atom(0, vec![term(seed, 3)])
        } else {
            Formula::Atom(1, vec![term(seed, 3), term(seed, 3)])
        }
    } else {
        match value % 7 {
            1 => Formula::True,
            2 => Formula::False,
            3 => Formula::Not(Box::new(formula(seed, depth - 1))),
            4 => Formula::And(
                Box::new(formula(seed, depth - 1)),
                Box::new(formula(seed, depth - 1)),
            ),
            5 => Formula::Or(
                Box::new(formula(seed, depth - 1)),
                Box::new(formula(seed, depth - 1)),
            ),
            _ => Formula::Implies(
                Box::new(formula(seed, depth - 1)),
                Box::new(formula(seed, depth - 1)),
            ),
        }
    }
}

fn value(term: &Term, valuation: u32) -> bool {
    match term {
        Term::Var(id) => valuation & (1 << id) != 0,
        Term::Fun(0, args) => {
            assert!(args.is_empty());
            false
        }
        Term::Fun(1, args) => !value(&args[0], valuation),
        Term::Fun(2, args) => value(&args[0], valuation) ^ value(&args[1], valuation),
        _ => panic!("Invalid generated function"),
    }
}

fn atom_truth(predicate: u32, arguments: &[Term], valuation: u32) -> bool {
    match predicate {
        0 => value(&arguments[0], valuation),
        1 => value(&arguments[0], valuation) == value(&arguments[1], valuation),
        _ => panic!("Invalid generated predicate"),
    }
}

fn truth(formula: &Formula, valuation: u32) -> bool {
    match formula {
        Formula::Atom(predicate, args) => atom_truth(*predicate, args, valuation),
        Formula::True => true,
        Formula::False => false,
        Formula::Not(body) => !truth(body, valuation),
        Formula::And(left, right) => truth(left, valuation) && truth(right, valuation),
        Formula::Or(left, right) => truth(left, valuation) || truth(right, valuation),
        Formula::Implies(left, right) => !truth(left, valuation) || truth(right, valuation),
    }
}

fn nnf_truth(formula: &Nnf, valuation: u32) -> bool {
    match formula {
        Nnf::Literal(literal) => {
            atom_truth(literal.predicate, &literal.arguments, valuation) == literal.positive
        }
        Nnf::True => true,
        Nnf::False => false,
        Nnf::And(left, right) => nnf_truth(left, valuation) && nnf_truth(right, valuation),
        Nnf::Or(left, right) => nnf_truth(left, valuation) || nnf_truth(right, valuation),
    }
}

fn cnf_truth(clauses: &[Clause], valuation: u32) -> bool {
    clauses.iter().all(|clause| {
        clause.iter().any(|literal| {
            atom_truth(literal.predicate, &literal.arguments, valuation) == literal.positive
        })
    })
}

#[test]
fn seeded_first_order_bodies_preserve_all_sixteen_valuations() {
    let mut count = 0;
    for mut seed in [0xfa16_b001, 0xfa16_b002, 0xfa16_b003, 0xfa16_b004] {
        for _ in 0..256 {
            let body = formula(&mut seed, 4);
            let clauses = preprocess_with_scope(
                &body,
                &signature(),
                VariableScope::Bound(4),
                &Limits::default(),
            )
            .unwrap();
            let negative = normalize_with_scope(
                &body,
                false,
                &signature(),
                VariableScope::Bound(4),
                &Limits::default(),
            )
            .unwrap();
            for valuation in 0..16 {
                assert_eq!(
                    cnf_truth(&clauses.clauses, valuation),
                    truth(&body, valuation)
                );
                assert_eq!(
                    nnf_truth(&negative.formula, valuation),
                    !truth(&body, valuation)
                );
                count += 1;
            }
        }
    }
    assert_eq!(count, 16_384);
}
