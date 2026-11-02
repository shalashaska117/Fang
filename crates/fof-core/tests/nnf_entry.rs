use fang::syntax::{Literal, Term};
use fang_fof_core::nnf_entry::clausify_nnf_from;
use fang_fof_core::{
    Error, Formula, Limits, Nnf, Resource, Signature, Statistics, VariableScope,
    preprocess_with_scope,
};

fn literal(predicate: u32, positive: bool, arguments: Vec<Term>) -> Literal {
    Literal {
        positive,
        predicate,
        arguments,
    }
}

fn atom(predicate: u32) -> Nnf {
    Nnf::Literal(literal(predicate, true, vec![]))
}

fn product() -> Nnf {
    Nnf::Or(
        Box::new(Nnf::And(Box::new(atom(0)), Box::new(atom(1)))),
        Box::new(Nnf::And(Box::new(atom(2)), Box::new(atom(3)))),
    )
}

#[test]
fn constants_distinguish_empty_problem_from_empty_clause() {
    let limits = Limits::default();
    let truth = clausify_nnf_from(&Nnf::True, &limits, Statistics::default()).unwrap();
    let falsity = clausify_nnf_from(&Nnf::False, &limits, Statistics::default()).unwrap();
    assert!(truth.clauses.is_empty());
    assert_eq!(truth.statistics.operations, 1);
    assert_eq!(truth.statistics.allocated_nodes, 0);
    assert_eq!(falsity.clauses, vec![vec![]]);
    assert_eq!(falsity.statistics.operations, 1);
    assert_eq!(falsity.statistics.allocated_nodes, 1);
}

#[test]
fn product_order_is_left_outer_right_inner() {
    let result = clausify_nnf_from(&product(), &Limits::default(), Statistics::default()).unwrap();
    let row = |a, b| vec![literal(a, true, vec![]), literal(b, true, vec![])];
    assert_eq!(
        result.clauses,
        vec![row(0, 2), row(0, 3), row(1, 2), row(1, 3)]
    );
    assert_eq!(result.statistics.output_clauses, 4);
    assert_eq!(result.statistics.output_literals, 8);
}

#[test]
fn literals_duplicates_and_scope_holes_remain_exact() {
    let arguments = vec![Term::Var(7), Term::Fun(1, vec![Term::Var(2)])];
    let positive = literal(0, true, arguments.clone());
    let negative = literal(0, false, arguments);
    let formula = Nnf::Or(
        Box::new(Nnf::Literal(positive.clone())),
        Box::new(Nnf::Or(
            Box::new(Nnf::Literal(negative.clone())),
            Box::new(Nnf::Literal(positive.clone())),
        )),
    );
    let result = clausify_nnf_from(&formula, &Limits::default(), Statistics::default()).unwrap();
    assert_eq!(
        result.clauses,
        vec![vec![positive.clone(), negative, positive]]
    );
}

#[test]
fn carried_counters_accumulate_and_output_fields_are_replaced() {
    let before = Statistics {
        operations: 7,
        input_formula_nodes: 11,
        input_term_nodes: 13,
        allocated_nodes: 17,
        output_clauses: 19,
        output_literals: 23,
        output_term_nodes: 29,
    };
    let result = clausify_nnf_from(&Nnf::False, &Limits::default(), before).unwrap();
    assert_eq!(
        result.statistics,
        Statistics {
            operations: 8,
            allocated_nodes: 18,
            output_clauses: 1,
            output_literals: 0,
            output_term_nodes: 0,
            ..before
        }
    );
}

#[test]
fn entry_guards_reject_over_cap_carried_counters() {
    let limits = Limits {
        max_operations: 3,
        max_stored_nodes: 5,
        ..Limits::default()
    };
    for operations in [4, usize::MAX] {
        assert_eq!(
            clausify_nnf_from(
                &Nnf::True,
                &limits,
                Statistics {
                    operations,
                    ..Statistics::default()
                },
            ),
            Err(Error::Resource(Resource::Operations)),
        );
    }
    for allocated_nodes in [6, usize::MAX] {
        assert_eq!(
            clausify_nnf_from(
                &Nnf::True,
                &limits,
                Statistics {
                    allocated_nodes,
                    ..Statistics::default()
                },
            ),
            Err(Error::Resource(Resource::StoredNodes)),
        );
    }
}

#[test]
fn saturated_machine_counters_return_typed_errors() {
    let limits = Limits {
        max_operations: usize::MAX,
        max_stored_nodes: usize::MAX,
        ..Limits::default()
    };
    assert_eq!(
        clausify_nnf_from(
            &Nnf::True,
            &limits,
            Statistics {
                operations: usize::MAX,
                ..Statistics::default()
            },
        ),
        Err(Error::Resource(Resource::Operations)),
    );
    assert_eq!(
        clausify_nnf_from(
            &Nnf::False,
            &limits,
            Statistics {
                allocated_nodes: usize::MAX,
                ..Statistics::default()
            },
        ),
        Err(Error::Resource(Resource::StoredNodes)),
    );
}

#[test]
fn exact_and_short_operation_storage_caps_keep_the_carried_offset() {
    let formula = product();
    let before = Statistics {
        operations: 5,
        allocated_nodes: 7,
        ..Statistics::default()
    };
    let full = clausify_nnf_from(&formula, &Limits::default(), before).unwrap();
    let exact = Limits {
        max_operations: full.statistics.operations,
        max_stored_nodes: full.statistics.allocated_nodes,
        ..Limits::default()
    };
    assert_eq!(clausify_nnf_from(&formula, &exact, before), Ok(full));
    assert_eq!(
        clausify_nnf_from(
            &formula,
            &Limits {
                max_operations: exact.max_operations - 1,
                ..exact
            },
            before,
        ),
        Err(Error::Resource(Resource::Operations)),
    );
    assert_eq!(
        clausify_nnf_from(
            &formula,
            &Limits {
                max_stored_nodes: exact.max_stored_nodes - 1,
                ..exact
            },
            before,
        ),
        Err(Error::Resource(Resource::StoredNodes)),
    );
}

#[test]
fn zero_and_shape_limits_remain_typed() {
    for (limits, expected) in [
        (
            Limits {
                max_operations: 0,
                ..Limits::default()
            },
            Resource::Operations,
        ),
        (
            Limits {
                max_stored_nodes: 0,
                ..Limits::default()
            },
            Resource::StoredNodes,
        ),
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
            clausify_nnf_from(&product(), &limits, Statistics::default()),
            Err(Error::Resource(expected)),
        );
    }
}

fn as_formula(formula: &Nnf) -> Formula {
    match formula {
        Nnf::Literal(literal) => {
            let atom = Formula::Atom(literal.predicate, literal.arguments.clone());
            if literal.positive {
                atom
            } else {
                Formula::Not(Box::new(atom))
            }
        }
        Nnf::True => Formula::True,
        Nnf::False => Formula::False,
        Nnf::And(left, right) => {
            Formula::And(Box::new(as_formula(left)), Box::new(as_formula(right)))
        }
        Nnf::Or(left, right) => {
            Formula::Or(Box::new(as_formula(left)), Box::new(as_formula(right)))
        }
    }
}

#[test]
fn raw_clause_lists_agree_with_the_existing_checked_preprocessing_path() {
    let signature = Signature {
        functions: vec![0, 1],
        predicates: vec![0, 0, 0, 0, 2],
    };
    let formulas = [
        Nnf::True,
        Nnf::False,
        product(),
        Nnf::And(Box::new(product()), Box::new(atom(3))),
        Nnf::Literal(literal(
            4,
            false,
            vec![Term::Var(7), Term::Fun(1, vec![Term::Var(2)])],
        )),
    ];
    for formula in formulas {
        let converted = as_formula(&formula);
        let old = preprocess_with_scope(
            &converted,
            &signature,
            VariableScope::Bound(8),
            &Limits::default(),
        )
        .unwrap();
        let direct =
            clausify_nnf_from(&formula, &Limits::default(), Statistics::default()).unwrap();
        assert_eq!(direct.clauses, old.clauses);
    }
}
