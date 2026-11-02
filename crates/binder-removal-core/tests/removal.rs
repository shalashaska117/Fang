use fang::syntax::{Literal, Term};
use fang_binder_removal_core::{Error, Limits, Resource, Statistics, remove_universals};
use fang_fof_core::Nnf as QuantifierFree;
use fang_quantified_fof_core::Nnf;

fn literal(positive: bool, variable: u32) -> Literal {
    Literal {
        positive,
        predicate: 0,
        arguments: vec![Term::Var(variable)],
    }
}

fn bounded_example() -> Nnf {
    Nnf::Forall(
        7,
        Box::new(Nnf::And(
            Box::new(Nnf::Literal(literal(true, 7))),
            Box::new(Nnf::Literal(literal(false, 7))),
        )),
    )
}

#[test]
fn leaves_and_constants_keep_their_exact_values() {
    let original = Literal {
        positive: false,
        predicate: u32::MAX,
        arguments: vec![Term::Fun(
            u32::MAX,
            vec![Term::Var(19), Term::Fun(3, vec![])],
        )],
    };
    let expected = QuantifierFree::Literal(original.clone());
    let output = remove_universals(Nnf::Literal(original), &Limits::default()).unwrap();
    assert_eq!(output.formula, expected);
    assert_eq!(
        output.statistics,
        Statistics {
            operations: 1,
            output_nodes: 1
        }
    );
    assert_eq!(
        remove_universals(Nnf::True, &Limits::default())
            .unwrap()
            .formula,
        QuantifierFree::True
    );
    assert_eq!(
        remove_universals(Nnf::False, &Limits::default())
            .unwrap()
            .formula,
        QuantifierFree::False
    );
}

#[test]
fn literal_argument_storage_is_moved() {
    let mut arguments = Vec::with_capacity(17);
    arguments.push(Term::Fun(4, vec![Term::Var(9)]));
    let pointer = arguments.as_ptr();
    let capacity = arguments.capacity();
    let source = Nnf::Forall(
        9,
        Box::new(Nnf::Literal(Literal {
            positive: true,
            predicate: 2,
            arguments,
        })),
    );
    let output = remove_universals(source, &Limits::default()).unwrap();
    let QuantifierFree::Literal(literal) = output.formula else {
        panic!("expected literal")
    };
    assert_eq!(literal.arguments.as_ptr(), pointer);
    assert_eq!(literal.arguments.capacity(), capacity);
}

#[test]
fn binary_order_polarity_and_duplicates_are_preserved() {
    let source = Nnf::Or(
        Box::new(Nnf::Forall(0, Box::new(Nnf::Literal(literal(false, 0))))),
        Box::new(Nnf::And(
            Box::new(Nnf::Literal(literal(true, 2))),
            Box::new(Nnf::Literal(literal(true, 2))),
        )),
    );
    let expected = QuantifierFree::Or(
        Box::new(QuantifierFree::Literal(literal(false, 0))),
        Box::new(QuantifierFree::And(
            Box::new(QuantifierFree::Literal(literal(true, 2))),
            Box::new(QuantifierFree::Literal(literal(true, 2))),
        )),
    );
    assert_eq!(
        remove_universals(source, &Limits::default())
            .unwrap()
            .formula,
        expected
    );
}

#[test]
fn every_unused_universal_is_counted() {
    let source = Nnf::Forall(3, Box::new(Nnf::Forall(11, Box::new(Nnf::True))));
    let output = remove_universals(source, &Limits::default()).unwrap();
    assert_eq!(output.formula, QuantifierFree::True);
    assert_eq!(
        output.statistics,
        Statistics {
            operations: 3,
            output_nodes: 1
        }
    );
}

#[test]
fn residual_existentials_are_rejected_at_any_visited_position() {
    for source in [
        Nnf::Exists(12, Box::new(Nnf::True)),
        Nnf::Forall(0, Box::new(Nnf::Exists(12, Box::new(Nnf::True)))),
        Nnf::And(
            Box::new(Nnf::True),
            Box::new(Nnf::Exists(12, Box::new(Nnf::False))),
        ),
        Nnf::Or(
            Box::new(Nnf::Exists(12, Box::new(Nnf::True))),
            Box::new(Nnf::True),
        ),
    ] {
        assert_eq!(
            remove_universals(source, &Limits::default()),
            Err(Error::ResidualExistential(12))
        );
    }
}

#[test]
fn zero_caps_return_typed_resources() {
    assert_eq!(
        remove_universals(
            Nnf::True,
            &Limits {
                max_operations: 0,
                ..Limits::default()
            }
        ),
        Err(Error::Resource(Resource::Operations))
    );
    assert_eq!(
        remove_universals(
            Nnf::True,
            &Limits {
                max_output_nodes: 0,
                ..Limits::default()
            }
        ),
        Err(Error::Resource(Resource::OutputNodes))
    );
    assert_eq!(
        remove_universals(
            Nnf::True,
            &Limits {
                max_formula_depth: 0,
                ..Limits::default()
            }
        ),
        Err(Error::Resource(Resource::FormulaDepth))
    );
}

#[test]
fn exact_and_one_short_caps_are_distinguished() {
    let exact = Limits {
        max_formula_depth: 3,
        max_operations: 4,
        max_output_nodes: 3,
    };
    let output = remove_universals(bounded_example(), &exact).unwrap();
    assert_eq!(
        output.statistics,
        Statistics {
            operations: 4,
            output_nodes: 3
        }
    );
    assert_eq!(
        remove_universals(
            bounded_example(),
            &Limits {
                max_operations: 3,
                ..exact
            }
        ),
        Err(Error::Resource(Resource::Operations))
    );
    assert_eq!(
        remove_universals(
            bounded_example(),
            &Limits {
                max_output_nodes: 2,
                ..exact
            }
        ),
        Err(Error::Resource(Resource::OutputNodes))
    );
    assert_eq!(
        remove_universals(
            bounded_example(),
            &Limits {
                max_formula_depth: 2,
                ..exact
            }
        ),
        Err(Error::Resource(Resource::FormulaDepth))
    );
}

#[test]
fn hard_depth_cap_cannot_be_disabled() {
    fn chain(count: u32) -> Nnf {
        let mut result = Nnf::True;
        for id in 0..count {
            result = Nnf::Forall(id, Box::new(result));
        }
        result
    }
    let limits = Limits {
        max_formula_depth: usize::MAX,
        ..Limits::default()
    };
    assert!(remove_universals(chain(63), &limits).is_ok());
    assert_eq!(
        remove_universals(chain(64), &limits),
        Err(Error::Resource(Resource::FormulaDepth))
    );
}

fn holds_literal(literal: &Literal, values: &[bool; 2]) -> bool {
    let [Term::Var(id)] = literal.arguments.as_slice() else {
        panic!("test vocabulary")
    };
    values[*id as usize] == literal.positive
}

fn holds(source: &Nnf, values: [bool; 2]) -> bool {
    match source {
        Nnf::Literal(literal) => holds_literal(literal, &values),
        Nnf::True => true,
        Nnf::False => false,
        Nnf::And(left, right) => holds(left, values) && holds(right, values),
        Nnf::Or(left, right) => holds(left, values) || holds(right, values),
        Nnf::Forall(id, body) => [false, true].into_iter().all(|value| {
            let mut changed = values;
            changed[*id as usize] = value;
            holds(body, changed)
        }),
        Nnf::Exists(id, body) => [false, true].into_iter().any(|value| {
            let mut changed = values;
            changed[*id as usize] = value;
            holds(body, changed)
        }),
    }
}

fn holds_output(source: &QuantifierFree, values: &[bool; 2]) -> bool {
    match source {
        QuantifierFree::Literal(literal) => holds_literal(literal, values),
        QuantifierFree::True => true,
        QuantifierFree::False => false,
        QuantifierFree::And(left, right) => {
            holds_output(left, values) && holds_output(right, values)
        }
        QuantifierFree::Or(left, right) => {
            holds_output(left, values) || holds_output(right, values)
        }
    }
}

fn valuations() -> [[bool; 2]; 4] {
    [[false, false], [false, true], [true, false], [true, true]]
}

#[test]
fn scope_premise_cannot_be_replaced_by_unique_binder_ids() {
    let source = Nnf::Or(
        Box::new(Nnf::Forall(0, Box::new(Nnf::Literal(literal(true, 0))))),
        Box::new(Nnf::Literal(literal(false, 0))),
    );
    assert!(
        !valuations()
            .into_iter()
            .all(|values| holds(&source, values))
    );
    let output = remove_universals(source, &Limits::default()).unwrap();
    assert!(
        valuations()
            .into_iter()
            .all(|values| holds_output(&output.formula, &values))
    );
}

#[test]
fn lexical_closure_does_not_replace_global_binder_freshness() {
    let source = Nnf::Or(
        Box::new(Nnf::Forall(0, Box::new(Nnf::Literal(literal(true, 0))))),
        Box::new(Nnf::Forall(0, Box::new(Nnf::Literal(literal(false, 0))))),
    );
    assert!(
        !valuations()
            .into_iter()
            .all(|values| holds(&source, values))
    );
    let output = remove_universals(source, &Limits::default()).unwrap();
    assert!(
        valuations()
            .into_iter()
            .all(|values| holds_output(&output.formula, &values))
    );
}

#[test]
fn rectified_binary_examples_preserve_universal_closure() {
    for positive_left in [false, true] {
        for positive_right in [false, true] {
            for conjunction in [false, true] {
                let left = Box::new(Nnf::Forall(
                    0,
                    Box::new(Nnf::Literal(literal(positive_left, 0))),
                ));
                let right = Box::new(Nnf::Forall(
                    1,
                    Box::new(Nnf::Literal(literal(positive_right, 1))),
                ));
                let source = if conjunction {
                    Nnf::And(left, right)
                } else {
                    Nnf::Or(left, right)
                };
                let original = valuations()
                    .into_iter()
                    .all(|values| holds(&source, values));
                let output = remove_universals(source, &Limits::default()).unwrap();
                let erased = valuations()
                    .into_iter()
                    .all(|values| holds_output(&output.formula, &values));
                assert_eq!(original, erased);
            }
        }
    }
}
