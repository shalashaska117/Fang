use fang::syntax::Term;
use fang_equality_inference_core::{Atom, Error as InputError, Limits, Literal};
use fang_equality_paramodulation_core::{
    Direction, Error, Position, Resource, Root, Witness, paramodulate,
};

fn c(id: u32) -> Term {
    Term::Fun(id, vec![])
}
fn g(term: Term) -> Term {
    Term::Fun(2, vec![term])
}
fn p(positive: bool, term: Term) -> Literal {
    Literal {
        positive,
        atom: Atom::Predicate(0, vec![term]),
    }
}
fn eq(positive: bool, left: Term, right: Term) -> Literal {
    Literal {
        positive,
        atom: Atom::Equal(left, right),
    }
}
fn position(path: Vec<usize>) -> Position {
    Position {
        literal: 0,
        root: Root::Argument(0),
        path,
    }
}
fn witness<'a>(position: &'a Position, substitution: &'a [(u32, Term)]) -> Witness<'a> {
    Witness {
        source_pivot: 0,
        direction: Direction::LeftToRight,
        position,
        substitution,
    }
}
const FUNCTIONS: &[usize] = &[0, 0, 1];
const PREDICATES: &[usize] = &[1];

#[test]
fn one_position_preserves_order_polarity_and_duplicates() {
    let source = [p(true, c(1)), eq(true, c(0), c(1)), p(true, c(1))];
    let target = [p(false, g(g(c(0)))), p(true, c(0)), p(true, c(0))];
    let at = position(vec![0, 0]);
    let proof = Witness {
        source_pivot: 1,
        ..witness(&at, &[])
    };
    let result = paramodulate(
        &source,
        &target,
        proof,
        FUNCTIONS,
        PREDICATES,
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(
        result.clause,
        [
            p(true, c(1)),
            p(true, c(1)),
            p(false, g(g(c(1)))),
            p(true, c(0)),
            p(true, c(0))
        ]
    );
    assert_eq!(target[0], p(false, g(g(c(0)))));
}

#[test]
fn equality_sides_and_reverse_orientation_are_distinct_positions() {
    let source = [eq(true, c(0), c(1))];
    let target = [eq(false, c(1), c(1))];
    for root in [Root::EqualityLeft, Root::EqualityRight] {
        let at = Position {
            literal: 0,
            root,
            path: vec![],
        };
        let proof = Witness {
            direction: Direction::RightToLeft,
            ..witness(&at, &[])
        };
        let result =
            paramodulate(&source, &target, proof, FUNCTIONS, &[], &Limits::default()).unwrap();
        let expected = if root == Root::EqualityLeft {
            eq(false, c(0), c(1))
        } else {
            eq(false, c(1), c(0))
        };
        assert_eq!(result.clause, [expected]);
    }
}

#[test]
fn substitution_is_simultaneous_and_position_is_in_the_instance() {
    let source = [eq(true, Term::Var(0), c(1)), p(true, Term::Var(0))];
    let target = [p(false, Term::Var(1)), p(true, Term::Var(1))];
    let image = g(Term::Var(2));
    let substitution = [(0, Term::Var(2)), (1, image.clone()), (2, c(0))];
    let at = position(vec![0]);
    let result = paramodulate(
        &source,
        &target,
        witness(&at, &substitution),
        FUNCTIONS,
        PREDICATES,
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(
        result.clause,
        [p(true, Term::Var(2)), p(false, g(c(1))), p(true, image)]
    );
}

#[test]
fn invalid_witnesses_and_rule_guards_are_explicit() {
    let source = [eq(true, c(0), c(1))];
    let target = [p(true, c(0))];
    let at = position(vec![]);
    let run = |source: &[Literal], target: &[Literal], w: Witness<'_>| {
        paramodulate(source, target, w, FUNCTIONS, PREDICATES, &Limits::default())
    };
    assert_eq!(
        run(
            &source,
            &target,
            Witness {
                source_pivot: 1,
                ..witness(&at, &[])
            }
        ),
        Err(Error::SourcePivot)
    );
    assert_eq!(
        run(&[eq(false, c(0), c(1))], &target, witness(&at, &[])),
        Err(Error::ExpectedPositiveEquality)
    );
    assert_eq!(
        run(&[p(true, c(0))], &target, witness(&at, &[])),
        Err(Error::ExpectedPositiveEquality)
    );
    assert_eq!(
        run(&source, &[p(true, c(1))], witness(&at, &[])),
        Err(Error::NotMatched)
    );
    let wrong_path = position(vec![0]);
    assert_eq!(
        run(&source, &target, witness(&wrong_path, &[])),
        Err(Error::InvalidPath)
    );
    let wrong_root = Position {
        root: Root::EqualityLeft,
        ..at.clone()
    };
    assert_eq!(
        run(&source, &target, witness(&wrong_root, &[])),
        Err(Error::TargetTerm)
    );
    let wrong_literal = Position {
        literal: 1,
        ..at.clone()
    };
    assert_eq!(
        run(&source, &target, witness(&wrong_literal, &[])),
        Err(Error::TargetLiteral)
    );
    assert_eq!(
        run(
            &[eq(true, Term::Var(0), c(1))],
            &[p(true, Term::Var(0))],
            witness(&at, &[])
        ),
        Err(Error::VariableOverlap)
    );
    assert_eq!(
        run(&source, &target, witness(&at, &[(1, c(0)), (1, c(1))])),
        Err(Error::Input(InputError::SubstitutionOrder))
    );
    assert_eq!(
        run(&source, &target, witness(&at, &[(99, c(99))])),
        Err(Error::Input(InputError::UnknownFunction))
    );
}

#[test]
fn complete_input_validation_precedes_pivot_and_path_guards() {
    let at = position(vec![999]);
    let proof = Witness {
        source_pivot: 999,
        ..witness(&at, &[])
    };
    assert_eq!(
        paramodulate(
            &[eq(true, c(99), c(0))],
            &[],
            proof,
            FUNCTIONS,
            PREDICATES,
            &Limits::default()
        ),
        Err(Error::Input(InputError::UnknownFunction))
    );
    assert_eq!(
        paramodulate(
            &[eq(true, c(0), c(1))],
            &[p(true, c(99))],
            proof,
            FUNCTIONS,
            PREDICATES,
            &Limits::default()
        ),
        Err(Error::Input(InputError::UnknownFunction))
    );
    let low = Limits {
        max_operations: 0,
        ..Limits::default()
    };
    assert_eq!(
        paramodulate(
            &[eq(true, c(0), c(1))],
            &[p(true, c(0))],
            proof,
            FUNCTIONS,
            PREDICATES,
            &low
        ),
        Err(Error::Input(InputError::Operations))
    );
}

#[test]
fn insertion_depth_is_checked_without_mutating_inputs() {
    let source = [eq(true, c(0), g(c(1)))];
    let target = [p(true, g(g(c(0))))];
    let before = target.clone();
    let at = position(vec![0, 0]);
    let limits = Limits {
        max_depth: 3,
        ..Limits::default()
    };
    assert_eq!(
        paramodulate(
            &source,
            &target,
            witness(&at, &[]),
            FUNCTIONS,
            PREDICATES,
            &limits
        ),
        Err(Error::Occurrence(
            fang_equality_occurrence_core::Error::Depth
        ))
    );
    assert_eq!(target, before);
}

#[test]
fn aggregate_resource_boundaries_cover_both_premises_and_replacement() {
    let source = [eq(true, c(0), c(1)), p(true, c(0))];
    let target = [p(false, g(c(0))), p(true, c(0))];
    let at = position(vec![0]);
    let generous = Limits::default();
    let result = paramodulate(
        &source,
        &target,
        witness(&at, &[]),
        FUNCTIONS,
        PREDICATES,
        &generous,
    )
    .unwrap();
    let exact = Limits {
        max_operations: result.statistics.operations,
        max_output_nodes: result.statistics.output_nodes,
        ..generous
    };
    assert_eq!(
        paramodulate(
            &source,
            &target,
            witness(&at, &[]),
            FUNCTIONS,
            PREDICATES,
            &exact
        ),
        Ok(result)
    );
    let short = Limits {
        max_operations: exact.max_operations - 1,
        ..exact
    };
    assert_eq!(
        paramodulate(
            &source,
            &target,
            witness(&at, &[]),
            FUNCTIONS,
            PREDICATES,
            &short
        ),
        Err(Error::Resource(Resource::Operations))
    );
    let nodes = Limits {
        max_output_nodes: exact.max_output_nodes - 1,
        ..exact
    };
    assert_eq!(
        paramodulate(
            &source,
            &target,
            witness(&at, &[]),
            FUNCTIONS,
            PREDICATES,
            &nodes
        ),
        Err(Error::Occurrence(
            fang_equality_occurrence_core::Error::OutputNodes
        ))
    );
    let literals = Limits {
        max_literals: 2,
        ..generous
    };
    assert_eq!(
        paramodulate(
            &source,
            &target,
            witness(&at, &[]),
            FUNCTIONS,
            PREDICATES,
            &literals
        ),
        Err(Error::Resource(Resource::Literals))
    );
}

fn eval_term(term: &Term, constants: [usize; 2], unary: usize, valuation: usize) -> usize {
    match term {
        Term::Var(id) => (valuation >> id) & 1,
        Term::Fun(id, arguments) => match *id {
            0 | 1 => constants[*id as usize],
            2 => (unary >> eval_term(&arguments[0], constants, unary, valuation)) & 1,
            _ => panic!("test signature"),
        },
    }
}

fn closed(clause: &[Literal], constants: [usize; 2], unary: usize, predicate: usize) -> bool {
    (0..16).all(|valuation| {
        clause.iter().any(|literal| {
            let value = match &literal.atom {
                Atom::Equal(left, right) => {
                    eval_term(left, constants, unary, valuation)
                        == eval_term(right, constants, unary, valuation)
                }
                Atom::Predicate(_, args) => {
                    (predicate >> eval_term(&args[0], constants, unary, valuation)) & 1 == 1
                }
            };
            literal.positive == value
        })
    })
}

#[test]
fn successful_reconstructions_preserve_models_on_all_two_element_tables() {
    let at = position(vec![]);
    let images = [(0, g(Term::Var(2))), (1, g(Term::Var(2)))];
    let mut cases = 0;
    let mut antecedents = 0;
    for polarity in [false, true] {
        for residual in [false, true] {
            let mut source = vec![eq(true, g(Term::Var(0)), Term::Var(0))];
            if residual {
                source.push(p(true, Term::Var(0)));
            }
            let target = [p(polarity, g(Term::Var(1)))];
            let result = paramodulate(
                &source,
                &target,
                witness(&at, &images),
                FUNCTIONS,
                PREDICATES,
                &Limits::default(),
            )
            .unwrap();
            for a in 0..2 {
                for b in 0..2 {
                    for unary in 0..4 {
                        for predicate in 0..4 {
                            cases += 1;
                            if closed(&source, [a, b], unary, predicate)
                                && closed(&target, [a, b], unary, predicate)
                            {
                                antecedents += 1;
                                assert!(closed(&result.clause, [a, b], unary, predicate));
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 256);
    assert!(antecedents > 0);
}
