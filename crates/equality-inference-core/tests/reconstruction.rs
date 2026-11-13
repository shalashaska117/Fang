use fang::syntax::Term;
use fang::unify::Unifier;
use fang_equality_inference_core::{Atom, Clause, Error, Limits, Literal, equality_resolution};

const FUNCTIONS: &[usize] = &[0, 0, 1, 2];
const PREDICATES: &[usize] = &[1, 0];

fn constant(id: u32) -> Term {
    Term::Fun(id, vec![])
}

fn disequality(left: Term, right: Term) -> Literal {
    Literal {
        positive: false,
        atom: Atom::Equal(left, right),
    }
}

fn predicate(positive: bool, term: Term) -> Literal {
    Literal {
        positive,
        atom: Atom::Predicate(0, vec![term]),
    }
}

fn reconstruct(
    premise: &[Literal],
    pivot: usize,
    substitution: &[(u32, Term)],
) -> Result<Clause, Error> {
    equality_resolution(
        premise,
        pivot,
        substitution,
        FUNCTIONS,
        PREDICATES,
        &Limits::default(),
    )
    .map(|result| result.clause)
}

#[test]
fn reflexive_negative_equality_yields_empty_clause() {
    assert_eq!(
        reconstruct(&[disequality(constant(0), constant(0))], 0, &[]),
        Ok(vec![])
    );
}

#[test]
fn residual_order_polarity_and_duplicates_are_exact() {
    let premise = vec![
        predicate(true, Term::Var(0)),
        disequality(Term::Var(0), constant(0)),
        predicate(false, Term::Var(0)),
        predicate(true, Term::Var(0)),
    ];
    let original = premise.clone();
    let substitution = vec![(0, constant(0))];
    assert_eq!(
        reconstruct(&premise, 1, &substitution),
        Ok(vec![
            predicate(true, constant(0)),
            predicate(false, constant(0)),
            predicate(true, constant(0)),
        ])
    );
    assert_eq!(premise, original);
    assert_eq!(substitution, vec![(0, constant(0))]);
}

#[test]
fn substitution_is_simultaneous_and_not_transitive() {
    let premise = vec![disequality(Term::Var(0), Term::Var(1))];
    assert_eq!(
        reconstruct(&premise, 0, &[(0, Term::Var(1)), (1, constant(0))]),
        Err(Error::NotEqualized)
    );
    let source = vec![disequality(Term::Var(0), Term::Fun(2, vec![Term::Var(0)]))];
    assert_eq!(
        reconstruct(&source, 0, &[(0, Term::Fun(2, vec![Term::Var(0)]))]),
        Err(Error::NotEqualized)
    );
}

#[test]
fn malformed_witness_and_pivot_are_distinct() {
    let premise = vec![disequality(Term::Var(0), constant(0))];
    assert_eq!(reconstruct(&premise, 1, &[]), Err(Error::PivotIndex));
    assert_eq!(reconstruct(&premise, 0, &[]), Err(Error::NotEqualized));
    assert_eq!(
        reconstruct(&premise, 0, &[(0, constant(0)), (0, constant(0))]),
        Err(Error::SubstitutionOrder)
    );
    assert_eq!(
        reconstruct(&premise, 0, &[(1, constant(0)), (0, constant(0))]),
        Err(Error::SubstitutionOrder)
    );
    let mut positive = premise.clone();
    positive[0].positive = true;
    assert_eq!(
        reconstruct(&positive, 0, &[]),
        Err(Error::ExpectedNegativeEquality)
    );
    assert_eq!(
        reconstruct(&[predicate(false, constant(0))], 0, &[]),
        Err(Error::ExpectedNegativeEquality)
    );
}

#[test]
fn validates_complete_inputs_and_unused_bindings() {
    let good = disequality(constant(0), constant(0));
    assert_eq!(
        reconstruct(&[good.clone(), predicate(true, constant(99))], 0, &[]),
        Err(Error::UnknownFunction)
    );
    assert_eq!(
        reconstruct(std::slice::from_ref(&good), 0, &[(9, Term::Fun(2, vec![]))]),
        Err(Error::FunctionArity)
    );
    let unknown = Literal {
        positive: true,
        atom: Atom::Predicate(2, vec![]),
    };
    assert_eq!(
        reconstruct(&[good.clone(), unknown], 0, &[]),
        Err(Error::UnknownPredicate)
    );
    let wrong = Literal {
        positive: true,
        atom: Atom::Predicate(0, vec![]),
    };
    assert_eq!(
        reconstruct(&[good, wrong], 0, &[]),
        Err(Error::PredicateArity)
    );
}

#[test]
fn resource_boundaries_and_precedence() {
    let premise = vec![
        disequality(Term::Var(0), constant(0)),
        predicate(true, Term::Var(0)),
    ];
    let witness = vec![(0, constant(0))];
    let good = equality_resolution(
        &premise,
        0,
        &witness,
        FUNCTIONS,
        PREDICATES,
        &Limits::default(),
    )
    .unwrap();
    for (limits, expected) in [
        (
            Limits {
                max_operations: good.statistics.operations - 1,
                ..Limits::default()
            },
            Error::Operations,
        ),
        (
            Limits {
                max_output_nodes: good.statistics.output_nodes - 1,
                ..Limits::default()
            },
            Error::OutputNodes,
        ),
        (
            Limits {
                max_literals: 1,
                ..Limits::default()
            },
            Error::Literals,
        ),
        (
            Limits {
                max_bindings: 0,
                ..Limits::default()
            },
            Error::Bindings,
        ),
        (
            Limits {
                max_depth: 0,
                ..Limits::default()
            },
            Error::Depth,
        ),
    ] {
        assert_eq!(
            equality_resolution(&premise, 0, &witness, FUNCTIONS, PREDICATES, &limits),
            Err(expected)
        );
    }
    let exact = Limits {
        max_operations: good.statistics.operations,
        max_output_nodes: good.statistics.output_nodes,
        ..Limits::default()
    };
    assert_eq!(
        equality_resolution(&premise, 0, &witness, FUNCTIONS, PREDICATES, &exact).unwrap(),
        good
    );
    assert_eq!(
        equality_resolution(
            &premise,
            usize::MAX,
            &[],
            FUNCTIONS,
            PREDICATES,
            &Limits {
                max_operations: 0,
                ..Limits::default()
            }
        ),
        Err(Error::Operations)
    );
}

#[test]
fn depth_cap_cannot_be_relaxed_and_substitution_can_exceed_it() {
    let mut deep = constant(0);
    for _ in 0..64 {
        deep = Term::Fun(2, vec![deep]);
    }
    assert_eq!(
        equality_resolution(
            &[disequality(deep.clone(), deep)],
            0,
            &[],
            FUNCTIONS,
            PREDICATES,
            &Limits {
                max_depth: 1000,
                ..Limits::default()
            }
        ),
        Err(Error::Depth)
    );
    let mut inner = constant(0);
    let mut outside = Term::Var(0);
    for _ in 0..32 {
        inner = Term::Fun(2, vec![inner]);
        outside = Term::Fun(2, vec![outside]);
    }
    assert_eq!(
        reconstruct(&[disequality(outside.clone(), outside)], 0, &[(0, inner)]),
        Err(Error::Depth)
    );
}

#[test]
fn maximum_variable_id_and_unbound_variables_are_preserved() {
    let term = Term::Var(u32::MAX);
    let premise = vec![
        disequality(term.clone(), term.clone()),
        predicate(true, term.clone()),
    ];
    assert_eq!(
        reconstruct(&premise, 0, &[]),
        Ok(vec![predicate(true, term)])
    );
}

#[test]
fn actual_unifier_is_only_a_witness_producer() {
    let mut terms = vec![Term::Var(0), Term::Var(1), constant(0), constant(1)];
    let small = terms.clone();
    for term in &small {
        terms.push(Term::Fun(2, vec![term.clone()]));
    }
    for left in &small {
        for right in &small {
            terms.push(Term::Fun(3, vec![left.clone(), right.clone()]));
        }
    }
    let mut accepted = 0;
    let mut rejected = 0;
    for left in &terms {
        for right in &terms {
            let mut unifier = Unifier::default();
            let limits = fang::Limits::default();
            if unifier
                .unify(&[(left.clone(), right.clone())], &limits)
                .unwrap()
            {
                let witness = unifier
                    .substitution(&limits)
                    .unwrap()
                    .iter()
                    .map(|(variable, term)| (*variable, term.clone()))
                    .collect::<Vec<_>>();
                let premise = vec![
                    disequality(left.clone(), right.clone()),
                    predicate(true, Term::Var(0)),
                ];
                let output = reconstruct(&premise, 0, &witness).unwrap();
                assert_eq!(output.len(), 1);
                accepted += 1;
            } else {
                rejected += 1;
            }
        }
    }
    assert_eq!(accepted + rejected, 576);
    assert!(accepted > 100 && rejected > 100);
}

#[test]
fn finite_self_containing_image_is_copied_once() {
    let image = Term::Fun(2, vec![Term::Var(0)]);
    let premise = vec![
        disequality(constant(0), constant(0)),
        predicate(true, Term::Var(0)),
    ];
    assert_eq!(
        reconstruct(&premise, 0, &[(0, image.clone())]),
        Ok(vec![predicate(true, image)])
    );
}

#[test]
fn positive_equality_residual_substitutes_both_sides() {
    let premise = vec![
        disequality(Term::Var(0), constant(0)),
        Literal {
            positive: true,
            atom: Atom::Equal(Term::Var(0), Term::Var(1)),
        },
    ];
    assert_eq!(
        reconstruct(&premise, 0, &[(0, constant(0)), (1, constant(1))]),
        Ok(vec![Literal {
            positive: true,
            atom: Atom::Equal(constant(0), constant(1))
        }])
    );
}
