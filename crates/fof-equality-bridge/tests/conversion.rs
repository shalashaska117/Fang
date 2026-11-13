// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::syntax::{Literal as EncodedLiteral, Term};
use fang_equality_inference_core::{Atom, Literal};
use fang_fof_equality_bridge::{Error, Reservation, reserved_id};

fn term() -> Term {
    Term::Fun(0, vec![Term::Var(7), Term::Fun(2, vec![])])
}

fn equal(positive: bool) -> Literal {
    Literal {
        positive,
        atom: Atom::Equal(term(), Term::Var(3)),
    }
}

#[test]
fn reserve_after_the_complete_original_table() {
    let reservation = Reservation::new(vec![1, 0], 3).unwrap();
    assert_eq!(reservation.equality_id(), 2);
    assert_eq!(reservation.extended_arities(), [1, 0, 2]);
    let empty = Reservation::new(vec![], 1).unwrap();
    assert_eq!(empty.equality_id(), 0);
    assert_eq!(empty.extended_arities(), [2]);
}

#[test]
fn reservation_checks_capacity_and_scalar_range_without_large_allocations() {
    assert_eq!(reserved_id(0, 0), Err(Error::PredicateLimit));
    assert_eq!(reserved_id(3, 3), Err(Error::PredicateLimit));
    assert_eq!(reserved_id(3, 4), Ok(3));
    if usize::BITS > 32 {
        let maximum_id = u32::MAX as usize;
        assert_eq!(reserved_id(maximum_id, usize::MAX), Ok(u32::MAX));
        assert_eq!(
            reserved_id(maximum_id + 1, usize::MAX),
            Err(Error::SymbolId)
        );
    }
}

#[test]
fn equality_round_trip_preserves_terms_order_and_polarity() {
    let reservation = Reservation::new(vec![1], 2).unwrap();
    for positive in [false, true] {
        let original = equal(positive);
        let encoded = reservation.encode_literal(original.clone()).unwrap();
        assert_eq!(encoded.predicate, 1);
        assert_eq!(encoded.arguments, [term(), Term::Var(3)]);
        assert_eq!(encoded.positive, positive);
        assert_eq!(reservation.decode_literal(encoded).unwrap(), original);
    }
}

#[test]
fn ordinary_predicates_keep_their_namespace_and_arity() {
    let reservation = Reservation::new(vec![1, 0], 3).unwrap();
    let original = Literal {
        positive: false,
        atom: Atom::Predicate(0, vec![term()]),
    };
    let encoded = reservation.encode_literal(original.clone()).unwrap();
    assert_eq!(encoded.predicate, 0);
    assert_eq!(reservation.decode_literal(encoded).unwrap(), original);
    assert_eq!(
        reservation.encode_literal(Literal {
            positive: true,
            atom: Atom::Predicate(0, vec![]),
        }),
        Err(Error::PredicateArity)
    );
}

#[test]
fn an_ordinary_head_cannot_claim_the_reserved_id() {
    let reservation = Reservation::new(vec![0], 2).unwrap();
    for predicate in [1, 2] {
        assert_eq!(
            reservation.encode_literal(Literal {
                positive: true,
                atom: Atom::Predicate(predicate, vec![term(), term()]),
            }),
            Err(Error::UnknownPredicate)
        );
    }
}

#[test]
fn decode_rejects_reserved_wrong_arities_and_unknown_heads() {
    let reservation = Reservation::new(vec![0], 2).unwrap();
    for arity in [0, 1, 3] {
        assert_eq!(
            reservation.decode_literal(EncodedLiteral {
                positive: false,
                predicate: 1,
                arguments: (0..arity).map(Term::Var).collect(),
            }),
            Err(Error::ReservedArity)
        );
    }
    assert_eq!(
        reservation.decode_literal(EncodedLiteral {
            positive: true,
            predicate: 2,
            arguments: vec![],
        }),
        Err(Error::UnknownPredicate)
    );
}

#[test]
fn clauses_preserve_duplicates_and_empty_clause_at_zero_cap() {
    let reservation = Reservation::new(vec![0], 2).unwrap();
    let predicate = Literal {
        positive: true,
        atom: Atom::Predicate(0, vec![]),
    };
    let original = vec![equal(false), predicate, equal(false), equal(true)];
    let encoded = reservation.encode_clause(original.clone(), 4).unwrap();
    assert_eq!(reservation.decode_clause(encoded, 4).unwrap(), original);
    assert!(reservation.encode_clause(vec![], 0).unwrap().is_empty());
    assert!(reservation.decode_clause(vec![], 0).unwrap().is_empty());
}

#[test]
fn clause_caps_precede_element_checks_and_errors_return_no_partial_clause() {
    let reservation = Reservation::new(vec![], 1).unwrap();
    let invalid = Literal {
        positive: true,
        atom: Atom::Predicate(0, vec![]),
    };
    assert_eq!(
        reservation.encode_clause(vec![invalid.clone()], 0),
        Err(Error::LiteralLimit)
    );
    assert_eq!(
        reservation.encode_clause(vec![equal(true), invalid], 2),
        Err(Error::UnknownPredicate)
    );
    let malformed = EncodedLiteral {
        positive: true,
        predicate: 0,
        arguments: vec![],
    };
    assert_eq!(
        reservation.decode_clause(vec![malformed.clone()], 0),
        Err(Error::LiteralLimit)
    );
    assert_eq!(
        reservation.decode_clause(
            vec![reservation.encode_literal(equal(false)).unwrap(), malformed],
            2
        ),
        Err(Error::ReservedArity)
    );
}
