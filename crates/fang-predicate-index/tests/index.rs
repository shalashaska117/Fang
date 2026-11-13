// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang_predicate_index_core::{Candidate, Index, IndexError, Limits, LiteralKey, Position};

fn key(predicate: usize, positive: bool) -> LiteralKey {
    LiteralKey {
        predicate,
        positive,
    }
}

fn limits() -> Limits {
    Limits {
        predicate_count: 1_000_001,
        max_clauses: 100,
        max_positions: 1000,
        max_buckets: 20,
        max_candidates: 10_000,
    }
}

fn scan_query(history: &[Vec<LiteralKey>], query: &LiteralKey) -> Vec<Position> {
    let mut result = Vec::new();
    for (clause, literals) in history.iter().enumerate() {
        for (literal, actual) in literals.iter().enumerate() {
            if actual.predicate == query.predicate && actual.positive != query.positive {
                result.push(Position { clause, literal });
            }
        }
    }
    result
}

fn scan_candidates(history: &[Vec<LiteralKey>]) -> Vec<Candidate> {
    let given = history.last().unwrap();
    let mut result = Vec::new();
    for (other, clause) in history.iter().enumerate() {
        for (left, query) in given.iter().enumerate() {
            for (right, actual) in clause.iter().enumerate() {
                if query.predicate == actual.predicate && query.positive != actual.positive {
                    result.push(Candidate { other, left, right });
                }
            }
        }
    }
    result
}

#[test]
fn exact_other_left_right_order_preserves_occurrences_and_self_resolution() {
    let mut index = Index::new(limits());
    index
        .activate(0, vec![key(0, false), key(3, false), key(0, false)])
        .unwrap();
    index
        .activate(1, vec![key(3, false), key(0, false)])
        .unwrap();
    index
        .activate(
            2,
            vec![key(0, true), key(3, true), key(0, false), key(0, true)],
        )
        .unwrap();
    assert_eq!(
        index.candidates(2).unwrap(),
        scan_candidates(index.history())
    );
    let result = index.candidates(2).unwrap();
    assert_eq!(
        &result[..5],
        &[
            Candidate {
                other: 0,
                left: 0,
                right: 0
            },
            Candidate {
                other: 0,
                left: 0,
                right: 2
            },
            Candidate {
                other: 0,
                left: 1,
                right: 1
            },
            Candidate {
                other: 0,
                left: 3,
                right: 0
            },
            Candidate {
                other: 0,
                left: 3,
                right: 2
            },
        ]
    );
    assert!(result.contains(&Candidate {
        other: 2,
        left: 0,
        right: 2
    }));
    assert!(result.contains(&Candidate {
        other: 2,
        left: 2,
        right: 0
    }));
    assert!(result.contains(&Candidate {
        other: 2,
        left: 2,
        right: 3
    }));
    assert_eq!(
        index.query_complement(&key(0, true)).unwrap(),
        vec![
            Position {
                clause: 0,
                literal: 0
            },
            Position {
                clause: 0,
                literal: 2
            },
            Position {
                clause: 1,
                literal: 1
            },
            Position {
                clause: 2,
                literal: 2
            },
        ]
    );
}

#[test]
fn empty_clauses_sparse_predicates_and_active_prefix_are_explicit() {
    let mut index = Index::new(limits());
    assert_eq!(index.candidates(0), Err(IndexError::InvalidGiven));
    assert_eq!(index.candidates(usize::MAX), Err(IndexError::InvalidGiven));
    assert!(index.query_complement(&key(17, true)).unwrap().is_empty());
    index.activate(0, vec![]).unwrap();
    assert!(index.candidates(0).unwrap().is_empty());
    index.activate(1, vec![key(1_000_000, true)]).unwrap();
    assert!(index.candidates(1).unwrap().is_empty());
    assert_eq!(index.candidates(0), Err(IndexError::InvalidGiven));
    index.activate(2, vec![key(1_000_000, false)]).unwrap();
    assert_eq!(
        index.candidates(2).unwrap(),
        vec![Candidate {
            other: 1,
            left: 0,
            right: 0
        }]
    );
    assert_eq!(index.active_count(), 3);
    assert_eq!(index.stored_positions(), 2);
}

#[test]
fn invalid_activation_is_transactional_and_can_be_retried() {
    let mut index = Index::new(limits());
    index.activate(0, vec![key(0, true)]).unwrap();
    let before = index.clone();
    for id in [0, 2, usize::MAX] {
        assert_eq!(
            index.activate(id, vec![key(3, false)]),
            Err(IndexError::ClauseOrder)
        );
        assert_eq!(index, before);
    }
    for invalid in [1_000_001, usize::MAX] {
        assert_eq!(
            index.activate(1, vec![key(3, false), key(invalid, true)]),
            Err(IndexError::InvalidPredicate)
        );
        assert_eq!(index, before);
        assert_eq!(
            index.query_complement(&key(invalid, true)),
            Err(IndexError::InvalidPredicate)
        );
        assert_eq!(index, before);
    }
    index.activate(1, vec![key(3, false)]).unwrap();
    assert_eq!(index.active_count(), 2);
}

#[test]
fn every_storage_cap_rejects_before_any_write() {
    for (configured, clause, expected) in [
        (
            Limits {
                max_clauses: 1,
                ..limits()
            },
            vec![],
            IndexError::ClauseLimit,
        ),
        (
            Limits {
                max_positions: 2,
                ..limits()
            },
            vec![key(0, true), key(3, false)],
            IndexError::PositionLimit,
        ),
        (
            Limits {
                max_buckets: 2,
                ..limits()
            },
            vec![key(0, true), key(3, false), key(3, true)],
            IndexError::BucketLimit,
        ),
    ] {
        let mut index = Index::new(configured);
        index.activate(0, vec![key(0, true)]).unwrap();
        let before = index.clone();
        assert_eq!(index.activate(1, clause), Err(expected));
        assert_eq!(index, before);
    }
    let mut index = Index::new(Limits {
        max_buckets: 1,
        ..limits()
    });
    index.activate(0, vec![key(3, false); 4]).unwrap();
    assert_eq!(index.stored_positions(), 4);
    let before = index.clone();
    assert_eq!(
        index.activate(1, vec![key(3, false), key(3, true)]),
        Err(IndexError::BucketLimit)
    );
    assert_eq!(index, before);
    index.activate(1, vec![key(3, false); 3]).unwrap();
    assert_eq!(index.query_complement(&key(3, true)).unwrap().len(), 7);
}

#[test]
fn bounded_query_and_schedule_fail_without_changing_the_index() {
    let mut index = Index::new(Limits {
        max_candidates: 2,
        ..limits()
    });
    index.activate(0, vec![key(0, false); 3]).unwrap();
    let before = index.clone();
    assert_eq!(
        index.query_complement(&key(0, true)),
        Err(IndexError::ResultLimit)
    );
    assert_eq!(index, before);
    index.activate(1, vec![key(0, true)]).unwrap();
    let before = index.clone();
    assert_eq!(index.candidates(1), Err(IndexError::ResultLimit));
    assert_eq!(index, before);
    let mut exact = Index::new(Limits {
        max_candidates: 2,
        ..limits()
    });
    exact.activate(0, vec![key(0, false); 2]).unwrap();
    exact.activate(1, vec![key(0, true)]).unwrap();
    assert_eq!(exact.candidates(1).unwrap().len(), 2);
    let mut zero = Index::new(Limits {
        max_candidates: 0,
        ..limits()
    });
    zero.activate(0, vec![key(0, true)]).unwrap();
    assert!(zero.candidates(0).unwrap().is_empty());
    zero.activate(1, vec![key(0, false)]).unwrap();
    assert_eq!(zero.candidates(1), Err(IndexError::ResultLimit));
}

fn random(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

#[test]
fn generated_queries_and_schedules_equal_the_independent_full_scan() {
    let mut prefixes = 0;
    let mut candidates = 0;
    for seed in 0..10 {
        let mut state = seed + 0x4641_4e47;
        for _ in 0..100 {
            let mut index = Index::new(limits());
            let count = (random(&mut state) % 8 + 1) as usize;
            for clause_id in 0..count {
                let mut clause = Vec::new();
                for _ in 0..random(&mut state) % 7 {
                    let predicate = [0, 3, 1_000_000][(random(&mut state) % 3) as usize];
                    clause.push(key(predicate, random(&mut state).is_multiple_of(2)));
                }
                index.activate(clause_id, clause).unwrap();
                for predicate in [0, 3, 17, 1_000_000] {
                    for positive in [false, true] {
                        let query = key(predicate, positive);
                        assert_eq!(
                            index.query_complement(&query).unwrap(),
                            scan_query(index.history(), &query)
                        );
                    }
                }
                let actual = index.candidates(clause_id).unwrap();
                assert_eq!(actual, scan_candidates(index.history()));
                for candidate in &actual {
                    assert!(candidate.other <= clause_id);
                    let left = &index.history()[clause_id][candidate.left];
                    let right = &index.history()[candidate.other][candidate.right];
                    assert_eq!(left.predicate, right.predicate);
                    assert_ne!(left.positive, right.positive);
                }
                candidates += actual.len();
                prefixes += 1;
            }
        }
    }
    assert!(prefixes > 4000);
    assert!(candidates > 10_000);
}
