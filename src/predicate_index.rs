// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Isolated, uninstrumented adapter for the actual extracted v2 index.
// Same operational credits as experiment.rs; no timing or formal adapter claim.
use crate::{Budget, Error, ErrorKind, Limits, syntax::Clause};
use fang_predicate_index_core::{Candidate, Index, IndexError, Limits as IndexLimits, LiteralKey};

const CANDIDATE_CAP: usize = 262_144;

pub(crate) fn new_index(predicates: usize, limits: &Limits) -> Result<Index, Error> {
    let positions = limits
        .max_clauses
        .checked_mul(limits.max_literals)
        .ok_or_else(|| Error::resource("index position-cap arithmetic overflow"))?;
    let buckets = predicates
        .checked_mul(2)
        .ok_or_else(|| Error::resource("index bucket-cap arithmetic overflow"))?;
    Ok(Index::new(IndexLimits {
        predicate_count: predicates,
        max_clauses: limits.max_clauses,
        max_positions: positions,
        max_buckets: buckets,
        max_candidates: CANDIDATE_CAP,
    }))
}

fn arithmetic() -> Error {
    Error::resource("index work-credit arithmetic overflow")
}

fn map_index(error: IndexError) -> Error {
    match error {
        IndexError::ClauseOrder | IndexError::InvalidPredicate | IndexError::InvalidGiven => {
            Error {
                kind: ErrorKind::InvalidInput,
                offset: None,
                message: format!("index-adapter-invariant: {error:?}"),
            }
        }
        _ => Error::resource(&format!("index capacity: {error:?}")),
    }
}

fn reserve(cost: usize, budget: &mut Budget) -> Result<(), Error> {
    if cost > budget.remaining {
        return Err(Error::resource("index work-credit reservation exhausted"));
    }
    budget.remaining -= cost;
    Ok(())
}

pub(crate) fn schedule(
    index: &mut Index,
    given_id: usize,
    clause: &Clause,
    predicates: usize,
    budget: &mut Budget,
) -> Result<Vec<Candidate>, Error> {
    let n = clause.len();
    let c = index.active_count().checked_add(1).ok_or_else(arithmetic)?;
    let p = index
        .stored_positions()
        .checked_add(n)
        .ok_or_else(arithmetic)?;
    let b = predicates.checked_mul(2).ok_or_else(arithmetic)?.min(p);
    let activation = b
        .checked_add(n)
        .and_then(|x| x.checked_mul(2))
        .and_then(|x| x.checked_add(n))
        .and_then(|x| x.checked_add(6))
        .and_then(|x| x.checked_mul(n))
        .and_then(|x| x.checked_add(1))
        .ok_or_else(arithmetic)?;
    reserve(activation, budget)?;
    let mut keys = Vec::new();
    for literal in clause {
        keys.push(LiteralKey {
            predicate: literal.predicate as usize,
            positive: literal.positive,
        });
    }
    index.activate(given_id, keys).map_err(map_index)?;
    let initialization = b
        .checked_add(2)
        .and_then(|x| x.checked_mul(n))
        .ok_or_else(arithmetic)?;
    let sweep = n
        .checked_add(1)
        .and_then(|x| x.checked_mul(c))
        .and_then(|x| x.checked_mul(3))
        .ok_or_else(arithmetic)?;
    let materialization = n
        .checked_mul(p)
        .map(|x| x.min(CANDIDATE_CAP + 1))
        .and_then(|x| x.checked_mul(3))
        .ok_or_else(arithmetic)?;
    let cost = initialization
        .checked_add(sweep)
        .and_then(|x| x.checked_add(materialization))
        .and_then(|x| x.checked_add(1))
        .ok_or_else(arithmetic)?;
    reserve(cost, budget)?;
    index.candidates(given_id).map_err(map_index)
}
