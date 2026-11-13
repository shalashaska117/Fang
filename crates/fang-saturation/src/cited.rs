// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Two-pass premise discovery. The bundle adapter supplies item mapping and
//! preparation, so this module does not depend on a newer bundle certificate API.
//! Only the second proof belongs to the kept task. Both proofs remain unchecked
//! candidates until the independent checker accepts them.

use crate::options::Options;
use crate::producer::{Refutation, refute_prepared_portfolio};
use fang_tptp_signed_roles::Prepared;
use std::time::Instant;

#[derive(Debug)]
pub enum Error<E> {
    Discovery(Refutation),
    Mapping(E),
    Preparation(E),
    Replay(Refutation),
}

pub struct Candidate<I> {
    pub premises: Vec<I>,
    /// Proof over the freshly prepared kept task, with its own symbol numbering.
    pub text: String,
}

/// Search the whole task, map used clauses to premise items, then prepare and
/// search the kept task again. The adapter adds the premise line and checks the
/// combined certificate length before writing any output.
///
/// `deadline` is absolute and includes both preparations and both searches.
/// `discovery_deadline` can reserve time for replay but cannot extend that budget.
/// The first preparation may use wider producer limits; `prepare_kept` must use
/// the checked path's limits. A failed second pass never returns the first proof.
pub fn refute<I, E>(
    prepared: Prepared,
    options: &Options,
    discovery_deadline: Option<Instant>,
    deadline: Option<Instant>,
    memory_mib: Option<u64>,
    map_inputs: impl FnOnce(&Prepared, &[usize]) -> Result<Vec<I>, E>,
    prepare_kept: impl FnOnce(&[I]) -> Result<Prepared, E>,
) -> Result<Candidate<I>, Error<E>> {
    let discovery_deadline = match (discovery_deadline, deadline) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    };
    let inputs = match refute_prepared_portfolio(&prepared, options, discovery_deadline, memory_mib)
    {
        Refutation::Candidate { inputs, .. } => inputs,
        outcome => return Err(Error::Discovery(outcome)),
    };
    if deadline.is_some_and(|end| Instant::now() >= end) {
        return Err(Error::Discovery(Refutation::Stopped("time limit")));
    }
    let premises = map_inputs(&prepared, &inputs).map_err(Error::Mapping)?;
    // Release the whole task before allocating the smaller task.
    drop(prepared);
    if deadline.is_some_and(|end| Instant::now() >= end) {
        return Err(Error::Replay(Refutation::Stopped("time limit")));
    }
    let kept = prepare_kept(&premises).map_err(Error::Preparation)?;
    match refute_prepared_portfolio(&kept, options, deadline, memory_mib) {
        Refutation::Candidate { text, .. } => {
            if deadline.is_some_and(|end| Instant::now() >= end) {
                return Err(Error::Replay(Refutation::Stopped("time limit")));
            }
            Ok(Candidate { premises, text })
        }
        outcome => Err(Error::Replay(outcome)),
    }
}
