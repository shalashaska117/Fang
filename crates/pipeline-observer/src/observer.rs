// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use crate::{Error, Introduced, Prepared};
use fang::syntax::{Clause, Symbol};
use fang_quantified_fof_frontend::Parsed;
use std::convert::Infallible;

/// Borrowed values from actual completed calls. No preprocessing is replayed.
/// A callback must bound its own copying/serialization. Values may be observed
/// before a later preparation error; only overall success can commit a trace.
pub enum Event<'a> {
    Parsed(&'a Parsed),
    Skolemized {
        /// Filtered FOF position -> complete mixed declaration position.
        fof_origins: &'a [usize],
        output: &'a fang_skolem_core::Skolemized,
    },
    Symbols {
        functions: &'a [Symbol],
        predicates: &'a [Symbol],
        introduced: &'a [Introduced],
    },
    Removed {
        declaration: usize,
        output: &'a fang_binder_removal_core::Removed,
    },
    ClauseBlock {
        declaration: usize,
        /// Raw literal order/multiplicity, including an empty block for true.
        clauses: &'a [Clause],
    },
    Prepared(&'a Prepared),
}

pub trait Observer {
    type Error;
    fn observe(&mut self, event: Event<'_>) -> Result<(), Self::Error>;
}

#[derive(Debug)]
pub enum ObservationError<E> {
    Preparation(Error),
    Observer(E),
}

impl<E> From<Error> for ObservationError<E> {
    fn from(error: Error) -> Self {
        Self::Preparation(error)
    }
}

pub(crate) struct Noop;

impl Observer for Noop {
    type Error = Infallible;
    fn observe(&mut self, _event: Event<'_>) -> Result<(), Self::Error> {
        Ok(())
    }
}

pub(crate) fn without_observation(error: ObservationError<Infallible>) -> Error {
    match error {
        ObservationError::Preparation(error) => error,
        ObservationError::Observer(never) => match never {},
    }
}
