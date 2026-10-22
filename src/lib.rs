// Copyright (c) 2026 Pietro Pellegrino.
// Upstream reference and retained notices: LICENSES/Vampire.txt and Vampire.ORIGIN.
// Vampire source: b75190a4b7946c325263b079ac8a67d2ea1c3e01.
#![forbid(unsafe_code)]

pub mod parser;
pub mod search;
pub mod syntax;
pub mod unify;

use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    InvalidInput,
    Unsupported,
    ResourceLimit,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub kind: ErrorKind,
    pub offset: Option<usize>,
    pub message: String,
}

impl Error {
    pub fn resource(message: &str) -> Self {
        Self {
            kind: ErrorKind::ResourceLimit,
            offset: None,
            message: message.into(),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.kind)?;
        if let Some(offset) = self.offset {
            write!(f, " at byte {offset}")?;
        }
        write!(f, ": {}", self.message)
    }
}

impl std::error::Error for Error {}

/// Operational limits, separate from the semantics of the supported fragment.
#[derive(Clone, Debug)]
pub struct Limits {
    pub max_input_bytes: usize,
    pub max_term_depth: usize,
    pub max_term_nodes: usize,
    pub max_literals: usize,
    pub max_clauses: usize,
    pub max_steps: usize,
    pub max_operations: usize,
    pub max_stored_nodes: usize,
    pub max_proof_bytes: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_input_bytes: 1 << 20,
            max_term_depth: 64,
            max_term_nodes: 100_000,
            max_literals: 256,
            max_clauses: 1_000,
            max_steps: 100_000,
            max_operations: 5_000_000,
            max_stored_nodes: 1_000_000,
            max_proof_bytes: 64 << 20,
        }
    }
}

pub(crate) struct Budget {
    remaining: usize,
}

impl Budget {
    pub(crate) fn new(limit: usize) -> Self {
        Self { remaining: limit }
    }
    pub(crate) fn tick(&mut self) -> Result<(), Error> {
        if self.try_tick() {
            Ok(())
        } else {
            Err(Error::resource("operation budget exhausted"))
        }
    }

    pub(crate) fn try_tick(&mut self) -> bool {
        if self.remaining == 0 {
            false
        } else {
            self.remaining -= 1;
            true
        }
    }
}

mod predicate_index;
