// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Numeric entry to the existing equality search; no original-byte acceptance.
use crate::{Error, Limits, Outcome};
use fang::syntax::Term;
use fang_equality_inference_core::{Atom, Clause};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InvalidPrepared {
    UnknownFunction,
    FunctionArity,
    UnknownPredicate,
    PredicateArity,
}

#[derive(Debug)]
pub enum PreparedError {
    Invalid(InvalidPrepared),
    Resource(&'static str),
    Search(Error),
}

struct Work {
    operations: usize,
    terms: usize,
}

impl Work {
    fn tick(&mut self) -> Result<(), PreparedError> {
        if self.operations == 0 {
            return Err(PreparedError::Resource(
                "prepared validation operation limit",
            ));
        }
        self.operations -= 1;
        Ok(())
    }

    fn term(
        &mut self,
        term: &Term,
        functions: &[usize],
        depth: usize,
        maximum: usize,
    ) -> Result<(), PreparedError> {
        self.tick()?;
        if depth > maximum || depth > 64 {
            return Err(PreparedError::Resource("prepared term depth limit"));
        }
        if self.terms == 0 {
            return Err(PreparedError::Resource("prepared term-node limit"));
        }
        self.terms -= 1;
        if let Term::Fun(id, arguments) = term {
            let arity = functions
                .get(*id as usize)
                .ok_or(PreparedError::Invalid(InvalidPrepared::UnknownFunction))?;
            if *arity != arguments.len() {
                return Err(PreparedError::Invalid(InvalidPrepared::FunctionArity));
            }
            for argument in arguments {
                self.term(argument, functions, depth + 1, maximum)?;
            }
        }
        Ok(())
    }
}

fn validate(
    clauses: &[Clause],
    functions: &[usize],
    predicates: &[usize],
    limits: &Limits,
) -> Result<(), PreparedError> {
    if clauses.len() > limits.input.max_clauses || clauses.len() > limits.max_stored_clauses {
        return Err(PreparedError::Resource("prepared clause limit"));
    }
    let mut work = Work {
        operations: limits.input.max_operations,
        terms: limits.input.max_term_nodes,
    };
    // Charge the complete tables, including unused slots, before copying them.
    for _ in functions.iter().chain(predicates) {
        work.tick()?;
    }
    for clause in clauses {
        work.tick()?;
        if clause.len() > limits.input.max_literals {
            return Err(PreparedError::Resource("prepared clause width limit"));
        }
        for literal in clause {
            work.tick()?;
            match &literal.atom {
                Atom::Predicate(id, arguments) => {
                    let arity = predicates
                        .get(*id as usize)
                        .ok_or(PreparedError::Invalid(InvalidPrepared::UnknownPredicate))?;
                    if *arity != arguments.len() {
                        return Err(PreparedError::Invalid(InvalidPrepared::PredicateArity));
                    }
                    for argument in arguments {
                        work.term(argument, functions, 0, limits.input.max_term_depth)?;
                    }
                }
                Atom::Equal(left, right) => {
                    work.term(left, functions, 0, limits.input.max_term_depth)?;
                    work.term(right, functions, 0, limits.input.max_term_depth)?;
                }
            }
        }
    }
    Ok(())
}

/// Search numeric clauses after validating every clause and the complete arity
/// tables, including clauses after an empty clause. Order and IDs are unchanged.
///
/// This borrows caller data; rejected deep terms are not dropped by this entry.
/// Native allocation and caller destruction are outside the typed error contract.
/// Validation has its own operation budget, followed by the unchanged search
/// budgets. Success returns only a candidate for these numeric clauses. It does
/// not establish that they came from any original FOF/CNF bytes. The existing
/// version-5 serializer still describes CNF and must not be relabelled as a FOF
/// certificate without a separately checked preprocessing envelope.
pub fn prove_prepared_ordered(
    clauses: &[Clause],
    functions: &[usize],
    predicates: &[usize],
    limits: &Limits,
) -> Result<Outcome, PreparedError> {
    validate(clauses, functions, predicates, limits)?;
    crate::prove_clauses(
        clauses.to_vec(),
        functions.to_vec(),
        predicates.to_vec(),
        limits,
        true,
    )
    .map_err(PreparedError::Search)
}
