// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Checked entrypoints that reuse the reconstruction kernel's actual helpers.

use super::{Error, Limits, Literal, Reconstructed, Statistics};
use fang::syntax::Term;

/// Instantiate every literal using a finite simultaneous substitution.
/// Validate the complete clause and every image, including unused bindings.
/// Cap and validation order matches equality_resolution before pivot selection.
pub fn instantiate(
    premise: &[Literal],
    substitution: &[(u32, Term)],
    functions: &[usize],
    predicates: &[usize],
    limits: &Limits,
) -> Result<Reconstructed, Error> {
    if premise.len() > limits.max_literals {
        return Err(Error::Literals);
    }
    if substitution.len() > limits.max_bindings {
        return Err(Error::Bindings);
    }
    let mut work = Statistics::default();
    super::validate_clause(premise, functions, predicates, limits, &mut work)?;
    super::validate_substitution(substitution, functions, limits, &mut work)?;
    let mut clause = Vec::new();
    let mut index = 0;
    while index < premise.len() {
        clause.push(super::apply_literal(
            &premise[index],
            substitution,
            limits,
            &mut work,
        )?);
        index += 1;
    }
    Ok(Reconstructed {
        clause,
        statistics: work,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Compared {
    pub equal: bool,
    pub statistics: Statistics,
}

/// Compare complete signature-valid terms. Resource exhaustion is an error,
/// distinct from a completed comparison returning false.
pub fn terms_equal(
    left: &Term,
    right: &Term,
    functions: &[usize],
    limits: &Limits,
) -> Result<Compared, Error> {
    let mut work = Statistics::default();
    super::validate_term(left, functions, 1, limits, &mut work)?;
    super::validate_term(right, functions, 1, limits, &mut work)?;
    let equal = super::same_term(left, right, limits, &mut work)?;
    Ok(Compared {
        equal,
        statistics: work,
    })
}
