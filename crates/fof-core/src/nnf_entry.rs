// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Additive entry point to the unchanged scoped-core clausifier.

use super::{Error, Limits, Nnf, Preprocessed, Resource, Statistics, Work};

/// Clausify an existing NNF while carrying the caller's structural counters.
///
/// This low-level entry point does not validate formula depth, term depth,
/// symbol arities or variable scope. The checked pipeline must establish those
/// properties before calling it. In particular, arbitrary caller-built deep
/// ASTs are outside the native stack guarantee. No variable is renumbered.
///
/// The operation and storage counters must fit their caps even for a trivial
/// input. Other carried input statistics are retained, while output fields are
/// replaced by this call's result. A failure exposes no partial clauses or
/// updated statistics. The input and limits are borrowed and remain unchanged.
pub fn clausify_nnf_from(
    formula: &Nnf,
    limits: &Limits,
    statistics: Statistics,
) -> Result<Preprocessed, Error> {
    super::bounded_add(
        statistics.operations,
        0,
        limits.max_operations,
        Resource::Operations,
    )?;
    super::bounded_add(
        statistics.allocated_nodes,
        0,
        limits.max_stored_nodes,
        Resource::StoredNodes,
    )?;
    let mut work = Work { statistics };
    let result = super::clausify_nnf(formula, limits, &mut work)?;
    work.statistics.output_clauses = result.clauses.len();
    work.statistics.output_literals = result.literals;
    work.statistics.output_term_nodes = result.term_nodes;
    Ok(Preprocessed {
        clauses: result.clauses,
        statistics: work.statistics,
    })
}
