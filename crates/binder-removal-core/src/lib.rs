// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Syntactic erasure only. Semantic use requires premises that this crate does not check.
#![forbid(unsafe_code)]

use fang_fof_core::Nnf as QuantifierFree;
use fang_quantified_fof_core::Nnf;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Input formula depth, including every removed binder; also capped at 64.
    pub max_formula_depth: usize,
    /// One credit per visited formula node, including unused binders.
    pub max_operations: usize,
    /// One credit per retained NNF node. Moved terms/literals are not copied.
    pub max_output_nodes: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_formula_depth: 64,
            max_operations: 100_000,
            max_output_nodes: 100_000,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Resource {
    FormulaDepth,
    Operations,
    OutputNodes,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    ResidualExistential(u32),
    Resource(Resource),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Statistics {
    pub operations: usize,
    pub output_nodes: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Removed {
    pub formula: QuantifierFree,
    pub statistics: Statistics,
}

fn increment(value: usize, cap: usize, resource: Resource) -> Result<usize, Error> {
    if value >= cap {
        Err(Error::Resource(resource))
    } else {
        Ok(value + 1)
    }
}

fn remove(
    source: Nnf,
    depth: usize,
    limits: &Limits,
    statistics: &mut Statistics,
) -> Result<QuantifierFree, Error> {
    statistics.operations = increment(
        statistics.operations,
        limits.max_operations,
        Resource::Operations,
    )?;
    if depth > limits.max_formula_depth.min(64) {
        return Err(Error::Resource(Resource::FormulaDepth));
    }
    match source {
        Nnf::Forall(_, body) => remove(*body, depth + 1, limits, statistics),
        Nnf::Exists(binder, _) => Err(Error::ResidualExistential(binder)),
        Nnf::Literal(literal) => {
            statistics.output_nodes = increment(
                statistics.output_nodes,
                limits.max_output_nodes,
                Resource::OutputNodes,
            )?;
            Ok(QuantifierFree::Literal(literal))
        }
        Nnf::True => {
            statistics.output_nodes = increment(
                statistics.output_nodes,
                limits.max_output_nodes,
                Resource::OutputNodes,
            )?;
            Ok(QuantifierFree::True)
        }
        Nnf::False => {
            statistics.output_nodes = increment(
                statistics.output_nodes,
                limits.max_output_nodes,
                Resource::OutputNodes,
            )?;
            Ok(QuantifierFree::False)
        }
        Nnf::And(left, right) => {
            statistics.output_nodes = increment(
                statistics.output_nodes,
                limits.max_output_nodes,
                Resource::OutputNodes,
            )?;
            let left = remove(*left, depth + 1, limits, statistics)?;
            let right = remove(*right, depth + 1, limits, statistics)?;
            Ok(QuantifierFree::And(Box::new(left), Box::new(right)))
        }
        Nnf::Or(left, right) => {
            statistics.output_nodes = increment(
                statistics.output_nodes,
                limits.max_output_nodes,
                Resource::OutputNodes,
            )?;
            let left = remove(*left, depth + 1, limits, statistics)?;
            let right = remove(*right, depth + 1, limits, statistics)?;
            Ok(QuantifierFree::Or(Box::new(left), Box::new(right)))
        }
    }
}

/// Remove universal nodes without renaming or copying literal/term values.
///
/// This function does not check lexical closure, distinct binder IDs, signature
/// validity or the caller's semantic premises. Error returns no partial result.
pub fn remove_universals(source: Nnf, limits: &Limits) -> Result<Removed, Error> {
    let mut statistics = Statistics {
        operations: 0,
        output_nodes: 0,
    };
    let formula = remove(source, 1, limits, &mut statistics)?;
    Ok(Removed {
        formula,
        statistics,
    })
}
