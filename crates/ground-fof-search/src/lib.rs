// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Local integration candidate. Independent checking remains required.
#![forbid(unsafe_code)]

use fang::syntax::{Problem, deduplicate};
use fang_ground_fof_core::{Error as CoreError, Limits as CoreLimits, Signature};
use fang_ground_fof_frontend::{Body, Limits as InputLimits};

#[derive(Debug)]
pub enum Error {
    Input(fang::Error),
    Preprocessing(CoreError),
    Resource(&'static str),
}

/// A source declaration and its zero-based raw output clause position.
#[derive(Debug, PartialEq, Eq)]
pub struct Origin {
    pub declaration: usize,
    pub local_clause: usize,
}

#[derive(Debug)]
pub struct Prepared {
    pub problem: Problem,
    pub origins: Vec<Origin>,
    pub preprocessing_operations: usize,
    pub stored_nodes: usize,
}

/// Lower in source order. An error exposes no partially prepared problem.
/// Parser, preprocessing and search have separate operational counters.
/// Physical memory and total elapsed time require the outer supervisor.
pub fn prepare(
    input: &[u8],
    input_limits: &InputLimits,
    limits: &CoreLimits,
) -> Result<Prepared, Error> {
    let parsed = fang_ground_fof_frontend::parse(input, input_limits).map_err(Error::Input)?;
    let signature = Signature {
        functions: parsed.functions.iter().map(|s| s.arity).collect(),
        predicates: parsed.predicates.iter().map(|s| s.arity).collect(),
    };
    let mut clauses = Vec::new();
    let mut clause_names = Vec::new();
    let mut origins = Vec::new();
    let mut operations = 0;
    let mut stored_nodes = 0;
    let mut literal_count = 0usize;
    for (index, declaration) in parsed.declarations.into_iter().enumerate() {
        let mut remaining = *limits;
        remaining.max_operations = limits.max_operations - operations;
        remaining.max_stored_nodes = limits.max_stored_nodes - stored_nodes;
        remaining.max_clauses = limits.max_clauses - clauses.len();
        remaining.max_literals = limits.max_literals - literal_count;
        let output = match declaration.body {
            Body::Cnf(clause) => vec![clause],
            Body::Fof(formula) => {
                let out = fang_ground_fof_core::preprocess(&formula, &signature, &remaining)
                    .map_err(Error::Preprocessing)?;
                operations = operations
                    .checked_add(out.statistics.operations)
                    .ok_or(Error::Resource("operation count overflow"))?;
                stored_nodes = stored_nodes
                    .checked_add(out.statistics.allocated_nodes)
                    .ok_or(Error::Resource("storage count overflow"))?;
                if operations > limits.max_operations || stored_nodes > limits.max_stored_nodes {
                    return Err(Error::Resource(
                        "preprocessing counters exceeded their caps",
                    ));
                }
                out.clauses
            }
        };
        for (local_clause, clause) in output.into_iter().enumerate() {
            if clauses.len() >= limits.max_clauses {
                return Err(Error::Resource("total output clause cap"));
            }
            if clause.len() > limits.max_literals_per_clause {
                return Err(Error::Resource("output clause width cap"));
            }
            literal_count = literal_count
                .checked_add(clause.len())
                .ok_or(Error::Resource("literal count overflow"))?;
            if literal_count > limits.max_literals {
                return Err(Error::Resource("total output literal cap"));
            }
            clause_names.push(format!("{}_{}_{}", declaration.name, index, local_clause));
            clauses.push(deduplicate(&clause));
            origins.push(Origin {
                declaration: index,
                local_clause,
            });
        }
    }
    Ok(Prepared {
        problem: Problem {
            functions: parsed.functions,
            predicates: parsed.predicates,
            clause_names,
            clauses,
        },
        origins,
        preprocessing_operations: operations,
        stored_nodes,
    })
}
