// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Adapted from Fang's universal/versioned wrapper.
// Reused Fang terms and search retain LICENSES/Vampire.txt and Vampire.ORIGIN.
#![forbid(unsafe_code)]

//! Isolated nested-quantifier preprocessing. This module reports no UNSAT/SAT.
//! Original-byte certificate composition remains a separate acceptance gate.

use fang::syntax::{Clause, Problem, Symbol, deduplicate};
use fang_fof_core::{Limits as ClauseLimits, Statistics as ClauseStatistics};
use fang_quantified_fof_frontend::{Body, Limits as InputLimits};
use std::collections::BTreeSet;

#[derive(Clone, Debug)]
pub struct Limits {
    pub input: InputLimits,
    pub preprocessing: fang_skolem_core::Limits,
    /// Wrapper iterations and generated-name collision attempts.
    pub max_bookkeeping_operations: usize,
    /// Total bytes in fresh function names, excluding original source names.
    pub max_generated_name_bytes: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            input: InputLimits::default(),
            preprocessing: fang_skolem_core::Limits::default(),
            max_bookkeeping_operations: 1_000_000,
            max_generated_name_bytes: 1 << 20,
        }
    }
}

#[derive(Debug)]
pub enum Error {
    Input(fang::Error),
    Skolem(fang_skolem_core::Error),
    Removal(fang_binder_removal_core::Error),
    Clausification(fang_fof_core::Error),
    Resource(&'static str),
    Internal(&'static str),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Origin {
    /// Position in the complete mixed CNF/FOF input, before filtering FOF rows.
    pub declaration: usize,
    pub local_clause: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Introduced {
    pub declaration: usize,
    pub binder: u32,
    pub function: u32,
    pub universals: Vec<u32>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Statistics {
    pub input_operations: usize,
    /// Credits charged by the Skolem, erasure and clausification components.
    pub preprocessing_operations: usize,
    /// Cumulative structural storage credits; not live allocations or bytes.
    pub stored_nodes: usize,
    pub bookkeeping_operations: usize,
    pub generated_name_bytes: usize,
    pub raw_output_literals: usize,
}

#[derive(Debug)]
pub struct Prepared {
    pub problem: Problem,
    pub origins: Vec<Origin>,
    pub introduced: Vec<Introduced>,
    pub statistics: Statistics,
}

enum SourceBody {
    Cnf(Clause),
    Fof,
}

fn add(value: usize, count: usize, cap: usize, message: &'static str) -> Result<usize, Error> {
    if value > cap || count > cap - value {
        Err(Error::Resource(message))
    } else {
        Ok(value + count)
    }
}

fn tick(statistics: &mut Statistics, limits: &Limits) -> Result<(), Error> {
    statistics.bookkeeping_operations = add(
        statistics.bookkeeping_operations,
        1,
        limits.max_bookkeeping_operations,
        "bookkeeping operation cap",
    )?;
    Ok(())
}

fn clause_limits(limits: &Limits) -> ClauseLimits {
    let core = limits.preprocessing.core;
    ClauseLimits {
        max_formula_depth: core.max_formula_depth,
        max_formula_nodes: core.max_formula_nodes,
        max_term_depth: core.max_term_depth,
        max_input_term_nodes: core.max_input_term_nodes,
        max_clauses: core.max_clauses,
        max_literals_per_clause: core.max_literals_per_clause,
        max_literals: core.max_literals,
        max_stored_nodes: core.max_stored_nodes,
        max_operations: core.max_operations,
    }
}

fn extend_symbols(
    functions: &mut Vec<Symbol>,
    arities: &[usize],
    statistics: &mut Statistics,
    limits: &Limits,
) -> Result<(), Error> {
    if functions.len() > arities.len()
        || functions
            .iter()
            .zip(arities)
            .any(|(symbol, arity)| symbol.arity != *arity)
    {
        return Err(Error::Internal(
            "Skolemizer changed the original function signature",
        ));
    }
    let mut used: BTreeSet<String> = functions.iter().map(|symbol| symbol.name.clone()).collect();
    while functions.len() < arities.len() {
        tick(statistics, limits)?;
        let id = functions.len();
        let mut name = format!("fang_skolem_{id}");
        loop {
            let bytes = add(
                statistics.generated_name_bytes,
                name.len(),
                limits.max_generated_name_bytes,
                "generated function-name byte cap",
            )?;
            if !used.contains(&name) {
                statistics.generated_name_bytes = bytes;
                break;
            }
            tick(statistics, limits)?;
            name.push('_');
        }
        used.insert(name.clone());
        functions.push(Symbol {
            name,
            arity: arities[id],
        });
    }
    Ok(())
}

/// Parse the complete input, reserve its full signature, Skolemize FOF rows with
/// one global fresh counter, erase universal binders and produce ordered CNF.
/// CNF rows remain in source order. Errors return no partial prepared problem.
/// The unchecked low-level clausifier receives only successful Skolem/remover
/// output here; its direct proof connection is not established by this wrapper.
pub fn prepare(input: &[u8], limits: &Limits) -> Result<Prepared, Error> {
    let parsed = fang_quantified_fof_frontend::parse(input, &limits.input).map_err(Error::Input)?;
    let mut statistics = Statistics {
        input_operations: parsed.statistics.operations,
        ..Statistics::default()
    };
    if parsed.declarations.len() > limits.preprocessing.max_declarations {
        return Err(Error::Resource("total source declaration cap"));
    }
    let signature = fang_quantified_fof_core::Signature {
        functions: parsed.functions.iter().map(|symbol| symbol.arity).collect(),
        predicates: parsed
            .predicates
            .iter()
            .map(|symbol| symbol.arity)
            .collect(),
    };
    let mut sources = Vec::new();
    let mut fof = Vec::new();
    let mut fof_origins = Vec::new();
    for (index, declaration) in parsed.declarations.into_iter().enumerate() {
        tick(&mut statistics, limits)?;
        let body = match declaration.body {
            Body::Cnf(clause) => SourceBody::Cnf(clause),
            Body::Fof(formula) => {
                fof_origins.push(index);
                fof.push(fang_skolem_core::Declaration {
                    formula,
                    positive: true,
                });
                SourceBody::Fof
            }
        };
        sources.push((declaration.name, body));
    }
    let skolem = fang_skolem_core::skolemize_problem(&fof, &signature, &limits.preprocessing)
        .map_err(Error::Skolem)?;
    if skolem.formulas.len() != fof.len() || skolem.signature.predicates != signature.predicates {
        return Err(Error::Internal(
            "Skolemizer changed declaration count or predicate signature",
        ));
    }
    statistics.preprocessing_operations = skolem.statistics.operations;
    statistics.stored_nodes = skolem.statistics.allocated_nodes;
    let mut functions = parsed.functions;
    extend_symbols(
        &mut functions,
        &skolem.signature.functions,
        &mut statistics,
        limits,
    )?;
    let mut introduced = Vec::new();
    for symbol in skolem.introduced {
        tick(&mut statistics, limits)?;
        let declaration = *fof_origins
            .get(symbol.declaration)
            .ok_or(Error::Internal("Skolem origin outside FOF declarations"))?;
        introduced.push(Introduced {
            declaration,
            binder: symbol.binder,
            function: symbol.function,
            universals: symbol.universals,
        });
    }
    let mut transformed = skolem.formulas.into_iter();
    let mut clauses = Vec::new();
    let mut clause_names = Vec::new();
    let mut origins = Vec::new();
    let caps = clause_limits(limits);
    for (declaration, (name, body)) in sources.into_iter().enumerate() {
        tick(&mut statistics, limits)?;
        let output = match body {
            SourceBody::Cnf(clause) => vec![clause],
            SourceBody::Fof => {
                let formula = transformed
                    .next()
                    .ok_or(Error::Internal("missing Skolem output"))?;
                let removal_limits = fang_binder_removal_core::Limits {
                    max_formula_depth: caps.max_formula_depth,
                    max_operations: caps
                        .max_operations
                        .checked_sub(statistics.preprocessing_operations)
                        .ok_or(Error::Resource("preprocessing operation cap"))?,
                    max_output_nodes: caps
                        .max_stored_nodes
                        .checked_sub(statistics.stored_nodes)
                        .ok_or(Error::Resource("preprocessing storage cap"))?,
                };
                let removed = fang_binder_removal_core::remove_universals(formula, &removal_limits)
                    .map_err(Error::Removal)?;
                statistics.preprocessing_operations = add(
                    statistics.preprocessing_operations,
                    removed.statistics.operations,
                    caps.max_operations,
                    "preprocessing operation cap",
                )?;
                statistics.stored_nodes = add(
                    statistics.stored_nodes,
                    removed.statistics.output_nodes,
                    caps.max_stored_nodes,
                    "preprocessing storage cap",
                )?;
                let mut remaining = caps;
                remaining.max_clauses = caps
                    .max_clauses
                    .checked_sub(clauses.len())
                    .ok_or(Error::Resource("total output clause cap"))?;
                remaining.max_literals = caps
                    .max_literals
                    .checked_sub(statistics.raw_output_literals)
                    .ok_or(Error::Resource("total output literal cap"))?;
                let carried = ClauseStatistics {
                    operations: statistics.preprocessing_operations,
                    allocated_nodes: statistics.stored_nodes,
                    ..ClauseStatistics::default()
                };
                let result = fang_fof_core::nnf_entry::clausify_nnf_from(
                    &removed.formula,
                    &remaining,
                    carried,
                )
                .map_err(Error::Clausification)?;
                statistics.preprocessing_operations = result.statistics.operations;
                statistics.stored_nodes = result.statistics.allocated_nodes;
                result.clauses
            }
        };
        for (local_clause, clause) in output.into_iter().enumerate() {
            tick(&mut statistics, limits)?;
            if clauses.len() >= caps.max_clauses {
                return Err(Error::Resource("total output clause cap"));
            }
            if clause.len() > caps.max_literals_per_clause {
                return Err(Error::Resource("output clause width cap"));
            }
            statistics.raw_output_literals = add(
                statistics.raw_output_literals,
                clause.len(),
                caps.max_literals,
                "total output literal cap",
            )?;
            clause_names.push(format!("{name}_{declaration}_{local_clause}"));
            clauses.push(deduplicate(&clause));
            origins.push(Origin {
                declaration,
                local_clause,
            });
        }
    }
    if transformed.next().is_some() {
        return Err(Error::Internal("extra Skolem output"));
    }
    Ok(Prepared {
        problem: Problem {
            functions,
            predicates: parsed.predicates,
            clause_names,
            clauses,
        },
        origins,
        introduced,
        statistics,
    })
}
