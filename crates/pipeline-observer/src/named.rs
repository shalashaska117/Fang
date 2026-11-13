// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! `prepare_parsed` with definitional clausification. The steps, counters and caps are those of
//! `prepare_impl`; only the clausification of each FOF block differs: after binder removal the block
//! is renamed and clausified by the naming entry at the caller's threshold, with fresh predicates
//! numbered from `first` and threaded from block to block, as the checker's `replayNamedBlocks` does.

use super::*;
pub use fang_fof_core::naming::renumber_predicate;

/// The assembled problem before renumbering, with the range of named predicates and their arities.
#[derive(Debug)]
pub struct NamedPrepared {
    pub prepared: Prepared,
    /// The first named predicate, one after the last predicate of the parsed table.
    pub first: u32,
    /// One after the last named predicate.
    pub next: u32,
    /// The arity of each named predicate, from `first` on.
    pub named_arities: Vec<usize>,
}

fn nnf_below(formula: &fang_fof_core::Nnf, first: u32) -> bool {
    match formula {
        fang_fof_core::Nnf::Literal(literal) => literal.predicate < first,
        fang_fof_core::Nnf::True | fang_fof_core::Nnf::False => true,
        fang_fof_core::Nnf::And(left, right) | fang_fof_core::Nnf::Or(left, right) => {
            nnf_below(left, first) && nnf_below(right, first)
        }
    }
}

/// Parse output to assembled clauses with naming. `first` must equal the length of the parsed
/// predicate table, whose last entry is the reserved equality slot.
pub fn prepare_parsed_named(
    parsed: fang_quantified_fof_frontend::Parsed,
    limits: &Limits,
    threshold: usize,
    first: u32,
) -> Result<NamedPrepared, Error> {
    if u32::try_from(parsed.predicates.len()).ok() != Some(first) {
        return Err(Error::Internal(
            "first named predicate does not follow the predicate table",
        ));
    }
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
    let mut next = first;
    let mut named_arities = Vec::new();
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
                if !nnf_below(&removed.formula, first) {
                    return Err(Error::Internal(
                        "block predicate at or above the first named predicate",
                    ));
                }
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
                let result = fang_fof_core::naming::name_then_clausify(
                    &removed.formula,
                    threshold,
                    next,
                    &remaining,
                    carried,
                )
                .map_err(Error::Clausification)?;
                statistics.preprocessing_operations = result.statistics.operations;
                statistics.stored_nodes = result.statistics.allocated_nodes;
                next = result.next;
                named_arities.extend(
                    result
                        .definitions
                        .iter()
                        .map(|definition| definition.arguments.len()),
                );
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
    Ok(NamedPrepared {
        prepared: Prepared {
            problem: Problem {
                functions,
                predicates: parsed.predicates,
                clause_names,
                clauses,
            },
            origins,
            introduced,
            statistics,
        },
        first,
        next,
        named_arities,
    })
}
