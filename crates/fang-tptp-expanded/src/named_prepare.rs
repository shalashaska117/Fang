// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! `prepare` with definitional clausification, as the checker's `replayNamedFrom` prepares: fresh
//! predicates are numbered from one after the reserved equality slot; after assembly the checks of
//! `finishWith` run, the slot moves above the named predicates (n becomes n+K, n+1+j becomes n+j) and
//! a fresh reservation over the original arities followed by the K named arities decodes every clause.

use super::*;
use fang_quantified_pipeline_observer::named::{prepare_parsed_named, renumber_predicate};
use std::collections::BTreeSet;

/// A fresh name for each named predicate, distinct from every original predicate name.
fn named_symbols(
    original: &[Symbol],
    arities: &[usize],
    work: &mut Work,
) -> Result<Vec<Symbol>, Error> {
    let mut used: BTreeSet<&str> = original.iter().map(|symbol| symbol.name.as_str()).collect();
    used.insert(EQUALITY_NAME);
    let mut symbols = Vec::with_capacity(arities.len());
    for (index, arity) in arities.iter().enumerate() {
        let mut name = format!("fang_named_{index}");
        while used.contains(name.as_str()) {
            work.add(1)?;
            name.push('_');
        }
        work.add(name.len())?;
        symbols.push(Symbol {
            name,
            arity: *arity,
        });
    }
    Ok(symbols)
}

/// Parse the entire input, reserve equality after every original predicate, run the shared
/// preprocessing with naming at `threshold`, check the named range, renumber, reserve again over
/// the extended table and decode every final clause. Failure exposes no partial Prepared value.
pub fn prepare_named(input: &[u8], limits: &Limits, threshold: usize) -> Result<Prepared, Error> {
    let parsed =
        fang_tptp_full_frontend_candidate::parse(input, &limits.input).map_err(Error::Input)?;
    let encoded = parsed
        .encode(limits.max_predicates, limits.max_bridge_literals)
        .map_err(Error::Encoding)?;
    let mut work = Work {
        used: 0,
        maximum: limits.max_adapter_operations,
    };
    if encoded.declarations.len() > limits.preprocessing.max_declarations {
        return Err(Error::Resource("total source declaration cap"));
    }
    let Converted {
        parsed,
        reservation,
        mut sources,
        original_predicates,
        active_sources,
    } = convert_parsed(encoded, &mut work)?;
    let shared_limits = pipeline::Limits {
        input: fang_quantified_fof_frontend::Limits {
            input: limits.input.input.clone(),
            max_formula_depth: limits.input.max_formula_depth,
            max_formula_nodes: limits.input.max_formula_nodes,
            max_binders: limits.input.max_binders,
        },
        preprocessing: limits.preprocessing,
        max_bookkeeping_operations: limits.max_bookkeeping_operations,
        max_generated_name_bytes: limits.max_generated_name_bytes,
    };
    let slot = reservation.equality_id();
    let first = slot
        .checked_add(1)
        .ok_or(Error::Internal("first named predicate overflows"))?;
    let named = prepare_parsed_named(parsed, &shared_limits, threshold, first)
        .map_err(Error::Preprocessing)?;
    let mut prepared = named.prepared;
    let mut problem = prepared.problem;
    let reserved = problem
        .predicates
        .pop()
        .ok_or(Error::Internal("missing reserved output slot"))?;
    if reserved.name != EQUALITY_NAME
        || reserved.arity != 2
        || problem.predicates != original_predicates
    {
        return Err(Error::Internal(
            "preprocessing changed the reserved predicate table",
        ));
    }
    if prepared.origins.len() != problem.clauses.len()
        || problem.clause_names.len() != problem.clauses.len()
    {
        return Err(Error::Internal(
            "preprocessing clause metadata length differs",
        ));
    }
    for origin in &mut prepared.origins {
        work.add(1)?;
        origin.declaration = *active_sources
            .get(origin.declaration)
            .ok_or(Error::Internal("active clause origin outside source map"))?;
    }
    for introduced in &mut prepared.introduced {
        work.add(1)?;
        introduced.declaration = *active_sources
            .get(introduced.declaration)
            .ok_or(Error::Internal("active Skolem origin outside source map"))?;
    }
    let mut cursor = 0;
    for (index, source) in sources.iter_mut().enumerate() {
        work.add(1)?;
        let start = cursor;
        while let Some(origin) = prepared.origins.get(cursor) {
            if origin.declaration != index {
                break;
            }
            work.add(1)?;
            if origin.local_clause != cursor - start {
                return Err(Error::Internal("preprocessing local clause order differs"));
            }
            cursor += 1;
        }
        if source
            .cnf_clauses
            .is_some_and(|expected| cursor - start != expected)
        {
            return Err(Error::Internal(
                "source CNF declaration changed clause count",
            ));
        }
        source.clauses = start..cursor;
    }
    if cursor != prepared.origins.len() {
        return Err(Error::Internal(
            "preprocessing origin outside complete source order",
        ));
    }
    // The checks of the checker's final step: the retained CNF clauses lie below the first named
    // predicate, every clause below the next free one, and there is one arity per named predicate.
    let count = named
        .next
        .checked_sub(first)
        .ok_or(Error::Internal("named predicate range shrinks"))?;
    if named.named_arities.len() != count as usize {
        return Err(Error::Internal("named predicate count and arities differ"));
    }
    for source in sources.iter().filter(|source| source.cnf_clauses.is_some()) {
        for clause in &problem.clauses[source.clauses.clone()] {
            work.add(clause.len())?;
            if clause.iter().any(|literal| literal.predicate >= first) {
                return Err(Error::Internal("retained clause reaches the named range"));
            }
        }
    }
    let mut table: Vec<usize> = original_predicates
        .iter()
        .map(|symbol| symbol.arity)
        .collect();
    work.add(named.named_arities.len())?;
    table.extend(named.named_arities.iter().copied());
    let named_reservation =
        Reservation::new(table, limits.max_predicates).map_err(Error::Conversion)?;
    let mut clauses = Vec::new();
    for mut clause in problem.clauses {
        work.add(1)?;
        work.add(clause.len())?;
        for literal in &mut clause {
            if literal.predicate >= named.next {
                return Err(Error::Internal("clause predicate beyond the named range"));
            }
            literal.predicate = renumber_predicate(literal.predicate, slot, count)
                .ok_or(Error::Internal("renumbered predicate overflows"))?;
        }
        clauses.push(
            named_reservation
                .decode_clause(clause, limits.max_bridge_literals)
                .map_err(Error::Conversion)?,
        );
    }
    let mut predicates = original_predicates;
    let named_symbols = named_symbols(&predicates, &named.named_arities, &mut work)?;
    predicates.extend(named_symbols);
    Ok(Prepared {
        clauses,
        functions: problem.functions,
        predicates,
        clause_names: problem.clause_names,
        sources,
        origins: prepared.origins,
        introduced: prepared.introduced,
        statistics: prepared.statistics,
        adapter_operations: work.used,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const DISJUNCTION: &[u8] =
        b"fof(a, axiom, ![X, Y] : ((p(X) & q(X) & r(X)) | (s(Y) & t(Y) & u(Y)))).\n";

    fn arities(prepared: &Prepared) -> Vec<usize> {
        prepared
            .predicates
            .iter()
            .map(|symbol| symbol.arity)
            .collect()
    }

    #[test]
    fn threshold_eight_names_one_side_as_the_checker_control_does() {
        let prepared = prepare_named(DISJUNCTION, &Limits::default(), 8).unwrap();
        assert_eq!(arities(&prepared), vec![1, 1, 1, 1, 1, 1, 1]);
        assert_eq!(prepared.clauses.len(), 6);
        assert_eq!(prepared.predicates[6].name, "fang_named_0");
    }

    #[test]
    fn a_threshold_that_names_nothing_gives_the_plain_preparation() {
        let inputs: [&[u8]; 4] = [
            DISJUNCTION,
            b"cnf(z,axiom,$true|hidden(f(a))).fof(e,axiom,![Unused,U]:?[X]:(X=U & q(X))).cnf(t,axiom,$true|late(fang_skolem_3)).",
            b"fof(a,axiom,p(a)).fof(b,conjecture,p(a)).",
            b"fof(a,axiom,![X]:(p(X) => (q(X) | r(X)))).cnf(c,axiom,~q(a)).fof(e,axiom,a = b).",
        ];
        for input in inputs {
            let plain = prepare(input, &Limits::default());
            let named = prepare_named(input, &Limits::default(), usize::MAX);
            match (plain, named) {
                (Ok(plain), Ok(named)) => {
                    assert_eq!(
                        format!("{:?}", plain.clauses),
                        format!("{:?}", named.clauses)
                    );
                    assert_eq!(plain.predicates, named.predicates);
                    assert_eq!(plain.functions, named.functions);
                    assert_eq!(plain.clause_names, named.clause_names);
                    assert_eq!(plain.origins, named.origins);
                    assert_eq!(plain.introduced, named.introduced);
                }
                (Err(plain), Err(named)) => assert_eq!(format!("{plain:?}"), format!("{named:?}")),
                (plain, named) => panic!("plain {plain:?} and named {named:?} disagree"),
            }
        }
    }

    #[test]
    fn named_predicates_count_toward_the_predicate_table_limit() {
        let limits = Limits {
            max_predicates: 7,
            ..Limits::default()
        };
        assert!(prepare_named(DISJUNCTION, &limits, usize::MAX).is_ok());
        assert!(matches!(
            prepare_named(DISJUNCTION, &limits, 8),
            Err(Error::Conversion(_))
        ));
    }
}
