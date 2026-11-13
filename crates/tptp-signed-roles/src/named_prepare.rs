// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Staged with the extracted naming core as a module of signed-roles.
use super::*;

fn nnf_below(formula: &fang_fof_core::Nnf, first: u32) -> bool {
    match formula {
        fang_fof_core::Nnf::Literal(literal) => literal.predicate < first,
        fang_fof_core::Nnf::True | fang_fof_core::Nnf::False => true,
        fang_fof_core::Nnf::And(left, right) | fang_fof_core::Nnf::Or(left, right) => {
            nnf_below(left, first) && nnf_below(right, first)
        }
    }
}

/// Prepare with the same naming, fresh predicate threading and equality-slot
/// renumbering as Lean replayNamedTask. Threshold is supplied by the shared
/// limits adapter; legacy prepare_task remains available unchanged.
pub fn prepare_task_named(
    input: &[u8],
    selection: Selection,
    limits: &Limits,
    threshold: usize,
) -> Result<Prepared, Error> {
    let parsed =
        fang_tptp_full_frontend_candidate::parse(input, &limits.input).map_err(Error::Input)?;
    let encoded = parsed
        .encode(limits.max_predicates, limits.max_bridge_literals)
        .map_err(Error::Encoding)?;
    let goals: Vec<usize> = encoded
        .declarations
        .iter()
        .enumerate()
        .filter(|(_, declaration)| declaration.role == Role::Conjecture)
        .map(|(index, _)| index)
        .collect();
    let goal = match selection {
        Selection::Goal(index) => Some(*goals.get(index).ok_or(Error::NoGoal)?),
        Selection::Inputs if goals.is_empty() => None,
        Selection::Inputs => return Err(Error::GoalsPresent),
    };
    // The role crate decides which declarations enter the task and with which sign.
    let selected: Vec<(usize, bool)> = {
        let obligation = encoded
            .obligations()
            .map_err(Error::Input)?
            .find(|obligation| obligation.goal_index() == goal)
            .ok_or(Error::Internal("selected obligation is missing"))?;
        obligation
            .declarations()
            .map(|signed| (signed.source_index, signed.positive))
            .collect()
    };
    let signature = encoded.signature();
    let reservation = encoded.reservation;
    let mut original_predicates: Vec<usize> = encoded
        .original_predicates
        .iter()
        .map(|symbol| symbol.arity)
        .collect();
    let mut sign_of = vec![None; encoded.declarations.len()];
    for &(index, positive) in &selected {
        *sign_of
            .get_mut(index)
            .ok_or(Error::Internal("selected declaration outside the source"))? = Some(positive);
    }
    let mut fof = Vec::new();
    let mut signs = Vec::new();
    // Each layout item with its source index, original role and sign.
    let mut layout = Vec::new();
    for (index, declaration) in encoded.declarations.into_iter().enumerate() {
        let Some(positive) = sign_of[index] else {
            continue;
        };
        let owner = (index, declaration.role, positive);
        match declaration.body {
            EncodedBody::Cnf(None) => layout.push((Item::Empty, owner)),
            EncodedBody::Cnf(Some(clause)) => {
                if !positive {
                    return Err(Error::Internal("negative CNF item"));
                }
                layout.push((Item::Cnf(clause), owner));
            }
            EncodedBody::Fof(formula) => {
                fof.push(fang_skolem_core::Declaration { formula, positive });
                signs.push((index, positive));
                layout.push((Item::Fof, owner));
            }
        }
    }
    let skolem = fang_skolem_core::skolemize_problem(&fof, &signature, &limits.skolem)
        .map_err(Error::Skolem)?;
    if skolem.formulas.len() != fof.len() || skolem.signature.predicates != signature.predicates {
        return Err(Error::Internal(
            "Skolemizer changed declaration count or predicate signature",
        ));
    }
    let function_arities = skolem.signature.functions;
    let mut formulas = skolem.formulas.into_iter();
    let first = reservation
        .equality_id()
        .checked_add(1)
        .ok_or(Error::Internal("first named predicate overflows"))?;
    let mut next = first;
    let mut named_arities = Vec::new();
    let mut ordinary = Vec::new();
    let mut origins = Vec::new();
    for (item, (source_index, role, positive)) in layout {
        let start = ordinary.len();
        match item {
            Item::Empty => {}
            Item::Cnf(clause) => ordinary.push(deduplicate(&clause)),
            Item::Fof => {
                let formula = formulas
                    .next()
                    .ok_or(Error::Internal("missing Skolem output"))?;
                let removed = fang_binder_removal_core::remove_universals(formula, &limits.removal)
                    .map_err(Error::Removal)?;
                if !nnf_below(&removed.formula, first) {
                    return Err(Error::Internal("block predicate reaches named range"));
                }
                let block = fang_fof_core::naming::name_then_clausify(
                    &removed.formula,
                    threshold,
                    next,
                    &limits.clausification,
                    Default::default(),
                )
                .map_err(Error::Clausification)?;
                next = block.next;
                named_arities.extend(
                    block
                        .definitions
                        .iter()
                        .map(|definition| definition.arguments.len()),
                );
                ordinary.extend(block.clauses.iter().map(deduplicate));
            }
        }
        origins.push(Origin {
            source_index,
            role,
            positive,
            clauses: start..ordinary.len(),
        });
    }
    if formulas.next().is_some() {
        return Err(Error::Internal("extra Skolem output"));
    }
    let count = next
        .checked_sub(first)
        .ok_or(Error::Internal("named predicate range shrinks"))?;
    if named_arities.len() != count as usize
        || ordinary
            .iter()
            .flatten()
            .any(|literal| literal.predicate >= next)
    {
        return Err(Error::Internal("named predicate range or arities differ"));
    }
    let slot = reservation.equality_id();
    original_predicates.extend(named_arities);
    let named_reservation = fang_fof_equality_bridge::Reservation::new(
        original_predicates.clone(),
        limits.max_predicates,
    )
    .map_err(Error::Conversion)?;
    let mut clauses = Vec::new();
    for mut clause in ordinary {
        for literal in &mut clause {
            literal.predicate =
                fang_fof_core::naming::renumber_predicate(literal.predicate, slot, count)
                    .ok_or(Error::Internal("renumbered predicate overflows"))?;
        }
        clauses.push(
            named_reservation
                .decode_clause(clause, limits.max_bridge_literals)
                .map_err(Error::Conversion)?,
        );
    }
    Ok(Prepared {
        goal,
        signs,
        clauses,
        function_arities,
        predicate_arities: original_predicates,
        origins,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    const INPUT: &[u8] = b"fof(a,axiom,![X,Y]:((p(X)&q(X)&r(X))|(s(Y)&t(Y)&u(Y)))).";

    #[test]
    fn naming_reduces_distribution_and_extends_predicate_table() {
        let limits = Limits::default();
        let plain = prepare_task(INPUT, Selection::Inputs, &limits).unwrap();
        let named = prepare_task_named(INPUT, Selection::Inputs, &limits, 8).unwrap();
        assert_eq!(plain.clauses.len(), 9);
        assert_eq!(named.clauses.len(), 6);
        assert_eq!(
            named.predicate_arities.len(),
            plain.predicate_arities.len() + 1
        );
        assert_eq!(named.origins[0].clauses, 0..6);
        assert_eq!(named.function_arities, plain.function_arities);
    }

    #[test]
    fn no_naming_preserves_exact_prepared_clauses_and_origins() {
        let limits = Limits::default();
        let plain = prepare_task(INPUT, Selection::Inputs, &limits).unwrap();
        let named = prepare_task_named(INPUT, Selection::Inputs, &limits, usize::MAX).unwrap();
        assert_eq!(named.clauses, plain.clauses);
        assert_eq!(named.origins, plain.origins);
        assert_eq!(named.predicate_arities, plain.predicate_arities);
        assert_eq!(named.function_arities, plain.function_arities);
    }

    #[test]
    fn named_predicates_count_toward_reserved_table_limit() {
        let limits = Limits {
            max_predicates: 7,
            ..Limits::default()
        };
        assert!(prepare_task(INPUT, Selection::Inputs, &limits).is_ok());
        assert!(matches!(
            prepare_task_named(INPUT, Selection::Inputs, &limits, 8),
            Err(Error::Conversion(
                fang_fof_equality_bridge::Error::PredicateLimit
            ))
        ));
    }

    #[test]
    fn equality_keeps_its_kind_after_named_predicate_insertion() {
        let mut input = INPUT.to_vec();
        input.extend_from_slice(b"cnf(e,axiom,a=b).fof(g,conjecture,$true).");
        let prepared =
            prepare_task_named(&input, Selection::Goal(0), &Limits::default(), 8).unwrap();
        assert_eq!(prepared.goal, Some(2));
        assert_eq!(prepared.origins[1].clauses, 6..7);
        assert!(matches!(
            &prepared.clauses[6][0].atom,
            fang_equality_inference_core::Atom::Equal(_, _)
        ));
        assert_eq!(prepared.origins[2].clauses, 7..8);
        assert!(!prepared.origins[2].positive);
    }
}
