// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Definitional clausification: renaming of subformulas of a quantifier-free NNF.

use super::{Error, Limits, Nnf, Resource, Statistics, Work};
use fang::syntax::{Clause, Literal, Term};

/// One fresh predicate. Its atom over `arguments` replaced one subformula, the
/// body, and the definition `~predicate(arguments) | body` is part of the output.
#[derive(Debug, PartialEq, Eq)]
pub struct Definition {
    pub predicate: u32,
    /// The variables of the body in increasing order, each once.
    pub arguments: Vec<u32>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Renamed {
    /// The renamed input, conjoined on the right with each definition in
    /// naming order. Without a definition it is a copy of the input.
    pub formula: Nnf,
    pub definitions: Vec<Definition>,
    /// The first predicate index this call did not use.
    pub next: u32,
    pub statistics: Statistics,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Named {
    /// The clauses of `Renamed::formula`, in the order of the distributive clausifier.
    pub clauses: Vec<Clause>,
    pub definitions: Vec<Definition>,
    pub next: u32,
    pub statistics: Statistics,
}

fn saturating_add(left: usize, right: usize) -> usize {
    match left.checked_add(right) {
        Some(value) => value,
        None => usize::MAX,
    }
}

fn saturating_mul(left: usize, right: usize) -> usize {
    match left.checked_mul(right) {
        Some(value) => value,
        None => usize::MAX,
    }
}

/// Insert one variable into an increasing list without repetition.
fn insert_variable(
    variables: &mut Vec<u32>,
    id: u32,
    limits: &Limits,
    work: &mut Work,
) -> Result<(), Error> {
    let mut index = 0;
    while index < variables.len() && variables[index] < id {
        work.tick(limits)?;
        index += 1;
    }
    if index < variables.len() && variables[index] == id {
        return Ok(());
    }
    work.allocate(1, limits)?;
    // The translated library accepts an insertion only before an existing element.
    if index < variables.len() {
        variables.insert(index, id);
    } else {
        variables.push(id);
    }
    Ok(())
}

// Term depth is bounded by the validation of the checked pipeline.
fn collect_term(
    term: &Term,
    variables: &mut Vec<u32>,
    limits: &Limits,
    work: &mut Work,
) -> Result<(), Error> {
    work.tick(limits)?;
    match term {
        Term::Var(id) => insert_variable(variables, *id, limits, work),
        Term::Fun(_, arguments) => {
            let mut index = 0;
            while index < arguments.len() {
                collect_term(&arguments[index], variables, limits, work)?;
                index += 1;
            }
            Ok(())
        }
    }
}

fn collect_nnf(
    formula: &Nnf,
    variables: &mut Vec<u32>,
    limits: &Limits,
    work: &mut Work,
) -> Result<(), Error> {
    work.tick(limits)?;
    match formula {
        Nnf::Literal(literal) => {
            let mut index = 0;
            while index < literal.arguments.len() {
                collect_term(&literal.arguments[index], variables, limits, work)?;
                index += 1;
            }
            Ok(())
        }
        Nnf::True | Nnf::False => Ok(()),
        Nnf::And(left, right) | Nnf::Or(left, right) => {
            collect_nnf(left, variables, limits, work)?;
            collect_nnf(right, variables, limits, work)
        }
    }
}

fn variable_terms(variables: &[u32], limits: &Limits, work: &mut Work) -> Result<Vec<Term>, Error> {
    let mut terms = Vec::new();
    let mut index = 0;
    while index < variables.len() {
        work.tick(limits)?;
        work.allocate(1, limits)?;
        terms.push(Term::Var(variables[index]));
        index += 1;
    }
    Ok(terms)
}

struct Renamer {
    threshold: usize,
    next: u32,
    definitions: Vec<Definition>,
    /// `~p(x) | body` for each definition, in naming order.
    bodies: Vec<Nnf>,
    work: Work,
}

impl Renamer {
    /// Replace `body` by a fresh atom over its variables and record the definition.
    fn name(&mut self, body: Nnf, limits: &Limits) -> Result<Nnf, Error> {
        self.work.tick(limits)?;
        let predicate = self.next;
        self.next = self
            .next
            .checked_add(1)
            .ok_or(Error::Resource(Resource::Arithmetic))?;
        let mut variables = Vec::new();
        collect_nnf(&body, &mut variables, limits, &mut self.work)?;
        let atom_arguments = variable_terms(&variables, limits, &mut self.work)?;
        let guard_arguments = variable_terms(&variables, limits, &mut self.work)?;
        // Two literals, one disjunction and one definition record.
        self.work.allocate(4, limits)?;
        let guard = Nnf::Literal(Literal {
            positive: false,
            predicate,
            arguments: guard_arguments,
        });
        self.bodies.push(Nnf::Or(Box::new(guard), Box::new(body)));
        self.definitions.push(Definition {
            predicate,
            arguments: variables,
        });
        Ok(Nnf::Literal(Literal {
            positive: true,
            predicate,
            arguments: atom_arguments,
        }))
    }

    /// Copy the formula bottom-up and return it with its clause count under
    /// distribution, saturated at `usize::MAX`. At a disjunction whose two
    /// sides both count more than one clause and whose product exceeds the
    /// threshold, the side with the larger count, the left one on a tie, is
    /// named and counts one clause. The other side then keeps the product at
    /// its own count, so a disjunction names at most one side.
    fn rename(&mut self, formula: &Nnf, limits: &Limits) -> Result<(Nnf, usize), Error> {
        self.work.tick(limits)?;
        match formula {
            Nnf::Literal(literal) => {
                self.work.allocate(1, limits)?;
                let literal = super::copy_literal(literal, limits, &mut self.work)?;
                Ok((Nnf::Literal(literal), 1))
            }
            Nnf::True => {
                self.work.allocate(1, limits)?;
                Ok((Nnf::True, 0))
            }
            Nnf::False => {
                self.work.allocate(1, limits)?;
                Ok((Nnf::False, 1))
            }
            Nnf::And(left, right) => {
                self.work.allocate(1, limits)?;
                let (left, left_count) = self.rename(left, limits)?;
                let (right, right_count) = self.rename(right, limits)?;
                Ok((
                    Nnf::And(Box::new(left), Box::new(right)),
                    saturating_add(left_count, right_count),
                ))
            }
            Nnf::Or(left, right) => {
                self.work.allocate(1, limits)?;
                let (left, left_count) = self.rename(left, limits)?;
                let (right, right_count) = self.rename(right, limits)?;
                if left_count > 1
                    && right_count > 1
                    && saturating_mul(left_count, right_count) > self.threshold
                {
                    if left_count >= right_count {
                        let atom = self.name(left, limits)?;
                        Ok((Nnf::Or(Box::new(atom), Box::new(right)), right_count))
                    } else {
                        let atom = self.name(right, limits)?;
                        Ok((Nnf::Or(Box::new(left), Box::new(atom)), left_count))
                    }
                } else {
                    Ok((
                        Nnf::Or(Box::new(left), Box::new(right)),
                        saturating_mul(left_count, right_count),
                    ))
                }
            }
        }
    }
}

/// Rename subformulas of a quantifier-free NNF so that no disjunction
/// distributes into more than `threshold` clauses unless one of its sides
/// counts at most one clause. Fresh predicates are `next`, `next + 1`, ... in
/// naming order, which is bottom-up and left to right. Every subformula occurs
/// positively in NNF, so the definition of a fresh predicate `p` naming `body`
/// is the single implication `~p(x) | body`, with `x` the variables of `body`.
///
/// The operation and storage counters start from `statistics` and are bounded
/// by `limits`. The input depth must already be bounded by the caller. A
/// failure exposes no partial result.
pub fn name_nnf(
    formula: &Nnf,
    threshold: usize,
    next: u32,
    limits: &Limits,
    statistics: Statistics,
) -> Result<Renamed, Error> {
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
    let mut renamer = Renamer {
        threshold,
        next,
        definitions: Vec::new(),
        bodies: Vec::new(),
        work: Work { statistics },
    };
    let (renamed, _) = renamer.rename(formula, limits)?;
    let Renamer {
        next,
        definitions,
        bodies,
        mut work,
        ..
    } = renamer;
    // One operation and one conjunction node per definition, charged before the loop.
    let count = bodies.len();
    work.statistics.operations = super::bounded_add(
        work.statistics.operations,
        count,
        limits.max_operations,
        Resource::Operations,
    )?;
    work.allocate(count, limits)?;
    let mut combined = renamed;
    for body in bodies {
        combined = Nnf::And(Box::new(combined), Box::new(body));
    }
    Ok(Renamed {
        formula: combined,
        definitions,
        next,
        statistics: work.statistics,
    })
}

/// Rename, then clausify the renamed formula with the distributive clausifier.
/// Both steps start their counters from `statistics`, so a formula in which
/// nothing is named gives the clauses and counters of `clausify_nnf_from` on
/// the input.
pub fn name_then_clausify(
    formula: &Nnf,
    threshold: usize,
    next: u32,
    limits: &Limits,
    statistics: Statistics,
) -> Result<Named, Error> {
    let renamed = name_nnf(formula, threshold, next, limits, statistics)?;
    let clausified = super::nnf_entry::clausify_nnf_from(&renamed.formula, limits, statistics)?;
    Ok(Named {
        clauses: clausified.clauses,
        definitions: renamed.definitions,
        next: renamed.next,
        statistics: clausified.statistics,
    })
}

/// The predicate index the checker uses after assembly, when `count` named
/// predicates follow the equality slot `slot`: the slot moves above them and
/// each of them moves down by one. Indices above the last named predicate and
/// below the slot keep their value. `None` when the moved slot does not fit.
pub fn renumber_predicate(predicate: u32, slot: u32, count: u32) -> Option<u32> {
    if predicate < slot {
        Some(predicate)
    } else if predicate == slot {
        slot.checked_add(count)
    } else if predicate - slot <= count {
        Some(predicate - 1)
    } else {
        Some(predicate)
    }
}
