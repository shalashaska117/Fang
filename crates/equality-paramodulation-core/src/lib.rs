// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// New single-occurrence paramodulation reconstruction.
#![forbid(unsafe_code)]

use fang::syntax::Term;
use fang_equality_inference_core::{Atom, Clause, Limits, Literal, Statistics, checked};
use fang_equality_occurrence_core as occurrence;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    LeftToRight,
    RightToLeft,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Root {
    Argument(usize),
    EqualityLeft,
    EqualityRight,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Position {
    pub literal: usize,
    pub root: Root,
    pub path: Vec<usize>,
}

#[derive(Clone, Copy, Debug)]
pub struct Witness<'a> {
    pub source_pivot: usize,
    pub direction: Direction,
    /// Position in the substituted target clause, not its original source AST.
    pub position: &'a Position,
    /// Finite simultaneous map, with strictly increasing keys.
    pub substitution: &'a [(u32, Term)],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Resource {
    Operations,
    OutputNodes,
    Literals,
    Arithmetic,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Input(fang_equality_inference_core::Error),
    Occurrence(occurrence::Error),
    Resource(Resource),
    SourcePivot,
    ExpectedPositiveEquality,
    TargetLiteral,
    TargetTerm,
    InvalidPath,
    NotMatched,
    VariableOverlap,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Reconstructed {
    pub clause: Clause,
    pub statistics: Statistics,
}

fn remaining(limits: &Limits, work: &Statistics) -> Limits {
    Limits {
        max_operations: limits.max_operations - work.operations,
        max_output_nodes: limits.max_output_nodes - work.output_nodes,
        ..*limits
    }
}

fn account(limits: &Limits, work: &mut Statistics, added: Statistics) -> Result<(), Error> {
    let operations = work
        .operations
        .checked_add(added.operations)
        .ok_or(Error::Resource(Resource::Arithmetic))?;
    let output_nodes = work
        .output_nodes
        .checked_add(added.output_nodes)
        .ok_or(Error::Resource(Resource::Arithmetic))?;
    if operations > limits.max_operations {
        return Err(Error::Resource(Resource::Operations));
    }
    if output_nodes > limits.max_output_nodes {
        return Err(Error::Resource(Resource::OutputNodes));
    }
    work.operations = operations;
    work.output_nodes = output_nodes;
    Ok(())
}

fn tick(limits: &Limits, work: &mut Statistics) -> Result<(), Error> {
    if work.operations >= limits.max_operations {
        return Err(Error::Resource(Resource::Operations));
    }
    work.operations += 1;
    Ok(())
}

fn variables(
    term: &Term,
    found: &mut Vec<u32>,
    limits: &Limits,
    work: &mut Statistics,
) -> Result<(), Error> {
    tick(limits, work)?;
    match term {
        Term::Var(id) => found.push(*id),
        Term::Fun(_, args) => variables_arguments(args, found, limits, work)?,
    }
    Ok(())
}

fn variables_arguments(
    args: &[Term],
    found: &mut Vec<u32>,
    limits: &Limits,
    work: &mut Statistics,
) -> Result<(), Error> {
    let mut index = 0;
    while index < args.len() {
        variables(&args[index], found, limits, work)?;
        index += 1;
    }
    Ok(())
}

fn literal_variables(
    literal: &Literal,
    found: &mut Vec<u32>,
    limits: &Limits,
    work: &mut Statistics,
) -> Result<(), Error> {
    tick(limits, work)?;
    match &literal.atom {
        Atom::Predicate(_, args) => variables_arguments(args, found, limits, work),
        Atom::Equal(left, right) => {
            variables(left, found, limits, work)?;
            variables(right, found, limits, work)
        }
    }
}

fn clause_variables(
    clause: &[Literal],
    limits: &Limits,
    work: &mut Statistics,
) -> Result<Vec<u32>, Error> {
    let mut found = Vec::new();
    let mut index = 0;
    while index < clause.len() {
        literal_variables(&clause[index], &mut found, limits, work)?;
        index += 1;
    }
    Ok(found)
}

fn absent(
    variable: u32,
    target: &[u32],
    limits: &Limits,
    work: &mut Statistics,
) -> Result<(), Error> {
    let mut right = 0;
    while right < target.len() {
        tick(limits, work)?;
        if variable == target[right] {
            return Err(Error::VariableOverlap);
        }
        right += 1;
    }
    Ok(())
}

fn apart(
    source: &[Literal],
    target: &[Literal],
    limits: &Limits,
    work: &mut Statistics,
) -> Result<(), Error> {
    let source = clause_variables(source, limits, work)?;
    let target = clause_variables(target, limits, work)?;
    let mut left = 0;
    while left < source.len() {
        absent(source[left], &target, limits, work)?;
        left += 1;
    }
    Ok(())
}

fn root_term(literal: &Literal, root: Root) -> Result<&Term, Error> {
    match (&literal.atom, root) {
        (Atom::Predicate(_, args), Root::Argument(index)) => {
            args.get(index).ok_or(Error::TargetTerm)
        }
        (Atom::Equal(left, _), Root::EqualityLeft) => Ok(left),
        (Atom::Equal(_, right), Root::EqualityRight) => Ok(right),
        _ => Err(Error::TargetTerm),
    }
}

fn equality_side(atom: &Atom, right_side: bool) -> Result<&Term, Error> {
    match (atom, right_side) {
        (Atom::Equal(left, _), false) => Ok(left),
        (Atom::Equal(_, right), true) => Ok(right),
        (Atom::Predicate(_, _), _) => Err(Error::ExpectedPositiveEquality),
    }
}

fn replace_root(literal: &mut Literal, root: Root, term: Term) -> Result<(), Error> {
    match (&mut literal.atom, root) {
        (Atom::Predicate(_, args), Root::Argument(index)) => {
            if index >= args.len() {
                return Err(Error::TargetTerm);
            }
            args[index] = term;
        }
        (Atom::Equal(left, _), Root::EqualityLeft) => *left = term,
        (Atom::Equal(_, right), Root::EqualityRight) => *right = term,
        _ => return Err(Error::TargetTerm),
    }
    Ok(())
}

fn selected<'a>(
    mut term: &'a Term,
    path: &[usize],
    limits: &Limits,
    work: &mut Statistics,
) -> Result<&'a Term, Error> {
    let mut index = 0;
    while index < path.len() {
        tick(limits, work)?;
        term = match term {
            Term::Fun(_, args) => args.get(path[index]).ok_or(Error::InvalidPath)?,
            Term::Var(_) => return Err(Error::InvalidPath),
        };
        index += 1;
    }
    Ok(term)
}

fn input_result<T>(result: Result<T, fang_equality_inference_core::Error>) -> Result<T, Error> {
    match result {
        Ok(value) => Ok(value),
        Err(error) => Err(Error::Input(error)),
    }
}

fn occurrence_result<T>(result: Result<T, occurrence::Error>) -> Result<T, Error> {
    match result {
        Ok(value) => Ok(value),
        Err(error) => Err(Error::Occurrence(error)),
    }
}

fn source_residual(
    source: Clause,
    pivot: usize,
    limits: &Limits,
    work: &mut Statistics,
) -> Result<Clause, Error> {
    let mut clause = Vec::new();
    for (index, literal) in source.into_iter().enumerate() {
        tick(limits, work)?;
        if index != pivot {
            clause.push(literal);
        }
    }
    Ok(clause)
}

fn append_target(
    target: Clause,
    clause: &mut Clause,
    limits: &Limits,
    work: &mut Statistics,
) -> Result<(), Error> {
    for literal in target {
        tick(limits, work)?;
        clause.push(literal);
    }
    Ok(())
}

fn replace_selected(
    root: &Term,
    path: &[usize],
    from: &Term,
    to: &Term,
    functions: &[usize],
    limits: &Limits,
    work: &mut Statistics,
) -> Result<Term, Error> {
    let at = selected(root, path, limits, work)?;
    let compared = input_result(checked::terms_equal(
        from,
        at,
        functions,
        &remaining(limits, work),
    ))?;
    account(limits, work, compared.statistics)?;
    if !compared.equal {
        return Err(Error::NotMatched);
    }
    let available = remaining(limits, work);
    let replacement = occurrence_result(occurrence::replace_at(
        root,
        path,
        to,
        functions,
        &occurrence::Limits {
            max_depth: available.max_depth,
            max_output_nodes: available.max_output_nodes,
            max_operations: available.max_operations,
        },
    ))?;
    account(
        limits,
        work,
        Statistics {
            operations: replacement.statistics.operations,
            output_nodes: replacement.statistics.output_nodes,
        },
    )?;
    Ok(replacement.term)
}

/// Reconstruct unrestricted paramodulation at one post-substitution occurrence.
/// Both premises are universally closed and must already have disjoint variable
/// IDs. The same simultaneous witness instantiates both premises. Signature and
/// witness validation precede rule guards. A failure returns no partial clause.
/// No term ordering, maximality, MGU or search-completeness claim is made here.
pub fn paramodulate(
    source: &[Literal],
    target: &[Literal],
    witness: Witness<'_>,
    functions: &[usize],
    predicates: &[usize],
    limits: &Limits,
) -> Result<Reconstructed, Error> {
    let mut work = Statistics::default();
    let source_result = input_result(checked::instantiate(
        source,
        witness.substitution,
        functions,
        predicates,
        &remaining(limits, &work),
    ))?;
    account(limits, &mut work, source_result.statistics)?;
    let target_result = input_result(checked::instantiate(
        target,
        witness.substitution,
        functions,
        predicates,
        &remaining(limits, &work),
    ))?;
    account(limits, &mut work, target_result.statistics)?;
    apart(source, target, limits, &mut work)?;
    let source_clause = source_result.clause;
    let mut target_clause = target_result.clause;
    let pivot = source_clause
        .get(witness.source_pivot)
        .ok_or(Error::SourcePivot)?;
    if !pivot.positive {
        return Err(Error::ExpectedPositiveEquality);
    }
    let reverse = match witness.direction {
        Direction::LeftToRight => false,
        Direction::RightToLeft => true,
    };
    let from = equality_side(&pivot.atom, reverse)?;
    let to = equality_side(&pivot.atom, !reverse)?;
    let position = witness.position;
    let literal = target_clause
        .get(position.literal)
        .ok_or(Error::TargetLiteral)?;
    let root = root_term(literal, position.root)?;
    let replacement =
        replace_selected(root, &position.path, from, to, functions, limits, &mut work)?;
    replace_root(
        &mut target_clause[position.literal],
        position.root,
        replacement,
    )?;
    let count = (source_clause.len() - 1)
        .checked_add(target_clause.len())
        .ok_or(Error::Resource(Resource::Arithmetic))?;
    if count > limits.max_literals {
        return Err(Error::Resource(Resource::Literals));
    }
    let mut clause = source_residual(source_clause, witness.source_pivot, limits, &mut work)?;
    append_target(target_clause, &mut clause, limits, &mut work)?;
    Ok(Reconstructed {
        clause,
        statistics: work,
    })
}
