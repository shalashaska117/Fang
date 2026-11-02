// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// New equality reconstruction code; Fang terms retain their existing notices.
#![forbid(unsafe_code)]

use fang::syntax::Term;

pub mod checked;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Atom {
    Predicate(u32, Vec<Term>),
    Equal(Term, Term),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Literal {
    pub positive: bool,
    pub atom: Atom,
}

pub type Clause = Vec<Literal>;
pub type Substitution = Vec<(u32, Term)>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub max_depth: usize,
    pub max_literals: usize,
    pub max_bindings: usize,
    pub max_output_nodes: usize,
    pub max_operations: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_depth: 64,
            max_literals: 256,
            max_bindings: 256,
            max_output_nodes: 100_000,
            max_operations: 1_000_000,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    PivotIndex,
    ExpectedNegativeEquality,
    NotEqualized,
    UnknownFunction,
    FunctionArity,
    UnknownPredicate,
    PredicateArity,
    SubstitutionOrder,
    Depth,
    Literals,
    Bindings,
    OutputNodes,
    Operations,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Statistics {
    pub operations: usize,
    /// Cumulative constructed term nodes, including discarded pivot instances.
    pub output_nodes: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Reconstructed {
    pub clause: Clause,
    pub statistics: Statistics,
}

fn tick(limits: &Limits, work: &mut Statistics) -> Result<(), Error> {
    if work.operations >= limits.max_operations {
        return Err(Error::Operations);
    }
    work.operations += 1;
    Ok(())
}

fn visit(depth: usize, limits: &Limits, work: &mut Statistics) -> Result<(), Error> {
    if depth > 64 || depth > limits.max_depth {
        return Err(Error::Depth);
    }
    tick(limits, work)
}

fn allocate(limits: &Limits, work: &mut Statistics) -> Result<(), Error> {
    if work.output_nodes >= limits.max_output_nodes {
        return Err(Error::OutputNodes);
    }
    work.output_nodes += 1;
    Ok(())
}

fn validate_term(
    term: &Term,
    arities: &[usize],
    depth: usize,
    limits: &Limits,
    work: &mut Statistics,
) -> Result<(), Error> {
    visit(depth, limits, work)?;
    match term {
        Term::Var(_) => Ok(()),
        Term::Fun(symbol, arguments) => {
            let symbol = *symbol as usize;
            if symbol >= arities.len() {
                return Err(Error::UnknownFunction);
            }
            if arities[symbol] != arguments.len() {
                return Err(Error::FunctionArity);
            }
            let mut index = 0;
            while index < arguments.len() {
                validate_term(&arguments[index], arities, depth + 1, limits, work)?;
                index += 1;
            }
            Ok(())
        }
    }
}

fn validate_literal(
    literal: &Literal,
    functions: &[usize],
    predicates: &[usize],
    limits: &Limits,
    work: &mut Statistics,
) -> Result<(), Error> {
    tick(limits, work)?;
    match &literal.atom {
        Atom::Predicate(symbol, arguments) => {
            let symbol = *symbol as usize;
            if symbol >= predicates.len() {
                return Err(Error::UnknownPredicate);
            }
            if predicates[symbol] != arguments.len() {
                return Err(Error::PredicateArity);
            }
            let mut index = 0;
            while index < arguments.len() {
                validate_term(&arguments[index], functions, 1, limits, work)?;
                index += 1;
            }
            Ok(())
        }
        Atom::Equal(left, right) => {
            validate_term(left, functions, 1, limits, work)?;
            validate_term(right, functions, 1, limits, work)
        }
    }
}

fn copy(term: &Term, depth: usize, limits: &Limits, work: &mut Statistics) -> Result<Term, Error> {
    visit(depth, limits, work)?;
    allocate(limits, work)?;
    match term {
        Term::Var(variable) => Ok(Term::Var(*variable)),
        Term::Fun(symbol, arguments) => {
            let mut result = Vec::new();
            let mut index = 0;
            while index < arguments.len() {
                result.push(copy(&arguments[index], depth + 1, limits, work)?);
                index += 1;
            }
            Ok(Term::Fun(*symbol, result))
        }
    }
}

/// Simultaneous substitution: an image is copied without recursively applying
/// the same substitution inside it. Missing variables remain unchanged.
fn apply_term(
    term: &Term,
    substitution: &[(u32, Term)],
    depth: usize,
    limits: &Limits,
    work: &mut Statistics,
) -> Result<Term, Error> {
    visit(depth, limits, work)?;
    match term {
        Term::Var(variable) => {
            let mut index = 0;
            while index < substitution.len() {
                tick(limits, work)?;
                if substitution[index].0 == *variable {
                    return copy(&substitution[index].1, depth, limits, work);
                }
                index += 1;
            }
            allocate(limits, work)?;
            Ok(Term::Var(*variable))
        }
        Term::Fun(symbol, arguments) => {
            allocate(limits, work)?;
            let mut result = Vec::new();
            let mut index = 0;
            while index < arguments.len() {
                result.push(apply_term(
                    &arguments[index],
                    substitution,
                    depth + 1,
                    limits,
                    work,
                )?);
                index += 1;
            }
            Ok(Term::Fun(*symbol, result))
        }
    }
}

fn apply_literal(
    literal: &Literal,
    substitution: &[(u32, Term)],
    limits: &Limits,
    work: &mut Statistics,
) -> Result<Literal, Error> {
    tick(limits, work)?;
    let atom = match &literal.atom {
        Atom::Predicate(symbol, arguments) => {
            let mut result = Vec::new();
            let mut index = 0;
            while index < arguments.len() {
                result.push(apply_term(
                    &arguments[index],
                    substitution,
                    1,
                    limits,
                    work,
                )?);
                index += 1;
            }
            Atom::Predicate(*symbol, result)
        }
        Atom::Equal(left, right) => Atom::Equal(
            apply_term(left, substitution, 1, limits, work)?,
            apply_term(right, substitution, 1, limits, work)?,
        ),
    };
    Ok(Literal {
        positive: literal.positive,
        atom,
    })
}

fn same_term(
    left: &Term,
    right: &Term,
    limits: &Limits,
    work: &mut Statistics,
) -> Result<bool, Error> {
    tick(limits, work)?;
    match (left, right) {
        (Term::Var(left), Term::Var(right)) => Ok(left == right),
        (Term::Fun(left, xs), Term::Fun(right, ys)) => {
            if left != right || xs.len() != ys.len() {
                return Ok(false);
            }
            let mut index = 0;
            while index < xs.len() {
                if !same_term(&xs[index], &ys[index], limits, work)? {
                    return Ok(false);
                }
                index += 1;
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

fn validate_clause(
    premise: &[Literal],
    functions: &[usize],
    predicates: &[usize],
    limits: &Limits,
    work: &mut Statistics,
) -> Result<(), Error> {
    let mut index = 0;
    while index < premise.len() {
        validate_literal(&premise[index], functions, predicates, limits, work)?;
        index += 1;
    }
    Ok(())
}

fn validate_substitution(
    substitution: &[(u32, Term)],
    functions: &[usize],
    limits: &Limits,
    work: &mut Statistics,
) -> Result<(), Error> {
    let mut index = 0;
    while index < substitution.len() {
        tick(limits, work)?;
        if index > 0 && substitution[index - 1].0 >= substitution[index].0 {
            return Err(Error::SubstitutionOrder);
        }
        validate_term(&substitution[index].1, functions, 1, limits, work)?;
        index += 1;
    }
    Ok(())
}

fn apply_residual(
    premise: &[Literal],
    pivot: usize,
    substitution: &[(u32, Term)],
    limits: &Limits,
    work: &mut Statistics,
) -> Result<Clause, Error> {
    let mut clause = Vec::new();
    let mut index = 0;
    while index < premise.len() {
        if index != pivot {
            clause.push(apply_literal(&premise[index], substitution, limits, work)?);
        }
        index += 1;
    }
    Ok(clause)
}

/// Reconstruct equality resolution from a finite, strictly increasing variable
/// map. This checks equalization; it neither computes nor requires an MGU.
/// All unselected literals keep their original order and multiplicity.
pub fn equality_resolution(
    premise: &[Literal],
    pivot: usize,
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
    validate_clause(premise, functions, predicates, limits, &mut work)?;
    validate_substitution(substitution, functions, limits, &mut work)?;
    if pivot >= premise.len() {
        return Err(Error::PivotIndex);
    }
    if premise[pivot].positive {
        return Err(Error::ExpectedNegativeEquality);
    }
    let (left, right) = match &premise[pivot].atom {
        Atom::Equal(left, right) => (left, right),
        Atom::Predicate(_, _) => return Err(Error::ExpectedNegativeEquality),
    };
    let left = apply_term(left, substitution, 1, limits, &mut work)?;
    let right = apply_term(right, substitution, 1, limits, &mut work)?;
    if !same_term(&left, &right, limits, &mut work)? {
        return Err(Error::NotEqualized);
    }
    let clause = apply_residual(premise, pivot, substitution, limits, &mut work)?;
    Ok(Reconstructed {
        clause,
        statistics: work,
    })
}
