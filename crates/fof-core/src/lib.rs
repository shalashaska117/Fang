// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Candidate replacement of the accepted ground core.
// Reused Fang term/literal types retain their upstream notices.
#![forbid(unsafe_code)]

use fang::syntax::{Clause, Literal, SymbolId, Term};

/// Numeric, equality-free, quantifier-free bodies; scope is checked separately.
#[derive(Debug, PartialEq, Eq)]
pub enum Formula {
    Atom(SymbolId, Vec<Term>),
    True,
    False,
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
}

/// Negation normal form. Its shape excludes implication and compound negation.
#[derive(Debug, PartialEq, Eq)]
pub enum Nnf {
    Literal(Literal),
    True,
    False,
    And(Box<Nnf>, Box<Nnf>),
    Or(Box<Nnf>, Box<Nnf>),
}

/// Arity tables indexed by the existing Fang numeric symbol IDs.
#[derive(Debug, PartialEq, Eq)]
pub struct Signature {
    pub functions: Vec<usize>,
    pub predicates: Vec<usize>,
}

/// A declaration-level scope; this core neither parses nor invents binders.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VariableScope {
    Ground,
    /// Prefix positions are 0 through count-1, including unused binders.
    Bound(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub max_formula_depth: usize,
    pub max_formula_nodes: usize,
    pub max_term_depth: usize,
    pub max_input_term_nodes: usize,
    pub max_clauses: usize,
    pub max_literals_per_clause: usize,
    pub max_literals: usize,
    /// Cumulative allocated NNF nodes, term nodes, clauses and literal positions.
    /// This is a conservative structural bound, not a byte/RSS limit.
    pub max_stored_nodes: usize,
    pub max_operations: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_formula_depth: 64,
            max_formula_nodes: 10_000,
            max_term_depth: 64,
            max_input_term_nodes: 100_000,
            max_clauses: 1_000,
            max_literals_per_clause: 256,
            max_literals: 100_000,
            max_stored_nodes: 1_000_000,
            max_operations: 5_000_000,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Invalid {
    FreeVariable,
    UnknownFunction(SymbolId),
    FunctionArity(SymbolId),
    UnknownPredicate(SymbolId),
    PredicateArity(SymbolId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Resource {
    FormulaDepth,
    FormulaNodes,
    TermDepth,
    InputTermNodes,
    Clauses,
    LiteralsPerClause,
    Literals,
    StoredNodes,
    Operations,
    Arithmetic,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Invalid(Invalid),
    Resource(Resource),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Statistics {
    pub operations: usize,
    pub input_formula_nodes: usize,
    pub input_term_nodes: usize,
    pub allocated_nodes: usize,
    pub output_clauses: usize,
    pub output_literals: usize,
    pub output_term_nodes: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Normalized {
    pub formula: Nnf,
    pub statistics: Statistics,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Preprocessed {
    /// Raw deterministic CNF. Stable literal deduplication is a later step.
    pub clauses: Vec<Clause>,
    pub statistics: Statistics,
}

struct Work {
    statistics: Statistics,
}

impl Work {
    fn new() -> Self {
        Self {
            statistics: Statistics::default(),
        }
    }

    fn tick(&mut self, limits: &Limits) -> Result<(), Error> {
        self.statistics.operations = bounded_add(
            self.statistics.operations,
            1,
            limits.max_operations,
            Resource::Operations,
        )?;
        Ok(())
    }

    fn allocate(&mut self, count: usize, limits: &Limits) -> Result<(), Error> {
        self.statistics.allocated_nodes = bounded_add(
            self.statistics.allocated_nodes,
            count,
            limits.max_stored_nodes,
            Resource::StoredNodes,
        )?;
        Ok(())
    }
}

fn bounded_add(left: usize, right: usize, cap: usize, kind: Resource) -> Result<usize, Error> {
    if left > cap || right > cap - left {
        Err(Error::Resource(kind))
    } else {
        Ok(left + right)
    }
}

fn add(left: usize, right: usize) -> Result<usize, Error> {
    left.checked_add(right)
        .ok_or(Error::Resource(Resource::Arithmetic))
}

fn multiply(left: usize, right: usize) -> Result<usize, Error> {
    left.checked_mul(right)
        .ok_or(Error::Resource(Resource::Arithmetic))
}

fn validate_term(
    term: &Term,
    depth: usize,
    signature: &Signature,
    scope: VariableScope,
    limits: &Limits,
    work: &mut Work,
) -> Result<(), Error> {
    work.tick(limits)?;
    if depth > limits.max_term_depth.min(64) {
        return Err(Error::Resource(Resource::TermDepth));
    }
    work.statistics.input_term_nodes = bounded_add(
        work.statistics.input_term_nodes,
        1,
        limits.max_input_term_nodes,
        Resource::InputTermNodes,
    )?;
    match term {
        Term::Var(id) => match scope {
            VariableScope::Ground => Err(Error::Invalid(Invalid::FreeVariable)),
            VariableScope::Bound(count) => {
                if *id < count {
                    Ok(())
                } else {
                    Err(Error::Invalid(Invalid::FreeVariable))
                }
            }
        },
        Term::Fun(symbol, arguments) => {
            let index = *symbol as usize;
            if index >= signature.functions.len() {
                return Err(Error::Invalid(Invalid::UnknownFunction(*symbol)));
            }
            if signature.functions[index] != arguments.len() {
                return Err(Error::Invalid(Invalid::FunctionArity(*symbol)));
            }
            let mut index = 0;
            while index < arguments.len() {
                validate_term(&arguments[index], depth + 1, signature, scope, limits, work)?;
                index += 1;
            }
            Ok(())
        }
    }
}

fn validate_formula(
    formula: &Formula,
    depth: usize,
    signature: &Signature,
    scope: VariableScope,
    limits: &Limits,
    work: &mut Work,
) -> Result<(), Error> {
    work.tick(limits)?;
    if depth > limits.max_formula_depth.min(64) {
        return Err(Error::Resource(Resource::FormulaDepth));
    }
    work.statistics.input_formula_nodes = bounded_add(
        work.statistics.input_formula_nodes,
        1,
        limits.max_formula_nodes,
        Resource::FormulaNodes,
    )?;
    match formula {
        Formula::Atom(predicate, arguments) => {
            let index = *predicate as usize;
            if index >= signature.predicates.len() {
                return Err(Error::Invalid(Invalid::UnknownPredicate(*predicate)));
            }
            if signature.predicates[index] != arguments.len() {
                return Err(Error::Invalid(Invalid::PredicateArity(*predicate)));
            }
            let mut index = 0;
            while index < arguments.len() {
                validate_term(&arguments[index], 1, signature, scope, limits, work)?;
                index += 1;
            }
            Ok(())
        }
        Formula::True | Formula::False => Ok(()),
        Formula::Not(inner) => validate_formula(inner, depth + 1, signature, scope, limits, work),
        Formula::And(left, right) | Formula::Or(left, right) | Formula::Implies(left, right) => {
            validate_formula(left, depth + 1, signature, scope, limits, work)?;
            validate_formula(right, depth + 1, signature, scope, limits, work)
        }
    }
}

/// Validate a caller-owned AST without modifying it or assigning symbols.
pub fn validate(
    formula: &Formula,
    signature: &Signature,
    limits: &Limits,
) -> Result<Statistics, Error> {
    validate_with_scope(formula, signature, VariableScope::Ground, limits)
}

/// Validate all branches and variable IDs before any recursive copying.
pub fn validate_with_scope(
    formula: &Formula,
    signature: &Signature,
    scope: VariableScope,
    limits: &Limits,
) -> Result<Statistics, Error> {
    let mut work = Work::new();
    validate_formula(formula, 1, signature, scope, limits, &mut work)?;
    Ok(work.statistics)
}

// Call only after validation has established the fixed recursive-depth cap.
fn copy_term(term: &Term, limits: &Limits, work: &mut Work) -> Result<Term, Error> {
    work.tick(limits)?;
    work.allocate(1, limits)?;
    match term {
        Term::Var(id) => Ok(Term::Var(*id)),
        Term::Fun(symbol, arguments) => {
            let mut copied = Vec::new();
            let mut index = 0;
            while index < arguments.len() {
                copied.push(copy_term(&arguments[index], limits, work)?);
                index += 1;
            }
            Ok(Term::Fun(*symbol, copied))
        }
    }
}

fn copy_arguments(
    arguments: &[Term],
    limits: &Limits,
    work: &mut Work,
) -> Result<Vec<Term>, Error> {
    let mut copied = Vec::new();
    let mut index = 0;
    while index < arguments.len() {
        copied.push(copy_term(&arguments[index], limits, work)?);
        index += 1;
    }
    Ok(copied)
}

fn normalize_formula(
    formula: &Formula,
    positive: bool,
    limits: &Limits,
    work: &mut Work,
) -> Result<Nnf, Error> {
    work.tick(limits)?;
    if let Formula::Not(inner) = formula {
        return normalize_formula(inner, !positive, limits, work);
    }
    work.allocate(1, limits)?;
    match formula {
        Formula::Atom(predicate, arguments) => Ok(Nnf::Literal(Literal {
            positive,
            predicate: *predicate,
            arguments: copy_arguments(arguments, limits, work)?,
        })),
        Formula::True => Ok(if positive { Nnf::True } else { Nnf::False }),
        Formula::False => Ok(if positive { Nnf::False } else { Nnf::True }),
        Formula::Not(inner) => normalize_formula(inner, !positive, limits, work),
        Formula::And(left, right) | Formula::Or(left, right) => {
            let normalized_left = normalize_formula(left, positive, limits, work)?;
            let normalized_right = normalize_formula(right, positive, limits, work)?;
            if matches!(formula, Formula::And(_, _)) == positive {
                Ok(Nnf::And(
                    Box::new(normalized_left),
                    Box::new(normalized_right),
                ))
            } else {
                Ok(Nnf::Or(
                    Box::new(normalized_left),
                    Box::new(normalized_right),
                ))
            }
        }
        Formula::Implies(left, right) => {
            let normalized_left = normalize_formula(left, !positive, limits, work)?;
            let normalized_right = normalize_formula(right, positive, limits, work)?;
            if positive {
                Ok(Nnf::Or(
                    Box::new(normalized_left),
                    Box::new(normalized_right),
                ))
            } else {
                Ok(Nnf::And(
                    Box::new(normalized_left),
                    Box::new(normalized_right),
                ))
            }
        }
    }
}

/// Normalize either the input (`positive`) or its negation (`!positive`).
pub fn normalize(
    formula: &Formula,
    positive: bool,
    signature: &Signature,
    limits: &Limits,
) -> Result<Normalized, Error> {
    normalize_with_scope(formula, positive, signature, VariableScope::Ground, limits)
}

/// Normalize with an explicit scope, preserving validated variable IDs.
pub fn normalize_with_scope(
    formula: &Formula,
    positive: bool,
    signature: &Signature,
    scope: VariableScope,
    limits: &Limits,
) -> Result<Normalized, Error> {
    let mut work = Work::new();
    validate_formula(formula, 1, signature, scope, limits, &mut work)?;
    let formula = normalize_formula(formula, positive, limits, &mut work)?;
    Ok(Normalized {
        formula,
        statistics: work.statistics,
    })
}

struct Cnf {
    clauses: Vec<Clause>,
    literals: usize,
    term_nodes: usize,
    max_width: usize,
}

fn check_shape(
    clauses: usize,
    literals: usize,
    max_width: usize,
    limits: &Limits,
) -> Result<(), Error> {
    if clauses > limits.max_clauses {
        return Err(Error::Resource(Resource::Clauses));
    }
    if max_width > limits.max_literals_per_clause {
        return Err(Error::Resource(Resource::LiteralsPerClause));
    }
    if literals > limits.max_literals {
        return Err(Error::Resource(Resource::Literals));
    }
    Ok(())
}

fn copy_literal(literal: &Literal, limits: &Limits, work: &mut Work) -> Result<Literal, Error> {
    work.tick(limits)?;
    work.allocate(1, limits)?;
    Ok(Literal {
        positive: literal.positive,
        predicate: literal.predicate,
        arguments: copy_arguments(&literal.arguments, limits, work)?,
    })
}

fn append_literals(
    source: &Clause,
    target: &mut Clause,
    limits: &Limits,
    work: &mut Work,
) -> Result<(), Error> {
    let mut index = 0;
    while index < source.len() {
        target.push(copy_literal(&source[index], limits, work)?);
        index += 1;
    }
    Ok(())
}

/// Check all storage arithmetic before starting a CNF result allocation.
fn check_storage(
    clauses: usize,
    literals: usize,
    terms: usize,
    limits: &Limits,
    work: &Work,
) -> Result<(), Error> {
    let amount = add(add(clauses, literals)?, terms)?;
    bounded_add(
        work.statistics.allocated_nodes,
        amount,
        limits.max_stored_nodes,
        Resource::StoredNodes,
    )?;
    Ok(())
}

fn append_clauses(
    source: &[Clause],
    target: &mut Vec<Clause>,
    limits: &Limits,
    work: &mut Work,
) -> Result<(), Error> {
    let mut index = 0;
    while index < source.len() {
        work.tick(limits)?;
        work.allocate(1, limits)?;
        let mut clause = Vec::new();
        append_literals(&source[index], &mut clause, limits, work)?;
        target.push(clause);
        index += 1;
    }
    Ok(())
}

fn append_cnf(left: &Cnf, right: &Cnf, limits: &Limits, work: &mut Work) -> Result<Cnf, Error> {
    let count = add(left.clauses.len(), right.clauses.len())?;
    let literals = add(left.literals, right.literals)?;
    let term_nodes = add(left.term_nodes, right.term_nodes)?;
    let max_width = left.max_width.max(right.max_width);
    check_shape(count, literals, max_width, limits)?;
    check_storage(count, literals, term_nodes, limits, work)?;
    let mut clauses = Vec::new();
    append_clauses(&left.clauses, &mut clauses, limits, work)?;
    append_clauses(&right.clauses, &mut clauses, limits, work)?;
    Ok(Cnf {
        clauses,
        literals,
        term_nodes,
        max_width,
    })
}

fn product_row(
    left: &Clause,
    right: &[Clause],
    target: &mut Vec<Clause>,
    limits: &Limits,
    work: &mut Work,
) -> Result<(), Error> {
    let mut right_index = 0;
    while right_index < right.len() {
        work.tick(limits)?;
        work.allocate(1, limits)?;
        let mut clause = Vec::new();
        append_literals(left, &mut clause, limits, work)?;
        append_literals(&right[right_index], &mut clause, limits, work)?;
        target.push(clause);
        right_index += 1;
    }
    Ok(())
}

fn product_cnf(left: &Cnf, right: &Cnf, limits: &Limits, work: &mut Work) -> Result<Cnf, Error> {
    let count = multiply(left.clauses.len(), right.clauses.len())?;
    if count == 0 {
        return Ok(Cnf {
            clauses: Vec::new(),
            literals: 0,
            term_nodes: 0,
            max_width: 0,
        });
    }
    let literals = add(
        multiply(left.literals, right.clauses.len())?,
        multiply(right.literals, left.clauses.len())?,
    )?;
    let term_nodes = add(
        multiply(left.term_nodes, right.clauses.len())?,
        multiply(right.term_nodes, left.clauses.len())?,
    )?;
    let max_width = add(left.max_width, right.max_width)?;
    check_shape(count, literals, max_width, limits)?;
    check_storage(count, literals, term_nodes, limits, work)?;
    let mut clauses = Vec::new();
    let mut left_index = 0;
    while left_index < left.clauses.len() {
        product_row(
            &left.clauses[left_index],
            &right.clauses,
            &mut clauses,
            limits,
            work,
        )?;
        left_index += 1;
    }
    Ok(Cnf {
        clauses,
        literals,
        term_nodes,
        max_width,
    })
}

// The pinned translator pulls an unknown MaybeUninit type through vec![value].
// Keep the same singleton construction in supported Vec operations.
#[allow(clippy::vec_init_then_push)]
fn singleton<T>(value: T) -> Vec<T> {
    let mut values = Vec::new();
    values.push(value);
    values
}

fn clausify_nnf(formula: &Nnf, limits: &Limits, work: &mut Work) -> Result<Cnf, Error> {
    work.tick(limits)?;
    match formula {
        Nnf::True => Ok(Cnf {
            clauses: Vec::new(),
            literals: 0,
            term_nodes: 0,
            max_width: 0,
        }),
        Nnf::False => {
            check_shape(1, 0, 0, limits)?;
            work.allocate(1, limits)?;
            Ok(Cnf {
                clauses: singleton(Vec::new()),
                literals: 0,
                term_nodes: 0,
                max_width: 0,
            })
        }
        Nnf::Literal(literal) => {
            check_shape(1, 1, 1, limits)?;
            work.allocate(1, limits)?;
            let before = work.statistics.allocated_nodes;
            let literal = copy_literal(literal, limits, work)?;
            let term_nodes = work.statistics.allocated_nodes - before - 1;
            Ok(Cnf {
                clauses: singleton(singleton(literal)),
                literals: 1,
                term_nodes,
                max_width: 1,
            })
        }
        Nnf::And(left, right) => {
            let left = clausify_nnf(left, limits, work)?;
            let right = clausify_nnf(right, limits, work)?;
            append_cnf(&left, &right, limits, work)
        }
        Nnf::Or(left, right) => {
            let left = clausify_nnf(left, limits, work)?;
            let right = clausify_nnf(right, limits, work)?;
            product_cnf(&left, &right, limits, work)
        }
    }
}

/// Validate, normalize positively and produce complete ordered raw CNF.
/// All mutable state is local. An error returns no partial formula or clauses.
pub fn preprocess(
    formula: &Formula,
    signature: &Signature,
    limits: &Limits,
) -> Result<Preprocessed, Error> {
    preprocess_with_scope(formula, signature, VariableScope::Ground, limits)
}

/// Return complete ordered raw CNF after validating the explicit variable scope.
/// Ground and Bound(0) have identical results, errors and structural counters.
pub fn preprocess_with_scope(
    formula: &Formula,
    signature: &Signature,
    scope: VariableScope,
    limits: &Limits,
) -> Result<Preprocessed, Error> {
    let mut work = Work::new();
    validate_formula(formula, 1, signature, scope, limits, &mut work)?;
    let normalized = normalize_formula(formula, true, limits, &mut work)?;
    let result = clausify_nnf(&normalized, limits, &mut work)?;
    work.statistics.output_clauses = result.clauses.len();
    work.statistics.output_literals = result.literals;
    work.statistics.output_term_nodes = result.term_nodes;
    Ok(Preprocessed {
        clauses: result.clauses,
        statistics: work.statistics,
    })
}

pub mod nnf_entry;
