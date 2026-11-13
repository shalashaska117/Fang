// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The input as the model search sees it: the expanded statements with their roles, the symbol names as the Lean
//! decoders store them, and the distinct objects. Parsing and include expansion are the coverage frontend's, through
//! the signed bundle crate, so the statements and their order are those of the checkers' expansion.

use fang::syntax::Term as SourceTerm;
use fang_equality_inference_core::{Atom, Literal};
use fang_tptp_coverage_candidate::{Body, CnfLiteral, Formula as SourceFormula, Root, Source};
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Term {
    Var(u32),
    App(u32, Vec<Term>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
    Atom(u32, Vec<Term>),
    Equal(Term, Term),
    Constant(bool),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Forall(u32, Box<Formula>),
    Exists(u32, Box<Formula>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    Premise,
    Goal,
    Negated,
}

#[derive(Clone, Debug)]
pub struct Statement {
    pub role: Role,
    /// Universally closed over the variables it leaves free (CNF clauses).
    pub formula: Formula,
    /// File and statement index in the bundle, as the checkers number bundle items.
    pub item: (usize, usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Symbol {
    /// The name as the Lean decoders store it; a distinct object is a 0x00 byte followed by its content.
    pub name: String,
    pub arity: usize,
}

#[derive(Clone, Debug)]
pub struct Problem {
    pub functions: Vec<Symbol>,
    pub predicates: Vec<Symbol>,
    pub statements: Vec<Statement>,
    /// Function IDs of the distinct objects, in first-occurrence order.
    pub objects: Vec<u32>,
}

#[derive(Debug)]
pub enum InputError {
    /// The frontend refused the input; the message is its diagnostic.
    Frontend(String),
    /// A role the checkers do not accept.
    Role(String),
    /// A selected conjecture together with a negated conjecture.
    Modes,
}

impl std::fmt::Display for InputError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InputError::Frontend(message) => write!(formatter, "input: {message}"),
            InputError::Role(role) => write!(formatter, "role: {role}"),
            InputError::Modes => write!(formatter, "modes: conjecture and negated conjecture"),
        }
    }
}

fn role(word: &str) -> Result<Role, InputError> {
    match word {
        "axiom" | "hypothesis" | "definition" | "lemma" | "theorem" | "corollary" => {
            Ok(Role::Premise)
        }
        "conjecture" => Ok(Role::Goal),
        "negated_conjecture" => Ok(Role::Negated),
        other => Err(InputError::Role(other.to_owned())),
    }
}

fn term(source: &SourceTerm) -> Term {
    match source {
        SourceTerm::Var(variable) => Term::Var(*variable),
        SourceTerm::Fun(symbol, arguments) => {
            Term::App(*symbol, arguments.iter().map(term).collect())
        }
    }
}

fn literal(source: &Literal) -> Formula {
    let atom = match &source.atom {
        Atom::Predicate(symbol, arguments) => {
            Formula::Atom(*symbol, arguments.iter().map(term).collect())
        }
        Atom::Equal(left, right) => Formula::Equal(term(left), term(right)),
    };
    if source.positive {
        atom
    } else {
        Formula::Not(Box::new(atom))
    }
}

fn formula(source: &SourceFormula) -> Formula {
    match source {
        SourceFormula::Atom(atom) => literal(&Literal {
            positive: true,
            atom: atom.clone(),
        }),
        SourceFormula::True => Formula::Constant(true),
        SourceFormula::False => Formula::Constant(false),
        SourceFormula::Not(body) => Formula::Not(Box::new(formula(body))),
        SourceFormula::And(left, right) => {
            Formula::And(Box::new(formula(left)), Box::new(formula(right)))
        }
        SourceFormula::Or(left, right) => {
            Formula::Or(Box::new(formula(left)), Box::new(formula(right)))
        }
        SourceFormula::Implies(left, right) => {
            Formula::Implies(Box::new(formula(left)), Box::new(formula(right)))
        }
        SourceFormula::Forall(variable, body) => {
            Formula::Forall(*variable, Box::new(formula(body)))
        }
        SourceFormula::Exists(variable, body) => {
            Formula::Exists(*variable, Box::new(formula(body)))
        }
    }
}

fn clause(literals: &[CnfLiteral]) -> Formula {
    let mut result: Option<Formula> = None;
    for item in literals.iter().rev() {
        let next = match item {
            CnfLiteral::Ordinary(source) => literal(source),
            CnfLiteral::Boolean { positive, value } => Formula::Constant(positive == value),
        };
        result = Some(match result {
            None => next,
            Some(rest) => Formula::Or(Box::new(next), Box::new(rest)),
        });
    }
    result.unwrap_or(Formula::Constant(false))
}

pub fn free_variables(formula: &Formula, bound: &mut Vec<u32>, output: &mut Vec<u32>) {
    fn in_term(term: &Term, bound: &[u32], output: &mut Vec<u32>) {
        match term {
            Term::Var(variable) => {
                if !bound.contains(variable) && !output.contains(variable) {
                    output.push(*variable);
                }
            }
            Term::App(_, arguments) => arguments
                .iter()
                .for_each(|argument| in_term(argument, bound, output)),
        }
    }
    match formula {
        Formula::Atom(_, arguments) => arguments
            .iter()
            .for_each(|argument| in_term(argument, bound, output)),
        Formula::Equal(left, right) => {
            in_term(left, bound, output);
            in_term(right, bound, output);
        }
        Formula::Constant(_) => {}
        Formula::Not(body) => free_variables(body, bound, output),
        Formula::And(left, right) | Formula::Or(left, right) | Formula::Implies(left, right) => {
            free_variables(left, bound, output);
            free_variables(right, bound, output);
        }
        Formula::Forall(variable, body) | Formula::Exists(variable, body) => {
            bound.push(*variable);
            free_variables(body, bound, output);
            bound.pop();
        }
    }
}

fn close(formula: Formula) -> Formula {
    let mut free = Vec::new();
    free_variables(&formula, &mut Vec::new(), &mut free);
    free.into_iter().rev().fold(formula, |body, variable| {
        Formula::Forall(variable, Box::new(body))
    })
}

/// Read a sealed bundle (ROOT, PATH, BYTES), top-level file first, as the checkers read it.
pub fn load(files: Vec<(Root, String, Vec<u8>)>) -> Result<Problem, InputError> {
    let bundle = fang_tptp_signed_bundle::sealed(files);
    let (expanded, roles) = fang_tptp_signed_bundle::expand(&bundle)
        .map_err(|error| InputError::Frontend(format!("{error:?}")))?;
    let mut statements = Vec::new();
    for (declaration, source) in expanded.parsed.declarations.iter().zip(&expanded.sources) {
        let Source::File {
            file, statement, ..
        } = source
        else {
            continue;
        };
        let word = roles
            .get(*file)
            .and_then(|found| found.get(statement))
            .ok_or_else(|| InputError::Frontend("record without a role".into()))?;
        let body = match &declaration.body {
            Body::Cnf(literals) => clause(literals),
            Body::Fof(source) => formula(source),
        };
        statements.push(Statement {
            role: role(word)?,
            formula: close(body),
            item: (*file, *statement),
        });
    }
    if statements
        .iter()
        .any(|statement| statement.role == Role::Goal)
        && statements
            .iter()
            .any(|statement| statement.role == Role::Negated)
    {
        return Err(InputError::Modes);
    }
    let objects: Vec<u32> = expanded
        .distinct_objects
        .iter()
        .map(|(id, _)| *id)
        .collect();
    let functions = expanded
        .parsed
        .functions
        .iter()
        .enumerate()
        .map(|(index, symbol)| {
            let name = match expanded
                .distinct_objects
                .iter()
                .find(|(id, _)| *id as usize == index)
            {
                Some((_, content)) => format!("\u{0}{content}"),
                None => symbol.name.clone(),
            };
            Symbol {
                name,
                arity: symbol.arity,
            }
        })
        .collect();
    let predicates = expanded
        .parsed
        .predicates
        .iter()
        .map(|symbol| Symbol {
            name: symbol.name.clone(),
            arity: symbol.arity,
        })
        .collect();
    Ok(Problem {
        functions,
        predicates,
        statements,
        objects,
    })
}

/// Function and predicate IDs that occur in the statements, as the checker's table rule counts them.
pub fn used_symbols(problem: &Problem) -> (BTreeSet<u32>, BTreeSet<u32>) {
    fn in_term(term: &Term, functions: &mut BTreeSet<u32>) {
        if let Term::App(symbol, arguments) = term {
            functions.insert(*symbol);
            arguments
                .iter()
                .for_each(|argument| in_term(argument, functions));
        }
    }
    fn walk(formula: &Formula, functions: &mut BTreeSet<u32>, predicates: &mut BTreeSet<u32>) {
        match formula {
            Formula::Atom(symbol, arguments) => {
                predicates.insert(*symbol);
                arguments
                    .iter()
                    .for_each(|argument| in_term(argument, functions));
            }
            Formula::Equal(left, right) => {
                in_term(left, functions);
                in_term(right, functions);
            }
            Formula::Constant(_) => {}
            Formula::Not(body) | Formula::Forall(_, body) | Formula::Exists(_, body) => {
                walk(body, functions, predicates)
            }
            Formula::And(left, right)
            | Formula::Or(left, right)
            | Formula::Implies(left, right) => {
                walk(left, functions, predicates);
                walk(right, functions, predicates);
            }
        }
    }
    let (mut functions, mut predicates) = (BTreeSet::new(), BTreeSet::new());
    for statement in &problem.statements {
        walk(&statement.formula, &mut functions, &mut predicates);
    }
    (functions, predicates)
}

/// Which statements must hold and which goal must fail.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Task {
    /// Single file or bundle without other roles: every statement.
    All,
    /// Signed input without a selected conjecture: premises and negated conjectures.
    Inputs,
    /// The selected conjecture with this index in expansion order, false; the premises true.
    Goal(usize),
}

#[derive(Debug)]
pub enum TaskError {
    GoalsPresent,
    NoGoal,
}

/// The formulas a model must satisfy, and the goal's bundle item for a goal task.
pub type TaskFormulas = (Vec<Formula>, Option<(usize, usize)>);

/// The formulas the model must satisfy for the task, and the goal's bundle item for a goal task.
pub fn task_formulas(problem: &Problem, task: Task) -> Result<TaskFormulas, TaskError> {
    let goals: Vec<&Statement> = problem
        .statements
        .iter()
        .filter(|statement| statement.role == Role::Goal)
        .collect();
    match task {
        Task::All | Task::Inputs => {
            if !goals.is_empty() {
                return Err(TaskError::GoalsPresent);
            }
            Ok((
                problem
                    .statements
                    .iter()
                    .map(|statement| statement.formula.clone())
                    .collect(),
                None,
            ))
        }
        Task::Goal(index) => {
            let goal = goals.get(index).ok_or(TaskError::NoGoal)?;
            let mut formulas: Vec<Formula> = problem
                .statements
                .iter()
                .filter(|statement| statement.role == Role::Premise)
                .map(|statement| statement.formula.clone())
                .collect();
            formulas.push(Formula::Not(Box::new(goal.formula.clone())));
            Ok((formulas, Some(goal.item)))
        }
    }
}
