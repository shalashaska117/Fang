// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The validated witness of recipe/mixed/generate.py, typed.
//!
//! `validate` builds it from a witness that passed every check, so each natural fits its cap
//! and each tag is one the checks allow. The only field that stays a JSON value is the Skolem
//! predicate table, which revision 7 compares with `==` but never checks the type of.

use fang_json::{Integer, Number, Value};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Term {
    Var(u64),
    Fun(u64, Vec<Term>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Literal {
    pub(crate) positive: bool,
    pub(crate) predicate: u64,
    pub(crate) arguments: Vec<Term>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Formula {
    Truth,
    Falsity,
    Conj(Box<Formula>, Box<Formula>),
    Disj(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    All(u64, Box<Formula>),
    Ex(u64, Box<Formula>),
    Not(Box<Formula>),
    Atom(u64, Vec<Term>),
    Literal(Literal),
}

impl Formula {
    /// The witness tag.
    pub(crate) fn tag(&self) -> &'static str {
        match self {
            Formula::Truth => "truth",
            Formula::Falsity => "falsity",
            Formula::Conj(..) => "conj",
            Formula::Disj(..) => "disj",
            Formula::Implies(..) => "implies",
            Formula::All(..) => "all",
            Formula::Ex(..) => "ex",
            Formula::Not(..) => "not",
            Formula::Atom(..) => "atom",
            Formula::Literal(..) => "literal",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Symbol {
    pub(crate) name: String,
    pub(crate) arity: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Body {
    Cnf(Vec<Literal>),
    Fof(Formula),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SourceDeclaration {
    pub(crate) name: String,
    pub(crate) variables: Vec<String>,
    pub(crate) body: Body,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Declaration {
    pub(crate) name: String,
    pub(crate) variables: Vec<String>,
    pub(crate) formula: Formula,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Standalone {
    pub(crate) validated: Vec<u64>,
    pub(crate) rectified: Formula,
    pub(crate) binder_count: u64,
    pub(crate) rectified_stats: Vec<u64>,
    pub(crate) normalized: Formula,
    pub(crate) normalized_stats: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Origin {
    pub(crate) declaration: u64,
    pub(crate) binder: u64,
    pub(crate) function: u64,
    pub(crate) universals: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Skolem {
    pub(crate) formulas: Vec<Formula>,
    pub(crate) functions: Vec<u64>,
    /// Equal to the original predicate arities under Python's `==`, of any number type.
    pub(crate) predicates: Vec<Value>,
    pub(crate) introduced: Vec<Origin>,
    pub(crate) statistics: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Block {
    pub(crate) removal_stats: Vec<u64>,
    pub(crate) clauses: Vec<Vec<Literal>>,
    pub(crate) clausifier_stats: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Witness {
    pub(crate) functions: Vec<Symbol>,
    pub(crate) predicates: Vec<Symbol>,
    pub(crate) source_declarations: Vec<SourceDeclaration>,
    pub(crate) declarations: Vec<Declaration>,
    pub(crate) standalone: Vec<Standalone>,
    pub(crate) skolem: Skolem,
    pub(crate) blocks: Vec<Block>,
}

fn natural(value: u64) -> Value {
    Value::Number(Number::Integer(Integer::from(value)))
}

/// The JSON value of a term, as the witness spells it.
pub(crate) fn term_value(term: &Term) -> Value {
    match term {
        Term::Var(index) => Value::Array(vec![Value::from("var"), natural(*index)]),
        Term::Fun(symbol, arguments) => Value::Array(vec![
            Value::from("fun"),
            natural(*symbol),
            Value::Array(arguments.iter().map(term_value).collect()),
        ]),
    }
}

/// The JSON value of a literal: `[positive, predicate, arguments]`.
pub(crate) fn literal_value(literal: &Literal) -> Value {
    Value::Array(vec![
        Value::Bool(literal.positive),
        natural(literal.predicate),
        Value::Array(literal.arguments.iter().map(term_value).collect()),
    ])
}

/// A JSON natural.
pub(crate) fn natural_value(value: u64) -> Value {
    natural(value)
}
