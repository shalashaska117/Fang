// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Adapted from the accepted quantified frontend and CNF equality parser.
// Reused Fang terms/literals retain the notices in LICENSES/Vampire.txt.
#![forbid(unsafe_code)]

//! Candidate TPTP frontend, starting with comments and ordinary word tokens.
//! This parser is untrusted by result certification. No production CLI uses it.

use fang::syntax::{Symbol, Term};
use fang::{Error, ErrorKind};
use fang_equality_inference_core::{Atom, Literal};
use fang_fof_equality_bridge::{Error as BridgeError, Reservation};
use fang_quantified_fof_core::Formula as EncodedFormula;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

/// Equality has its own constructor before numeric predicate reservation.
#[derive(Debug, PartialEq, Eq)]
pub enum Formula {
    Atom(Atom),
    True,
    False,
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Forall(u32, Box<Formula>),
    Exists(u32, Box<Formula>),
}

#[derive(Debug)]
enum NamedTerm {
    Variable(String, usize),
    Function(String, Vec<NamedTerm>),
}

#[derive(Clone, Debug)]
pub struct Limits {
    pub input: fang::Limits,
    /// Formula depth, including grouping and each expanded binder, capped at 64.
    pub max_formula_depth: usize,
    /// Total FOF AST nodes in the file. Parentheses add no AST node.
    pub max_formula_nodes: usize,
    /// Total binder occurrences in the file, including unused/shadowed names.
    pub max_binders: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            input: fang::Limits::default(),
            max_formula_depth: 64,
            max_formula_nodes: 10_000,
            max_binders: 10_000,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Body {
    /// Original literal order and multiplicity, before stable deduplication.
    Cnf(Vec<CnfLiteral>),
    Fof(Formula),
}

/// Source CNF literals retain constants and their signs before normalization.
#[derive(Debug, PartialEq, Eq)]
pub enum CnfLiteral {
    Ordinary(Literal),
    Boolean { positive: bool, value: bool },
}

/// Record-name identity is separate from its printable source spelling.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum NameKind {
    Atom,
    Integer,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Declaration<B = Body> {
    /// Canonical value; use name_kind as part of identity.
    pub name: String,
    pub name_kind: NameKind,
    /// From the declaration keyword through its period, excluding outer space.
    pub bytes: Range<usize>,
    /// Source-name identities in first occurrence order, local to this declaration.
    /// Shadowed binders share the source ID; the core rectifies each occurrence.
    pub variables: Vec<String>,
    /// Entire formula, including any CNF whole-clause parentheses.
    pub body_bytes: Range<usize>,
    pub body: B,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Statistics {
    /// One operation per lexed byte, consumed token and copied AST node.
    pub operations: usize,
    pub formula_nodes: usize,
    pub term_nodes: usize,
    pub binders: usize,
}

#[derive(Debug)]
pub struct Parsed {
    pub functions: Vec<Symbol>,
    pub predicates: Vec<Symbol>,
    pub declarations: Vec<Declaration>,
    pub statistics: Statistics,
}

#[derive(Debug, PartialEq, Eq)]
pub enum EncodedBody {
    /// None is a true clause; Some(empty) is a false clause.
    Cnf(Option<fang::syntax::Clause>),
    Fof(EncodedFormula),
}

/// Input to an equality-aware preprocessing composition. The reserved numeric
/// head has no source spelling. This object alone does not certify a result.
#[derive(Debug)]
pub struct Encoded {
    pub functions: Vec<Symbol>,
    pub original_predicates: Vec<Symbol>,
    pub reservation: Reservation,
    pub declarations: Vec<Declaration<EncodedBody>>,
    pub statistics: Statistics,
}

fn encode_formula(
    formula: Formula,
    reservation: &Reservation,
) -> Result<EncodedFormula, BridgeError> {
    Ok(match formula {
        Formula::Atom(atom) => {
            let literal = reservation.encode_literal(Literal {
                positive: true,
                atom,
            })?;
            EncodedFormula::Atom(literal.predicate, literal.arguments)
        }
        Formula::True => EncodedFormula::True,
        Formula::False => EncodedFormula::False,
        Formula::Not(body) => EncodedFormula::Not(Box::new(encode_formula(*body, reservation)?)),
        Formula::And(left, right) => EncodedFormula::And(
            Box::new(encode_formula(*left, reservation)?),
            Box::new(encode_formula(*right, reservation)?),
        ),
        Formula::Or(left, right) => EncodedFormula::Or(
            Box::new(encode_formula(*left, reservation)?),
            Box::new(encode_formula(*right, reservation)?),
        ),
        Formula::Implies(left, right) => EncodedFormula::Implies(
            Box::new(encode_formula(*left, reservation)?),
            Box::new(encode_formula(*right, reservation)?),
        ),
        Formula::Forall(id, body) => {
            EncodedFormula::Forall(id, Box::new(encode_formula(*body, reservation)?))
        }
        Formula::Exists(id, body) => {
            EncodedFormula::Exists(id, Box::new(encode_formula(*body, reservation)?))
        }
    })
}

// Consume every original literal, even after a true constant. This checks all
// ordinary heads and preserves the complete source tables and later failures.
fn encode_cnf(
    input: Vec<CnfLiteral>,
    reservation: &Reservation,
    maximum: usize,
) -> Result<Option<fang::syntax::Clause>, BridgeError> {
    if input.len() > maximum {
        return Err(BridgeError::LiteralLimit);
    }
    let mut tautology = false;
    let mut output = Vec::new();
    for literal in input {
        match literal {
            CnfLiteral::Ordinary(value) => output.push(reservation.encode_literal(value)?),
            CnfLiteral::Boolean { positive, value } => {
                tautology |= positive == value;
            }
        }
    }
    Ok(if tautology { None } else { Some(output) })
}

impl Parsed {
    /// Reserve after parsing the whole source table, then move terms unchanged.
    /// The maximum includes the reserved entry. A failure returns no partial
    /// encoded problem. This pass has no separate native allocation/work budget.
    /// Its parser-produced AST is bounded by parser limits; callers can mutate
    /// public fields, so this is not a validated-typestate API.
    pub fn encode(
        self,
        max_predicates: usize,
        max_literals: usize,
    ) -> Result<Encoded, BridgeError> {
        let reservation = Reservation::new(
            self.predicates.iter().map(|symbol| symbol.arity).collect(),
            max_predicates,
        )?;
        let mut declarations = Vec::new();
        for declaration in self.declarations {
            let body = match declaration.body {
                Body::Cnf(clause) => {
                    EncodedBody::Cnf(encode_cnf(clause, &reservation, max_literals)?)
                }
                Body::Fof(formula) => EncodedBody::Fof(encode_formula(formula, &reservation)?),
            };
            declarations.push(Declaration {
                name: declaration.name,
                name_kind: declaration.name_kind,
                bytes: declaration.bytes,
                variables: declaration.variables,
                body_bytes: declaration.body_bytes,
                body,
            });
        }
        Ok(Encoded {
            functions: self.functions,
            original_predicates: self.predicates,
            reservation,
            declarations,
            statistics: self.statistics,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Kind {
    Lower(String),
    Quoted(String),
    IntegerName(String),
    Variable(String),
    True,
    False,
    Implies,
    ReverseImplies,
    Nand,
    Nor,
    Iff,
    Xor,
    Equality(bool),
    Punctuation(u8),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Scope {
    CnfImplicit,
    FofExplicit,
}

#[derive(Clone, Debug)]
struct Token {
    kind: Kind,
    offset: usize,
    end: usize,
}

fn error(kind: ErrorKind, offset: usize, message: &str) -> Error {
    Error {
        kind,
        offset: Some(offset),
        message: message.into(),
    }
}

fn tick(statistics: &mut Statistics, cap: usize) -> Result<(), Error> {
    if statistics.operations >= cap {
        return Err(Error::resource("parser operation limit exceeded"));
    }
    statistics.operations += 1;
    Ok(())
}

fn lex(input: &[u8], limits: &Limits, statistics: &mut Statistics) -> Result<Vec<Token>, Error> {
    if input.len() > limits.input.max_input_bytes {
        return Err(Error::resource("input byte limit exceeded"));
    }
    let mut tokens = Vec::new();
    let mut pos = 0;
    while pos < input.len() {
        let start = pos;
        tick(statistics, limits.input.max_operations)?;
        let byte = input[pos];
        if byte == b' ' || (b'\t'..=b'\r').contains(&byte) {
            pos += 1;
            continue;
        }
        if byte == b'%' {
            pos += 1;
            while pos < input.len() && !matches!(input[pos], b'\r' | b'\n') {
                tick(statistics, limits.input.max_operations)?;
                if !input[pos].is_ascii() || input[pos] == 0 {
                    return Err(error(
                        ErrorKind::InvalidInput,
                        pos,
                        "ASCII comment required",
                    ));
                }
                pos += 1;
            }
            continue;
        }
        if byte == b'/' && input.get(pos + 1) == Some(&b'*') {
            tick(statistics, limits.input.max_operations)?;
            pos += 2;
            loop {
                if pos >= input.len() {
                    return Err(error(
                        ErrorKind::InvalidInput,
                        start,
                        "unterminated block comment",
                    ));
                }
                tick(statistics, limits.input.max_operations)?;
                if input[pos] == b'*' && input.get(pos + 1) == Some(&b'/') {
                    tick(statistics, limits.input.max_operations)?;
                    pos += 2;
                    break;
                }
                if !input[pos].is_ascii() || input[pos] == 0 {
                    return Err(error(
                        ErrorKind::InvalidInput,
                        pos,
                        "ASCII comment required",
                    ));
                }
                pos += 1;
            }
            continue;
        }
        let kind = match byte {
            b'\'' => {
                pos += 1;
                let mut value = String::new();
                loop {
                    let Some(&character) = input.get(pos) else {
                        return Err(error(
                            ErrorKind::InvalidInput,
                            start,
                            "unterminated quoted atom",
                        ));
                    };
                    tick(statistics, limits.input.max_operations)?;
                    pos += 1;
                    match character {
                        b'\'' => {
                            if value.is_empty() {
                                return Err(error(
                                    ErrorKind::InvalidInput,
                                    start,
                                    "empty quoted atom",
                                ));
                            }
                            break;
                        }
                        b'\\' => {
                            let Some(&escaped) = input.get(pos) else {
                                return Err(error(
                                    ErrorKind::InvalidInput,
                                    start,
                                    "unfinished quoted escape",
                                ));
                            };
                            tick(statistics, limits.input.max_operations)?;
                            if !matches!(escaped, b'\'' | b'\\') {
                                return Err(error(
                                    ErrorKind::InvalidInput,
                                    pos,
                                    "invalid quoted escape",
                                ));
                            }
                            value.push(escaped as char);
                            pos += 1;
                        }
                        32..=126 => value.push(character as char),
                        _ => {
                            return Err(error(
                                ErrorKind::InvalidInput,
                                pos - 1,
                                "non-visible quoted character",
                            ));
                        }
                    }
                }
                Kind::Quoted(value)
            }
            b'0'..=b'9' | b'+' | b'-' => {
                let negative = byte == b'-';
                let digits = if matches!(byte, b'+' | b'-') {
                    pos += 1;
                    if !input.get(pos).is_some_and(u8::is_ascii_digit) {
                        return Err(error(
                            ErrorKind::InvalidInput,
                            start,
                            "integer name requires digits",
                        ));
                    }
                    tick(statistics, limits.input.max_operations)?;
                    pos
                } else {
                    pos
                };
                pos += 1;
                while input.get(pos).is_some_and(u8::is_ascii_digit) {
                    tick(statistics, limits.input.max_operations)?;
                    pos += 1;
                }
                if input[digits] == b'0' && pos - digits != 1 {
                    return Err(error(
                        ErrorKind::InvalidInput,
                        start,
                        "leading zero in integer name",
                    ));
                }
                let mut value = String::new();
                if negative && input[digits] != b'0' {
                    value.push('-');
                }
                value.push_str(std::str::from_utf8(&input[digits..pos]).expect("ASCII digits"));
                Kind::IntegerName(value)
            }
            b'a'..=b'z' | b'A'..=b'Z' => {
                let variable = byte.is_ascii_uppercase();
                pos += 1;
                while pos < input.len()
                    && (input[pos].is_ascii_alphanumeric() || input[pos] == b'_')
                {
                    tick(statistics, limits.input.max_operations)?;
                    pos += 1;
                }
                let name = String::from_utf8(input[start..pos].to_vec()).expect("ASCII identifier");
                if variable {
                    Kind::Variable(name)
                } else {
                    Kind::Lower(name)
                }
            }
            b'$' => {
                pos += 1;
                while pos < input.len()
                    && (input[pos].is_ascii_alphanumeric() || input[pos] == b'_')
                {
                    tick(statistics, limits.input.max_operations)?;
                    pos += 1;
                }
                match &input[start..pos] {
                    b"$true" => Kind::True,
                    b"$false" => Kind::False,
                    _ => {
                        return Err(error(
                            ErrorKind::Unsupported,
                            start,
                            "interpreted symbols are unsupported",
                        ));
                    }
                }
            }
            b'=' if input.get(pos + 1) == Some(&b'>') => {
                tick(statistics, limits.input.max_operations)?;
                pos += 2;
                Kind::Implies
            }
            b'=' => {
                pos += 1;
                Kind::Equality(true)
            }
            b'!' if input.get(pos + 1) == Some(&b'=') => {
                tick(statistics, limits.input.max_operations)?;
                pos += 2;
                Kind::Equality(false)
            }
            b'<' if input.get(pos + 1) == Some(&b'=') && input.get(pos + 2) != Some(&b'>') => {
                tick(statistics, limits.input.max_operations)?;
                pos += 2;
                Kind::ReverseImplies
            }
            b'<' if input.get(pos + 1..pos + 3) == Some(b"=>") => {
                tick(statistics, limits.input.max_operations)?;
                tick(statistics, limits.input.max_operations)?;
                pos += 3;
                Kind::Iff
            }
            b'<' if input.get(pos + 1..pos + 3) == Some(b"~>") => {
                tick(statistics, limits.input.max_operations)?;
                tick(statistics, limits.input.max_operations)?;
                pos += 3;
                Kind::Xor
            }
            b'~' if matches!(input.get(pos + 1), Some(b'&' | b'|')) => {
                tick(statistics, limits.input.max_operations)?;
                let operator = input[pos + 1];
                pos += 2;
                if operator == b'&' {
                    Kind::Nand
                } else {
                    Kind::Nor
                }
            }
            b'(' | b')' | b',' | b'.' | b'|' | b'~' | b'&' | b'!' | b'?' | b'[' | b']' | b':' => {
                pos += 1;
                Kind::Punctuation(byte)
            }
            b'>' | b'<' | b'"' | b'%' | b'/' | b'_' => {
                return Err(error(
                    ErrorKind::Unsupported,
                    start,
                    "token is outside the supported CNF/quantified FOF fragment",
                ));
            }
            128..=255 => {
                return Err(error(
                    ErrorKind::InvalidInput,
                    start,
                    "input must contain ASCII bytes only",
                ));
            }
            _ => return Err(error(ErrorKind::InvalidInput, start, "invalid character")),
        };
        tokens.push(Token {
            kind,
            offset: start,
            end: pos,
        });
    }
    Ok(tokens)
}

#[derive(Default)]
struct Symbols {
    ids: BTreeMap<(String, usize), u32>,
    entries: Vec<Symbol>,
}

impl Symbols {
    fn reserve(&mut self, name: &str, arity: usize) -> Result<u32, Error> {
        let key = (name.to_owned(), arity);
        if let Some(id) = self.ids.get(&key) {
            return Ok(*id);
        }
        let id =
            u32::try_from(self.entries.len()).map_err(|_| Error::resource("symbol ID overflow"))?;
        self.ids.insert(key, id);
        self.entries.push(Symbol {
            name: name.into(),
            arity,
        });
        Ok(id)
    }

    fn finish(self) -> Vec<Symbol> {
        self.entries
    }
}

struct Parser<'a> {
    tokens: Vec<Token>,
    cursor: usize,
    input_len: usize,
    limits: &'a Limits,
    functions: Symbols,
    predicates: Symbols,
    variables: BTreeMap<String, u32>,
    variable_names: Vec<String>,
    active_binders: Vec<u32>,
    scope: Scope,
    statistics: Statistics,
}

impl Parser<'_> {
    fn offset(&self) -> usize {
        self.tokens
            .get(self.cursor)
            .map_or(self.input_len, |t| t.offset)
    }
    fn invalid(&self, message: &str) -> Error {
        error(ErrorKind::InvalidInput, self.offset(), message)
    }
    fn peek(&self) -> Option<&Kind> {
        self.tokens.get(self.cursor).map(|t| &t.kind)
    }
    fn advance(&mut self) -> Result<(), Error> {
        tick(&mut self.statistics, self.limits.input.max_operations)?;
        self.cursor += 1;
        Ok(())
    }
    fn punctuation(&mut self, p: u8) -> Result<(), Error> {
        if self.accept(p)? {
            Ok(())
        } else {
            Err(self.invalid(&format!("expected '{}'", p as char)))
        }
    }
    fn accept(&mut self, p: u8) -> Result<bool, Error> {
        if self.peek() == Some(&Kind::Punctuation(p)) {
            self.advance()?;
            Ok(true)
        } else {
            Ok(false)
        }
    }
    fn lower(&mut self) -> Result<String, Error> {
        if let Some(Kind::Lower(name)) = self.peek() {
            let name = name.clone();
            self.advance()?;
            Ok(name)
        } else {
            Err(self.invalid("expected a lowercase identifier"))
        }
    }
    fn declaration_name(&mut self) -> Result<(NameKind, String), Error> {
        let name = match self.peek().cloned() {
            Some(Kind::Lower(name) | Kind::Quoted(name)) => (NameKind::Atom, name),
            Some(Kind::IntegerName(name)) => (NameKind::Integer, name),
            _ => return Err(self.invalid("expected an atomic or integer declaration name")),
        };
        self.advance()?;
        Ok(name)
    }
    // Classify a neutral head only after seeing an optional equality operator.
    // This prevents an equality operand from taking a predicate ID.
    fn named_term(&mut self, depth: usize) -> Result<NamedTerm, Error> {
        if depth > 64 {
            return Err(Error::resource("source syntax depth limit exceeded"));
        }
        let offset = self.offset();
        match self.peek().cloned() {
            Some(Kind::Variable(name)) => {
                self.advance()?;
                Ok(NamedTerm::Variable(name, offset))
            }
            Some(Kind::Lower(name) | Kind::Quoted(name)) => {
                self.advance()?;
                let mut arguments = Vec::new();
                if self.accept(b'(')? {
                    arguments.push(self.named_term(depth + 1)?);
                    while self.accept(b',')? {
                        arguments.push(self.named_term(depth + 1)?);
                    }
                    self.punctuation(b')')?;
                }
                Ok(NamedTerm::Function(name, arguments))
            }
            Some(Kind::IntegerName(_)) => Err(error(
                ErrorKind::Unsupported,
                offset,
                "numeric terms have no enabled untyped interpretation",
            )),
            _ => Err(self.invalid("expected an uninterpreted term or predicate head")),
        }
    }

    fn encode_term(&mut self, term: NamedTerm, depth: usize) -> Result<Term, Error> {
        if depth > self.limits.input.max_term_depth.min(64) {
            return Err(Error::resource("term depth limit exceeded"));
        }
        if self.statistics.term_nodes >= self.limits.input.max_term_nodes {
            return Err(Error::resource("input term node limit exceeded"));
        }
        self.statistics.term_nodes += 1;
        match term {
            NamedTerm::Variable(name, offset) => {
                if self.scope == Scope::FofExplicit {
                    let id = self.variables.get(&name).copied().ok_or_else(|| {
                        error(
                            ErrorKind::InvalidInput,
                            offset,
                            "free variables are invalid in FOF",
                        )
                    })?;
                    if !self.active_binders.contains(&id) {
                        return Err(error(
                            ErrorKind::InvalidInput,
                            offset,
                            "variable is outside its lexical binder scope",
                        ));
                    }
                    return Ok(Term::Var(id));
                }
                let next = u32::try_from(self.variables.len())
                    .map_err(|_| Error::resource("variable ID overflow"))?;
                if !self.variables.contains_key(&name) {
                    self.variable_names.push(name.clone());
                }
                Ok(Term::Var(*self.variables.entry(name).or_insert(next)))
            }
            NamedTerm::Function(name, arguments) => {
                let id = self.functions.reserve(&name, arguments.len())?;
                let mut args = Vec::new();
                for argument in arguments {
                    args.push(self.encode_term(argument, depth + 1)?);
                }
                Ok(Term::Fun(id, args))
            }
        }
    }

    fn atom(&mut self) -> Result<Literal, Error> {
        if matches!(self.peek(), Some(Kind::Punctuation(b'!' | b'?'))) {
            return Err(error(
                ErrorKind::Unsupported,
                self.offset(),
                "quantifiers are unsupported in CNF",
            ));
        }
        let first = self.named_term(0)?;
        if let Some(Kind::Equality(positive)) = self.peek().cloned() {
            self.advance()?;
            let second = self.named_term(0)?;
            return Ok(Literal {
                positive,
                atom: Atom::Equal(self.encode_term(first, 1)?, self.encode_term(second, 1)?),
            });
        }
        match first {
            NamedTerm::Variable(_, offset) => Err(error(
                ErrorKind::InvalidInput,
                offset,
                "a variable cannot be a predicate",
            )),
            NamedTerm::Function(name, arguments) => {
                let predicate = self.predicates.reserve(&name, arguments.len())?;
                let mut args = Vec::new();
                for argument in arguments {
                    args.push(self.encode_term(argument, 1)?);
                }
                Ok(Literal {
                    positive: true,
                    atom: Atom::Predicate(predicate, args),
                })
            }
        }
    }

    fn literal(&mut self) -> Result<CnfLiteral, Error> {
        let negated = self.accept(b'~')?;
        // A negated atomic formula may have one parenthesis pair.
        let parenthesized = negated && self.accept(b'(')?;
        let mut literal = match self.peek() {
            Some(Kind::True | Kind::False) => {
                let value = self.peek() == Some(&Kind::True);
                self.advance()?;
                CnfLiteral::Boolean {
                    positive: true,
                    value,
                }
            }
            _ => CnfLiteral::Ordinary(self.atom()?),
        };
        if parenthesized {
            self.punctuation(b')')?;
        }
        if negated {
            match &mut literal {
                CnfLiteral::Ordinary(value) => {
                    if !value.positive {
                        return Err(error(
                            ErrorKind::InvalidInput,
                            self.offset(),
                            "infix inequality is not an atomic formula under CNF negation",
                        ));
                    }
                    value.positive = false;
                }
                CnfLiteral::Boolean { positive, .. } => *positive = false,
            }
        }
        Ok(literal)
    }
    fn clause_formula(&mut self, depth: usize) -> Result<Vec<CnfLiteral>, Error> {
        if depth > self.limits.max_formula_depth.min(64) {
            return Err(Error::resource("CNF parenthesis depth limit exceeded"));
        }
        if self.accept(b'(')? {
            let clause = self.clause_formula(depth + 1)?;
            self.punctuation(b')')?;
            Ok(clause)
        } else {
            self.clause()
        }
    }
    fn clause(&mut self) -> Result<Vec<CnfLiteral>, Error> {
        let mut literals = Vec::new();
        loop {
            if literals.len() >= self.limits.input.max_literals {
                return Err(Error::resource("input literal limit exceeded"));
            }
            literals.push(self.literal()?);
            if !self.accept(b'|')? {
                break;
            }
        }
        if matches!(self.peek(), Some(Kind::Implies | Kind::Punctuation(b'&'))) {
            return Err(error(
                ErrorKind::Unsupported,
                self.offset(),
                "formula connectives are unsupported in CNF",
            ));
        }
        Ok(literals)
    }
    fn count_formula(&mut self) -> Result<(), Error> {
        if self.statistics.formula_nodes >= self.limits.max_formula_nodes {
            return Err(Error::resource("input formula node limit exceeded"));
        }
        self.statistics.formula_nodes += 1;
        Ok(())
    }

    // Duplication for iff/XOR stays inside the parser's AST budgets. Numeric
    // source IDs are copied verbatim; later rectification handles each binder
    // occurrence. No new source table entry is allocated by these functions.
    fn copy_term(&mut self, value: &Term, depth: usize) -> Result<Term, Error> {
        if depth > self.limits.input.max_term_depth.min(64) {
            return Err(Error::resource("copied term depth limit exceeded"));
        }
        tick(&mut self.statistics, self.limits.input.max_operations)?;
        if self.statistics.term_nodes >= self.limits.input.max_term_nodes {
            return Err(Error::resource("copied term node limit exceeded"));
        }
        self.statistics.term_nodes += 1;
        Ok(match value {
            Term::Var(id) => Term::Var(*id),
            Term::Fun(id, arguments) => {
                let mut copied = Vec::new();
                for argument in arguments {
                    copied.push(self.copy_term(argument, depth + 1)?);
                }
                Term::Fun(*id, copied)
            }
        })
    }

    fn copy_formula(&mut self, value: &Formula, depth: usize) -> Result<Formula, Error> {
        self.check_height(depth, 1)?;
        tick(&mut self.statistics, self.limits.input.max_operations)?;
        self.count_formula()?;
        Ok(match value {
            Formula::Atom(Atom::Predicate(id, arguments)) => {
                let mut copied = Vec::new();
                for argument in arguments {
                    copied.push(self.copy_term(argument, 1)?);
                }
                Formula::Atom(Atom::Predicate(*id, copied))
            }
            Formula::Atom(Atom::Equal(left, right)) => Formula::Atom(Atom::Equal(
                self.copy_term(left, 1)?,
                self.copy_term(right, 1)?,
            )),
            Formula::True => Formula::True,
            Formula::False => Formula::False,
            Formula::Not(body) => Formula::Not(Box::new(self.copy_formula(body, depth + 1)?)),
            Formula::And(left, right) => Formula::And(
                Box::new(self.copy_formula(left, depth + 1)?),
                Box::new(self.copy_formula(right, depth + 1)?),
            ),
            Formula::Or(left, right) => Formula::Or(
                Box::new(self.copy_formula(left, depth + 1)?),
                Box::new(self.copy_formula(right, depth + 1)?),
            ),
            Formula::Implies(left, right) => Formula::Implies(
                Box::new(self.copy_formula(left, depth + 1)?),
                Box::new(self.copy_formula(right, depth + 1)?),
            ),
            Formula::Forall(id, body) => {
                Formula::Forall(*id, Box::new(self.copy_formula(body, depth + 1)?))
            }
            Formula::Exists(id, body) => {
                Formula::Exists(*id, Box::new(self.copy_formula(body, depth + 1)?))
            }
        })
    }
    fn quantified(&mut self, universal: bool, depth: usize) -> Result<(Formula, usize), Error> {
        self.advance()?;
        self.punctuation(b'[')?;
        let mut binders = Vec::new();
        loop {
            let Some(Kind::Variable(name)) = self.peek().cloned() else {
                return Err(self.invalid("expected a nonempty list of uppercase binder names"));
            };
            if self.statistics.binders >= self.limits.max_binders {
                return Err(Error::resource("input binder limit exceeded"));
            }
            // Each list element is a real nested AST node, even if unused.
            // Check before allocation so a long flat prefix cannot bypass depth.
            if depth + binders.len() >= self.limits.max_formula_depth.min(64) {
                return Err(Error::resource("formula nesting limit exceeded"));
            }
            self.count_formula()?;
            self.statistics.binders += 1;
            let next = u32::try_from(self.variable_names.len())
                .map_err(|_| Error::resource("variable ID overflow"))?;
            if !self.variables.contains_key(&name) {
                self.variable_names.push(name.clone());
            }
            let id = *self.variables.entry(name).or_insert(next);
            binders.push(id);
            self.advance()?;
            if self.peek() == Some(&Kind::Punctuation(b':')) {
                return Err(error(
                    ErrorKind::Unsupported,
                    self.offset(),
                    "typed binders are unsupported",
                ));
            }
            if !self.accept(b',')? {
                break;
            }
        }
        self.punctuation(b']')?;
        self.punctuation(b':')?;
        let previous = self.active_binders.len();
        self.active_binders.extend_from_slice(&binders);
        let result = self.unit_formula(depth + binders.len());
        self.active_binders.truncate(previous);
        let (mut body, height) = result?;
        let height = height + binders.len();
        for id in binders.into_iter().rev() {
            body = if universal {
                Formula::Forall(id, Box::new(body))
            } else {
                Formula::Exists(id, Box::new(body))
            };
        }
        Ok((body, height))
    }
    fn check_height(&self, depth: usize, height: usize) -> Result<(), Error> {
        let end = depth
            .checked_add(height.saturating_sub(1))
            .ok_or_else(|| Error::resource("formula depth overflow"))?;
        if end > self.limits.max_formula_depth.min(64) {
            return Err(Error::resource("formula nesting limit exceeded"));
        }
        Ok(())
    }

    /// A unit consumes only one unary/quantified/atomic/grouped formula.
    /// Returned height counts the actual AST, including lowered NAND/NOR.
    fn unit_formula(&mut self, depth: usize) -> Result<(Formula, usize), Error> {
        self.check_height(depth, 1)?;
        match self.peek().cloned() {
            Some(Kind::True) => {
                self.advance()?;
                self.count_formula()?;
                Ok((Formula::True, 1))
            }
            Some(Kind::False) => {
                self.advance()?;
                self.count_formula()?;
                Ok((Formula::False, 1))
            }
            Some(Kind::Punctuation(b'~')) => {
                self.advance()?;
                self.count_formula()?;
                let (body, height) = self.unit_formula(depth + 1)?;
                Ok((Formula::Not(Box::new(body)), height + 1))
            }
            Some(Kind::Punctuation(b'(')) => {
                self.advance()?;
                let body = self.logic_formula(depth + 1)?;
                self.punctuation(b')')?;
                Ok(body)
            }
            Some(Kind::Lower(_) | Kind::Quoted(_) | Kind::Variable(_)) => {
                self.count_formula()?;
                let literal = self.atom()?;
                let atom = Formula::Atom(literal.atom);
                if literal.positive {
                    Ok((atom, 1))
                } else {
                    self.check_height(depth, 2)?;
                    self.count_formula()?;
                    Ok((Formula::Not(Box::new(atom)), 2))
                }
            }
            Some(Kind::Punctuation(b'!')) => self.quantified(true, depth),
            Some(Kind::Punctuation(b'?')) => self.quantified(false, depth),
            Some(Kind::IntegerName(_)) => Err(error(
                ErrorKind::Unsupported,
                self.offset(),
                "numeric terms have no enabled untyped interpretation",
            )),
            _ => Err(self.invalid("expected a first-order unit formula")),
        }
    }

    fn logic_formula(&mut self, depth: usize) -> Result<(Formula, usize), Error> {
        let (mut left, mut height) = self.unit_formula(depth)?;
        let Some(operator) = self.peek().cloned() else {
            return Ok((left, height));
        };
        if !matches!(
            operator,
            Kind::Implies
                | Kind::ReverseImplies
                | Kind::Nand
                | Kind::Nor
                | Kind::Iff
                | Kind::Xor
                | Kind::Punctuation(b'&' | b'|')
        ) {
            return Ok((left, height));
        }
        let associative = matches!(operator, Kind::Punctuation(b'&' | b'|'));
        let (extra, parents) = match operator {
            Kind::Nand | Kind::Nor => (2, 2),
            Kind::Iff => (2, 3),
            Kind::Xor => (3, 4),
            _ => (1, 1),
        };
        loop {
            self.advance()?;
            for _ in 0..parents {
                self.count_formula()?;
            }
            let (right, right_height) = self.unit_formula(depth + extra)?;
            height = height
                .max(right_height)
                .checked_add(extra)
                .ok_or_else(|| Error::resource("formula depth overflow"))?;
            self.check_height(depth, height)?;
            if matches!(operator, Kind::Iff | Kind::Xor) {
                let copied_left = self.copy_formula(&left, depth + extra)?;
                let copied_right = self.copy_formula(&right, depth + extra)?;
                let equivalent = Formula::And(
                    Box::new(Formula::Implies(Box::new(left), Box::new(right))),
                    Box::new(Formula::Implies(
                        Box::new(copied_right),
                        Box::new(copied_left),
                    )),
                );
                return Ok((
                    if matches!(operator, Kind::Xor) {
                        Formula::Not(Box::new(equivalent))
                    } else {
                        equivalent
                    },
                    height,
                ));
            }
            // Source tables were populated left-to-right before any operand swap.
            left = match operator {
                Kind::Implies => Formula::Implies(Box::new(left), Box::new(right)),
                Kind::ReverseImplies => Formula::Implies(Box::new(right), Box::new(left)),
                Kind::Punctuation(b'&') => Formula::And(Box::new(left), Box::new(right)),
                Kind::Punctuation(b'|') => Formula::Or(Box::new(left), Box::new(right)),
                Kind::Nand => Formula::Not(Box::new(Formula::And(Box::new(left), Box::new(right)))),
                Kind::Nor => Formula::Not(Box::new(Formula::Or(Box::new(left), Box::new(right)))),
                _ => unreachable!("operator was checked above"),
            };
            if !associative || self.peek() != Some(&operator) {
                break;
            }
        }
        // Mixed lists and repeated nonassociative pairs are rejected by framing.
        Ok((left, height))
    }

    fn formula(&mut self, depth: usize) -> Result<Formula, Error> {
        self.logic_formula(depth).map(|value| value.0)
    }
}

/// Parse every byte, retaining raw clauses and original declaration order.
/// Errors publish no partial result. This function performs no preprocessing.
pub fn parse(input: &[u8], limits: &Limits) -> Result<Parsed, Error> {
    let mut statistics = Statistics::default();
    let tokens = lex(input, limits, &mut statistics)?;
    let mut parser = Parser {
        tokens,
        cursor: 0,
        input_len: input.len(),
        limits,
        functions: Symbols::default(),
        predicates: Symbols::default(),
        variables: BTreeMap::new(),
        variable_names: Vec::new(),
        active_binders: Vec::new(),
        scope: Scope::FofExplicit,
        statistics,
    };
    let mut names = BTreeSet::new();
    let mut declarations = Vec::new();
    while parser.peek().is_some() {
        // Before clausification, max_clauses bounds source declarations.
        if declarations.len() >= limits.input.max_clauses {
            return Err(Error::resource("input declaration limit exceeded"));
        }
        let start = parser.offset();
        let kind = parser.lower()?;
        if kind != "cnf" && kind != "fof" {
            let classification = if ["include", "tff", "thf", "tcf"].contains(&kind.as_str()) {
                ErrorKind::Unsupported
            } else {
                ErrorKind::InvalidInput
            };
            return Err(error(
                classification,
                start,
                "only CNF and the restricted FOF statements are supported",
            ));
        }
        parser.punctuation(b'(')?;
        let offset = parser.offset();
        let (name_kind, name) = parser.declaration_name()?;
        if !names.insert((name_kind, name.clone())) {
            return Err(error(
                ErrorKind::InvalidInput,
                offset,
                "duplicate statement name",
            ));
        }
        parser.punctuation(b',')?;
        let role_offset = parser.offset();
        if parser.lower()? != "axiom" {
            return Err(error(
                ErrorKind::Unsupported,
                role_offset,
                "only the axiom role is supported",
            ));
        }
        parser.punctuation(b',')?;
        parser.variables.clear();
        parser.variable_names.clear();
        parser.active_binders.clear();
        parser.scope = if kind == "cnf" {
            Scope::CnfImplicit
        } else {
            Scope::FofExplicit
        };
        let body_start = parser.offset();
        let body = if kind == "cnf" {
            Body::Cnf(parser.clause_formula(1)?)
        } else {
            let formula = parser.formula(1)?;
            Body::Fof(formula)
        };
        let body_end = parser.tokens[parser.cursor - 1].end;
        if parser.peek() == Some(&Kind::Punctuation(b',')) {
            return Err(error(
                ErrorKind::Unsupported,
                parser.offset(),
                "TPTP annotations are unsupported",
            ));
        }
        parser.punctuation(b')')?;
        parser.punctuation(b'.')?;
        let end = parser.tokens[parser.cursor - 1].end;
        declarations.push(Declaration {
            name,
            name_kind,
            bytes: start..end,
            variables: std::mem::take(&mut parser.variable_names),
            body_bytes: body_start..body_end,
            body,
        });
    }
    Ok(Parsed {
        functions: parser.functions.finish(),
        predicates: parser.predicates.finish(),
        declarations,
        statistics: parser.statistics,
    })
}
