// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Adapted from the accepted ground FOF frontend.
// Reused Fang terms/literals retain the notices in LICENSES/Vampire.txt.
#![forbid(unsafe_code)]

//! Isolated parser for mixed CNF, ground FOF and one explicit universal prefix.
//! This parser is untrusted by result certification. No production CLI uses it.

use fang::syntax::{Clause, Literal, Symbol, Term};
use fang::{Error, ErrorKind};
use fang_fof_core::Formula;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

#[derive(Clone, Debug)]
pub struct Limits {
    pub input: fang::Limits,
    /// Recursive formula calls, including redundant grouping, capped at 64.
    pub max_formula_depth: usize,
    /// Total FOF AST nodes in the file. Parentheses add no AST node.
    pub max_formula_nodes: usize,
    /// Distinct positions in one universal prefix, including unused names.
    pub max_binders: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            input: fang::Limits::default(),
            max_formula_depth: 64,
            max_formula_nodes: 10_000,
            max_binders: 4_096,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Body {
    /// Original literal order and multiplicity, before stable deduplication.
    Cnf(Clause),
    Fof(Formula),
    /// Quantifier-free body whose variables are the declaration's prefix IDs.
    Universal(Formula),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Declaration {
    pub name: String,
    /// From the declaration keyword through its period, excluding outer space.
    pub bytes: Range<usize>,
    /// First occurrence order in CNF; prefix position order in universal FOF.
    /// Empty for ground FOF. Reset at each declaration.
    pub variables: Vec<String>,
    /// Exact prefix bytes from '!' through ':', excluding surrounding space.
    pub prefix_bytes: Option<Range<usize>>,
    /// The quantifier-free formula, or CNF body including its required parentheses.
    pub body_bytes: Range<usize>,
    pub body: Body,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Statistics {
    /// One operation per lexed byte and per consumed token.
    pub operations: usize,
    pub formula_nodes: usize,
    pub term_nodes: usize,
}

#[derive(Debug)]
pub struct Parsed {
    pub functions: Vec<Symbol>,
    pub predicates: Vec<Symbol>,
    pub declarations: Vec<Declaration>,
    pub statistics: Statistics,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Kind {
    Lower(String),
    Variable(String),
    True,
    False,
    Implies,
    Punctuation(u8),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Scope {
    CnfImplicit,
    GroundFof,
    UniversalPrefix,
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
        let kind = match byte {
            b'a'..=b'z' | b'A'..=b'Z' => {
                let variable = byte.is_ascii_uppercase();
                pos += 1;
                while pos < input.len()
                    && (input[pos].is_ascii_alphanumeric() || input[pos] == b'_')
                {
                    tick(statistics, limits.input.max_operations)?;
                    if !variable && input[pos].is_ascii_uppercase() {
                        return Err(error(
                            ErrorKind::InvalidInput,
                            pos,
                            "uppercase character in a lowercase identifier",
                        ));
                    }
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
            b'~' if matches!(input.get(pos + 1), Some(b'&' | b'|')) => {
                return Err(error(
                    ErrorKind::Unsupported,
                    start,
                    "NAND and NOR are unsupported",
                ));
            }
            b'(' | b')' | b',' | b'.' | b'|' | b'~' | b'&' | b'!' | b'[' | b']' | b':' => {
                pos += 1;
                Kind::Punctuation(byte)
            }
            b'=' | b'?' | b'>' | b'<' | b'\'' | b'"' | b'%' | b'/' | b'_' | b'0'..=b'9' => {
                return Err(error(
                    ErrorKind::Unsupported,
                    start,
                    "token is outside the supported CNF/universal FOF fragment",
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
    ids: BTreeMap<String, u32>,
    entries: Vec<(String, Option<usize>)>,
}

impl Symbols {
    fn reserve(&mut self, name: &str) -> Result<u32, Error> {
        if let Some(id) = self.ids.get(name) {
            return Ok(*id);
        }
        let id =
            u32::try_from(self.entries.len()).map_err(|_| Error::resource("symbol ID overflow"))?;
        self.ids.insert(name.into(), id);
        self.entries.push((name.into(), None));
        Ok(id)
    }

    fn arity(&mut self, id: u32, arity: usize, offset: usize) -> Result<(), Error> {
        let entry = &mut self.entries[id as usize];
        if entry.1.is_some_and(|previous| previous != arity) {
            return Err(error(
                ErrorKind::InvalidInput,
                offset,
                "inconsistent symbol arity",
            ));
        }
        entry.1 = Some(arity);
        Ok(())
    }

    fn finish(self) -> Vec<Symbol> {
        self.entries
            .into_iter()
            .map(|(name, arity)| Symbol {
                name,
                arity: arity.expect("completed symbol"),
            })
            .collect()
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
    fn args(&mut self, depth: usize) -> Result<Vec<Term>, Error> {
        if !self.accept(b'(')? {
            return Ok(Vec::new());
        }
        let mut args = vec![self.term(depth)?];
        while self.accept(b',')? {
            args.push(self.term(depth)?);
        }
        self.punctuation(b')')?;
        Ok(args)
    }
    fn term(&mut self, depth: usize) -> Result<Term, Error> {
        if depth > self.limits.input.max_term_depth.min(64) {
            return Err(Error::resource("term depth limit exceeded"));
        }
        if self.statistics.term_nodes >= self.limits.input.max_term_nodes {
            return Err(Error::resource("input term node limit exceeded"));
        }
        self.statistics.term_nodes += 1;
        let offset = self.offset();
        match self.peek().cloned() {
            Some(Kind::Variable(name)) => {
                match self.scope {
                    Scope::GroundFof => {
                        return Err(self.invalid("free variables are invalid in ground FOF"));
                    }
                    Scope::UniversalPrefix => {
                        let id = self.variables.get(&name).copied().ok_or_else(|| {
                            self.invalid("variable is not declared in the universal prefix")
                        })?;
                        self.advance()?;
                        return Ok(Term::Var(id));
                    }
                    Scope::CnfImplicit => {}
                }
                self.advance()?;
                let next = u32::try_from(self.variables.len())
                    .map_err(|_| Error::resource("variable ID overflow"))?;
                if !self.variables.contains_key(&name) {
                    self.variable_names.push(name.clone());
                }
                let id = *self.variables.entry(name).or_insert(next);
                Ok(Term::Var(id))
            }
            Some(Kind::Lower(name)) => {
                self.advance()?;
                // Reserve before children: f(g(a)) assigns f first.
                let id = self.functions.reserve(&name)?;
                let args = self.args(depth + 1)?;
                self.functions.arity(id, args.len(), offset)?;
                Ok(Term::Fun(id, args))
            }
            _ => Err(self.invalid("expected a term")),
        }
    }
    fn atom(&mut self) -> Result<(u32, Vec<Term>), Error> {
        if self.peek() == Some(&Kind::Punctuation(b'!')) {
            return Err(error(
                ErrorKind::Unsupported,
                self.offset(),
                "quantifier outside a single FOF declaration prefix",
            ));
        }
        let offset = self.offset();
        let name = self.lower()?;
        let predicate = self.predicates.reserve(&name)?;
        let arguments = self.args(1)?;
        self.predicates.arity(predicate, arguments.len(), offset)?;
        Ok((predicate, arguments))
    }
    fn literal(&mut self) -> Result<Literal, Error> {
        let positive = !self.accept(b'~')?;
        let (predicate, arguments) = self.atom()?;
        Ok(Literal {
            positive,
            predicate,
            arguments,
        })
    }
    fn clause(&mut self) -> Result<Clause, Error> {
        if self.peek() == Some(&Kind::False) {
            self.advance()?;
            return Ok(Vec::new());
        }
        if self.peek() == Some(&Kind::True) {
            return Err(error(
                ErrorKind::Unsupported,
                self.offset(),
                "$true is unsupported in CNF",
            ));
        }
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
    fn universal_prefix(&mut self) -> Result<Range<usize>, Error> {
        let start = self.offset();
        self.punctuation(b'!')?;
        self.punctuation(b'[')?;
        loop {
            let Some(Kind::Variable(name)) = self.peek().cloned() else {
                return Err(self.invalid("expected a nonempty list of uppercase binder names"));
            };
            if self.variables.contains_key(&name) {
                return Err(self.invalid("duplicate universal binder"));
            }
            if self.variable_names.len() >= self.limits.max_binders {
                return Err(Error::resource("universal binder limit exceeded"));
            }
            let count = self
                .variable_names
                .len()
                .checked_add(1)
                .and_then(|count| u32::try_from(count).ok())
                .ok_or_else(|| Error::resource("universal binder count overflow"))?;
            self.advance()?;
            self.variables.insert(name.clone(), count - 1);
            self.variable_names.push(name);
            if self.peek() == Some(&Kind::Punctuation(b':')) {
                return Err(error(
                    ErrorKind::Unsupported,
                    self.offset(),
                    "typed universal binders are unsupported",
                ));
            }
            if !self.accept(b',')? {
                break;
            }
        }
        self.punctuation(b']')?;
        self.punctuation(b':')?;
        Ok(start..self.tokens[self.cursor - 1].end)
    }
    fn formula(&mut self, depth: usize) -> Result<Formula, Error> {
        if depth > self.limits.max_formula_depth.min(64) {
            return Err(Error::resource("formula nesting limit exceeded"));
        }
        match self.peek().cloned() {
            Some(Kind::True) => {
                self.advance()?;
                self.count_formula()?;
                Ok(Formula::True)
            }
            Some(Kind::False) => {
                self.advance()?;
                self.count_formula()?;
                Ok(Formula::False)
            }
            Some(Kind::Punctuation(b'~')) => {
                self.advance()?;
                self.count_formula()?;
                Ok(Formula::Not(Box::new(self.formula(depth + 1)?)))
            }
            Some(Kind::Punctuation(b'(')) => {
                self.advance()?;
                let left = self.formula(depth + 1)?;
                let operator = self.peek().cloned();
                if matches!(
                    operator,
                    Some(Kind::Implies | Kind::Punctuation(b'&' | b'|'))
                ) {
                    self.advance()?;
                    self.count_formula()?;
                    let right = self.formula(depth + 1)?;
                    self.punctuation(b')')?;
                    let left = Box::new(left);
                    let right = Box::new(right);
                    match operator {
                        Some(Kind::Implies) => Ok(Formula::Implies(left, right)),
                        Some(Kind::Punctuation(b'&')) => Ok(Formula::And(left, right)),
                        Some(Kind::Punctuation(b'|')) => Ok(Formula::Or(left, right)),
                        _ => unreachable!("operator was checked above"),
                    }
                } else {
                    self.punctuation(b')')?;
                    Ok(left)
                }
            }
            Some(Kind::Lower(_)) => {
                self.count_formula()?;
                let (predicate, arguments) = self.atom()?;
                Ok(Formula::Atom(predicate, arguments))
            }
            Some(Kind::Variable(_)) => Err(self.invalid("a variable cannot be a formula")),
            Some(Kind::Punctuation(b'!')) => Err(error(
                ErrorKind::Unsupported,
                self.offset(),
                "nested or parenthesized universal prefixes are unsupported",
            )),
            _ => Err(self.invalid("expected a quantifier-free formula")),
        }
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
        scope: Scope::GroundFof,
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
        let name = parser.lower()?;
        if !names.insert(name.clone()) {
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
        parser.scope = if kind == "cnf" {
            Scope::CnfImplicit
        } else {
            Scope::GroundFof
        };
        let prefix_bytes = if kind == "fof" && parser.peek() == Some(&Kind::Punctuation(b'!')) {
            let prefix = parser.universal_prefix()?;
            parser.scope = Scope::UniversalPrefix;
            Some(prefix)
        } else {
            None
        };
        let body_start = parser.offset();
        let body = if kind == "cnf" {
            parser.punctuation(b'(')?;
            let clause = parser.clause()?;
            parser.punctuation(b')')?;
            Body::Cnf(clause)
        } else {
            let formula = parser.formula(1)?;
            if parser.scope == Scope::UniversalPrefix {
                Body::Universal(formula)
            } else {
                Body::Fof(formula)
            }
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
            bytes: start..end,
            variables: std::mem::take(&mut parser.variable_names),
            prefix_bytes,
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
