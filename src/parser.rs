// Copyright (c) 2026 Pietro Pellegrino.
// Grammar: docs/USAGE.md. This parser is not trusted by the Lean checker.
use crate::syntax::{Clause, Literal, Problem, Symbol, Term, deduplicate};
use crate::{Error, ErrorKind, Limits};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Kind {
    Lower(String),
    Variable(String),
    False,
    Punctuation(u8),
}

#[derive(Clone, Debug)]
struct Token {
    kind: Kind,
    offset: usize,
}

fn error(kind: ErrorKind, offset: usize, message: &str) -> Error {
    Error {
        kind,
        offset: Some(offset),
        message: message.into(),
    }
}

fn lex(input: &[u8], limits: &Limits) -> Result<Vec<Token>, Error> {
    if input.len() > limits.max_input_bytes {
        return Err(Error::resource("input byte limit exceeded"));
    }
    let mut tokens = Vec::new();
    let mut pos = 0;
    while pos < input.len() {
        let start = pos;
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
                    if !variable && input[pos].is_ascii_uppercase() {
                        return Err(error(
                            ErrorKind::InvalidInput,
                            pos,
                            "uppercase character in a lowercase identifier",
                        ));
                    }
                    pos += 1;
                }
                // The scan above accepts ASCII only, so this conversion cannot fail.
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
                    pos += 1;
                }
                if &input[start..pos] == b"$false" {
                    Kind::False
                } else {
                    return Err(error(
                        ErrorKind::Unsupported,
                        start,
                        "interpreted symbols and $true are unsupported",
                    ));
                }
            }
            b'(' | b')' | b',' | b'.' | b'|' | b'~' => {
                pos += 1;
                Kind::Punctuation(byte)
            }
            b'='
            | b'!'
            | b'?'
            | b'&'
            | b'>'
            | b'<'
            | b':'
            | b'['
            | b']'
            | b'\''
            | b'"'
            | b'%'
            | b'/'
            | b'_'
            | b'0'..=b'9' => {
                return Err(error(
                    ErrorKind::Unsupported,
                    start,
                    "token is outside the supported TPTP CNF fragment",
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
    term_nodes: usize,
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
    fn punctuation(&mut self, p: u8) -> Result<(), Error> {
        if self.peek() == Some(&Kind::Punctuation(p)) {
            self.cursor += 1;
            Ok(())
        } else {
            Err(self.invalid(&format!("expected '{}'", p as char)))
        }
    }
    fn accept(&mut self, p: u8) -> bool {
        if self.peek() == Some(&Kind::Punctuation(p)) {
            self.cursor += 1;
            true
        } else {
            false
        }
    }
    fn lower(&mut self) -> Result<String, Error> {
        if let Some(Kind::Lower(name)) = self.peek() {
            let name = name.clone();
            self.cursor += 1;
            Ok(name)
        } else {
            Err(self.invalid("expected a lowercase identifier"))
        }
    }
    fn args(&mut self, depth: usize) -> Result<Vec<Term>, Error> {
        if !self.accept(b'(') {
            return Ok(Vec::new());
        }
        let mut args = vec![self.term(depth)?];
        while self.accept(b',') {
            args.push(self.term(depth)?);
        }
        self.punctuation(b')')?;
        Ok(args)
    }
    fn term(&mut self, depth: usize) -> Result<Term, Error> {
        if depth > self.limits.max_term_depth.min(64) {
            return Err(Error::resource("term depth limit exceeded"));
        }
        self.term_nodes += 1;
        if self.term_nodes > self.limits.max_term_nodes {
            return Err(Error::resource("input term node limit exceeded"));
        }
        let offset = self.offset();
        match self.peek().cloned() {
            Some(Kind::Variable(name)) => {
                self.cursor += 1;
                let next = u32::try_from(self.variables.len())
                    .map_err(|_| Error::resource("variable ID overflow"))?;
                let id = *self.variables.entry(name).or_insert(next);
                Ok(Term::Var(id))
            }
            Some(Kind::Lower(name)) => {
                self.cursor += 1;
                // Reserve before descending so f(g(a)) assigns f its ID first.
                let id = self.functions.reserve(&name)?;
                let args = self.args(depth + 1)?;
                self.functions.arity(id, args.len(), offset)?;
                Ok(Term::Fun(id, args))
            }
            _ => Err(self.invalid("expected a term")),
        }
    }
    fn literal(&mut self) -> Result<Literal, Error> {
        let positive = !self.accept(b'~');
        let offset = self.offset();
        let name = self.lower()?;
        let predicate = self.predicates.reserve(&name)?;
        let arguments = self.args(1)?;
        self.predicates.arity(predicate, arguments.len(), offset)?;
        Ok(Literal {
            positive,
            predicate,
            arguments,
        })
    }
    fn clause(&mut self) -> Result<Clause, Error> {
        if self.peek() == Some(&Kind::False) {
            self.cursor += 1;
            return Ok(Vec::new());
        }
        let mut literals = vec![self.literal()?];
        while self.accept(b'|') {
            if literals.len() >= self.limits.max_literals {
                return Err(Error::resource("input literal limit exceeded"));
            }
            literals.push(self.literal()?);
        }
        if literals.len() > self.limits.max_literals {
            return Err(Error::resource("input literal limit exceeded"));
        }
        Ok(deduplicate(&literals))
    }
}

/// Parse the strict grammar, consume every byte, then stably deduplicate literals.
pub fn parse(input: &[u8], limits: &Limits) -> Result<Problem, Error> {
    let tokens = lex(input, limits)?;
    let mut parser = Parser {
        tokens,
        cursor: 0,
        input_len: input.len(),
        limits,
        functions: Symbols::default(),
        predicates: Symbols::default(),
        variables: BTreeMap::new(),
        term_nodes: 0,
    };
    let mut names = BTreeSet::new();
    let mut clause_names = Vec::new();
    let mut clauses = Vec::new();
    while parser.peek().is_some() {
        if clauses.len() >= limits.max_clauses {
            return Err(Error::resource("input clause limit exceeded"));
        }
        let offset = parser.offset();
        let kind = parser.lower()?;
        if kind != "cnf" {
            let classification = if ["include", "fof", "tff", "thf", "tcf"].contains(&kind.as_str())
            {
                ErrorKind::Unsupported
            } else {
                ErrorKind::InvalidInput
            };
            return Err(error(
                classification,
                offset,
                "only cnf statements are supported",
            ));
        }
        parser.punctuation(b'(')?;
        let offset = parser.offset();
        let name = parser.lower()?;
        if !names.insert(name.clone()) {
            return Err(error(
                ErrorKind::InvalidInput,
                offset,
                "duplicate clause name",
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
        parser.punctuation(b'(')?;
        parser.variables.clear();
        let clause = parser.clause()?;
        parser.punctuation(b')')?;
        if parser.peek() == Some(&Kind::Punctuation(b',')) {
            return Err(error(
                ErrorKind::Unsupported,
                parser.offset(),
                "TPTP annotations are unsupported",
            ));
        }
        parser.punctuation(b')')?;
        parser.punctuation(b'.')?;
        clause_names.push(name);
        clauses.push(clause);
    }
    Ok(Problem {
        functions: parser.functions.finish(),
        predicates: parser.predicates.finish(),
        clause_names,
        clauses,
    })
}
