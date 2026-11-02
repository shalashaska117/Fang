// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Annotation parsing. Nothing here reads or writes the symbol tables, the
//! variable table, binder scope or the distinct-object inventory.

use crate::{Error, FORMULA_DATA, Kind, NameKind, Parser, syntax};
use std::ops::Range;

/// A BNF `<general_term>`, retained as metadata only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GeneralTerm {
    /// Decoded atomic word.
    Word(String),
    Function(String, Vec<GeneralTerm>),
    Variable(String),
    /// Canonical integer value, as for integer formula names.
    Integer(String),
    /// Rational or real spelling.
    Number(String),
    /// Decoded distinct-object content.
    Distinct(String),
    /// `$fof(...)` and the other formula data, kept as a byte span only.
    FormulaData {
        language: String,
        bytes: Range<usize>,
    },
    Colon(Box<GeneralTerm>, Box<GeneralTerm>),
    List(Vec<GeneralTerm>),
}

/// Classification of the source field; none of it is trusted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceClass {
    File {
        file: String,
        name: Option<(NameKind, String)>,
    },
    Inference,
    Introduced,
    Name(NameKind, String),
    List,
    Other,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Annotation {
    /// From the source's first byte through the last annotation byte.
    pub bytes: Range<usize>,
    pub source: GeneralTerm,
    pub source_bytes: Range<usize>,
    pub class: SourceClass,
    pub useful_info: Option<(Vec<GeneralTerm>, Range<usize>)>,
}

fn classify(source: &GeneralTerm) -> SourceClass {
    match source {
        GeneralTerm::Function(head, arguments) if head == "file" => match arguments.as_slice() {
            [GeneralTerm::Word(file)] => SourceClass::File {
                file: file.clone(),
                name: None,
            },
            [GeneralTerm::Word(file), GeneralTerm::Word(name)] => SourceClass::File {
                file: file.clone(),
                name: Some((NameKind::Atom, name.clone())),
            },
            [GeneralTerm::Word(file), GeneralTerm::Integer(name)] => SourceClass::File {
                file: file.clone(),
                name: Some((NameKind::Integer, name.clone())),
            },
            _ => SourceClass::Other,
        },
        GeneralTerm::Function(head, arguments) if head == "inference" && arguments.len() == 3 => {
            SourceClass::Inference
        }
        GeneralTerm::Function(head, arguments) if head == "introduced" && arguments.len() == 3 => {
            SourceClass::Introduced
        }
        GeneralTerm::Word(name) => SourceClass::Name(NameKind::Atom, name.clone()),
        GeneralTerm::Integer(name) => SourceClass::Name(NameKind::Integer, name.clone()),
        GeneralTerm::List(_) => SourceClass::List,
        _ => SourceClass::Other,
    }
}

impl Parser<'_> {
    fn end(&self) -> usize {
        self.tokens[self.cursor - 1].end
    }

    fn count_annotation(&mut self, depth: usize) -> Result<(), Error> {
        if depth > 64 {
            return Err(Error::resource("annotation depth limit exceeded"));
        }
        if self.statistics.annotation_nodes >= self.limits.max_annotation_nodes {
            return Err(Error::resource("annotation node limit exceeded"));
        }
        self.statistics.annotation_nodes += 1;
        Ok(())
    }

    /// After the comma that follows a formula: `<source>[,<useful_info>]`.
    pub(crate) fn annotation(&mut self) -> Result<Annotation, Error> {
        let start = self.offset();
        let source = self.general_term(1)?;
        let source_bytes = start..self.end();
        let useful_info = if self.accept(b',')? {
            let info_start = self.offset();
            if self.peek() != Some(&Kind::Punctuation(b'[')) {
                return Err(syntax(info_start, "useful info must be a general list"));
            }
            let GeneralTerm::List(items) = self.general_term(1)? else {
                unreachable!("a bracket starts a general list");
            };
            if self.peek() == Some(&Kind::Punctuation(b',')) {
                return Err(syntax(self.offset(), "at most two annotation fields"));
            }
            Some((items, info_start..self.end()))
        } else {
            None
        };
        Ok(Annotation {
            bytes: start..self.end(),
            class: classify(&source),
            source,
            source_bytes,
            useful_info,
        })
    }

    fn general_terms(&mut self, close: u8, depth: usize) -> Result<Vec<GeneralTerm>, Error> {
        let mut items = vec![self.general_term(depth)?];
        while self.accept(b',')? {
            items.push(self.general_term(depth)?);
        }
        self.punctuation(close)?;
        Ok(items)
    }

    fn general_term(&mut self, depth: usize) -> Result<GeneralTerm, Error> {
        self.count_annotation(depth)?;
        if self.accept(b'[')? {
            if self.accept(b']')? {
                return Ok(GeneralTerm::List(Vec::new()));
            }
            return self.general_terms(b']', depth + 1).map(GeneralTerm::List);
        }
        let data = self.general_data(depth)?;
        if self.accept(b':')? {
            let right = self.general_term(depth + 1)?;
            return Ok(GeneralTerm::Colon(Box::new(data), Box::new(right)));
        }
        Ok(data)
    }

    fn general_data(&mut self, depth: usize) -> Result<GeneralTerm, Error> {
        let offset = self.offset();
        let Some(kind) = self.peek().cloned() else {
            return Err(syntax(offset, "expected general data"));
        };
        self.advance()?;
        Ok(match kind {
            Kind::Lower(word) | Kind::Quoted(word) => {
                if self.accept(b'(')? {
                    GeneralTerm::Function(word, self.general_terms(b')', depth + 1)?)
                } else {
                    GeneralTerm::Word(word)
                }
            }
            Kind::Variable(name) => GeneralTerm::Variable(name),
            Kind::IntegerName(value) => GeneralTerm::Integer(value),
            Kind::Number(value) => GeneralTerm::Number(value),
            Kind::Distinct(value, _) => GeneralTerm::Distinct(value),
            Kind::Defined(language)
                if FORMULA_DATA.contains(&language.as_str())
                    && self.peek() == Some(&Kind::Punctuation(b'(')) =>
            {
                let bytes = self.balanced(depth)?;
                GeneralTerm::FormulaData { language, bytes }
            }
            _ => return Err(syntax(offset, "expected general data")),
        })
    }

    /// Skip one bracket-balanced group starting at `(`; return its byte span.
    fn balanced(&mut self, depth: usize) -> Result<Range<usize>, Error> {
        let start = self.offset();
        let mut open = Vec::new();
        loop {
            let offset = self.offset();
            let Some(kind) = self.peek().cloned() else {
                return Err(syntax(offset, "unbalanced formula data"));
            };
            self.advance()?;
            self.count_annotation(depth)?;
            match kind {
                Kind::Punctuation(b'(') => open.push(b')'),
                Kind::Punctuation(b'[') => open.push(b']'),
                Kind::Punctuation(close @ (b')' | b']')) => {
                    if open.pop() != Some(close) {
                        return Err(syntax(offset, "unbalanced formula data"));
                    }
                    if open.is_empty() {
                        return Ok(start..self.end());
                    }
                }
                _ => {}
            }
            if open.len() > 64 {
                return Err(Error::resource("annotation depth limit exceeded"));
            }
        }
    }
}
