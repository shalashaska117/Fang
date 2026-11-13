// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The TOML subset of Cargo.toml, Cargo.lock and rust-toolchain.toml, read into the value
//! Python's `tomllib.loads` gives, as `fang_json::Value`.
//!
//! Supported: tables, arrays of tables, bare, quoted and dotted keys, basic and literal
//! strings (single and multi-line, every TOML 1.0 escape), integers (decimal, hexadecimal,
//! octal, binary, with underscores), booleans, arrays and inline tables, and comments.
//! Refused: floats, dates and times, which no manifest or lockfile uses. A key defined
//! twice, a table defined twice, a header over a table made by dotted keys and an
//! extension of an inline table, an array or a value are errors, as in tomllib.
#![forbid(unsafe_code)]

use std::collections::HashSet;

use fang_json::{Integer, Object, Value};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TomlError {
    pub line: usize,
    pub message: String,
}

impl std::fmt::Display for TomlError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{} (at line {})", self.message, self.line)
    }
}

impl std::error::Error for TomlError {}

/// A path of keys in which every array of tables is followed by "#index" of its last element.
type Path = Vec<String>;

struct Parser<'a> {
    text: &'a str,
    position: usize,
    root: Object,
    /// Tables defined by a [header].
    headers: HashSet<Path>,
    /// Tables created by dotted keys; no header may define them later.
    dotted: HashSet<Path>,
    /// Keys holding a value (plain, array or inline table); none may be extended.
    frozen: HashSet<Path>,
    /// Arrays created by [[header]]s.
    table_arrays: HashSet<Path>,
}

/// Parse a TOML document into the value `tomllib.loads` gives.
pub fn parse(text: &str) -> Result<Value, TomlError> {
    let mut parser = Parser {
        text,
        position: 0,
        root: Object::new(),
        headers: HashSet::new(),
        dotted: HashSet::new(),
        frozen: HashSet::new(),
        table_arrays: HashSet::new(),
    };
    parser.document()?;
    Ok(Value::Object(parser.root))
}

fn is_bare(character: char) -> bool {
    character.is_ascii_alphanumeric() || character == '_' || character == '-'
}

fn line_of(text: &str, at: usize) -> usize {
    text[..at.min(text.len())].matches('\n').count() + 1
}

fn illegal(character: char, newline_allowed: bool) -> bool {
    (character < ' ' && character != '\t' && !(newline_allowed && character == '\n'))
        || character == '\u{7f}'
}

impl<'a> Parser<'a> {
    fn failure(&self, at: usize, message: impl Into<String>) -> TomlError {
        TomlError {
            line: line_of(self.text, at),
            message: message.into(),
        }
    }

    fn error<T>(&self, message: impl Into<String>) -> Result<T, TomlError> {
        Err(self.failure(self.position, message))
    }

    fn peek(&self) -> Option<char> {
        self.text[self.position..].chars().next()
    }

    fn peek_at(&self, offset: usize) -> Option<char> {
        self.text[self.position..].chars().nth(offset)
    }

    fn rest(&self) -> &'a str {
        &self.text[self.position..]
    }

    fn bump(&mut self) -> Option<char> {
        let character = self.peek()?;
        self.position += character.len_utf8();
        Some(character)
    }

    fn skip_spaces(&mut self) {
        while matches!(self.peek(), Some(' ' | '\t')) {
            self.position += 1;
        }
    }

    fn skip_comment(&mut self) -> Result<(), TomlError> {
        if self.peek() == Some('#') {
            while let Some(character) = self.peek() {
                if character == '\n' || self.rest().starts_with("\r\n") {
                    break;
                }
                if illegal(character, false) {
                    return self.error("Illegal character in a comment");
                }
                self.position += character.len_utf8();
            }
        }
        Ok(())
    }

    fn newline(&mut self) -> bool {
        if self.rest().starts_with("\r\n") {
            self.position += 2;
            true
        } else if self.peek() == Some('\n') {
            self.position += 1;
            true
        } else {
            false
        }
    }

    /// Spaces, a comment, then a newline or the end of the document.
    fn end_of_line(&mut self) -> Result<(), TomlError> {
        self.skip_spaces();
        self.skip_comment()?;
        if !self.newline() && self.peek().is_some() {
            return self.error("Expected newline or end of document after a statement");
        }
        Ok(())
    }

    /// Whitespace, newlines and comments, as allowed between array items.
    fn skip_blank(&mut self) -> Result<(), TomlError> {
        loop {
            self.skip_spaces();
            self.skip_comment()?;
            if !self.newline() {
                return Ok(());
            }
        }
    }

    fn document(&mut self) -> Result<(), TomlError> {
        let mut section: Path = Vec::new();
        loop {
            self.skip_spaces();
            match self.peek() {
                None => return Ok(()),
                Some('#') => self.end_of_line()?,
                Some('\n' | '\r') => {
                    if !self.newline() {
                        return self.error("Illegal carriage return");
                    }
                }
                Some('[') => {
                    section = self.header()?;
                    self.end_of_line()?;
                }
                Some(_) => {
                    self.key_value(&section)?;
                    self.end_of_line()?;
                }
            }
        }
    }

    /// The path of `key`: every array of tables among its parents is followed by the index of its last element.
    fn path_of(&self, key: &[String]) -> Path {
        let mut path = Vec::new();
        let mut table = Some(&self.root);
        for (index, name) in key.iter().enumerate() {
            path.push(name.clone());
            if index + 1 == key.len() {
                break;
            }
            table = match table.and_then(|table| table.get(name)) {
                Some(Value::Object(inner)) => Some(inner),
                Some(Value::Array(items)) if self.table_arrays.contains(&path) => {
                    path.push(format!("#{}", items.len() - 1));
                    items.last().and_then(Value::as_object)
                }
                _ => None,
            };
        }
        path
    }

    /// The table at `key`, creating missing tables. Values, arrays and inline tables cannot be entered.
    fn walk(&mut self, key: &[String]) -> Result<&mut Object, TomlError> {
        for length in 1..=key.len() {
            let path = self.path_of(&key[..length]);
            if self.frozen.contains(&path) {
                return self.error("Cannot extend an inline table, an array or a value");
            }
        }
        let line = line_of(self.text, self.position);
        let table_arrays = &self.table_arrays;
        let mut path: Path = Vec::new();
        let mut table: &mut Object = &mut self.root;
        for name in key {
            path.push(name.clone());
            if !table.contains_key(name) {
                table.set(name.clone(), Value::Object(Object::new()));
            }
            let is_table_array = table_arrays.contains(&path);
            table = match table.get_mut(name) {
                Some(Value::Object(inner)) => inner,
                Some(Value::Array(items)) if is_table_array => {
                    path.push(format!("#{}", items.len() - 1));
                    match items.last_mut() {
                        Some(Value::Object(inner)) => inner,
                        _ => {
                            return Err(TomlError {
                                line,
                                message: "Malformed array of tables".into(),
                            });
                        }
                    }
                }
                _ => {
                    return Err(TomlError {
                        line,
                        message: "Cannot extend a value that is not a table".into(),
                    });
                }
            };
        }
        Ok(table)
    }

    fn header(&mut self) -> Result<Path, TomlError> {
        let start = self.position;
        let array = self.rest().starts_with("[[");
        self.position += if array { 2 } else { 1 };
        self.skip_spaces();
        let key = self.key()?;
        self.skip_spaces();
        let closing = if array { "]]" } else { "]" };
        if !self.rest().starts_with(closing) {
            return self.error("Expected ']' at the end of a table header");
        }
        self.position += closing.len();
        let path = self.path_of(&key);
        let fail = |parser: &Parser<'_>, message: &str| Err(parser.failure(start, message));
        if self.frozen.contains(&path) || self.dotted.contains(&path) {
            return fail(self, "Cannot redefine a value or a namespace");
        }
        let (parent, last) = key.split_at(key.len() - 1);
        let name = last[0].clone();
        if array {
            let exists = self.table_arrays.contains(&path);
            let table = self.walk(parent)?;
            let appended = match table.get_mut(&name) {
                None => {
                    table.set(name, Value::Array(vec![Value::Object(Object::new())]));
                    true
                }
                Some(Value::Array(items)) if exists => {
                    items.push(Value::Object(Object::new()));
                    true
                }
                Some(_) => false,
            };
            if !appended {
                return fail(self, "Cannot append to a table, a value or a static array");
            }
            self.table_arrays.insert(path);
        } else {
            if self.headers.contains(&path) || self.table_arrays.contains(&path) {
                return fail(self, "Cannot declare a table twice");
            }
            self.walk(&key)?;
            self.headers.insert(path);
        }
        Ok(key)
    }

    fn key(&mut self) -> Result<Path, TomlError> {
        let mut parts = Vec::new();
        loop {
            self.skip_spaces();
            let part = match self.peek() {
                Some('"') if !self.rest().starts_with("\"\"\"") => self.basic_string()?,
                Some('\'') if !self.rest().starts_with("'''") => self.literal_string()?,
                Some(character) if is_bare(character) => {
                    let start = self.position;
                    while self.peek().is_some_and(is_bare) {
                        self.position += 1;
                    }
                    self.text[start..self.position].to_owned()
                }
                _ => return self.error("Invalid key"),
            };
            parts.push(part);
            self.skip_spaces();
            if self.peek() == Some('.') {
                self.position += 1;
            } else {
                return Ok(parts);
            }
        }
    }

    fn key_value(&mut self, section: &Path) -> Result<(), TomlError> {
        let start = self.position;
        let key = self.key()?;
        self.skip_spaces();
        if self.bump() != Some('=') {
            return self.error("Expected '=' after a key");
        }
        self.skip_spaces();
        let value = self.value()?;
        let mut full = section.clone();
        full.extend(key.iter().cloned());
        for length in section.len() + 1..full.len() {
            let path = self.path_of(&full[..length]);
            if self.headers.contains(&path) || self.table_arrays.contains(&path) {
                return Err(self.failure(
                    start,
                    "Cannot extend a table defined by a header with dotted keys",
                ));
            }
            self.dotted.insert(path);
        }
        let path = self.path_of(&full);
        let (parent, last) = full.split_at(full.len() - 1);
        let table = self.walk(parent)?;
        let exists = table.contains_key(&last[0]);
        if !exists {
            table.set(last[0].clone(), value);
        }
        if exists {
            return Err(self.failure(start, "Cannot overwrite a value"));
        }
        self.frozen.insert(path);
        Ok(())
    }

    fn value(&mut self) -> Result<Value, TomlError> {
        match self.peek() {
            Some('"') if self.rest().starts_with("\"\"\"") => {
                Ok(Value::String(self.multiline_basic_string()?))
            }
            Some('"') => Ok(Value::String(self.basic_string()?)),
            Some('\'') if self.rest().starts_with("'''") => {
                Ok(Value::String(self.multiline_literal_string()?))
            }
            Some('\'') => Ok(Value::String(self.literal_string()?)),
            Some('[') => self.array(),
            Some('{') => self.inline_table(),
            Some('t') if self.rest().starts_with("true") => {
                self.position += 4;
                Ok(Value::Bool(true))
            }
            Some('f') if self.rest().starts_with("false") => {
                self.position += 5;
                Ok(Value::Bool(false))
            }
            Some(_) => self.integer(),
            None => self.error("Expected a value"),
        }
    }

    fn integer(&mut self) -> Result<Value, TomlError> {
        let start = self.position;
        while self.peek().is_some_and(|character| {
            character.is_ascii_alphanumeric() || matches!(character, '_' | '+' | '-' | '.' | ':')
        }) {
            self.position += 1;
        }
        let token = &self.text[start..self.position];
        let invalid = || {
            Err(self.failure(
                start,
                format!("Invalid value (floats, dates and times are not read): {token}"),
            ))
        };
        if token.is_empty() {
            return invalid();
        }
        let (negative, unsigned) = match token.as_bytes()[0] {
            b'+' => (false, &token[1..]),
            b'-' => (true, &token[1..]),
            _ => (false, token),
        };
        let (radix, digits) = if let Some(rest) = token.strip_prefix("0x") {
            (16, rest)
        } else if let Some(rest) = token.strip_prefix("0o") {
            (8, rest)
        } else if let Some(rest) = token.strip_prefix("0b") {
            (2, rest)
        } else {
            (10, unsigned)
        };
        if digits.is_empty()
            || digits.starts_with('_')
            || digits.ends_with('_')
            || digits.contains("__")
        {
            return invalid();
        }
        if radix == 10 && digits.len() > 1 && digits.starts_with('0') {
            return invalid();
        }
        let mut magnitude: u128 = 0;
        for character in digits.chars().filter(|character| *character != '_') {
            let Some(digit) = character.to_digit(radix) else {
                return invalid();
            };
            match magnitude
                .checked_mul(u128::from(radix))
                .and_then(|value| value.checked_add(u128::from(digit)))
            {
                Some(value) => magnitude = value,
                None => return invalid(),
            }
        }
        Ok(Value::from(Integer::new(
            negative && radix == 10,
            magnitude,
        )))
    }

    fn array(&mut self) -> Result<Value, TomlError> {
        self.position += 1;
        let mut items = Vec::new();
        loop {
            self.skip_blank()?;
            if self.peek() == Some(']') {
                self.position += 1;
                return Ok(Value::Array(items));
            }
            items.push(self.value()?);
            self.skip_blank()?;
            match self.bump() {
                Some(',') => {}
                Some(']') => return Ok(Value::Array(items)),
                _ => return self.error("Unclosed array"),
            }
        }
    }

    fn inline_table(&mut self) -> Result<Value, TomlError> {
        self.position += 1;
        let mut table = Object::new();
        let mut made: HashSet<Path> = HashSet::new();
        self.skip_spaces();
        if self.peek() == Some('}') {
            self.position += 1;
            return Ok(Value::Object(table));
        }
        loop {
            let key = self.key()?;
            self.skip_spaces();
            if self.bump() != Some('=') {
                return self.error("Expected '=' after a key in an inline table");
            }
            self.skip_spaces();
            let value = self.value()?;
            let mut inner = &mut table;
            for (index, name) in key[..key.len() - 1].iter().enumerate() {
                let prefix: Path = key[..=index].to_vec();
                if !inner.contains_key(name) {
                    inner.set(name.clone(), Value::Object(Object::new()));
                    made.insert(prefix);
                } else if !made.contains(&prefix) {
                    return self.error("Cannot extend a value in an inline table");
                }
                inner = match inner.get_mut(name) {
                    Some(Value::Object(object)) => object,
                    _ => return self.error("Cannot extend a value in an inline table"),
                };
            }
            let name = key[key.len() - 1].clone();
            if inner.contains_key(&name) {
                return self.error("Duplicate key in an inline table");
            }
            inner.set(name, value);
            self.skip_spaces();
            match self.bump() {
                Some(',') => self.skip_spaces(),
                Some('}') => return Ok(Value::Object(table)),
                _ => return self.error("Unclosed inline table"),
            }
        }
    }

    fn escape(&mut self) -> Result<char, TomlError> {
        let character = match self.bump() {
            Some('b') => '\u{8}',
            Some('t') => '\t',
            Some('n') => '\n',
            Some('f') => '\u{c}',
            Some('r') => '\r',
            Some('"') => '"',
            Some('\\') => '\\',
            Some('u') => return self.unicode(4),
            Some('U') => return self.unicode(8),
            _ => return self.error("Unescaped '\\' in a string"),
        };
        Ok(character)
    }

    fn unicode(&mut self, length: usize) -> Result<char, TomlError> {
        let digits = self.rest().get(..length).unwrap_or("");
        if digits.len() != length
            || !digits
                .chars()
                .all(|character| character.is_ascii_hexdigit())
        {
            return self.error("Invalid hex value in a unicode escape");
        }
        self.position += length;
        match u32::from_str_radix(digits, 16)
            .ok()
            .and_then(char::from_u32)
        {
            Some(character) => Ok(character),
            None => self.error("Escaped character is not a Unicode scalar value"),
        }
    }

    fn basic_string(&mut self) -> Result<String, TomlError> {
        self.position += 1;
        let mut output = String::new();
        loop {
            match self.bump() {
                None => return self.error("Unterminated string"),
                Some('"') => return Ok(output),
                Some('\\') => output.push(self.escape()?),
                Some(character) if illegal(character, false) => {
                    return self.error("Illegal character in a string");
                }
                Some(character) => output.push(character),
            }
        }
    }

    fn literal_string(&mut self) -> Result<String, TomlError> {
        self.position += 1;
        let start = self.position;
        loop {
            match self.bump() {
                None => return self.error("Unterminated string"),
                Some('\'') => return Ok(self.text[start..self.position - 1].to_owned()),
                Some(character) if illegal(character, false) => {
                    return self.error("Illegal character in a string");
                }
                Some(_) => {}
            }
        }
    }

    /// Up to two more quotes may end the content; returns their count after the closing three.
    fn closing_quotes(&self, quote: char) -> usize {
        let mut count = 0;
        while count < 2 && self.peek_at(3 + count) == Some(quote) {
            count += 1;
        }
        count
    }

    fn multiline_basic_string(&mut self) -> Result<String, TomlError> {
        self.position += 3;
        self.newline();
        let mut output = String::new();
        loop {
            if self.rest().starts_with("\"\"\"") {
                let extra = self.closing_quotes('"');
                output.extend(std::iter::repeat_n('"', extra));
                self.position += 3 + extra;
                return Ok(output);
            }
            match self.bump() {
                None => return self.error("Unterminated string"),
                Some('\\') => {
                    // A backslash at the end of a line trims every space and newline that follows.
                    let saved = self.position;
                    self.skip_spaces();
                    if self.newline() {
                        loop {
                            self.skip_spaces();
                            if !self.newline() {
                                break;
                            }
                        }
                    } else {
                        self.position = saved;
                        output.push(self.escape()?);
                    }
                }
                Some('\r') if self.peek() == Some('\n') => {
                    self.position += 1;
                    output.push('\n');
                }
                Some(character) if illegal(character, true) => {
                    return self.error("Illegal character in a string");
                }
                Some(character) => output.push(character),
            }
        }
    }

    fn multiline_literal_string(&mut self) -> Result<String, TomlError> {
        self.position += 3;
        self.newline();
        let mut output = String::new();
        loop {
            if self.rest().starts_with("'''") {
                let extra = self.closing_quotes('\'');
                output.extend(std::iter::repeat_n('\'', extra));
                self.position += 3 + extra;
                return Ok(output);
            }
            match self.bump() {
                None => return self.error("Unterminated string"),
                Some('\r') if self.peek() == Some('\n') => {
                    self.position += 1;
                    output.push('\n');
                }
                Some(character) if illegal(character, true) => {
                    return self.error("Illegal character in a string");
                }
                Some(character) => output.push(character),
            }
        }
    }
}
