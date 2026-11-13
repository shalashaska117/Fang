// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The strict reader. Its control flow follows CPython's C scanner (Modules/_json.c):
//! the same token rules, the same error kinds at the same positions. The refusals Python
//! does not have are marked below. It keeps an explicit stack instead of recursing.

use crate::value::{Integer, Number, Object, Value};

#[derive(Clone, Copy, Debug)]
pub struct ParseLimits {
    pub max_bytes: usize,
    pub max_depth: usize,
}

impl Default for ParseLimits {
    fn default() -> ParseLimits {
        ParseLimits {
            max_bytes: 256 << 20,
            max_depth: 512,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    // Python's JSONDecodeError messages, positioned.
    ExpectingValue,
    ExpectingPropertyName,
    ExpectingColon,
    ExpectingComma,
    TrailingCommaObject,
    TrailingCommaArray,
    UnterminatedString,
    InvalidControlCharacter,
    InvalidEscape,
    InvalidUnicodeEscape,
    ExtraData,
    UnexpectedBom,
    // The two refusals of supervisor.strict_json, Python's texts, unpositioned.
    DuplicateKey,
    Nonfinite,
    // Refusals Python does not have.
    TooLarge,
    InvalidUtf8,
    TooDeep,
    IntegerOutOfRange,
    FloatOutOfRange,
    LoneSurrogate,
}

impl ErrorKind {
    pub fn message(self) -> &'static str {
        match self {
            ErrorKind::ExpectingValue => "Expecting value",
            ErrorKind::ExpectingPropertyName => "Expecting property name enclosed in double quotes",
            ErrorKind::ExpectingColon => "Expecting ':' delimiter",
            ErrorKind::ExpectingComma => "Expecting ',' delimiter",
            ErrorKind::TrailingCommaObject => "Illegal trailing comma before end of object",
            ErrorKind::TrailingCommaArray => "Illegal trailing comma before end of array",
            ErrorKind::UnterminatedString => "Unterminated string starting at",
            ErrorKind::InvalidControlCharacter => "Invalid control character at",
            ErrorKind::InvalidEscape => "Invalid \\escape",
            ErrorKind::InvalidUnicodeEscape => "Invalid \\uXXXX escape",
            ErrorKind::ExtraData => "Extra data",
            ErrorKind::UnexpectedBom => "Unexpected UTF-8 BOM (decode using utf-8-sig)",
            ErrorKind::DuplicateKey => "Duplicate JSON field",
            ErrorKind::Nonfinite => "Nonfinite JSON number",
            ErrorKind::TooLarge => "JSON input above its byte limit",
            ErrorKind::InvalidUtf8 => "JSON input is not UTF-8",
            ErrorKind::TooDeep => "JSON nesting above its depth limit",
            ErrorKind::IntegerOutOfRange => "JSON integer out of range",
            ErrorKind::FloatOutOfRange => "Nonfinite JSON number",
            ErrorKind::LoneSurrogate => "Lone surrogate in a JSON string",
        }
    }

    fn positioned(self) -> bool {
        !matches!(
            self,
            ErrorKind::DuplicateKey
                | ErrorKind::Nonfinite
                | ErrorKind::TooLarge
                | ErrorKind::InvalidUtf8
                | ErrorKind::FloatOutOfRange
        )
    }
}

/// An error with the byte offset where it was found.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JsonError {
    pub kind: ErrorKind,
    pub offset: usize,
}

impl JsonError {
    /// The text Python gives: `msg: line L column C (char P)`, positions counted in characters.
    /// Unpositioned refusals give the bare message.
    pub fn python_message(&self, text: &[u8]) -> String {
        if !self.kind.positioned() {
            return self.kind.message().to_owned();
        }
        let prefix = &text[..self.offset.min(text.len())];
        let prefix = std::str::from_utf8(prefix).unwrap_or_else(|error| {
            std::str::from_utf8(&prefix[..error.valid_up_to()]).unwrap_or("")
        });
        let position = prefix.chars().count();
        let line = prefix.matches('\n').count() + 1;
        let column = match prefix.rfind('\n') {
            Some(newline) => prefix[newline + 1..].chars().count() + 1,
            None => position + 1,
        };
        format!(
            "{}: line {} column {} (char {})",
            self.kind.message(),
            line,
            column,
            position
        )
    }
}

impl std::fmt::Display for JsonError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{} (byte {})", self.kind.message(), self.offset)
    }
}

impl std::error::Error for JsonError {}

fn error<T>(kind: ErrorKind, offset: usize) -> Result<T, JsonError> {
    Err(JsonError { kind, offset })
}

enum Frame {
    Array(Vec<Value>),
    Object {
        object: Object,
        key: Option<String>,
        duplicate: bool,
    },
}

struct Scanner<'a> {
    text: &'a str,
    bytes: &'a [u8],
}

impl<'a> Scanner<'a> {
    fn byte(&self, index: usize) -> Option<u8> {
        self.bytes.get(index).copied()
    }

    fn skip_whitespace(&self, mut index: usize) -> usize {
        while matches!(self.byte(index), Some(b' ' | b'\t' | b'\n' | b'\r')) {
            index += 1;
        }
        index
    }

    fn starts_with(&self, index: usize, word: &[u8]) -> bool {
        self.bytes.get(index..index + word.len()) == Some(word)
    }

    /// scanstring_unicode: `start` is just after the opening quote.
    fn string(&self, start: usize) -> Result<(String, usize), JsonError> {
        let begin = start - 1;
        let mut output = String::new();
        let mut end = start;
        loop {
            let mut next = end;
            let mut found = None;
            while next < self.bytes.len() {
                let byte = self.bytes[next];
                if byte == b'"' || byte == b'\\' {
                    found = Some(byte);
                    break;
                }
                if byte <= 0x1f {
                    return error(ErrorKind::InvalidControlCharacter, next);
                }
                next += 1;
            }
            let Some(terminator) = found else {
                return error(ErrorKind::UnterminatedString, begin);
            };
            output.push_str(&self.text[end..next]);
            next += 1;
            if terminator == b'"' {
                return Ok((output, next));
            }
            let Some(escape) = self.byte(next) else {
                return error(ErrorKind::UnterminatedString, begin);
            };
            if escape != b'u' {
                end = next + 1;
                let character = match escape {
                    b'"' => '"',
                    b'\\' => '\\',
                    b'/' => '/',
                    b'b' => '\u{8}',
                    b'f' => '\u{c}',
                    b'n' => '\n',
                    b'r' => '\r',
                    b't' => '\t',
                    _ => return error(ErrorKind::InvalidEscape, end - 2),
                };
                output.push(character);
                continue;
            }
            // \uXXXX
            let backslash = next - 1;
            next += 1;
            end = next + 4;
            if end >= self.bytes.len() {
                return error(ErrorKind::InvalidUnicodeEscape, next - 1);
            }
            let mut code = self.hex4(next).ok_or(JsonError {
                kind: ErrorKind::InvalidUnicodeEscape,
                offset: end - 5,
            })?;
            if (0xd800..0xdc00).contains(&code)
                && end + 6 < self.bytes.len()
                && self.bytes[end] == b'\\'
                && self.bytes[end + 1] == b'u'
            {
                let second = self.hex4(end + 2).ok_or(JsonError {
                    kind: ErrorKind::InvalidUnicodeEscape,
                    offset: end + 1,
                })?;
                if (0xdc00..0xe000).contains(&second) {
                    code = 0x10000 + ((code - 0xd800) << 10) + (second - 0xdc00);
                    end += 6;
                }
            }
            // Python keeps a lone surrogate in the string; this reader refuses it.
            let Some(character) = char::from_u32(code) else {
                return error(ErrorKind::LoneSurrogate, backslash);
            };
            output.push(character);
        }
    }

    fn hex4(&self, start: usize) -> Option<u32> {
        let mut code = 0u32;
        for index in start..start + 4 {
            let digit = match self.bytes[index] {
                byte @ b'0'..=b'9' => byte - b'0',
                byte @ b'a'..=b'f' => byte - b'a' + 10,
                byte @ b'A'..=b'F' => byte - b'A' + 10,
                _ => return None,
            };
            code = code << 4 | u32::from(digit);
        }
        Some(code)
    }

    /// _match_number_unicode. `None` means no number starts here (Python's StopIteration).
    fn number(&self, start: usize) -> Result<Option<(Number, usize)>, JsonError> {
        let last = self.bytes.len().wrapping_sub(1);
        let digit = |index: usize| self.byte(index).is_some_and(|byte| byte.is_ascii_digit());
        let mut index = start;
        if self.byte(index) == Some(b'-') {
            index += 1;
            if index > last || self.bytes.is_empty() {
                return Ok(None);
            }
        }
        match self.byte(index) {
            Some(b'1'..=b'9') => {
                index += 1;
                while digit(index) {
                    index += 1;
                }
            }
            Some(b'0') => index += 1,
            _ => return Ok(None),
        }
        let mut float = false;
        if index < last && self.byte(index) == Some(b'.') && digit(index + 1) {
            float = true;
            index += 2;
            while digit(index) {
                index += 1;
            }
        }
        if index < last && matches!(self.byte(index), Some(b'e' | b'E')) {
            let exponent_start = index;
            index += 1;
            if index < last && matches!(self.byte(index), Some(b'-' | b'+')) {
                index += 1;
            }
            while digit(index) {
                index += 1;
            }
            if digit(index - 1) {
                float = true;
            } else {
                index = exponent_start;
            }
        }
        let token = &self.text[start..index];
        if float {
            let value: f64 = token.parse().map_err(|_| JsonError {
                kind: ErrorKind::ExpectingValue,
                offset: start,
            })?;
            if !value.is_finite() {
                return error(ErrorKind::FloatOutOfRange, start);
            }
            return Ok(Some((Number::Float(value), index)));
        }
        let (negative, digits) = match token.strip_prefix('-') {
            Some(digits) => (true, digits),
            None => (false, token),
        };
        let mut magnitude: u128 = 0;
        for byte in digits.bytes() {
            magnitude = magnitude
                .checked_mul(10)
                .and_then(|value| value.checked_add(u128::from(byte - b'0')))
                .ok_or(JsonError {
                    kind: ErrorKind::IntegerOutOfRange,
                    offset: start,
                })?;
        }
        Ok(Some((
            Number::Integer(Integer::new(negative, magnitude)),
            index,
        )))
    }
}

/// Parse one JSON document. Errors carry Python's message through `JsonError::python_message`.
pub fn parse(bytes: &[u8], limits: &ParseLimits) -> Result<Value, JsonError> {
    if bytes.len() > limits.max_bytes {
        return error(ErrorKind::TooLarge, limits.max_bytes);
    }
    let text = std::str::from_utf8(bytes).map_err(|failure| JsonError {
        kind: ErrorKind::InvalidUtf8,
        offset: failure.valid_up_to(),
    })?;
    if text.starts_with('\u{feff}') {
        return error(ErrorKind::UnexpectedBom, 0);
    }
    let scanner = Scanner { text, bytes };
    let mut stack: Vec<Frame> = Vec::new();
    let mut position = scanner.skip_whitespace(0);
    'value: loop {
        // scan_once_unicode at `position`.
        let (mut value, mut next) = match scanner.byte(position) {
            None => return error(ErrorKind::ExpectingValue, position),
            Some(b'"') => {
                let (text, next) = scanner.string(position + 1)?;
                (Value::String(text), next)
            }
            Some(b'{') => {
                if stack.len() >= limits.max_depth {
                    return error(ErrorKind::TooDeep, position);
                }
                let index = scanner.skip_whitespace(position + 1);
                if scanner.byte(index) == Some(b'}') {
                    (Value::Object(Object::new()), index + 1)
                } else {
                    let key = object_key(&scanner, index)?;
                    position = key.1;
                    stack.push(Frame::Object {
                        object: Object::new(),
                        key: Some(key.0),
                        duplicate: false,
                    });
                    continue 'value;
                }
            }
            Some(b'[') => {
                if stack.len() >= limits.max_depth {
                    return error(ErrorKind::TooDeep, position);
                }
                let index = scanner.skip_whitespace(position + 1);
                match scanner.byte(index) {
                    Some(b']') => (Value::Array(Vec::new()), index + 1),
                    // An unterminated empty array: "Expecting value" where the input ends.
                    None => return error(ErrorKind::ExpectingValue, index),
                    Some(_) => {
                        stack.push(Frame::Array(Vec::new()));
                        position = index;
                        continue 'value;
                    }
                }
            }
            Some(b'n') if scanner.starts_with(position, b"null") => (Value::Null, position + 4),
            Some(b't') if scanner.starts_with(position, b"true") => {
                (Value::Bool(true), position + 4)
            }
            Some(b'f') if scanner.starts_with(position, b"false") => {
                (Value::Bool(false), position + 5)
            }
            Some(b'N') if scanner.starts_with(position, b"NaN") => {
                return error(ErrorKind::Nonfinite, position);
            }
            Some(b'I') if scanner.starts_with(position, b"Infinity") => {
                return error(ErrorKind::Nonfinite, position);
            }
            Some(b'-') if scanner.starts_with(position, b"-Infinity") => {
                return error(ErrorKind::Nonfinite, position);
            }
            Some(_) => match scanner.number(position)? {
                Some((number, next)) => (Value::Number(number), next),
                None => return error(ErrorKind::ExpectingValue, position),
            },
        };
        // Attach the finished value to the open containers, closing those that end here.
        loop {
            match stack.last_mut() {
                None => {
                    let end = scanner.skip_whitespace(next);
                    if end != bytes.len() {
                        return error(ErrorKind::ExtraData, end);
                    }
                    return Ok(value);
                }
                Some(Frame::Array(items)) => {
                    items.push(value);
                    let index = scanner.skip_whitespace(next);
                    match scanner.byte(index) {
                        Some(b']') => {
                            let Some(Frame::Array(items)) = stack.pop() else {
                                unreachable!()
                            };
                            value = Value::Array(items);
                            next = index + 1;
                        }
                        Some(b',') => {
                            let after = scanner.skip_whitespace(index + 1);
                            if scanner.byte(after) == Some(b']') {
                                return error(ErrorKind::TrailingCommaArray, index);
                            }
                            position = after;
                            continue 'value;
                        }
                        _ => return error(ErrorKind::ExpectingComma, index),
                    }
                }
                Some(Frame::Object {
                    object,
                    key,
                    duplicate,
                }) => {
                    let name = key.take().expect("an open object always has a pending key");
                    if let Err((name, value)) = object.insert_new(name, value) {
                        // strict_json's hook sees the pairs when the object closes; keep the
                        // first value and report the duplicate then, as Python's order of errors requires.
                        let _ = (name, value);
                        *duplicate = true;
                    }
                    let index = scanner.skip_whitespace(next);
                    match scanner.byte(index) {
                        Some(b'}') => {
                            let Some(Frame::Object {
                                object, duplicate, ..
                            }) = stack.pop()
                            else {
                                unreachable!()
                            };
                            if duplicate {
                                return error(ErrorKind::DuplicateKey, index);
                            }
                            value = Value::Object(object);
                            next = index + 1;
                        }
                        Some(b',') => {
                            let after = scanner.skip_whitespace(index + 1);
                            if scanner.byte(after) == Some(b'}') {
                                return error(ErrorKind::TrailingCommaObject, index);
                            }
                            let (name, after_key) = object_key(&scanner, after)?;
                            *key = Some(name);
                            position = after_key;
                            continue 'value;
                        }
                        _ => return error(ErrorKind::ExpectingComma, index),
                    }
                }
            }
        }
    }
}

/// A key, its colon and the whitespace after it; returns the key and the position of its value.
fn object_key(scanner: &Scanner<'_>, index: usize) -> Result<(String, usize), JsonError> {
    if scanner.byte(index) != Some(b'"') {
        return error(ErrorKind::ExpectingPropertyName, index);
    }
    let (key, after) = scanner.string(index + 1)?;
    let colon = scanner.skip_whitespace(after);
    if scanner.byte(colon) != Some(b':') {
        return error(ErrorKind::ExpectingColon, colon);
    }
    Ok((key, scanner.skip_whitespace(colon + 1)))
}
