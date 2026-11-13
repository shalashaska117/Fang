// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Python semantics for the witness values revision 7 uses before, or without, checking their
//! types.
//!
//! Where revision 7 compares a witness value with `==`, Python treats `true`, `1` and `1.0` as
//! equal; where it prints one with `str`, the spelling stays (`True`, `1.0`), and Lean then
//! refuses the module. Where it iterates or indexes a value of the wrong type, Python raises
//! TypeError or KeyError, which the entry reports as Error. These functions reproduce the three,
//! so that revision 8 writes the same bytes and refuses with the same class on every witness
//! fang-json reads.

use fang_json::{Integer, Number, Value};

use super::{Outcome, Refusal};

enum Numeric {
    Integer(Integer),
    Float(f64),
}

/// A number as Python sees it; bool is an int.
fn numeric(value: &Value) -> Option<Numeric> {
    match value {
        Value::Bool(flag) => Some(Numeric::Integer(Integer::from(u8::from(*flag)))),
        Value::Number(Number::Integer(integer)) => Some(Numeric::Integer(*integer)),
        Value::Number(Number::Float(float)) => Some(Numeric::Float(*float)),
        _ => None,
    }
}

/// int == float is exact in Python: the float must be integral and name the same integer.
fn integer_equals_float(integer: Integer, float: f64) -> bool {
    if !float.is_finite() || float.fract() != 0.0 || float.abs() >= 2f64.powi(128) {
        return false;
    }
    Integer::new(float < 0.0, float.abs() as u128) == integer
}

/// Python's `==` on JSON values: numbers by value across bool, int and float, lists in order,
/// dicts by key regardless of order.
pub(crate) fn equals(left: &Value, right: &Value) -> bool {
    match (left, right) {
        (Value::Null, Value::Null) => true,
        (Value::String(left), Value::String(right)) => left == right,
        (Value::Array(left), Value::Array(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| equals(left, right))
        }
        (Value::Object(left), Value::Object(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .all(|(key, value)| right.get(key).is_some_and(|other| equals(value, other)))
        }
        _ => match (numeric(left), numeric(right)) {
            (Some(Numeric::Integer(left)), Some(Numeric::Integer(right))) => left == right,
            (Some(Numeric::Float(left)), Some(Numeric::Float(right))) => left == right,
            (Some(Numeric::Integer(integer)), Some(Numeric::Float(float)))
            | (Some(Numeric::Float(float)), Some(Numeric::Integer(integer))) => {
                integer_equals_float(integer, float)
            }
            _ => false,
        },
    }
}

/// `str(value)`.
pub(crate) fn text(value: &Value) -> String {
    match value {
        Value::String(text) => text.clone(),
        other => repr(other),
    }
}

/// `repr(value)`. Strings follow Python's quoting; outside ASCII the printable test is
/// approximated, which can only change an error message.
pub(crate) fn repr(value: &Value) -> String {
    match value {
        Value::Null => "None".to_owned(),
        Value::Bool(true) => "True".to_owned(),
        Value::Bool(false) => "False".to_owned(),
        Value::Number(Number::Integer(integer)) => integer.to_string(),
        Value::Number(Number::Float(float)) => float_repr(*float),
        Value::String(text) => string_repr(text),
        Value::Array(items) => format!(
            "[{}]",
            items.iter().map(repr).collect::<Vec<_>>().join(", ")
        ),
        Value::Object(object) => {
            let items: Vec<String> = object
                .iter()
                .map(|(key, value)| format!("{}: {}", string_repr(key), repr(value)))
                .collect();
            format!("{{{}}}", items.join(", "))
        }
    }
}

fn float_repr(float: f64) -> String {
    match fang_json::python_float_repr(float) {
        Some(text) => text,
        None if float.is_nan() => "nan".to_owned(),
        None if float > 0.0 => "inf".to_owned(),
        None => "-inf".to_owned(),
    }
}

fn string_repr(text: &str) -> String {
    let quote = if text.contains('\'') && !text.contains('"') {
        '"'
    } else {
        '\''
    };
    let mut result = String::new();
    result.push(quote);
    for character in text.chars() {
        match character {
            '\\' => result.push_str("\\\\"),
            '\t' => result.push_str("\\t"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            _ if character == quote => {
                result.push('\\');
                result.push(character);
            }
            ' '..='~' => result.push(character),
            _ if u32::from(character) <= 0xa0 => {
                result.push_str(&format!("\\x{:02x}", u32::from(character)))
            }
            _ => result.push(character),
        }
    }
    result.push(quote);
    result
}

/// Python's name of the value's type, for TypeError messages.
pub(crate) fn type_name(value: &Value) -> &'static str {
    match value {
        Value::Null => "NoneType",
        Value::Bool(_) => "bool",
        Value::Number(Number::Integer(_)) => "int",
        Value::Number(Number::Float(_)) => "float",
        Value::String(_) => "str",
        Value::Array(_) => "list",
        Value::Object(_) => "dict",
    }
}

pub(crate) fn type_error(message: impl Into<String>) -> Refusal {
    Refusal::Error(message.into())
}

/// `KeyError(key)`; its `str` is the key's repr.
pub(crate) fn key_error(key: &Value) -> Refusal {
    Refusal::Error(repr(key))
}

/// `for item in value`: a list's items, a string's characters, a dict's keys.
pub(crate) fn iterate(value: &Value) -> Outcome<Vec<Value>> {
    match value {
        Value::Array(items) => Ok(items.clone()),
        Value::String(text) => Ok(text
            .chars()
            .map(|character| Value::String(character.to_string()))
            .collect()),
        Value::Object(object) => Ok(object
            .keys()
            .map(|key| Value::String(key.to_owned()))
            .collect()),
        other => Err(type_error(format!(
            "'{}' object is not iterable",
            type_name(other)
        ))),
    }
}

/// `value[key]` with a string key.
pub(crate) fn item<'a>(value: &'a Value, key: &str) -> Outcome<&'a Value> {
    match value {
        Value::Object(object) => object
            .get(key)
            .ok_or_else(|| key_error(&Value::String(key.to_owned()))),
        Value::String(_) => Err(type_error("string indices must be integers, not 'str'")),
        Value::Array(_) => Err(type_error(
            "list indices must be integers or slices, not str",
        )),
        other => Err(type_error(format!(
            "'{}' object is not subscriptable",
            type_name(other)
        ))),
    }
}

/// Unpacking `first, second = value`.
pub(crate) fn unpack_two(value: &Value) -> Outcome<(Value, Value)> {
    let items = iterate(value)?;
    match <[Value; 2]>::try_from(items) {
        Ok([first, second]) => Ok((first, second)),
        Err(items) if items.len() < 2 => Err(super::rejected(format!(
            "not enough values to unpack (expected 2, got {})",
            items.len()
        ))),
        Err(_) => Err(super::rejected("too many values to unpack (expected 2)")),
    }
}

/// `text.isascii() and text.isprintable()`.
pub(crate) fn printable_ascii(text: &str) -> bool {
    text.bytes().all(|byte| (0x20..=0x7e).contains(&byte))
}

/// `value == "tag"`.
pub(crate) fn is_text(value: &Value, tag: &str) -> bool {
    matches!(value, Value::String(text) if text == tag)
}
