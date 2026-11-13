// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use std::collections::HashMap;
use std::fmt;

/// An exact integer of at most 128 bits of magnitude. Zero is never negative.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Integer {
    negative: bool,
    magnitude: u128,
}

impl Integer {
    pub fn new(negative: bool, magnitude: u128) -> Integer {
        Integer {
            negative: negative && magnitude != 0,
            magnitude,
        }
    }

    pub fn is_negative(&self) -> bool {
        self.negative
    }

    pub fn magnitude(&self) -> u128 {
        self.magnitude
    }

    pub fn as_u128(&self) -> Option<u128> {
        if self.negative {
            None
        } else {
            Some(self.magnitude)
        }
    }

    pub fn as_i128(&self) -> Option<i128> {
        if self.negative {
            if self.magnitude <= i128::MAX as u128 {
                Some(-(self.magnitude as i128))
            } else if self.magnitude == i128::MAX as u128 + 1 {
                Some(i128::MIN)
            } else {
                None
            }
        } else {
            i128::try_from(self.magnitude).ok()
        }
    }

    pub fn as_u64(&self) -> Option<u64> {
        self.as_u128().and_then(|value| u64::try_from(value).ok())
    }

    pub fn as_i64(&self) -> Option<i64> {
        self.as_i128().and_then(|value| i64::try_from(value).ok())
    }
}

impl fmt::Display for Integer {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.negative {
            write!(formatter, "-{}", self.magnitude)
        } else {
            write!(formatter, "{}", self.magnitude)
        }
    }
}

macro_rules! integer_from_unsigned {
    ($($kind:ty),*) => {$(
        impl From<$kind> for Integer {
            fn from(value: $kind) -> Integer {
                Integer::new(false, value as u128)
            }
        }
    )*};
}
macro_rules! integer_from_signed {
    ($($kind:ty),*) => {$(
        impl From<$kind> for Integer {
            fn from(value: $kind) -> Integer {
                Integer::new(value < 0, (value as i128).unsigned_abs())
            }
        }
    )*};
}
integer_from_unsigned!(u8, u16, u32, u64, u128, usize);
integer_from_signed!(i8, i16, i32, i64, i128, isize);

/// A JSON number. The token kind is kept: an integer token is `Integer`, a token with a
/// fraction or an exponent is `Float`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Number {
    Integer(Integer),
    Float(f64),
}

/// An object in key order: insertion order when built, document order when parsed.
/// Equality ignores the order, as Python's dict equality does.
#[derive(Clone, Debug, Default)]
pub struct Object {
    entries: Vec<(String, Value)>,
    index: HashMap<String, usize>,
}

impl Object {
    pub fn new() -> Object {
        Object::default()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn contains_key(&self, key: &str) -> bool {
        self.index.contains_key(key)
    }

    pub fn get(&self, key: &str) -> Option<&Value> {
        self.index
            .get(key)
            .map(|&position| &self.entries[position].1)
    }

    pub fn get_mut(&mut self, key: &str) -> Option<&mut Value> {
        match self.index.get(key) {
            Some(&position) => Some(&mut self.entries[position].1),
            None => None,
        }
    }

    /// Set a key as a Python dict assignment does: an existing key keeps its position.
    pub fn set(&mut self, key: impl Into<String>, value: impl Into<Value>) {
        let key = key.into();
        let value = value.into();
        match self.index.get(&key) {
            Some(&position) => self.entries[position].1 = value,
            None => {
                self.index.insert(key.clone(), self.entries.len());
                self.entries.push((key, value));
            }
        }
    }

    /// Add a key that must be new; returns the value back if the key exists.
    pub fn insert_new(&mut self, key: String, value: Value) -> Result<(), (String, Value)> {
        if self.index.contains_key(&key) {
            return Err((key, value));
        }
        self.index.insert(key.clone(), self.entries.len());
        self.entries.push((key, value));
        Ok(())
    }

    pub fn remove(&mut self, key: &str) -> Option<Value> {
        let position = self.index.remove(key)?;
        let (_, value) = self.entries.remove(position);
        for slot in self.index.values_mut() {
            if *slot > position {
                *slot -= 1;
            }
        }
        Some(value)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&str, &Value)> {
        self.entries
            .iter()
            .map(|(key, value)| (key.as_str(), value))
    }

    pub fn keys(&self) -> impl Iterator<Item = &str> {
        self.entries.iter().map(|(key, _)| key.as_str())
    }

    pub fn values(&self) -> impl Iterator<Item = &Value> {
        self.entries.iter().map(|(_, value)| value)
    }

    /// Equality that also requires the same key order.
    pub fn ordered_eq(&self, other: &Object) -> bool {
        self.entries.len() == other.entries.len()
            && self
                .entries
                .iter()
                .zip(&other.entries)
                .all(|(left, right)| left.0 == right.0 && left.1 == right.1)
    }
}

impl PartialEq for Object {
    fn eq(&self, other: &Object) -> bool {
        self.entries.len() == other.entries.len()
            && self
                .entries
                .iter()
                .all(|(key, value)| other.get(key) == Some(value))
    }
}

impl<K: Into<String>, V: Into<Value>> FromIterator<(K, V)> for Object {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(items: T) -> Object {
        let mut object = Object::new();
        for (key, value) in items {
            object.set(key, value);
        }
        object
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Null,
    Bool(bool),
    Number(Number),
    String(String),
    Array(Vec<Value>),
    Object(Object),
}

impl Value {
    pub fn as_object(&self) -> Option<&Object> {
        if let Value::Object(object) = self {
            Some(object)
        } else {
            None
        }
    }

    pub fn as_object_mut(&mut self) -> Option<&mut Object> {
        if let Value::Object(object) = self {
            Some(object)
        } else {
            None
        }
    }

    pub fn as_array(&self) -> Option<&Vec<Value>> {
        if let Value::Array(items) = self {
            Some(items)
        } else {
            None
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        if let Value::String(text) = self {
            Some(text)
        } else {
            None
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        if let Value::Bool(value) = self {
            Some(*value)
        } else {
            None
        }
    }

    pub fn as_integer(&self) -> Option<Integer> {
        if let Value::Number(Number::Integer(value)) = self {
            Some(*value)
        } else {
            None
        }
    }

    pub fn as_u64(&self) -> Option<u64> {
        self.as_integer().and_then(|value| value.as_u64())
    }

    pub fn as_i64(&self) -> Option<i64> {
        self.as_integer().and_then(|value| value.as_i64())
    }

    pub fn as_f64(&self) -> Option<f64> {
        if let Value::Number(Number::Float(value)) = self {
            Some(*value)
        } else {
            None
        }
    }

    /// `value[key]` for an object, `None` otherwise.
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.as_object().and_then(|object| object.get(key))
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Value {
        Value::Bool(value)
    }
}
impl From<f64> for Value {
    fn from(value: f64) -> Value {
        Value::Number(Number::Float(value))
    }
}
impl From<Integer> for Value {
    fn from(value: Integer) -> Value {
        Value::Number(Number::Integer(value))
    }
}
impl From<&str> for Value {
    fn from(value: &str) -> Value {
        Value::String(value.to_owned())
    }
}
impl From<String> for Value {
    fn from(value: String) -> Value {
        Value::String(value)
    }
}
impl From<Vec<Value>> for Value {
    fn from(value: Vec<Value>) -> Value {
        Value::Array(value)
    }
}
impl From<Object> for Value {
    fn from(value: Object) -> Value {
        Value::Object(value)
    }
}
impl<T: Into<Value>> From<Option<T>> for Value {
    fn from(value: Option<T>) -> Value {
        value.map_or(Value::Null, Into::into)
    }
}
macro_rules! value_from_integer {
    ($($kind:ty),*) => {$(
        impl From<$kind> for Value {
            fn from(value: $kind) -> Value {
                Value::Number(Number::Integer(Integer::from(value)))
            }
        }
    )*};
}
value_from_integer!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
);
