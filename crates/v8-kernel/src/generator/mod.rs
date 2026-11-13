// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The exact-instance generator, version 4, as revision 7 ran it.
//!
//! Each module ports one Python file and keeps its structure, so that the two can be read side
//! by side:
//!
//! | module | revision 7 |
//! |---|---|
//! | `v8` | generator/generate-v8.py, and generator_name in entry/check.py |
//! | `recipe` | recipe/equality/generate-cnf.py and generate-quantified.py |
//! | `certificate` | recipe/equality/generate-certificate.py |
//! | `validate`, `emit` | recipe/mixed/generate.py |
//! | `rectify` | recipe/mixed/generate-rectify.py |
//! | `skolem` | recipe/mixed/generate-skolem.py and generate-transform.py |
//! | `split` | recipe/mixed/generate-split-transform.py and generate-split-declarations.py |
//! | `removal`, `clausifier` | recipe/mixed/generate-removal.py and generate-clausifier.py |
//!
//! Witness values are untrusted suggestions; Lean checks every equation on the sealed bytes.
//! A refusal has the class revision 7 reported: a failed check, which Python raised as a
//! ValueError, is `Rejected`; a TypeError, KeyError or IndexError on a malformed witness is
//! `Error`. `py` holds the Python semantics this needs.

mod certificate;
mod clausifier;
mod emit;
mod py;
mod recipe;
mod rectify;
mod removal;
mod skolem;
mod split;
mod v8;
mod validate;
mod witness;

pub use v8::{Generated, generate, selected_recipe};

/// Why no modules were generated, with revision 7's class.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// A construction rejection: Python raised a ValueError.
    Rejected(String),
    /// Any other exception Python raised while generating.
    Error(String),
}

impl Refusal {
    pub fn class(&self) -> &'static str {
        match self {
            Refusal::Rejected(_) => "Rejected",
            Refusal::Error(_) => "Error",
        }
    }

    pub fn message(&self) -> &str {
        match self {
            Refusal::Rejected(message) | Refusal::Error(message) => message,
        }
    }
}

pub(crate) type Outcome<T> = Result<T, Refusal>;

pub(crate) fn rejected(message: impl Into<String>) -> Refusal {
    Refusal::Rejected(message.into())
}

pub(crate) fn require(condition: bool, message: &str) -> Outcome<()> {
    if condition {
        Ok(())
    } else {
        Err(rejected(message))
    }
}

/// Generated modules in Python dict order: assigning an existing name keeps its position.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Modules {
    entries: Vec<(String, String)>,
}

impl Modules {
    pub(crate) fn new() -> Modules {
        Modules::default()
    }

    pub(crate) fn set(&mut self, name: impl Into<String>, text: String) {
        let name = name.into();
        match self
            .entries
            .iter_mut()
            .find(|(existing, _)| *existing == name)
        {
            Some(entry) => entry.1 = text,
            None => self.entries.push((name, text)),
        }
    }

    pub(crate) fn get(&self, name: &str) -> Option<&String> {
        self.entries
            .iter()
            .find(|(existing, _)| existing == name)
            .map(|(_, text)| text)
    }

    pub(crate) fn contains(&self, name: &str) -> bool {
        self.get(name).is_some()
    }

    pub(crate) fn names(&self) -> Vec<String> {
        self.entries.iter().map(|(name, _)| name.clone()).collect()
    }

    /// `dict.update`.
    pub(crate) fn update(&mut self, other: Modules) {
        for (name, text) in other.entries {
            self.set(name, text);
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&str, &str)> {
        self.entries
            .iter()
            .map(|(name, text)| (name.as_str(), text.as_str()))
    }

    pub(crate) fn into_entries(self) -> Vec<(String, String)> {
        self.entries
    }
}

/// `", ".join(items)` for anything displayable.
pub(crate) fn join<T: std::fmt::Display>(
    items: impl IntoIterator<Item = T>,
    separator: &str,
) -> String {
    let mut text = String::new();
    for (index, item) in items.into_iter().enumerate() {
        if index > 0 {
            text.push_str(separator);
        }
        text.push_str(&item.to_string());
    }
    text
}

/// `json.dumps(text)`: a JSON string with Python's default ensure_ascii escaping.
pub(crate) fn json_string(text: &str) -> Outcome<String> {
    json_dumps(&fang_json::Value::String(text.to_owned()))
}

/// `json.dumps(value)` with the default separators.
pub(crate) fn json_dumps(value: &fang_json::Value) -> Outcome<String> {
    fang_json::dumps(value, &fang_json::DumpOptions::default())
        .map_err(|error| Refusal::Error(error.0))
}

/// Python's `str` of a list of naturals: `[1, 2]`.
pub(crate) fn list_text(values: &[u64]) -> String {
    format!("[{}]", join(values, ", "))
}

/// The witness namespace check every emitter repeats: `[A-Z][A-Za-z0-9]*`.
pub(crate) fn require_namespace(namespace: &str, message: &str) -> Outcome<()> {
    let mut characters = namespace.chars();
    let first = characters
        .next()
        .is_some_and(|character| character.is_ascii_uppercase());
    require(
        first && characters.all(|character| character.is_ascii_alphanumeric()),
        message,
    )
}
