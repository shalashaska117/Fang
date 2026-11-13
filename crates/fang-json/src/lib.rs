// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! JSON for the Fang tools: a strict reader and a writer that reproduces Python's `json.dumps`.
//!
//! The reader follows CPython's scanner, including its error messages, with these refusals
//! added: duplicate keys at any depth, NaN and Infinity, an integer beyond the u128 range,
//! a float literal that overflows f64, a lone surrogate escape, a byte limit and a nesting
//! limit. It never recurses, so no input can exhaust the stack. Integers and floats stay
//! apart: `1` is an `Integer`, `1.0` and `1e0` are `Float`.
//!
//! The writer reproduces `json.dumps(value, indent=..., sort_keys=..., allow_nan=False)`
//! byte for byte, floats included.
#![forbid(unsafe_code)]

mod float;
mod parse;
mod python;
mod value;
mod write;

pub use float::python_float_repr;
pub use parse::{ErrorKind, JsonError, ParseLimits, parse};
pub use python::{python_repr_list, python_repr_str};
pub use value::{Integer, Number, Object, Value};
pub use write::{DumpOptions, WriteError, dumps, dumps_manifest, write_json};
