// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Python's `json.dumps(value, indent=..., sort_keys=..., allow_nan=False)` (Lib/json/encoder.py),
//! with the default `ensure_ascii=True`.

use std::io::Write as _;
use std::path::Path;

use crate::float::python_float_repr;
use crate::value::{Number, Value};

#[derive(Clone, Copy, Debug, Default)]
pub struct DumpOptions {
    /// `indent=n`; `None` writes one line with ", " and ": " between items.
    pub indent: Option<usize>,
    pub sort_keys: bool,
}

/// The only refusal of the writer: a NaN or infinite float, with Python's message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WriteError(pub String);

impl std::fmt::Display for WriteError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for WriteError {}

pub fn dumps(value: &Value, options: &DumpOptions) -> Result<String, WriteError> {
    let mut output = String::new();
    encode(value, options, 0, &mut output)?;
    Ok(output)
}

/// `json.dumps(value, indent=2, sort_keys=True, allow_nan=False)`, the manifest form.
pub fn dumps_manifest(value: &Value) -> Result<String, WriteError> {
    dumps(
        value,
        &DumpOptions {
            indent: Some(2),
            sort_keys: true,
        },
    )
}

/// supervisor.write_json: write `name.new` exclusively, then rename it over `path`.
pub fn write_json(path: &Path, value: &Value) -> std::io::Result<()> {
    let mut text = dumps_manifest(value)
        .map_err(|error| std::io::Error::new(std::io::ErrorKind::InvalidData, error))?;
    text.push('\n');
    let name = path.file_name().ok_or_else(|| {
        std::io::Error::new(std::io::ErrorKind::InvalidInput, "path has no file name")
    })?;
    let mut temporary_name = name.to_os_string();
    temporary_name.push(".new");
    let temporary = path.with_file_name(temporary_name);
    let mut stream = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)?;
    stream.write_all(text.as_bytes())?;
    drop(stream);
    std::fs::rename(&temporary, path)
}

fn newline(options: &DumpOptions, level: usize, output: &mut String) {
    if let Some(indent) = options.indent {
        output.push('\n');
        for _ in 0..indent * level {
            output.push(' ');
        }
    }
}

fn encode(
    value: &Value,
    options: &DumpOptions,
    level: usize,
    output: &mut String,
) -> Result<(), WriteError> {
    let item_separator = if options.indent.is_some() { "," } else { ", " };
    match value {
        Value::Null => output.push_str("null"),
        Value::Bool(true) => output.push_str("true"),
        Value::Bool(false) => output.push_str("false"),
        Value::Number(Number::Integer(integer)) => output.push_str(&integer.to_string()),
        Value::Number(Number::Float(float)) => match python_float_repr(*float) {
            Some(text) => output.push_str(&text),
            None => {
                let shown = if float.is_nan() {
                    "nan"
                } else if *float > 0.0 {
                    "inf"
                } else {
                    "-inf"
                };
                return Err(WriteError(format!(
                    "Out of range float values are not JSON compliant: {shown}"
                )));
            }
        },
        Value::String(text) => encode_string(text, output),
        Value::Array(items) => {
            if items.is_empty() {
                output.push_str("[]");
                return Ok(());
            }
            output.push('[');
            newline(options, level + 1, output);
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    output.push_str(item_separator);
                    newline(options, level + 1, output);
                }
                encode(item, options, level + 1, output)?;
            }
            newline(options, level, output);
            output.push(']');
        }
        Value::Object(object) => {
            if object.is_empty() {
                output.push_str("{}");
                return Ok(());
            }
            let mut entries: Vec<(&str, &Value)> = object.iter().collect();
            if options.sort_keys {
                // Code point order, which is the byte order of UTF-8.
                entries.sort_by(|left, right| left.0.cmp(right.0));
            }
            output.push('{');
            newline(options, level + 1, output);
            for (index, (key, item)) in entries.into_iter().enumerate() {
                if index > 0 {
                    output.push_str(item_separator);
                    newline(options, level + 1, output);
                }
                encode_string(key, output);
                output.push_str(": ");
                encode(item, options, level + 1, output)?;
            }
            newline(options, level, output);
            output.push('}');
        }
    }
    Ok(())
}

/// encode_basestring_ascii: every character outside ' '..='~', and '"' and '\\', is escaped;
/// non-ASCII as lowercase \uXXXX, with a surrogate pair above U+FFFF.
fn encode_string(text: &str, output: &mut String) {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let unit = |output: &mut String, code: u32| {
        output.push_str("\\u");
        for shift in [12, 8, 4, 0] {
            output.push(HEX[((code >> shift) & 15) as usize] as char);
        }
    };
    output.push('"');
    for character in text.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            '\u{8}' => output.push_str("\\b"),
            '\u{c}' => output.push_str("\\f"),
            ' '..='~' => output.push(character),
            _ => {
                let code = u32::from(character);
                if code < 0x10000 {
                    unit(output, code);
                } else {
                    let shifted = code - 0x10000;
                    unit(output, 0xd800 | (shifted >> 10));
                    unit(output, 0xdc00 | (shifted & 0x3ff));
                }
            }
        }
    }
    output.push('"');
}
