// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use std::path::PathBuf;

use fang_supervisor::Failure;

/// The exceptions the Python checks raise, with `str(error)` as Display.
#[derive(Debug)]
pub enum Error {
    /// ValueError (and the RuntimeErrors of the scripts): the message.
    Value(String),
    /// OSError, with the file it names when Python's does.
    Os(std::io::Error, Option<PathBuf>),
    /// KeyError: Python prints the quoted key.
    Key(String),
    /// A Failure raised by the caller's check.
    Failure(Failure),
}

impl Error {
    pub fn value(message: impl Into<String>) -> Error {
        Error::Value(message.into())
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Value(message) => formatter.write_str(message),
            Error::Key(key) => formatter.write_str(&fang_json::python_repr_str(key)),
            Error::Failure(failure) => formatter.write_str(&failure.reason),
            Error::Os(error, path) => {
                let text = error.to_string();
                match error.raw_os_error() {
                    Some(code) => {
                        let strerror = text
                            .strip_suffix(&format!(" (os error {code})"))
                            .unwrap_or(&text);
                        match path {
                            Some(path) => write!(
                                formatter,
                                "[Errno {code}] {strerror}: {}",
                                fang_json::python_repr_str(&path.to_string_lossy())
                            ),
                            None => write!(formatter, "[Errno {code}] {strerror}"),
                        }
                    }
                    None => formatter.write_str(&text),
                }
            }
        }
    }
}

impl std::error::Error for Error {}

impl From<Failure> for Error {
    fn from(failure: Failure) -> Error {
        Error::Failure(failure)
    }
}
