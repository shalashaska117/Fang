// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Loading a configuration file: the older profiles' installation and capability files, and any other pinned
//! JSON record a profile reads before it runs.

use std::path::Path;

use fang_json::Value;
use fang_supervisor::Fault;

use crate::capability::Record;

/// A loaded configuration file: its JSON value and the SHA-256 of its bytes.
#[derive(Clone, Debug)]
pub struct Loaded {
    pub value: Value,
    pub sha256: String,
}

/// Read at most `byte_limit` bytes of the regular file at `path`, parse it as strict JSON (duplicate keys and
/// non-finite numbers refused) and, when `pin` is given, require its SHA-256 to equal the pin. A changed pin is
/// a `Fault::Value`; the schema of the value is the caller's to check.
pub fn load(path: &Path, byte_limit: u64, pin: Option<&Record>) -> Result<Loaded, Fault> {
    let mut check = || -> Result<(), fang_supervisor::Failure> { Ok(()) };
    let bytes = fang_supervisor::read_regular(path, byte_limit, &mut check)?;
    let sha256 = fang_hash::sha256_hex(&bytes);
    if let Some(record) = pin
        && record.sha256 != sha256
    {
        return Err(Fault::Value(format!(
            "Pinned configuration file changed: {}",
            path.display()
        )));
    }
    let value = fang_supervisor::strict_json(&bytes)?;
    Ok(Loaded { value, sha256 })
}
