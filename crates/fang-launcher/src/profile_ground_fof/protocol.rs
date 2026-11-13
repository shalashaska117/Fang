// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The exact driver and checker contracts of the ground-FOF profile: a port of tools/fof_szs/protocol.py.
//! Its refusals are Python ValueErrors (`Fault::Value`), which the profile records at stage "adapter".

use fang_supervisor::{Fault, StageOutput};

use crate::older::contract;

pub const ACCEPTED: &[u8] =
    b"accepted-original-ground-fof (compiled checker; compiler/runtime trusted)\n";

const UNSUPPORTED: [&str; 8] = [
    "interpreted symbols are unsupported",
    "NAND and NOR are unsupported",
    "token is outside the supported CNF/ground FOF fragment",
    "$true is unsupported in CNF",
    "formula connectives are unsupported in CNF",
    "only CNF and ground FOF statements are supported",
    "only the axiom role is supported",
    "TPTP annotations are unsupported",
];

const INVALID: [&str; 14] = [
    "uppercase character in a lowercase identifier",
    "input must contain ASCII bytes only",
    "invalid character",
    "inconsistent symbol arity",
    "expected a lowercase identifier",
    "expected a term",
    "free variables are invalid in ground FOF",
    "expected a ground formula",
    "duplicate statement name",
    "only CNF and ground FOF statements are supported",
    "expected '('",
    "expected ')'",
    "expected ','",
    "expected '.'",
];

/// `normal_exit`: the exit code of a normally completed child.
pub fn normal_exit(output: &StageOutput) -> Result<i64, Fault> {
    crate::older::normal_code(output)
        .ok_or_else(|| crate::older::value("Child did not complete its declared exit contract"))
}

/// Python's `bytes.decode("ascii")` error text, for a diagnostic message that is not ASCII.
fn ascii_text(data: &[u8]) -> Result<String, Fault> {
    match data.iter().position(|byte| !byte.is_ascii()) {
        None => Ok(String::from_utf8_lossy(data).to_string()),
        Some(position) => Err(crate::older::value(format!(
            "'ascii' codec can't decode byte 0x{:02x} in position {position}: ordinal not in range(128)",
            data[position]
        ))),
    }
}

/// `engine_outcome`: candidate, or a final status with its reason.
pub fn engine_outcome(output: &StageOutput, source: &[u8]) -> Result<(String, String), Fault> {
    let code = normal_exit(output)?;
    let (stdout, stderr) = (&output.stdout[..], &output.stderr[..]);
    if code == 0 && stdout == b"candidate-refutation\n" && contract::candidate_stderr(stderr) {
        return Ok((
            "candidate".into(),
            "Candidate requires independent original-byte checking".into(),
        ));
    }
    if code == 2 && stdout == b"unknown\n" && contract::unknown_stderr(stderr) {
        return Ok((
            "GaveUp".into(),
            "Search exhausted its queue without a certified result".into(),
        ));
    }
    if stdout.is_empty() {
        if let Some(found) = contract::diagnostic(stderr) {
            let message = ascii_text(found.message)?;
            if found.offset_value() > source.len() as u128 {
                return Err(crate::older::value(
                    "Driver diagnostic offset exceeds captured input",
                ));
            }
            if code == 3 && found.kind == "InvalidInput" && INVALID.contains(&message.as_str()) {
                return Ok(("InputError".into(), message));
            }
            if code == 4 && found.kind == "Unsupported" && UNSUPPORTED.contains(&message.as_str()) {
                return Ok(("Inappropriate".into(), message));
            }
        }
        if code == 5 && contract::resource_stderr(stderr) {
            return Ok((
                "ResourceOut".into(),
                String::from_utf8_lossy(&stderr[..stderr.len() - 1]).to_string(),
            ));
        }
    }
    Err(crate::older::value(
        "Malformed, unrecognized or failed FOF driver contract",
    ))
}

/// `checker_acceptance`.
pub fn checker_acceptance(output: &StageOutput) -> Result<(), Fault> {
    if normal_exit(output)? != 0 || output.stdout != ACCEPTED || !output.stderr.is_empty() {
        return Err(crate::older::value(
            "Pinned original-byte version-2 checker did not accept",
        ));
    }
    Ok(())
}
