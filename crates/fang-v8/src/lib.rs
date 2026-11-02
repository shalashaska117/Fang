// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Envelope adaptation only. Shared Fang components retain their existing notices.
#![forbid(unsafe_code)]

//! Candidate-only version-8 envelope for the expanded byte-input adapter.
//! Only the independent original-byte checker can accept these candidates.

use fang_equality_search::{Certificate, Statistics};
use fang_tptp_expanded_integration::{Limits, Prepared};

pub const VERSION: u32 = 8;
pub const CAPABILITY: &str = "expanded-fof-equality-skolem-distributive-v1";
pub const HEADER: &str =
    "(fang-proof 8\n  (preprocessing expanded-fof-equality-skolem-distributive-v1)\n";
const TRACE_HEADER: &str = "(fang-proof 5\n  (preprocessing identity-cnf-equality-v1)\n";

/// The limits record of every native main (`NativeLimits.lean`).
/// Declarations, the Skolem work counters, the symbol caps, the predicate table and the
/// literals per clause take the record's values. The parser's whole-file counts of term nodes,
/// formula nodes and binders have no counterpart in the record; they are raised to the input
/// byte bound, which already caps them. Skolemization does not read the core clause and literal
/// counts. The producer's pipeline reads them as caps on the output of the whole problem, which
/// the checker does not have, so they are raised to the stored-node bound. The pipeline also
/// spends one operation and storage budget on Skolemization, removal and clausification
/// together, where the checker gives removal and clausification a fresh budget per declaration,
/// so the producer can still refuse a large FOF input that the checker accepts.
pub fn native_limits() -> Limits {
    let mut limits = Limits::default();
    let bytes = limits.input.input.max_input_bytes;
    limits.input.input.max_clauses = 65_536;
    limits.input.input.max_term_nodes = bytes;
    limits.input.max_formula_nodes = bytes;
    limits.input.max_binders = bytes;
    limits.preprocessing.max_declarations = 65_536;
    limits.preprocessing.max_functions = 7_081;
    limits.preprocessing.max_skolem_symbols = 4_703;
    let stored = 4_000_000;
    limits.preprocessing.core.max_stored_nodes = stored;
    limits.preprocessing.core.max_operations = 16_000_000;
    limits.preprocessing.core.max_clauses = stored;
    limits.preprocessing.core.max_literals = stored;
    limits.max_predicates = 5_808;
    limits.max_bridge_literals = 256;
    limits
}

#[derive(Debug)]
pub enum Error {
    Adapter(fang_tptp_expanded_integration::Error),
    Serialization(fang_equality_search::Error),
    WrongTraceVersion,
}

#[derive(Debug)]
pub enum Outcome {
    CandidateRefutation {
        certificate: Certificate,
        text: String,
        statistics: Statistics,
    },
    Unknown(Statistics),
}

#[derive(Debug)]
pub struct Produced {
    pub prepared: Prepared,
    pub outcome: Outcome,
}

/// Reserve the envelope overhead, then call the authoritative bounded ordered
/// serializer. Only its version-5 header is replaced; node order, node bytes and
/// the final reference are kept. The cap bounds the returned text, not the two
/// temporary Strings or the allocator.
pub fn certificate_text(certificate: &Certificate, max_bytes: usize) -> Result<String, Error> {
    let extra = HEADER.len() - TRACE_HEADER.len();
    let trace_cap = max_bytes.checked_sub(extra).ok_or(Error::Serialization(
        fang_equality_search::Error::Resource("expanded certificate byte limit"),
    ))?;
    let original = certificate
        .to_text(trace_cap)
        .map_err(Error::Serialization)?;
    let body = original
        .strip_prefix(TRACE_HEADER)
        .ok_or(Error::WrongTraceVersion)?;
    let mut text = String::with_capacity(original.len() + extra);
    text.push_str(HEADER);
    text.push_str(body);
    Ok(text)
}

/// A successful result is a candidate or Unknown. Errors expose no partial
/// Produced value. The complete original input is parsed before search.
pub fn produce(input: &[u8], limits: &Limits) -> Result<Produced, Error> {
    let run = fang_tptp_expanded_integration::prove_bytes(input, limits).map_err(Error::Adapter)?;
    let outcome = match run.outcome {
        fang_equality_search::Outcome::CandidateRefutation {
            certificate,
            statistics,
        } => {
            let text = certificate_text(&certificate, limits.search.input.max_proof_bytes)?;
            Outcome::CandidateRefutation {
                certificate,
                text,
                statistics,
            }
        }
        fang_equality_search::Outcome::Unknown(statistics) => Outcome::Unknown(statistics),
    };
    Ok(Produced {
        prepared: run.prepared,
        outcome,
    })
}
