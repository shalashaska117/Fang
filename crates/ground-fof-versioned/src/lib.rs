// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
#![forbid(unsafe_code)]

use fang::{Error, ErrorKind, search::Certificate};

const OLD_HEADER: &str = "(fang-proof 1\n";
const HEADER: &str = "(fang-proof 2\n  (preprocessing ground-fof-distributive-v1)\n";

/// Version the changed source-to-leaf meaning without changing the rule trace.
/// The independent decoder checks the full new envelope and every proof step.
/// This limits serialized bytes, not total peak allocation.
pub fn certificate_text(certificate: &Certificate, max_bytes: usize) -> Result<String, Error> {
    let extra = HEADER.len() - OLD_HEADER.len();
    let old_cap = max_bytes
        .checked_sub(extra)
        .ok_or_else(|| Error::resource("FOF certificate byte limit exceeded"))?;
    let original = certificate.to_text(old_cap)?;
    let body = original.strip_prefix(OLD_HEADER).ok_or_else(|| Error {
        kind: ErrorKind::InvalidInput,
        offset: None,
        message: "internal certificate serializer version mismatch".into(),
    })?;
    let mut result = String::with_capacity(original.len() + extra);
    result.push_str(HEADER);
    result.push_str(body);
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fang::search::{Outcome, prove};

    #[test]
    fn exact_trace_and_serialized_byte_cap() {
        let prepared = fang_ground_fof_search::prepare(
            b"fof(a,axiom,(p=>q)).fof(b,axiom,p).fof(c,axiom,~q).",
            &Default::default(),
            &Default::default(),
        )
        .unwrap();
        let Outcome::CandidateRefutation(certificate) =
            prove(&prepared.problem, &Default::default()).unwrap()
        else {
            panic!("Expected candidate refutation");
        };
        let old = certificate.to_text(100_000).unwrap();
        let text = certificate_text(&certificate, 100_000).unwrap();
        assert_eq!(text.strip_prefix(HEADER), old.strip_prefix(OLD_HEADER));
        assert_eq!(certificate_text(&certificate, text.len()).unwrap(), text);
        for cap in [0, HEADER.len() - 1, text.len() - 1] {
            assert_eq!(
                certificate_text(&certificate, cap).unwrap_err().kind,
                ErrorKind::ResourceLimit
            );
        }
    }
}
