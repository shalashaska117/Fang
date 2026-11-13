// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Version-8 process contracts and SZS mapping. Only exact checker acceptance authorizes a result.
//!
//! The producer prints its typed adapter errors with the `adapter:` prefix. The patterns are those of the
//! earlier Python adapter, kept verbatim and matched over the whole stream.

use std::sync::OnceLock;

use fang_json::Value;

use crate::pattern::{Pattern, group};

pub const ACCEPTED: &[u8] =
    b"accepted-original-expanded-equality (native checker; compiler/runtime trusted)\n";
pub const CANDIDATE: &[u8] = b"candidate-certificate: unchecked original input\n";
pub const HEADER: &[u8] =
    b"(fang-proof 8\n  (preprocessing expanded-fof-equality-skolem-distributive-v1)\n";
pub const TEXT: &str = r#""(?:[^"\\\r\n]|\\.)*""#;
pub const RESOURCE: &str = r#"Resource\("[^"\\\r\n]+"\)"#;
const CORE_CAP: &str = "(FormulaDepth|FormulaNodes|TermDepth|InputTermNodes|Clauses|LiteralsPerClause|Literals|StoredNodes|\
                        Operations|Arithmetic|Binders)";

/// The input diagnostic: kind, offset (with its digits as group 3) and the message as a JSON string.
pub fn input_pattern() -> String {
    format!(
        r"Error \{{ kind: (InvalidInput|Unsupported|ResourceLimit), offset: (None|Some\(([0-9]+)\)), message: ({TEXT}) \}}"
    )
}

fn preprocessing_resources() -> Vec<String> {
    vec![
        RESOURCE.to_string(),
        r"Skolem\(Resource\((Declarations|Functions|SkolemSymbols|Operations|StoredNodes|TermDepth)\)\)".to_string(),
        format!(r"Skolem\(Core\(Resource\({CORE_CAP}\)\)\)"),
        r"Removal\(Resource\((FormulaDepth|Operations|OutputNodes)\)\)".to_string(),
        concat!(
            r"Clausification\(Resource\((FormulaDepth|FormulaNodes|TermDepth|InputTermNodes|Clauses|",
            r"LiteralsPerClause|Literals|StoredNodes|Operations|Arithmetic)\)\)"
        )
        .to_string(),
    ]
}

/// The structural resource bounds the producer reports after `adapter: `.
pub fn adapter_resources() -> Vec<String> {
    let mut patterns = vec![
        RESOURCE.to_string(),
        r"(Encoding|Conversion)\((PredicateLimit|SymbolId|LiteralLimit)\)".to_string(),
        format!(r"Search\({RESOURCE}\)"),
        format!(r"Search\(Search\({RESOURCE}\)\)"),
        format!(r"Search\(Search\(Unification\(Error \{{ kind: ResourceLimit, offset: None, message: {TEXT} \}}\)\)\)"),
        r"Search\(Search\(Reconstruction\((Depth|Literals|Bindings|OutputNodes|Operations)\)\)\)".to_string(),
        r"Search\(Search\(Paramodulation\(Resource\((Operations|OutputNodes|Literals|Arithmetic)\)\)\)\)".to_string(),
        r"Search\(Search\(Paramodulation\(Input\((Depth|Literals|Bindings|OutputNodes|Operations)\)\)\)\)".to_string(),
        r"Search\(Search\(Paramodulation\(Occurrence\((Depth|OutputNodes|Operations)\)\)\)\)".to_string(),
    ];
    patterns.extend(
        preprocessing_resources()
            .into_iter()
            .map(|pattern| format!(r"Preprocessing\({pattern}\)")),
    );
    patterns
}

struct Compiled {
    unknown: Pattern,
    input: Pattern,
    adapter: Vec<Pattern>,
    serialization: Pattern,
    logical: Pattern,
    certificate: Pattern,
    resources: Vec<Pattern>,
    rejected: Vec<Pattern>,
    internal: Pattern,
    io: Pattern,
}

fn compiled() -> &'static Compiled {
    static COMPILED: OnceLock<Compiled> = OnceLock::new();
    COMPILED.get_or_init(|| Compiled {
        unknown: Pattern::of(r"unknown: processed=[0-9]+ attempted=[0-9]+\n"),
        input: Pattern::of(&format!(r"adapter: Input\({}\)\n", input_pattern())),
        adapter: adapter_resources().iter().map(|pattern| Pattern::of(&format!(r"adapter: {pattern}\n"))).collect(),
        serialization: Pattern::of(&format!(r"serialization: {RESOURCE}\n")),
        logical: Pattern::of(concat!(
            r"logical-rejection: Fang\.Equality\.TraceError\.((inputIndex|parentIndex) [0-9]+|inferenceWitness|",
            r"claimedClause|finalIndex|finalNotEmpty)\n"
        )),
        certificate: Pattern::of(r"certificate: (invalid-certificate|invalid-syntax|unsupported): [ -~]+\n"),
        resources: [
            r"resource\.(bytes\.(input|certificate)|replay\.(skolem|skolem-core|removal|clausification))",
            r"resource\.replay\.input:[0-9]+",
            r"resource\.replay\.(width|conversion-width): [ -~]+",
            r"replay\.(reservation|conversion)\.(predicate-limit|symbol-width|literal-limit)",
            r"(certificate|replay\.(transport-input|preprocessing-input)): resource-exhaustion[ -~]*",
        ]
        .iter()
        .map(|pattern| Pattern::of(&format!(r"{pattern}\n")))
        .collect(),
        rejected: [
            r"replay\.input\.(invalid|unsupported):[0-9]+",
            r"replay\.(transport-input|preprocessing-input): [ -~]+",
            r"replay\.nonliteral",
            r"replay\.(reservation|conversion)\.(unknown-predicate|predicate-arity|reserved-arity)",
            concat!(
                r"replay\.(missing-function-arity|missing-predicate-arity|skolem-invalid|skolem-unsupported|",
                r"residual-existential|clausification-invalid)"
            ),
            r"invalid-utf8\.(input|certificate)",
            r"(invalid-nul|unsupported-non-ascii)\.(input|certificate):[0-9]+",
        ]
        .iter()
        .map(|pattern| Pattern::of(&format!(r"{pattern}\n")))
        .collect(),
        internal: Pattern::of(concat!(
            r"(replay\.(input\.internal:[0-9]+|transport-runtime-effect|transport-divergence|runtime-effect|",
            r"divergence|clause-block-count)|internal-byte-roundtrip\.(input|certificate))\n"
        )),
        io: Pattern::of(r"io-error: [ -~]+\n(?:  [ -~]+\n)*"),
    })
}

/// A child that did not keep its declared exit contract; the caller turns it into an Error with this text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContractError(pub String);

/// The exit code of a stage record that completed (exit 0) or exited with a code; anything else, such as a
/// signal, breaks the contract.
pub fn normal(record: &fang_json::Object) -> Result<i64, ContractError> {
    let code = record.get("exit_code").and_then(Value::as_i64);
    let classification = record.get("classification").and_then(Value::as_str);
    match code {
        Some(code)
            if code >= 0
                && classification
                    == Some(if code == 0 {
                        "completed"
                    } else {
                        "nonzero-exit"
                    }) =>
        {
            Ok(code)
        }
        _ => Err(ContractError(
            "Child did not complete its declared exit contract".to_string(),
        )),
    }
}

/// The status of an input diagnostic kind.
fn input_status(kind: &[u8]) -> &'static str {
    match kind {
        b"InvalidInput" => "InputError",
        b"Unsupported" => "Inappropriate",
        _ => "ResourceOut",
    }
}

/// The producer's outcome: `candidate` with the certificate on stdout, or a status with its reason. A
/// candidate is never a result.
pub fn engine_outcome(
    record: &fang_json::Object,
    stdout: &[u8],
    stderr: &[u8],
    source: &[u8],
) -> Result<(String, String), ContractError> {
    let code = normal(record)?;
    let patterns = compiled();
    if code == 0 && stdout.starts_with(HEADER) && stderr == CANDIDATE {
        return Ok((
            "candidate".to_string(),
            "Original-byte checking is required".to_string(),
        ));
    }
    if !stdout.is_empty() {
        return Err(ContractError(
            "Noncandidate or malformed producer emitted certificate bytes".to_string(),
        ));
    }
    if code == 2 && patterns.unknown.is_full(stderr) {
        return Ok((
            "GaveUp".to_string(),
            "Search stopped without a certified result".to_string(),
        ));
    }
    if code == 3 {
        if let Some(captures) = patterns.input.fullmatch(stderr) {
            if let Some(offset) = group(stderr, &captures, 3) {
                let beyond = std::str::from_utf8(offset)
                    .ok()
                    .and_then(|digits| digits.parse::<u128>().ok())
                    .is_none_or(|value| value > source.len() as u128);
                if beyond {
                    return Err(ContractError(
                        "Diagnostic offset exceeds captured input".to_string(),
                    ));
                }
            }
            let message = group(stderr, &captures, 4).unwrap_or_default();
            let decoded = fang_json::parse(message, &fang_json::ParseLimits::default())
                .ok()
                .and_then(|value| value.as_str().map(str::to_string));
            let Some(message) =
                decoded.filter(|text| text.chars().all(|c| (' '..='~').contains(&c)))
            else {
                return Err(ContractError("Malformed producer diagnostic".to_string()));
            };
            let kind = group(stderr, &captures, 1).unwrap_or_default();
            return Ok((input_status(kind).to_string(), message));
        }
        if patterns
            .adapter
            .iter()
            .any(|pattern| pattern.is_full(stderr))
        {
            return Ok((
                "ResourceOut".to_string(),
                "Preprocessing or search reached a structural resource bound".to_string(),
            ));
        }
    }
    if code == 4 && patterns.serialization.is_full(stderr) {
        return Ok((
            "ResourceOut".to_string(),
            "Serialization reached a structural resource bound".to_string(),
        ));
    }
    Err(ContractError(
        "Unrecognized or failed version-8 producer contract".to_string(),
    ))
}

/// The checker's outcome; only `accepted` can lead to a result.
pub fn checker_outcome(
    record: &fang_json::Object,
    stdout: &[u8],
    stderr: &[u8],
) -> Result<&'static str, ContractError> {
    let code = normal(record)?;
    let patterns = compiled();
    if code == 0 && stdout == ACCEPTED && stderr.is_empty() {
        return Ok("accepted");
    }
    if !stdout.is_empty() {
        return Err(ContractError(
            "Rejected or malformed checker result emitted acceptance output".to_string(),
        ));
    }
    if code == 1 && patterns.logical.is_full(stderr) {
        return Ok("logical-rejection");
    }
    if code == 6 && stderr == b"signature-rejection\n" {
        return Ok("signature-rejection");
    }
    if code == 3 && patterns.certificate.is_full(stderr) {
        return Ok("certificate-rejection");
    }
    if code == 4
        && patterns
            .resources
            .iter()
            .any(|pattern| pattern.is_full(stderr))
    {
        return Ok("resource");
    }
    if code == 2
        && patterns
            .rejected
            .iter()
            .any(|pattern| pattern.is_full(stderr))
    {
        return Ok("input-or-replay-rejection");
    }
    if code == 5 && patterns.internal.is_full(stderr) {
        return Ok("internal-replay-failure");
    }
    if code == 74 && patterns.io.is_full(stderr) {
        return Ok("io-failure");
    }
    Err(ContractError(
        "Unrecognized or failed version-8 checker contract".to_string(),
    ))
}

/// The status after a producer candidate; a rejection is an error, never a result.
pub fn checked_status(outcome: &str) -> (&'static str, String) {
    match outcome {
        "accepted" => (
            "Unsatisfiable",
            "The native version-8 checker accepted the exact captured pair".to_string(),
        ),
        "resource" => (
            "ResourceOut",
            "The native checker reached its declared resource bound".to_string(),
        ),
        other => (
            "Error",
            format!("The original-byte checker rejected the producer candidate: {other}"),
        ),
    }
}

/// The status rule for conjectures: Theorem only when every selected conjecture was accepted; with none
/// selected, Unsatisfiable only when the inputs task was accepted.
pub fn task_status(conjectures: usize, accepted: usize) -> &'static str {
    if conjectures > 0 {
        if accepted == conjectures {
            "Theorem"
        } else {
            "GaveUp"
        }
    } else if accepted == 1 {
        "Unsatisfiable"
    } else {
        "GaveUp"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fang_json::Object;

    const SOURCE: &[u8] = b"cnf(a,axiom,($false)).";

    fn exited(code: i64) -> Object {
        let mut record = Object::new();
        record.set("exit_code", Value::from(code));
        record.set(
            "classification",
            Value::from(if code == 0 {
                "completed"
            } else {
                "nonzero-exit"
            }),
        );
        record
    }

    fn certificate() -> Vec<u8> {
        [HEADER, b"  (input 0 0)\n  (final 0)\n)\n"].concat()
    }

    #[test]
    fn engine_contracts() {
        let cases: Vec<(i64, Vec<u8>, &[u8], &str)> = vec![
            (0, certificate(), CANDIDATE, "candidate"),
            (2, vec![], b"unknown: processed=0 attempted=0\n", "GaveUp"),
            (3, vec![], b"adapter: Input(Error { kind: Unsupported, offset: Some(6), message: \"only the axiom role is supported\" })\n", "Inappropriate"),
            (3, vec![], b"adapter: Input(Error { kind: InvalidInput, offset: None, message: \"duplicate name\" })\n", "InputError"),
            (3, vec![], b"adapter: Input(Error { kind: ResourceLimit, offset: Some(3), message: \"too many declarations\" })\n", "ResourceOut"),
            (3, vec![], b"adapter: Encoding(PredicateLimit)\n", "ResourceOut"),
            (3, vec![], b"adapter: Search(Search(Resource(\"operations\")))\n", "ResourceOut"),
            (3, vec![], b"adapter: Preprocessing(Clausification(Resource(Clauses)))\n", "ResourceOut"),
            (4, vec![], b"serialization: Resource(\"expanded certificate byte limit\")\n", "ResourceOut"),
        ];
        for (code, out, err, expected) in cases {
            let (status, _) = engine_outcome(&exited(code), &out, err, SOURCE).expect("recognized");
            assert_eq!(status, expected, "{}", String::from_utf8_lossy(err));
        }
    }

    #[test]
    fn engine_contract_failures() {
        let cases: Vec<(i64, Vec<u8>, &[u8])> = vec![
            (2, b"x".to_vec(), b"unknown: processed=0 attempted=0\n"),
            (0, b"(fang-proof 7\n".to_vec(), CANDIDATE),
            (0, certificate(), b""),
            (3, vec![], b"adapter: Input(Error { kind: InvalidInput, offset: Some(999), message: \"x\" })\n"),
            (3, vec![], b"adapter: Internal(\"unexpected\")\n"),
            (3, vec![], b"adapter: Encoding(UnknownPredicate)\n"),
            (5, vec![], b"internal: ordered serializer envelope mismatch\n"),
            (74, vec![], b"io: input read failed\n"),
            (101, vec![], b"panicked\n"),
        ];
        for (code, out, err) in cases {
            assert!(
                engine_outcome(&exited(code), &out, err, SOURCE).is_err(),
                "{}",
                String::from_utf8_lossy(err)
            );
        }
        let mut odd = Object::new();
        odd.set("exit_code", Value::from(2i64));
        odd.set("classification", Value::from("completed"));
        assert!(engine_outcome(&odd, b"", b"unknown: processed=0 attempted=0\n", SOURCE).is_err());
    }

    #[test]
    fn checker_contracts() {
        let cases: Vec<(i64, &[u8], &[u8], &str)> = vec![
            (0, ACCEPTED, b"", "accepted"),
            (
                1,
                b"",
                b"logical-rejection: Fang.Equality.TraceError.inferenceWitness\n",
                "logical-rejection",
            ),
            (
                3,
                b"",
                b"certificate: unsupported: expanded certificate version at byte 16\n",
                "certificate-rejection",
            ),
            (6, b"", b"signature-rejection\n", "signature-rejection"),
            (
                2,
                b"",
                b"replay.input.unsupported:6\n",
                "input-or-replay-rejection",
            ),
            (
                2,
                b"",
                b"invalid-nul.certificate:104\n",
                "input-or-replay-rejection",
            ),
            (4, b"", b"resource.replay.input:21890\n", "resource"),
            (4, b"", b"resource.bytes.input\n", "resource"),
            (
                74,
                b"",
                b"io-error: no such file or directory (error code: 2)\n  file: /tmp/x\n",
                "io-failure",
            ),
        ];
        for (code, out, err, expected) in cases {
            assert_eq!(
                checker_outcome(&exited(code), out, err).expect("recognized"),
                expected
            );
        }
        let failures: Vec<(i64, &[u8], &[u8])> = vec![
            (0, ACCEPTED, b"warning\n"),
            (1, ACCEPTED, b""),
            (
                64,
                b"",
                b"usage: fang-expanded-native-linear INPUT CERTIFICATE\n",
            ),
            (0, b"accepted\n", b""),
        ];
        for (code, out, err) in failures {
            assert!(checker_outcome(&exited(code), out, err).is_err());
        }
    }

    #[test]
    fn checked_status_never_turns_rejection_into_result() {
        assert_eq!(checked_status("accepted").0, "Unsatisfiable");
        assert_eq!(checked_status("resource").0, "ResourceOut");
        for outcome in [
            "logical-rejection",
            "signature-rejection",
            "certificate-rejection",
            "input-or-replay-rejection",
            "internal-replay-failure",
            "io-failure",
        ] {
            assert_eq!(checked_status(outcome).0, "Error");
        }
    }

    #[test]
    fn signed_task_rules() {
        assert_eq!(task_status(0, 1), "Unsatisfiable");
        assert_eq!(task_status(0, 0), "GaveUp");
        assert_eq!(task_status(2, 2), "Theorem");
        assert_eq!(task_status(2, 1), "GaveUp");
    }
}
