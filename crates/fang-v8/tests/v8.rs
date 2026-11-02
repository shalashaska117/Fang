// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang_equality_search::{Outcome as SearchOutcome, Statistics};
use fang_tptp_expanded_integration::{Limits, prove_bytes};
use fang_tptp_expanded_v8::{
    CAPABILITY, Error, HEADER, Outcome, VERSION, certificate_text, produce,
};
use std::io::Write;
use std::process::{Command, Stdio};

const OLD: &str = "(fang-proof 5\n  (preprocessing identity-cnf-equality-v1)\n";
const MARKER: &str = "candidate-certificate: unchecked original input\n";

fn counters(s: &Statistics) -> [usize; 4] {
    [
        s.processed_clauses,
        s.attempted_inferences,
        s.derived_clauses,
        s.stored_term_nodes,
    ]
}

#[test]
fn header_names_version_eight_and_its_own_marker() {
    assert_eq!(VERSION, 8);
    assert_eq!(
        HEADER,
        format!("(fang-proof {VERSION}\n  (preprocessing {CAPABILITY})\n")
    );
    assert_ne!(CAPABILITY, "nested-fof-equality-skolem-distributive-v1");
    assert!(HEADER.len() > OLD.len());
}

#[test]
fn envelope_keeps_every_authoritative_trace_byte_and_counter() {
    for input in [
        "cnf(a,axiom,($false)).",
        "cnf(a,axiom,(X!=X)).",
        "cnf(e,axiom,(a=b)).cnf(p,axiom,(p(a))).cnf(n,axiom,(~p(b))).",
        "fof(a,axiom,?[X]:(X!=X)).",
        "fof(a,axiom,p<=q).cnf(b,axiom,q).cnf(c,axiom,~p).",
        "fof(a,axiom,p<~>q).cnf(b,axiom,p).cnf(c,axiom,q).",
        "cnf(z,axiom,$true).cnf(f,axiom,~$true).",
    ] {
        let limits = Limits::default();
        let run = produce(input.as_bytes(), &limits).unwrap();
        let raw = prove_bytes(input.as_bytes(), &limits).unwrap();
        let Outcome::CandidateRefutation {
            certificate,
            text,
            statistics,
        } = run.outcome
        else {
            panic!("candidate expected for {input}")
        };
        let SearchOutcome::CandidateRefutation {
            certificate: raw_certificate,
            statistics: raw_statistics,
        } = raw.outcome
        else {
            panic!("candidate expected for {input}")
        };
        let old = certificate.to_text(1 << 20).unwrap();
        assert_eq!(old, raw_certificate.to_text(1 << 20).unwrap());
        assert_eq!(text.strip_prefix(HEADER), old.strip_prefix(OLD));
        assert!(text.starts_with(HEADER) && text.ends_with(")\n"));
        assert_eq!(counters(&statistics), counters(&raw_statistics));
        assert_eq!(run.prepared.clauses, raw.prepared.clauses);
        assert_eq!(run.prepared.sources, raw.prepared.sources);
    }
}

#[test]
fn exact_byte_cap_and_small_caps_return_no_partial_text() {
    let run = produce(b"fof(a,axiom,?[X]:(X!=X)).", &Limits::default()).unwrap();
    let Outcome::CandidateRefutation {
        certificate, text, ..
    } = run.outcome
    else {
        panic!()
    };
    assert_eq!(certificate_text(&certificate, text.len()).unwrap(), text);
    assert_eq!(certificate_text(&certificate, usize::MAX).unwrap(), text);
    for cap in [0, HEADER.len() - OLD.len() - 1, text.len() - 1] {
        assert!(matches!(
            certificate_text(&certificate, cap),
            Err(Error::Serialization(fang_equality_search::Error::Resource(
                _
            )))
        ));
    }
    let mut limits = Limits::default();
    limits.search.input.max_proof_bytes = text.len() - 1;
    assert!(matches!(
        produce(b"fof(a,axiom,?[X]:(X!=X)).", &limits),
        Err(Error::Serialization(_))
    ));
}

#[test]
fn unknown_and_typed_errors_are_unchanged() {
    for input in ["cnf(a,axiom,$true).", "fof(a,axiom,p<=>p)."] {
        let run = produce(input.as_bytes(), &Limits::default()).unwrap();
        assert!(matches!(run.outcome, Outcome::Unknown(_)), "{input}");
    }
    for input in [
        "fof(a,conjecture,p).",
        "thf(a,axiom,p).",
        "cnf(a,axiom,$false).fof(b,axiom,p(X)).",
    ] {
        assert!(
            matches!(
                produce(input.as_bytes(), &Limits::default()),
                Err(Error::Adapter(_))
            ),
            "{input}"
        );
    }
}

fn candidate(input: &[u8]) -> (Option<i32>, Vec<u8>, Vec<u8>) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_fang-expanded-candidate"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(input).unwrap();
    let output = child.wait_with_output().unwrap();
    (output.status.code(), output.stdout, output.stderr)
}

#[test]
fn binary_transport_exit_codes_and_marker() {
    let input = b"fof(a,axiom,p<=q).cnf(b,axiom,q).cnf(c,axiom,~p).";
    let (code, stdout, stderr) = candidate(input);
    let Outcome::CandidateRefutation { text, .. } =
        produce(input, &Limits::default()).unwrap().outcome
    else {
        panic!()
    };
    assert_eq!(code, Some(0));
    assert_eq!(stdout, text.as_bytes());
    assert_eq!(stderr, MARKER.as_bytes());
    let (code, stdout, stderr) = candidate(b"cnf(a,axiom,$true).");
    assert_eq!(code, Some(2));
    assert!(stdout.is_empty() && stderr.starts_with(b"unknown: "));
    let (code, stdout, stderr) = candidate(b"fof(a,conjecture,p).");
    assert_eq!(code, Some(3));
    assert!(stdout.is_empty() && stderr.starts_with(b"adapter: "));
}
