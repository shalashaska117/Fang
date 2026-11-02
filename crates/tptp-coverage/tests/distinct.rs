// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Distinct objects: lexing, identity, table order and generated axioms.

use fang::ErrorKind;
use fang::syntax::Term;
use fang_equality_inference_core::{Atom, Literal};
use fang_tptp_coverage_candidate::{
    Body, Bundle, CnfLiteral, EncodedBody, Expanded, Limits, Reason, Source, expand,
};

fn run(text: &str) -> Expanded {
    expand(
        &Bundle::single(text.as_bytes().to_vec()),
        &Limits::default(),
    )
    .unwrap()
}

fn failure(text: &str) -> (ErrorKind, Reason, Option<usize>) {
    let error = expand(
        &Bundle::single(text.as_bytes().to_vec()),
        &Limits::default(),
    )
    .unwrap_err();
    (error.kind, error.reason, error.offset)
}

#[test]
fn lexing_follows_the_bnf() {
    let value = run(r#"fof(a,axiom,"a\"b" = "c\\d" & "a\"b" != " ~!")."#);
    let contents: Vec<_> = value
        .distinct_objects
        .iter()
        .map(|(_, content)| content.as_str())
        .collect();
    assert_eq!(contents, ["a\"b", "c\\d", " ~!"]);
    let spellings: Vec<_> = value
        .parsed
        .functions
        .iter()
        .map(|s| s.name.as_str())
        .collect();
    assert_eq!(spellings, [r#""a\"b""#, r#""c\\d""#, r#"" ~!""#]);
    for (text, offset) in [
        ("fof(a,axiom,p(\"\")).", 14),
        ("fof(a,axiom,p(\"abc)).", 14),
        ("fof(a,axiom,p(\"a\\x\")).", 17),
        ("fof(a,axiom,p(\"a\tb\")).", 16),
        ("fof(a,axiom,p(\"a\\", 14),
    ] {
        assert_eq!(
            failure(text),
            (ErrorKind::InvalidInput, Reason::Syntax, Some(offset)),
            "{text:?}"
        );
    }
    let error = expand(
        &Bundle::single(b"fof(a,axiom,p(\"\xc3\xa9\")).".to_vec()),
        &Limits::default(),
    )
    .unwrap_err();
    assert_eq!(error.kind, ErrorKind::InvalidInput);
}

#[test]
fn identity_is_separate_from_ordinary_symbols() {
    let value = run(r#"fof(a,axiom,p("cat") & p('cat') & p(cat) & p('"cat"') & p("cat"))."#);
    assert_eq!(value.parsed.functions.len(), 3);
    assert_eq!(value.distinct_objects, [(0, "cat".to_owned())]);
    let names: Vec<_> = value
        .parsed
        .functions
        .iter()
        .map(|s| s.name.as_str())
        .collect();
    assert_eq!(names, ["\"cat\"", "cat", "\"cat\""]);
    // Ordinary symbols and objects share one first-occurrence ID order.
    let value = run(r#"cnf(a,axiom,f(b) = "x" | g("y",c) != "x")."#);
    let names: Vec<_> = value
        .parsed
        .functions
        .iter()
        .map(|s| (s.name.as_str(), s.arity))
        .collect();
    assert_eq!(
        names,
        [
            ("f", 1),
            ("b", 0),
            ("\"x\"", 0),
            ("g", 2),
            ("\"y\"", 0),
            ("c", 0)
        ]
    );
    assert_eq!(
        value.distinct_objects,
        [(2, "x".to_owned()), (4, "y".to_owned())]
    );
}

#[test]
fn objects_are_constant_terms_only() {
    for text in [
        "fof(a,axiom,\"a\").",
        "fof(a,axiom,~\"a\").",
        "cnf(a,axiom,\"a\" | p).",
        "fof(a,axiom,p(\"a\"(b))).",
        "fof(a,axiom,\"a\"(b) = c).",
        "fof(a,axiom,![\"X\"]:p).",
        "fof(\"a\",axiom,p).",
    ] {
        let error = failure(text);
        assert_eq!(error.0, ErrorKind::InvalidInput, "{text}");
    }
    assert!(
        run("fof(a,axiom,![X]:(X = \"a\" | p(X,\"b\"))).")
            .distinct_objects
            .len()
            == 2
    );
}

fn generated(value: &Expanded) -> Vec<(usize, usize, u32, u32)> {
    value
        .sources
        .iter()
        .zip(&value.parsed.declarations)
        .filter_map(|(source, declaration)| match (source, &declaration.body) {
            (Source::DistinctPair { left, right }, Body::Cnf(literals)) => {
                let [
                    CnfLiteral::Ordinary(Literal {
                        positive: false,
                        atom: Atom::Equal(Term::Fun(a, x), Term::Fun(b, y)),
                    }),
                ] = literals.as_slice()
                else {
                    panic!("unexpected generated clause");
                };
                assert!(x.is_empty() && y.is_empty());
                Some((*left, *right, *a, *b))
            }
            (Source::DistinctPair { .. }, _) => panic!("generated FOF"),
            _ => None,
        })
        .collect()
}

#[test]
fn pairwise_axioms_follow_the_inventory() {
    for count in 0usize..8 {
        let terms: Vec<String> = (0..count).map(|i| format!("p(\"o{i}\")")).collect();
        let body = if terms.is_empty() {
            "p(a)".to_owned()
        } else {
            terms.join(" & ")
        };
        let value = run(&format!("fof(a,axiom,{body}). fof(b,axiom,q)."));
        let pairs = generated(&value);
        assert_eq!(pairs.len(), count * count.saturating_sub(1) / 2);
        let mut expected = Vec::new();
        for left in 0..count {
            for right in left + 1..count {
                expected.push((
                    left,
                    right,
                    value.distinct_objects[left].0,
                    value.distinct_objects[right].0,
                ));
            }
        }
        assert_eq!(pairs, expected);
        // Source declarations come first, in order, then the generated ones.
        assert_eq!(value.parsed.declarations[0].name, "a");
        assert_eq!(value.parsed.declarations[1].name, "b");
        assert_eq!(value.parsed.declarations.len(), 2 + pairs.len());
        let encoded = value.parsed.encode(100, 100).unwrap();
        let equality = encoded.reservation.equality_id();
        for declaration in &encoded.declarations[2..] {
            let EncodedBody::Cnf(Some(clause)) = &declaration.body else {
                panic!("generated clause");
            };
            assert_eq!(clause.len(), 1);
            assert!(!clause[0].positive);
            assert_eq!(clause[0].predicate, equality);
        }
    }
}

#[test]
fn inventory_caps_are_resource_errors() {
    let terms: Vec<String> = (0..5).map(|i| format!("p(\"o{i}\")")).collect();
    let text = format!("fof(a,axiom,{}).", terms.join(" & "));
    let limits = Limits {
        max_distinct_objects: 4,
        ..Limits::default()
    };
    let error = expand(&Bundle::single(text.clone().into_bytes()), &limits).unwrap_err();
    assert_eq!(error.kind, ErrorKind::ResourceLimit);
    // The generated clauses are bounded by the object cap alone: one formula and the 15 clauses of
    // six objects pass a limit of one formula per file.
    let mut limits = Limits::default();
    limits.input.max_clauses = 1;
    assert!(expand(&Bundle::single(text.clone().into_bytes()), &limits).is_ok());
    let six: Vec<String> = (0..6).map(|i| format!("p(\"o{i}\")")).collect();
    let text = format!("fof(a,axiom,{}).", six.join(" & "));
    let expanded = expand(&Bundle::single(text.into_bytes()), &limits).unwrap();
    assert_eq!(expanded.parsed.declarations.len(), 16);
    // Objects only in unselected formulas or annotations do not count.
    let text = format!(
        "fof(a,axiom,p,[{}]). fof(b,axiom,q(\"one\")).",
        (0..80)
            .map(|i| format!("\"x{i}\""))
            .collect::<Vec<_>>()
            .join(",")
    );
    assert_eq!(run(&text).distinct_objects.len(), 1);
}
