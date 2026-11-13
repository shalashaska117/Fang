// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::{ErrorKind, syntax::Term};
use fang_equality_inference_core::Atom;
use fang_tptp_coverage_candidate::{Body, Formula, Limits, NameKind, parse};

#[test]
fn quoted_atoms_share_ordinary_identity_but_are_not_variables_or_builtins() {
    let parsed = parse(
        b"fof('case',axiom,(![X]:'p'(X) & (p('X') & '$true'))).",
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(parsed.declarations[0].name_kind, NameKind::Atom);
    assert_eq!(
        parsed
            .predicates
            .iter()
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>(),
        ["p", "$true"]
    );
    assert_eq!(
        parsed
            .functions
            .iter()
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>(),
        ["X"]
    );
    let simple = parse(b"fof(a,axiom,'quoted' = 'quoted').", &Limits::default()).unwrap();
    assert_eq!(simple.functions.len(), 1);
    assert_eq!(
        simple.declarations[0].body,
        Body::Fof(Formula::Atom(Atom::Equal(
            Term::Fun(0, vec![]),
            Term::Fun(0, vec![])
        )))
    );
    for input in [
        "fof(a,axiom,p).fof('a',axiom,p).",
        "'fof'(a,axiom,p).",
        "fof(a,'axiom',p).",
    ] {
        assert_eq!(
            parse(input.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::InvalidInput
        );
    }
}

#[test]
fn escapes_and_comment_markers_remain_part_of_the_atom() {
    let input = br"fof('a\'b\\c',axiom,'p%/* */'('it\'s','back\\slash')).";
    let parsed = parse(input, &Limits::default()).unwrap();
    assert_eq!(parsed.declarations[0].name, "a'b\\c");
    assert_eq!(parsed.predicates[0].name, "p%/* */");
    assert_eq!(
        parsed
            .functions
            .iter()
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>(),
        ["it's", "back\\slash"]
    );
    assert_eq!(&input[parsed.declarations[0].bytes.clone()], input);
}

#[test]
fn integer_record_names_keep_a_separate_canonical_identity() {
    let parsed = parse(
        b"fof(123,axiom,p).fof('123',axiom,p).fof(-2,axiom,p).fof(+3,axiom,p).",
        &Limits::default(),
    )
    .unwrap();
    let names = parsed
        .declarations
        .iter()
        .map(|d| (d.name_kind, d.name.as_str()))
        .collect::<Vec<_>>();
    assert_eq!(
        names,
        [
            (NameKind::Integer, "123"),
            (NameKind::Atom, "123"),
            (NameKind::Integer, "-2"),
            (NameKind::Integer, "3")
        ]
    );
    let encoded = parsed.encode(100, 100).unwrap();
    assert_eq!(encoded.declarations[0].name_kind, NameKind::Integer);
    assert_eq!(encoded.declarations[1].name_kind, NameKind::Atom);
    for input in [
        "fof(+1,axiom,p).fof(1,axiom,p).",
        "fof(-0,axiom,p).fof(0,axiom,p).",
        "fof(01,axiom,p).",
        "fof(-01,axiom,p).",
        "fof(1a,axiom,p).",
    ] {
        assert_eq!(
            parse(input.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::InvalidInput
        );
    }
}

#[test]
fn arbitrarily_long_integer_names_do_not_use_machine_integer_conversion() {
    let name = "9".repeat(4096);
    let source = format!("cnf({name},axiom,($false)).");
    let parsed = parse(source.as_bytes(), &Limits::default()).unwrap();
    assert_eq!(parsed.declarations[0].name, name);
    assert_eq!(parsed.declarations[0].name_kind, NameKind::Integer);
}

#[test]
fn invalid_quoted_characters_and_numeric_terms_stay_explicit() {
    for input in [
        "fof('',axiom,p).",
        "fof('a\\q',axiom,p).",
        "fof('a\nb',axiom,p).",
        "fof('unterminated",
        "fof('escape\\",
        "fof('a\0b',axiom,p).",
    ] {
        assert_eq!(
            parse(input.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::InvalidInput,
            "{input}"
        );
    }
    for input in [
        "fof(a,axiom,1 = 1).",
        "fof(a,axiom,p(-1)).",
        "cnf(a,axiom,(p(+1))).",
    ] {
        assert_eq!(
            parse(input.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::Unsupported
        );
    }
}

#[test]
fn quoted_and_signed_name_bytes_obey_the_existing_work_and_input_caps() {
    let source = br"fof(+12,axiom,'p\'q'('a\\b')).";
    let parsed = parse(source, &Limits::default()).unwrap();
    let mut limits = Limits::default();
    limits.input.max_operations = parsed.statistics.operations;
    assert!(parse(source, &limits).is_ok());
    limits.input.max_operations -= 1;
    assert_eq!(
        parse(source, &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.input.max_operations = usize::MAX;
    limits.input.max_input_bytes = source.len() - 1;
    assert_eq!(
        parse(source, &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
}
