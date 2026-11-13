// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::ErrorKind;
use fang_tptp_coverage_candidate::{Limits, parse};

#[test]
fn comments_preserve_the_ordered_ast_and_encoding() {
    let plain = b"fof(a,axiom,![X]:(p(X) => X = a)). cnf(b,axiom,(~p(a))).";
    let decorated = b"% header\r\nfof/*$note*/(a,axiom,![X]:/*x*/(p(X) => X = a)).\n/*body*/cnf(b,axiom,(~p(a))).% eof";
    let a = parse(plain, &Limits::default()).unwrap();
    let b = parse(decorated, &Limits::default()).unwrap();
    assert_eq!(a.functions, b.functions);
    assert_eq!(a.predicates, b.predicates);
    for (left, right) in a.declarations.iter().zip(&b.declarations) {
        assert_eq!(left.name, right.name);
        assert_eq!(left.variables, right.variables);
        assert_eq!(left.body, right.body);
    }
    let a = a.encode(100, 100).unwrap();
    let b = b.encode(100, 100).unwrap();
    assert_eq!(a.reservation.equality_id(), b.reservation.equality_id());
    for (left, right) in a.declarations.iter().zip(&b.declarations) {
        assert_eq!(left.body, right.body);
    }
}

#[test]
fn comments_preserve_byte_spans() {
    let source = b"/*lead*/fof/*tag*/(a,axiom,/*before*/p/*inside*/(a)/*after*/).%tail";
    let parsed = parse(source, &Limits::default()).unwrap();
    let d = &parsed.declarations[0];
    assert_eq!(
        &source[d.bytes.clone()],
        b"fof/*tag*/(a,axiom,/*before*/p/*inside*/(a)/*after*/)."
    );
    assert_eq!(&source[d.body_bytes.clone()], b"p/*inside*/(a)");
}

#[test]
fn comments_do_not_join_tokens_or_operators() {
    for input in [
        "fo/*c*/f(a,axiom,p).",
        "fof(a,axiom,p/*c*/q).",
        "fof(a,axiom,(p =/*c*/> q)).",
        "fof(a,axiom,a !/*c*/= b).",
    ] {
        assert!(
            parse(input.as_bytes(), &Limits::default()).is_err(),
            "{input}"
        );
    }
}

#[test]
fn first_block_terminator_wins_and_eof_lines_are_valid() {
    for input in [
        "",
        "% only",
        "%\r%\n",
        "/**/",
        "/*/* nested-looking text */",
    ] {
        assert!(
            parse(input.as_bytes(), &Limits::default())
                .unwrap()
                .declarations
                .is_empty()
        );
    }
    for input in ["/*", "/*x*", "/*x", "/*one*/ */"] {
        assert_eq!(
            parse(input.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::InvalidInput
        );
    }
}

#[test]
fn lower_words_allow_uppercase_tail_and_keep_case_identity() {
    let p = parse(
        b"fof(aA_1,axiom,![Xy_0]:(pA(fB(Xy_0)) & pa(fb(Xy_0)))).",
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(p.declarations[0].name, "aA_1");
    assert_eq!(p.declarations[0].variables, ["Xy_0"]);
    assert_eq!(
        p.functions
            .iter()
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>(),
        ["fB", "fb"]
    );
    assert_eq!(
        p.predicates
            .iter()
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>(),
        ["pA", "pa"]
    );
}

#[test]
fn comment_bytes_consume_exact_operation_credits() {
    for input in [b"%abc".as_slice(), b"/*abc*/", b"%a\r\n/**/"] {
        let mut limits = Limits::default();
        limits.input.max_operations = input.len();
        let p = parse(input, &limits).unwrap();
        assert_eq!(p.statistics.operations, input.len());
        limits.input.max_operations -= 1;
        assert_eq!(
            parse(input, &limits).unwrap_err().kind,
            ErrorKind::ResourceLimit
        );
        limits.input.max_operations = usize::MAX;
        limits.input.max_input_bytes = input.len() - 1;
        assert_eq!(
            parse(input, &limits).unwrap_err().kind,
            ErrorKind::ResourceLimit
        );
    }
}

#[test]
fn comment_transport_boundary_and_error_offsets_are_explicit() {
    for input in [b"%\xff".as_slice(), b"/*\xff*/", b"%\0", b"/*\0*/"] {
        assert_eq!(
            parse(input, &Limits::default()).unwrap_err().kind,
            ErrorKind::InvalidInput
        );
    }
    let error = parse(b"%head\n/* open", &Limits::default()).unwrap_err();
    assert_eq!(error.offset, Some(6));
}
