// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The numeric and defined-symbol profile: typed rejections, never symbols.

use fang::ErrorKind;
use fang_tptp_coverage_candidate::{Bundle, Limits, Reason, expand};

fn outcome(text: &str) -> Result<(), (ErrorKind, Reason, Option<usize>)> {
    expand(
        &Bundle::single(text.as_bytes().to_vec()),
        &Limits::default(),
    )
    .map(|_| ())
    .map_err(|error| (error.kind, error.reason, error.offset))
}

use ErrorKind::{InvalidInput as Invalid, Unsupported};

#[test]
fn table_rows_have_their_typed_outcome() {
    let rows: &[(&str, ErrorKind, Reason)] = &[
        ("fof(a,axiom,p(1)).", Unsupported, Reason::Number),
        ("fof(a,axiom,p(-7)).", Unsupported, Reason::Number),
        ("fof(a,axiom,p(1/2)).", Unsupported, Reason::Number),
        ("fof(a,axiom,p(-1/2)).", Unsupported, Reason::Number),
        ("fof(a,axiom,p(1.5)).", Unsupported, Reason::Number),
        ("fof(a,axiom,p(1.5e-3)).", Unsupported, Reason::Number),
        ("fof(a,axiom,p(007E2)).", Unsupported, Reason::Number),
        ("fof(a,axiom,1 = 2).", Unsupported, Reason::Number),
        ("fof(a,axiom,a = 2.0).", Unsupported, Reason::Number),
        ("fof(a,axiom,1).", Unsupported, Reason::Number),
        ("cnf(a,axiom,~ p(+3)).", Unsupported, Reason::Number),
        ("cnf(a,axiom,X != 0).", Unsupported, Reason::Number),
        ("fof(a,axiom,$less(a,b)).", Unsupported, Reason::Arithmetic),
        (
            "fof(a,axiom,$sum(a,b) = c).",
            Unsupported,
            Reason::Arithmetic,
        ),
        (
            "cnf(a,axiom,p($to_real(a))).",
            Unsupported,
            Reason::Arithmetic,
        ),
        (
            "fof(a,axiom,$distinct(a,b)).",
            Unsupported,
            Reason::TypedOnly,
        ),
        (
            "cnf(a,axiom,$distinct(a,b)).",
            Unsupported,
            Reason::TypedOnly,
        ),
        ("fof(a,axiom,$ite(p,q,r)).", Unsupported, Reason::TypedOnly),
        ("fof(a,axiom,p($i)).", Unsupported, Reason::TypedOnly),
        ("fof(a,axiom,$foo(a)).", Unsupported, Reason::UndefinedWord),
        ("fof(a,axiom,p($)).", Unsupported, Reason::UndefinedWord),
        ("fof(a,axiom,$$foo(a)).", Unsupported, Reason::System),
        ("fof(a,axiom,p($$c)).", Unsupported, Reason::System),
        ("fof(a,axiom,$fof(p)).", Invalid, Reason::Syntax),
        ("fof(a,axiom,p(`X)).", Unsupported, Reason::BackQuoted),
        ("tff(a,axiom,p).", Unsupported, Reason::Language),
        ("thf(a,axiom,p).", Unsupported, Reason::Language),
        ("tcf(a,axiom,p).", Unsupported, Reason::Language),
        ("tpi(a,axiom,p).", Unsupported, Reason::Language),
        ("fof(a,axiom,[p] --> [q]).", Unsupported, Reason::Sequent),
        ("fof(a,axiom,p --> q).", Unsupported, Reason::Sequent),
    ];
    for (text, kind, reason) in rows {
        let (actual_kind, actual_reason, _) = outcome(text).unwrap_err();
        assert_eq!((actual_kind, actual_reason), (*kind, *reason), "{text}");
    }
}

#[test]
fn numbers_in_every_position() {
    // Formula names and selections are names, not numbers.
    assert!(outcome("fof(12,axiom,p).").is_ok());
    assert!(outcome("fof(-0,axiom,p).").is_ok());
    for text in [
        "fof(1.5,axiom,p).",
        "fof(1/2,axiom,p).",
        "fof(a,1,p).",
        "fof(a,axiom,![1]:p).",
        "fof(01,axiom,p).",
        "fof(a,axiom,p(01)).",
        "fof(a,axiom,p(1/0)).",
        "fof(a,axiom,p(01/2)).",
        "fof(a,axiom,p(01.5)).",
    ] {
        assert_eq!(outcome(text).unwrap_err().0, Invalid, "{text}");
    }
    // Annotation numbers are metadata.
    assert!(outcome("fof(a,axiom,p,[1,-2,3/4,5.5,6e7,-8.9E-1]).").is_ok());
    // Exponent markers without digits end the number.
    assert_eq!(
        outcome("fof(a,axiom,p(1e)).").unwrap_err().1,
        Reason::Number
    );
    assert_eq!(outcome("fof(a,axiom,p(1.5e+)).").unwrap_err().0, Invalid);
}

#[test]
fn rejection_offsets_point_at_the_construct() {
    for (text, offset) in [
        ("fof(a,axiom,p(1.5)).", 14),
        ("fof(a,axiom,$less(a,b)).", 12),
        ("fof(a,axiom,p & $$x).", 16),
        ("fof(a,axiom,q(a) = 3/4).", 19),
    ] {
        assert_eq!(outcome(text).unwrap_err().2, Some(offset), "{text}");
    }
}

#[test]
fn defined_and_system_comments_are_comments() {
    assert!(outcome("%$ pragma\n/*$$Otter 3.3: Demodulator */ fof(a,axiom,p).").is_ok());
}
