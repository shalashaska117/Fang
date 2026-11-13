// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang_axiom_audit::{
    audit_axioms, check_suite_audit, parse_build_audit, python_strip, reports, self_test,
    strip_reports,
};

#[test]
fn python_controls_pass() {
    let result = self_test().unwrap();
    assert_eq!(result.get("controls").unwrap().as_i64(), Some(9));
}

#[test]
fn audit_results_and_messages() {
    let output = "'A' depends on axioms: [Quot.sound, propext]\nnoise\n'B' does not depend on any axioms\n'A' depends on axioms: [propext, Quot.sound]";
    let result = audit_axioms(output, &["A", "B"]).unwrap();
    assert_eq!(
        result,
        vec![
            (
                "A".to_owned(),
                vec!["Quot.sound".to_owned(), "propext".to_owned()]
            ),
            ("B".to_owned(), vec![])
        ]
    );
    assert_eq!(
        audit_axioms("'A' depends on axioms: [b, a, propext]", &["A"])
            .unwrap_err()
            .0,
        "Unexpected axioms for A: ['a', 'b']"
    );
    assert_eq!(
        audit_axioms("'A' does not depend on any axioms", &["A", "C", "B"])
            .unwrap_err()
            .0,
        "Missing Lean theorem audits: ['B', 'C']"
    );
    assert_eq!(
        audit_axioms(
            "'A' depends on axioms: [propext]\n'A' does not depend on any axioms",
            &["A"]
        )
        .unwrap_err()
        .0,
        "Conflicting axiom reports for A"
    );
    assert_eq!(
        audit_axioms("x", &[]).unwrap_err().0,
        "At least one theorem must be required by the audit"
    );
    assert_eq!(
        audit_axioms("'A' does not depend on any axioms sorryAx", &["A"])
            .unwrap_err()
            .0,
        "Lean audit contains sorryAx"
    );
}

#[test]
fn spans_and_strip_follow_finditer() {
    let output = "pre 'a' foo 'B'\u{a0}\tdepends on axioms:\n[propext] mid 'C' does not depend on any axioms post";
    let found = reports(output);
    assert_eq!(found.len(), 2);
    assert_eq!(found[0].name, "B");
    assert_eq!(found[0].axioms.as_deref(), Some("propext"));
    assert_eq!(found[1].name, "C");
    assert_eq!(found[1].axioms, None);
    assert_eq!(strip_reports(output), "pre 'a' foo  mid  post");
    assert_eq!(
        python_strip(strip_reports(output).as_str()),
        "pre 'a' foo  mid  post"
    );
    assert!(reports("'a\nb' does not depend on any axioms").is_empty());
}

#[test]
fn build_audit_is_exact() {
    let text = "'A' depends on axioms: [propext, Quot.sound]\n'B' does not depend on any axioms\n";
    let recorded = [
        ("A", vec!["propext".to_owned(), "Quot.sound".to_owned()]),
        ("B", vec![]),
    ];
    let result = parse_build_audit(text, &["B", "A"], &recorded).unwrap();
    assert_eq!(
        result[0].1,
        vec!["Quot.sound".to_owned(), "propext".to_owned()]
    );
    for (bad, message) in [
        (
            "x'A' does not depend on any axioms\n",
            "Unexpected audit output",
        ),
        (
            "'A' does not depend on any axioms\n\n",
            "Unexpected trailing audit output",
        ),
        (
            "'A' does not depend on any axioms",
            "Unexpected trailing audit output",
        ),
        (
            "'A' does not depend on any axioms\n'A' does not depend on any axioms\n",
            "Duplicate audit report: A",
        ),
        (
            "'A' depends on axioms: [propext, x]\n",
            "Nonstandard axiom in A: ['propext', 'x']",
        ),
        (
            "'A' depends on axioms: []\n",
            "Nonstandard axiom in A: ['']",
        ),
        (
            "'A' does not depend on any axioms\n",
            "Audit reports differ from the fixed audit list",
        ),
        (
            "'A' does not depend on any axioms\n'B' does not depend on any axioms\n",
            "Axioms differ from the gate record: A",
        ),
        (
            "'A' depends on axioms: [sorryAx]\n",
            "Audit output mentions sorryAx",
        ),
    ] {
        assert_eq!(
            parse_build_audit(bad, &["A", "B"], &recorded)
                .unwrap_err()
                .0,
            message,
            "text {bad:?}"
        );
    }
}

#[test]
fn check_suite_reads_depends_then_none() {
    let text = "'Z' does not depend on any axioms\n'Y' depends on axioms: [propext, propext,\n Quot.sound]";
    let result = check_suite_audit(text, "M").unwrap();
    assert_eq!(
        result,
        vec![
            (
                "Y".to_owned(),
                vec!["Quot.sound".to_owned(), "propext".to_owned()]
            ),
            ("Z".to_owned(), vec![])
        ]
    );
    assert_eq!(
        check_suite_audit("'Y' depends on axioms: [b, a]", "M")
            .unwrap_err()
            .0,
        "Unexpected assumptions for Y: {'a', 'b'}"
    );
    assert_eq!(
        check_suite_audit("sorryAx", "M").unwrap_err().0,
        "Unexpected sorryAx in M"
    );
}
