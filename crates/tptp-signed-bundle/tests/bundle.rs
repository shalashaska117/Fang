// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang_tptp_coverage_candidate::{Bundle, Root};
use fang_tptp_signed_bundle::{Error, flatten, neutral_roles, produce_bundle_task, sealed};
use fang_tptp_signed_roles::{Limits, Outcome, Selection};

fn bundle(files: &[(&str, &str)]) -> Bundle {
    sealed(
        files
            .iter()
            .map(|(path, text)| (Root::Base, path.to_string(), text.as_bytes().to_vec()))
            .collect(),
    )
}

fn candidate(files: &[(&str, &str)], selection: Selection) -> bool {
    let (_, produced) = produce_bundle_task(&bundle(files), selection, &Limits::default()).unwrap();
    matches!(produced.outcome, Outcome::CandidateRefutation { .. })
}

#[test]
fn roles_are_neutralized_by_statement() {
    let (bytes, roles) = neutral_roles(
        b"include('a.ax').\nfof(g , conjecture, p). % c\ncnf('x y',negated_conjecture,q).",
        0,
    )
    .unwrap();
    assert_eq!(
        String::from_utf8(bytes).unwrap(),
        "include('a.ax').\nfof(g , axiom, p). % c\ncnf('x y',axiom,q)."
    );
    assert_eq!(roles.get(&1).map(String::as_str), Some("conjecture"));
    assert_eq!(
        roles.get(&2).map(String::as_str),
        Some("negated_conjecture")
    );
    assert!(!roles.contains_key(&0));
}

#[test]
fn included_goal_keeps_its_item_and_is_proved() {
    let files = [
        ("input", "include('ax.ax').fof(a,axiom,p)."),
        ("ax.ax", "fof(b,axiom,p=>q).fof(g,conjecture,q)."),
    ];
    let flat = flatten(&bundle(&files), &Limits::default()).unwrap();
    assert_eq!(flat.goals, vec![(1, 1)]);
    assert!(candidate(&files, Selection::Goal(0)));
}

#[test]
fn unselected_conjecture_is_not_a_goal() {
    let files = [
        ("input", "include('ax.ax',[b]).fof(a,axiom,p)."),
        ("ax.ax", "fof(b,axiom,q).fof(g,conjecture,r)."),
    ];
    let flat = flatten(&bundle(&files), &Limits::default()).unwrap();
    assert!(flat.goals.is_empty());
    assert!(!flat.text.contains("conjecture"));
}

#[test]
fn distinct_objects_prove_a_disequality() {
    let files = [(
        "input",
        "fof(a,axiom,p(\"x\") & p(\"y\")).fof(g,conjecture,\"y\" != \"x\").",
    )];
    let flat = flatten(&bundle(&files), &Limits::default()).unwrap();
    assert_eq!(flat.distinct_clauses, 1);
    assert!(candidate(&files, Selection::Goal(0)));
}

#[test]
fn objects_follow_the_function_table() {
    let files = [(
        "input",
        "fof(a,axiom,q(\"b\",f(\"a\"))).fof(c,axiom,r(\"c\")).",
    )];
    let flat = flatten(&bundle(&files), &Limits::default()).unwrap();
    assert_eq!(flat.distinct_clauses, 3);
    let generated: Vec<&str> = flat
        .text
        .lines()
        .filter(|line| line.starts_with("cnf(fang_distinct"))
        .collect();
    assert_eq!(
        generated,
        [
            "cnf(fang_distinct_0_1,axiom,fang_object_0 != fang_object_1).",
            "cnf(fang_distinct_0_2,axiom,fang_object_0 != fang_object_2).",
            "cnf(fang_distinct_1_2,axiom,fang_object_1 != fang_object_2).",
        ]
    );
}

#[test]
fn inputs_task_refuses_a_selected_goal() {
    let files = [
        ("input", "include('ax.ax').fof(a,axiom,p)."),
        ("ax.ax", "fof(g,conjecture,p)."),
    ];
    let error =
        produce_bundle_task(&bundle(&files), Selection::Inputs, &Limits::default()).unwrap_err();
    assert!(matches!(
        error,
        Error::Signed(fang_tptp_signed_roles::Error::GoalsPresent)
    ));
}

#[test]
fn missing_include_is_typed() {
    let error = flatten(
        &bundle(&[("input", "include('nope.ax').")]),
        &Limits::default(),
    )
    .unwrap_err();
    assert_eq!(fang_tptp_signed_bundle::error_kind(&error), "missing");
}

#[test]
fn mixed_goal_modes_are_typed() {
    let files = [
        ("input", "include('ax.ax').fof(g,conjecture,p)."),
        ("ax.ax", "cnf(n,negated_conjecture,~q)."),
    ];
    let error = flatten(&bundle(&files), &Limits::default()).unwrap_err();
    assert_eq!(fang_tptp_signed_bundle::error_kind(&error), "modes");
}

/// Comment lines of about `bytes` bytes; inside a record body the flat text copies them.
fn filler(bytes: usize) -> String {
    let line = format!("% {}\n", "x".repeat(77));
    line.repeat(bytes / line.len() + 1)
}

#[test]
fn bundle_over_one_mebibyte_is_produced() {
    let top = format!(
        "include('ax.ax').fof(g,conjecture,(q\n{})).",
        filler(600 << 10)
    );
    let axioms = format!("fof(a,axiom,(p\n{})).fof(b,axiom,p=>q).", filler(600 << 10));
    assert!(top.len() < 1 << 20 && axioms.len() < 1 << 20);
    assert!(top.len() + axioms.len() > 1 << 20);
    let files = [("input", top.as_str()), ("ax.ax", axioms.as_str())];
    let flat = flatten(&bundle(&files), &Limits::default()).unwrap();
    assert!(flat.text.len() > 1 << 20);
    assert!(candidate(&files, Selection::Goal(0)));
}

/// One file of 1,002 records: 1,000 premises that clausify to nothing, one unit premise and the goal.
#[test]
fn more_than_one_thousand_records_are_produced() {
    let mut text: String = (0..1000)
        .map(|index| format!("cnf(t{index},axiom,$true|p)."))
        .collect();
    text.push_str("cnf(a,axiom,p).fof(g,conjecture,p).");
    let files = [("input", text.as_str())];
    let flat = flatten(&bundle(&files), &Limits::default()).unwrap();
    assert_eq!(flat.goals, vec![(0, 1001)]);
    assert!(candidate(&files, Selection::Goal(0)));
}

/// The expansion accepts 1,001 unit premises; the search then refuses more than 1,000 prepared clauses.
#[test]
fn prepared_clauses_over_the_search_bound_are_refused() {
    let mut text: String = (0..1001)
        .map(|index| format!("cnf(a{index},axiom,p{}).", index % 5))
        .collect();
    text.push_str("fof(g,conjecture,p0).");
    let files = [("input", text.as_str())];
    let flat = flatten(&bundle(&files), &Limits::default()).unwrap();
    assert_eq!(flat.goals, vec![(0, 1001)]);
    let error =
        produce_bundle_task(&bundle(&files), Selection::Goal(0), &Limits::default()).unwrap_err();
    assert!(matches!(
        error,
        Error::Signed(fang_tptp_signed_roles::Error::Search(
            fang_equality_search::PreparedError::Resource("prepared clause limit")
        ))
    ));
}
