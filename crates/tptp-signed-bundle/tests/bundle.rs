// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang_tptp_coverage_candidate::{Bundle, Root};
use fang_tptp_full_frontend_candidate::Role;
use fang_tptp_signed_bundle::{
    Error, flatten, flatten_kept, neutral_roles, premise_line, prepare_bundle_task,
    prepare_cited_task, produce_bundle_task, produce_cited_task, sealed,
};
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

/// Origins index the declarations of the flat text: the expanded records, then the generated disequalities.
#[test]
fn bundle_origins_index_the_flat_text() {
    let files = [
        (
            "input",
            "include('ax.ax').fof(g,conjecture,\"x\" != \"y\").",
        ),
        (
            "ax.ax",
            "fof(a,axiom,p(\"x\") & p(\"y\")).cnf(n,axiom,$true|q).",
        ),
    ];
    let (flat, prepared) =
        prepare_bundle_task(&bundle(&files), Selection::Goal(0), &Limits::default()).unwrap();
    assert_eq!(flat.distinct_clauses, 1);
    let mut next = 0;
    for origin in &prepared.origins {
        assert_eq!(origin.clauses.start, next);
        next = origin.clauses.end;
    }
    assert_eq!(next, prepared.clauses.len());
    let shape: Vec<(usize, Role, bool, usize)> = prepared
        .origins
        .iter()
        .map(|origin| {
            (
                origin.source_index,
                origin.role,
                origin.positive,
                origin.clauses.len(),
            )
        })
        .collect();
    assert_eq!(
        shape,
        vec![
            (0, Role::Axiom, true, 2),
            (1, Role::Axiom, true, 0),
            (2, Role::Conjecture, false, 1),
            (3, Role::Axiom, true, 1),
        ]
    );
}

#[test]
fn premise_line_is_canonical() {
    assert_eq!(
        premise_line(&[(0, 12), (1, 7)]),
        "(premises (item 0 12) (item 1 7))"
    );
    assert_eq!(premise_line(&[]), "(premises)");
}

/// The kept text holds the cited records and the goal in expansion order, under their names in the whole expansion, with disequalities over their own objects only.
#[test]
fn kept_text_keeps_cited_records_and_their_objects() {
    let files = [
        (
            "input",
            "include('ax.ax').fof(g,conjecture,\"x\" != \"y\").",
        ),
        (
            "ax.ax",
            "fof(a,axiom,p(\"x\") & p(\"y\")).fof(b,axiom,q(\"z\")).fof(c,axiom,r).",
        ),
    ];
    let whole = flatten(&bundle(&files), &Limits::default()).unwrap();
    assert_eq!(whole.items, vec![(1, 0), (1, 1), (1, 2), (0, 1)]);
    assert_eq!(whole.distinct_clauses, 3);
    let kept = flatten_kept(&bundle(&files), &Limits::default(), &[(1, 0)], Some((0, 1))).unwrap();
    assert_eq!(kept.items, vec![(1, 0), (0, 1)]);
    assert_eq!(kept.goals, vec![(0, 1)]);
    assert_eq!(kept.distinct_clauses, 1);
    assert!(kept.text.starts_with("fof(fang_bundle_0,axiom,"));
    assert!(kept.text.contains("fof(fang_bundle_3,conjecture,"));
}

/// A goal task over cited premises only is produced; the citations come back in expansion order.
#[test]
fn cited_goal_task_is_produced() {
    let files = [
        ("input", "include('ax.ax').fof(g,conjecture,q)."),
        ("ax.ax", "fof(a,axiom,p).fof(b,axiom,p=>q).fof(c,axiom,r)."),
    ];
    let (citations, kept, produced) = produce_cited_task(
        &bundle(&files),
        Selection::Goal(0),
        &[(1, 1), (1, 0)],
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(citations, vec![(1, 0), (1, 1)]);
    assert_eq!(kept.items, vec![(1, 0), (1, 1), (0, 1)]);
    assert!(matches!(
        produced.outcome,
        Outcome::CandidateRefutation { .. }
    ));
}

/// A citation must be an expanded premise: another conjecture, the goal itself and an unknown item are refused.
#[test]
fn citations_must_be_expanded_premises() {
    let files = [
        (
            "input",
            "include('ax.ax').fof(g,conjecture,q).fof(h,conjecture,p).",
        ),
        ("ax.ax", "fof(a,axiom,p).fof(b,axiom,p=>q)."),
    ];
    for cited in [vec![(0, 2)], vec![(1, 5)], vec![(0, 1)]] {
        let error = prepare_cited_task(
            &bundle(&files),
            Selection::Goal(0),
            &cited,
            &Limits::default(),
        )
        .unwrap_err();
        assert_eq!(fang_tptp_signed_bundle::error_kind(&error), "citation");
    }
}

#[test]
fn repeated_expansion_citations_are_canonical_and_goal_selection_is_checked() {
    let files = bundle(&[
        (
            "input",
            "include('ax.ax').include('ax.ax').fof(g,conjecture,p).",
        ),
        ("ax.ax", "fof(a,axiom,p).fof(b,axiom,q)."),
    ]);
    let limits = Limits::default();
    let (cited, kept, _) = prepare_cited_task(
        &files,
        Selection::Goal(0),
        &[(1, 1), (1, 0), (1, 1)],
        &limits,
    )
    .unwrap();
    assert_eq!(cited, vec![(1, 0), (1, 1)]);
    assert_eq!(kept.items, vec![(1, 0), (1, 1), (0, 2)]);
    assert!(matches!(
        prepare_cited_task(&files, Selection::Goal(1), &[(1, 0)], &limits),
        Err(Error::Signed(fang_tptp_signed_roles::Error::NoGoal))
    ));
    assert!(matches!(
        prepare_cited_task(&files, Selection::Goal(0), &[(0, 2)], &limits),
        Err(Error::Citation((0, 2)))
    ));
}

#[test]
fn bundle_formulas_are_read_to_the_task_height() {
    let deep = format!(
        "fof(a,axiom,({})).fof(g,conjecture,p).",
        vec!["p"; 100].join("&")
    );
    let files = bundle(&[("input", "include('deep.ax')."), ("deep.ax", &deep)]);
    assert!(matches!(
        flatten(&files, &Limits::default()),
        Err(Error::Expansion(_))
    ));
    let mut limits = Limits::default();
    limits.input.max_formula_depth = 128;
    let flat = flatten(&files, &limits).unwrap();
    assert_eq!(flat.items, vec![(1, 0), (1, 1)]);
}
