// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang_equality_inference_core::Atom;
use fang_tptp_signed_roles::{
    Error, HEADER, Limits, Outcome, Selection, goal_count, prepare_task, produce_task,
};

fn candidate(input: &[u8], selection: Selection) -> bool {
    let produced = produce_task(input, selection, &Limits::default()).unwrap();
    match produced.outcome {
        Outcome::CandidateRefutation { text, .. } => {
            assert!(text.starts_with(HEADER));
            true
        }
        Outcome::Unknown(_) => false,
    }
}

#[test]
fn goal_task_produces_a_version_8_candidate() {
    let input = b"fof(a,axiom,![X]:(p(X)=>q(X))).fof(b,axiom,p(c)).fof(g,conjecture,?[Y]:q(Y)).";
    assert!(candidate(input, Selection::Goal(0)));
}

#[test]
fn each_goal_gets_its_own_candidate() {
    let input = b"fof(a,axiom,(p&q)).fof(g,conjecture,p).fof(h,conjecture,q).";
    assert!(candidate(input, Selection::Goal(0)));
    assert!(candidate(input, Selection::Goal(1)));
}

#[test]
fn non_theorem_goal_is_unknown() {
    assert!(!candidate(
        b"fof(a,axiom,p).fof(g,conjecture,q).",
        Selection::Goal(0)
    ));
}

#[test]
fn inputs_task_is_candidate_or_unknown() {
    assert!(candidate(
        b"cnf(a,axiom,p).cnf(n,negated_conjecture,~p).",
        Selection::Inputs
    ));
    assert!(!candidate(b"cnf(a,axiom,p).", Selection::Inputs));
}

const TWO_GOALS: &[u8] =
    b"fof(a,axiom,p).fof(g,conjecture,q).cnf(b,hypothesis,r|~p).fof(h,conjecture,s).";

#[test]
fn one_negative_declaration_per_goal_task() {
    let limits = Limits::default();
    assert_eq!(goal_count(TWO_GOALS, &limits).unwrap(), 2);
    let first = prepare_task(TWO_GOALS, Selection::Goal(0), &limits).unwrap();
    assert_eq!(first.goal, Some(1));
    assert_eq!(first.signs, vec![(0, true), (1, false)]);
    let second = prepare_task(TWO_GOALS, Selection::Goal(1), &limits).unwrap();
    assert_eq!(second.goal, Some(3));
    assert_eq!(second.signs, vec![(0, true), (3, false)]);
}

#[test]
fn goal_keeps_source_position_and_cnf_premises() {
    let limits = Limits::default();
    let task = prepare_task(TWO_GOALS, Selection::Goal(0), &limits).unwrap();
    // p, then the negated goal q, then the CNF premise r | ~p; predicates p, q, r, s.
    assert_eq!(task.clauses.len(), 3);
    assert_eq!(task.clauses[0].len(), 1);
    assert!(task.clauses[0][0].positive);
    assert_eq!(task.clauses[1].len(), 1);
    assert!(!task.clauses[1][0].positive);
    assert_eq!(task.clauses[1][0].atom, Atom::Predicate(1, vec![]));
    assert_eq!(task.clauses[2].len(), 2);
    assert_eq!(task.predicate_arities, vec![0, 0, 0, 0]);
}

#[test]
fn negative_goal_goes_through_the_skolem_entry() {
    let limits = Limits::default();
    let input = b"fof(a,axiom,![X]:(p(X)=>q(X))).fof(b,axiom,p(c)).fof(g,conjecture,?[Y]:q(Y)).";
    let task = prepare_task(input, Selection::Goal(0), &limits).unwrap();
    assert_eq!(task.signs, vec![(0, true), (1, true), (2, false)]);
    // The negated existential goal becomes one universal negative unit clause.
    let goal = task.clauses.last().unwrap();
    assert_eq!(goal.len(), 1);
    assert!(!goal[0].positive);
    assert!(matches!(&goal[0].atom, Atom::Predicate(1, arguments) if arguments.len() == 1));
}

#[test]
fn existential_goal_is_skolemized_only_when_negated_universal() {
    let limits = Limits::default();
    // Negating a universal goal introduces one Skolem constant.
    let task = prepare_task(b"fof(g,conjecture,![X]:p(X)).", Selection::Goal(0), &limits).unwrap();
    assert_eq!(task.function_arities, vec![0]);
    // Negating an existential goal introduces none.
    let task = prepare_task(b"fof(g,conjecture,?[X]:p(X)).", Selection::Goal(0), &limits).unwrap();
    assert!(task.function_arities.is_empty());
}

#[test]
fn equality_goal_uses_native_equality() {
    let limits = Limits::default();
    let task = prepare_task(
        b"fof(a,axiom,a=b).fof(g,conjecture,b=a).",
        Selection::Goal(0),
        &limits,
    )
    .unwrap();
    assert_eq!(task.clauses.len(), 2);
    assert!(matches!(task.clauses[1][0].atom, Atom::Equal(_, _)));
    assert!(!task.clauses[1][0].positive);
}

#[test]
fn selection_rejections_are_typed() {
    let limits = Limits::default();
    assert!(matches!(
        prepare_task(TWO_GOALS, Selection::Goal(2), &limits),
        Err(Error::NoGoal)
    ));
    assert!(matches!(
        prepare_task(TWO_GOALS, Selection::Inputs, &limits),
        Err(Error::GoalsPresent)
    ));
    assert!(matches!(
        prepare_task(b"cnf(g,conjecture,p).", Selection::Goal(0), &limits),
        Err(Error::Input(_))
    ));
}

#[test]
fn no_goal_task_keeps_negated_conjectures_positive() {
    let limits = Limits::default();
    let input = b"cnf(a,axiom,p).cnf(n,negated_conjecture,~p).";
    assert_eq!(goal_count(input, &limits).unwrap(), 0);
    let task = prepare_task(input, Selection::Inputs, &limits).unwrap();
    assert!(task.goal.is_none());
    assert!(task.signs.is_empty());
    assert_eq!(task.clauses.len(), 2);
}

#[test]
fn true_cnf_premise_has_no_clause() {
    let limits = Limits::default();
    let task = prepare_task(
        b"cnf(t,axiom,$true|p).fof(g,conjecture,p).",
        Selection::Goal(0),
        &limits,
    )
    .unwrap();
    assert_eq!(task.clauses.len(), 1);
}
