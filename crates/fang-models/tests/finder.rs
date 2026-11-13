// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang_models::problem::{self, Task};
use fang_models::{Found, Settings, find};
use fang_tptp_coverage_candidate::Root;
use std::time::{Duration, Instant};

fn run(text: &str, task: Task, to: u32) -> Found {
    let problem = problem::load(vec![(
        Root::Base,
        "input.p".into(),
        text.as_bytes().to_vec(),
    )])
    .expect("input");
    let mut settings = Settings::new(Instant::now() + Duration::from_secs(20));
    settings.to = to;
    settings.self_check = true;
    find(&problem, task, &settings).expect("task")
}

fn certificate(found: Found) -> (u32, String) {
    match found {
        Found::Certificate { size, text, .. } => (size, text),
        other => panic!("no model: {other:?}"),
    }
}

#[test]
fn two_elements_for_a_predicate_and_its_negation() {
    let (size, text) = certificate(run(
        "fof(a,axiom,? [X] : p(X)).\nfof(b,axiom,? [X] : ~ p(X)).\n",
        Task::All,
        4,
    ));
    assert_eq!(size, 2);
    assert!(text.starts_with("fang-model 1\ndomain 2\n") && text.ends_with("end\n"));
    // Only the input predicate has a table; the Skolem constants do not.
    assert_eq!(
        text.lines()
            .filter(|line| line.starts_with("predicate 70 1 "))
            .count(),
        1
    );
    assert!(!text.contains("function"));
}

#[test]
fn contradiction_has_no_model() {
    match run("fof(a,axiom,p).\nfof(b,axiom,~ p).\n", Task::All, 4) {
        Found::Exhausted { last } => assert_eq!(last, 4),
        other => panic!("{other:?}"),
    }
}

#[test]
fn distinct_objects_get_different_elements() {
    let (size, text) = certificate(run("fof(a,axiom,f(\"x\") = \"y\").\n", Task::All, 4));
    assert_eq!(size, 2);
    // "x" and "y" are named with their leading 0x00 byte.
    assert!(text.contains("function 0078 0 dense"));
    assert!(text.contains("function 0079 0 dense"));
}

#[test]
fn countermodel_makes_the_goal_false() {
    let input = "fof(a,axiom,p(c)).\nfof(g,conjecture,q(c)).\n";
    match run(input, Task::Goal(0), 4) {
        Found::Certificate { size, item, .. } => {
            assert_eq!(size, 1);
            assert_eq!(item, Some((0, 1)));
        }
        other => panic!("{other:?}"),
    }
}

#[test]
fn entailed_goal_has_no_countermodel() {
    let input =
        "fof(a,axiom,! [X] : (p(X) => q(X))).\nfof(b,axiom,p(c)).\nfof(g,conjecture,q(c)).\n";
    assert!(matches!(
        run(input, Task::Goal(0), 5),
        Found::Exhausted { last: 5 }
    ));
}

#[test]
fn equations_and_nested_terms() {
    // A group of order two where the generator is not the identity.
    let input = "fof(identity,axiom,! [X] : f(e,X) = X).\n\
                 fof(inverse,axiom,! [X] : f(i(X),X) = e).\n\
                 fof(associative,axiom,! [X,Y,Z] : f(f(X,Y),Z) = f(X,f(Y,Z))).\n\
                 fof(generator,axiom,g != e).\n";
    let (size, _) = certificate(run(input, Task::All, 4));
    assert_eq!(size, 2);
}
