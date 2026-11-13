// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Small refutations under every preset. Each certificate is replayed step by step through the reviewed Rust
//! reconstruction while it is written, so these tests also check the step mapping of DESIGN.md section (a).

use crate::kbo::{Cmp, Order, Precedence};
use crate::options::Options;
use crate::producer::{Mode, split};
use crate::proof::HEADER;
use crate::search::{Limits, Search, Stop};
use crate::subst::{Bindings, Renamer};
use crate::term::Bank;
use fang::syntax::Term;
use fang_equality_inference_core::{Atom, Clause, Literal};
use std::time::Instant;

fn constant(id: u32) -> Term {
    Term::Fun(id, vec![])
}

fn app(id: u32, arguments: Vec<Term>) -> Term {
    Term::Fun(id, arguments)
}

fn var(id: u32) -> Term {
    Term::Var(id)
}

fn pred(positive: bool, predicate: u32, arguments: Vec<Term>) -> Literal {
    Literal {
        positive,
        atom: Atom::Predicate(predicate, arguments),
    }
}

fn eq(positive: bool, left: Term, right: Term) -> Literal {
    Literal {
        positive,
        atom: Atom::Equal(left, right),
    }
}

const PRESETS: [&str; 5] = ["step1", "step2", "step3", "step4", "step5"];

fn cited_task() -> fang_tptp_signed_roles::Prepared {
    fang_tptp_signed_roles::prepare_task(
        b"fof(unused,axiom,r(b)). fof(fact,axiom,p(a)). fof(rule,axiom,![X]:(p(X)=>q(X))). fof(goal,conjecture,q(a)).",
        fang_tptp_signed_roles::Selection::Goal(0),
        &fang_tptp_signed_roles::Limits::default(),
    )
    .expect("prepared signed task")
}

fn kept_cited_task() -> fang_tptp_signed_roles::Prepared {
    fang_tptp_signed_roles::prepare_task(
        b"fof(fact,axiom,p(a)). fof(rule,axiom,![X]:(p(X)=>q(X))). fof(goal,conjecture,q(a)).",
        fang_tptp_signed_roles::Selection::Goal(0),
        &fang_tptp_signed_roles::Limits::default(),
    )
    .expect("prepared kept task")
}

#[test]
fn prepared_portfolio_keeps_original_input_indices_after_a_stopped_slice() {
    use crate::producer::{Refutation, refute_prepared, refute_prepared_portfolio};
    let prepared = cited_task();
    let mut stopped = Options::preset("step5").unwrap();
    stopped.given_limit = Some(0);
    assert!(matches!(
        refute_prepared(&prepared, &stopped, None, None),
        Refutation::Stopped(_)
    ));
    let mut options = Options::preset("step5").unwrap();
    options.portfolio = vec![(1, stopped), (1, options.clone())];
    let Refutation::Candidate { inputs, .. } =
        refute_prepared_portfolio(&prepared, &options, None, None)
    else {
        panic!("second slice should refute the task");
    };
    assert!(inputs.windows(2).all(|pair| pair[0] < pair[1]));
    let sources: std::collections::BTreeSet<_> = inputs
        .iter()
        .map(|index| {
            prepared
                .origins
                .iter()
                .find(|origin| origin.clauses.contains(index))
                .expect("input has an origin")
                .source_index
        })
        .collect();
    assert_eq!(sources, [1, 2, 3].into_iter().collect());
}

#[test]
fn prepared_portfolio_does_not_restart_an_expired_budget() {
    use crate::producer::{Refutation, refute_prepared_portfolio};
    let prepared = cited_task();
    let options = Options::preset("step5").unwrap();
    assert!(matches!(
        refute_prepared_portfolio(&prepared, &options, Some(Instant::now()), None),
        Refutation::Stopped("time limit")
    ));
}

#[test]
fn prepared_portfolio_cited_replays_the_kept_task_and_never_returns_first_proof() {
    use crate::producer::{Refutation, refute_prepared_portfolio};
    let options = Options::preset("step5").unwrap();
    let Refutation::Candidate {
        text: discovery_text,
        ..
    } = refute_prepared_portfolio(&cited_task(), &options, None, None)
    else {
        panic!("discovery should refute");
    };
    let Refutation::Candidate {
        text: expected_text,
        ..
    } = refute_prepared_portfolio(&kept_cited_task(), &options, None, None)
    else {
        panic!("kept task should refute");
    };
    assert_ne!(
        discovery_text, expected_text,
        "the kept task has different numbering"
    );
    let result = crate::cited::refute(
        cited_task(),
        &options,
        None,
        None,
        None,
        |prepared, inputs| {
            let sources: std::collections::BTreeSet<_> = inputs
                .iter()
                .map(|index| {
                    prepared
                        .origins
                        .iter()
                        .find(|origin| origin.clauses.contains(index))
                        .unwrap()
                        .source_index
                })
                .filter(|source| Some(*source) != prepared.goal)
                .collect();
            Ok::<_, &'static str>(sources.into_iter().collect::<Vec<_>>())
        },
        |premises| {
            assert_eq!(premises, [1, 2]);
            Ok(kept_cited_task())
        },
    )
    .expect("kept task refuted");
    assert_eq!(result.premises, [1, 2]);
    assert_eq!(result.text, expected_text);
    assert_ne!(result.text, discovery_text);
    let failed = crate::cited::refute(
        cited_task(),
        &options,
        None,
        None,
        None,
        |_, _| Ok::<_, &'static str>(vec![1usize]),
        |_| Err("kept task refused"),
    );
    assert!(matches!(
        failed,
        Err(crate::cited::Error::Preparation("kept task refused"))
    ));
    let unrefutable = crate::cited::refute(
        cited_task(),
        &options,
        None,
        None,
        None,
        |_, _| Ok::<_, &'static str>(vec![1usize]),
        |_| {
            fang_tptp_signed_roles::prepare_task(
                b"fof(fact,axiom,p(a)). fof(goal,conjecture,q(a)).",
                fang_tptp_signed_roles::Selection::Goal(0),
                &fang_tptp_signed_roles::Limits::default(),
            )
            .map_err(|_| "kept preparation")
        },
    );
    assert!(matches!(
        unrefutable,
        Err(crate::cited::Error::Replay(Refutation::Unknown { .. }))
    ));
}

#[test]
fn prepared_portfolio_unknown_keeps_actual_final_slice_counters() {
    use crate::producer::{Refutation, refute_prepared, refute_prepared_portfolio};
    let prepared = fang_tptp_signed_roles::prepare_task(
        b"fof(a,axiom,p(a)). fof(b,axiom,![X]:(p(X)=>q(X))).",
        fang_tptp_signed_roles::Selection::Inputs,
        &fang_tptp_signed_roles::Limits::default(),
    )
    .unwrap();
    let options = Options::preset("step5").unwrap();
    let Refutation::Unknown {
        processed,
        attempted,
    } = refute_prepared(&prepared, &options, None, None)
    else {
        panic!("satisfiable task must not yield a refutation");
    };
    assert!(processed >= 2);
    assert!(attempted > 0);
    let mut stopped = options.clone();
    stopped.given_limit = Some(0);
    let mut portfolio = options.clone();
    portfolio.portfolio = vec![(1, stopped), (1, options)];
    assert!(matches!(
        refute_prepared_portfolio(&prepared, &portfolio, None, None),
        Refutation::Unknown { processed: p, attempted: a } if p == processed && a == attempted
    ));
}

fn prove(clauses: &[Clause], functions: &[usize], predicates: &[usize], preset: &str) -> String {
    let options = Options::from_settings(&[("preset".into(), preset.into())]).expect("preset");
    let mut search = Search::new(clauses, functions, predicates, &options, Limits::default())
        .expect("valid input");
    match search.run() {
        Stop::Proof(empty) => {
            let certificate = search.certificate(empty, 1 << 20).expect("certificate");
            assert!(certificate.text.starts_with(HEADER));
            assert!(certificate.text.ends_with("))\n"));
            assert_eq!(certificate.unchecked, 0, "every step replayed");
            certificate.text
        }
        other => panic!("{preset}: no refutation, {other:?}"),
    }
}

#[test]
fn resolution_chain() {
    // P(a), ~P(x) | Q(x), ~Q(a); functions: a; predicates: P, Q.
    let clauses = vec![
        vec![pred(true, 0, vec![constant(0)])],
        vec![pred(false, 0, vec![var(0)]), pred(true, 1, vec![var(0)])],
        vec![pred(false, 1, vec![constant(0)])],
    ];
    for preset in PRESETS {
        let text = prove(&clauses, &[0], &[1, 1], preset);
        assert!(text.contains("(resolve "), "{preset}: {text}");
    }
}

#[test]
fn superposition_into_predicate() {
    // f(a) = b, P(f(a)), ~P(b); functions: a, b, f.
    let clauses = vec![
        vec![eq(true, app(2, vec![constant(0)]), constant(1))],
        vec![pred(true, 0, vec![app(2, vec![constant(0)])])],
        vec![pred(false, 0, vec![constant(1)])],
    ];
    for preset in PRESETS {
        let text = prove(&clauses, &[0, 0, 1], &[1], preset);
        assert!(text.contains("(paramodulate "), "{preset}: {text}");
    }
}

#[test]
fn rewriting_to_normal_form() {
    // f(x) = x, P(f(f(a))), ~P(a).
    let clauses = vec![
        vec![eq(true, app(1, vec![var(0)]), var(0))],
        vec![pred(true, 0, vec![app(1, vec![app(1, vec![constant(0)])])])],
        vec![pred(false, 0, vec![constant(0)])],
    ];
    for preset in PRESETS {
        prove(&clauses, &[0, 1], &[1], preset);
    }
}

#[test]
fn equality_resolution_and_original_variable_numbers() {
    // ~(f(X7) = f(a)) | P(X7, X3) | P(X3, X7), ~P(a, Y), with input variables that are not 0, 1, 2, ...
    let clauses = vec![
        vec![
            eq(false, app(1, vec![var(7)]), app(1, vec![constant(0)])),
            pred(true, 0, vec![var(7), var(3)]),
            pred(true, 0, vec![var(3), var(7)]),
        ],
        vec![pred(false, 0, vec![constant(0), var(5)])],
    ];
    for preset in PRESETS {
        let text = prove(&clauses, &[0, 1], &[2], preset);
        assert!(text.contains("(eq-resolve "), "{preset}: {text}");
    }
}

#[test]
fn duplicate_literals_and_trivial_disequations() {
    // P(x) | P(x) | ~(b = b), ~P(a): the renaming steps remove both extra literals under step3 and later.
    let clauses = vec![
        vec![
            pred(true, 0, vec![var(0)]),
            pred(true, 0, vec![var(0)]),
            eq(false, constant(1), constant(1)),
        ],
        vec![pred(false, 0, vec![constant(0)])],
    ];
    for preset in PRESETS {
        prove(&clauses, &[0, 0], &[1], preset);
    }
}

#[test]
fn empty_input_clause() {
    let clauses = vec![vec![pred(true, 0, vec![])], vec![]];
    let text = prove(&clauses, &[], &[0], "step4");
    assert_eq!(text, format!("{HEADER}  (input 0 1)\n  (final 0))\n"));
}

#[test]
fn invalid_arity_is_rejected() {
    let clauses = vec![vec![pred(true, 0, vec![constant(0)])]];
    let options = Options::preset("step1").expect("preset");
    let result = Search::new(&clauses, &[1], &[1], &options, Limits::default());
    assert!(matches!(
        result,
        Err(fang_equality_search::InvalidPrepared::FunctionArity)
    ));
}

#[test]
fn saturation_without_refutation() {
    let clauses = vec![
        vec![pred(true, 0, vec![constant(0)])],
        vec![pred(false, 1, vec![constant(0)])],
    ];
    for preset in PRESETS {
        let options = Options::from_settings(&[("preset".into(), preset.into())]).expect("preset");
        let mut search =
            Search::new(&clauses, &[0], &[1, 1], &options, Limits::default()).expect("valid");
        assert_eq!(search.run(), Stop::Saturated);
    }
}

#[test]
fn knuth_bendix_basics() {
    let mut bank = Bank::new();
    let a = bank.app(0, &[]);
    let x = bank.var(0);
    let fx = bank.app(1, &[x]);
    let fa = bank.app(1, &[a]);
    let ffx = bank.app(1, &[fx]);
    // Symbols: a (arity 0), f (arity 1).
    let order = Order::new(&[0, 1], &[1, 1], 2, Precedence::Arity);
    assert_eq!(order.compare(&bank, fx, x), Cmp::Greater);
    assert_eq!(order.compare(&bank, x, fx), Cmp::Less);
    assert_eq!(order.compare(&bank, ffx, fx), Cmp::Greater);
    assert_eq!(order.compare(&bank, fa, a), Cmp::Greater);
    assert_eq!(order.compare(&bank, fx, fa), Cmp::Incomparable);
    assert_eq!(order.compare(&bank, fa, fa), Cmp::Equal);
}

#[test]
fn unification_and_matching() {
    let mut bank = Bank::new();
    let a = bank.app(0, &[]);
    let x = bank.var(0);
    let y = bank.var(1);
    let gxa = bank.app(1, &[x, a]);
    let gay = bank.app(1, &[a, y]);
    let mut binds = Bindings::new();
    assert!(binds.unify(&bank, gxa, 0, gay, 1));
    let mut renamer = Renamer::new();
    let left = binds.apply(&mut bank, gxa, 0, &mut renamer);
    let right = binds.apply(&mut bank, gay, 1, &mut renamer);
    assert_eq!(left, right);
    binds.clear();
    // x does not match a term in which the target keeps its own variable y in x's place.
    let gxx = bank.app(1, &[x, x]);
    let gay2 = bank.app(1, &[a, y]);
    assert!(!binds.matches(&bank, gxx, gay2));
    let gaa = bank.app(1, &[a, a]);
    assert!(binds.matches(&bank, gxx, gaa));
    binds.clear();
    // Occurs check.
    let fx = bank.app(2, &[x]);
    assert!(!binds.unify(&bank, x, 0, fx, 0));
}

#[test]
fn flags_are_split_from_the_producer_arguments() {
    let arguments: Vec<String> = [
        "--search",
        "v3",
        "--set",
        "preset=step2",
        "--time-limit",
        "5",
        "--goal",
        "0",
    ]
    .iter()
    .map(|item| item.to_string())
    .collect();
    let (flags, rest) = split(arguments, Instant::now()).expect("flags");
    assert_eq!(flags.mode, Mode::V3);
    assert_eq!(flags.time_limit, Some(5.0));
    assert_eq!(rest, vec!["--goal".to_string(), "0".to_string()]);
    assert_eq!(flags.options().expect("options").preset, "step2");
    assert!(split(vec!["--set".into(), "preset=step2".into()], Instant::now()).is_err());
}

#[test]
fn subsumption_resolution_is_stated_as_resolve_and_factor() {
    // ~P(x) | Q(x), ~Q(f(f(f(a)))), then P(f(f(f(a)))) | Q(f(f(f(a)))) selected last: subsumption resolution by
    // the first clause leaves Q(f(f(f(a)))), and unit deletion by the second leaves the empty clause.
    let t = || app(1, vec![app(1, vec![app(1, vec![constant(0)])])]);
    let clauses = vec![
        vec![pred(false, 0, vec![var(0)]), pred(true, 1, vec![var(0)])],
        vec![pred(false, 1, vec![t()])],
        vec![pred(true, 0, vec![t()]), pred(true, 1, vec![t()])],
    ];
    let options = Options::from_settings(&[("preset".into(), "step5".into())]).expect("preset");
    let mut search =
        Search::new(&clauses, &[0, 1], &[1, 1], &options, Limits::default()).expect("valid");
    let Stop::Proof(empty) = search.run() else {
        panic!("no refutation")
    };
    assert!(search.stats.subsumption_resolutions >= 1);
    let certificate = search.certificate(empty, 1 << 20).expect("certificate");
    assert_eq!(certificate.unchecked, 0);
    assert!(
        certificate.text.contains("(resolve "),
        "{}",
        certificate.text
    );
}

#[test]
fn filter_and_index_change_no_inference() {
    // The same refutation, step for step, with the linear scan, the clause filter and the indexes.
    let problems: Vec<(Vec<Clause>, Vec<usize>, Vec<usize>)> = vec![
        (
            vec![
                vec![eq(true, app(2, vec![constant(0)]), constant(1))],
                vec![pred(true, 0, vec![app(2, vec![constant(0)])])],
                vec![pred(false, 0, vec![constant(1)])],
            ],
            vec![0, 0, 1],
            vec![1],
        ),
        (
            vec![
                vec![pred(false, 0, vec![var(0)]), pred(true, 1, vec![var(0)])],
                vec![pred(true, 0, vec![constant(0)])],
                vec![eq(true, app(1, vec![var(0)]), var(0))],
                vec![pred(
                    false,
                    1,
                    vec![app(1, vec![app(1, vec![constant(0)])])],
                )],
            ],
            vec![0, 1],
            vec![1, 1],
        ),
    ];
    for (clauses, functions, predicates) in problems {
        for preset in PRESETS {
            let texts: Vec<String> = [("filter", "off"), ("filter", "on"), ("index", "on")]
                .iter()
                .map(|(key, value)| {
                    let settings = [
                        ("preset".to_string(), preset.to_string()),
                        (key.to_string(), value.to_string()),
                    ];
                    let options = Options::from_settings(&settings).expect("options");
                    let mut search = Search::new(
                        &clauses,
                        &functions,
                        &predicates,
                        &options,
                        Limits::default(),
                    )
                    .expect("valid");
                    let Stop::Proof(empty) = search.run() else {
                        panic!("{preset}: no refutation")
                    };
                    search
                        .certificate(empty, 1 << 20)
                        .expect("certificate")
                        .text
                })
                .collect();
            assert_eq!(texts[0], texts[1], "{preset}: filter");
            assert_eq!(texts[0], texts[2], "{preset}: index");
        }
    }
}

#[test]
fn portfolio_slices_are_parsed() {
    let settings = [(
        "portfolio".to_string(),
        "30/step3,filter:on;70/step5,from_variables:off".to_string(),
    )];
    let options = Options::from_settings(&settings).expect("portfolio");
    assert_eq!(options.portfolio.len(), 2);
    assert_eq!(options.portfolio[0].0, 30);
    assert!(options.portfolio[0].1.filter);
    assert_eq!(options.portfolio[1].1.preset, "step5");
    assert!(!options.portfolio[1].1.from_variables);
    let nested = [("portfolio".to_string(), "50/step1,portfolio:x".to_string())];
    assert!(Options::from_settings(&nested).is_err());
}

#[test]
fn queue_options_are_parsed_and_still_refute() {
    let parse = |pairs: &[(&str, &str)]| {
        let settings: Vec<(String, String)> = pairs
            .iter()
            .map(|(key, value)| (key.to_string(), value.to_string()))
            .collect();
        Options::from_settings(&settings)
    };
    let horn = parse(&[("horn_layer", "on")]).expect("horn layer");
    assert_eq!(horn.layer_cutoffs(), vec![1, u32::MAX]);
    assert_eq!(horn.layer_picks(), vec![1, 1]);
    let sine = parse(&[("sine_layer", "on"), ("layer_ratio", "2:1:1")]).expect("sine ratio");
    assert_eq!(sine.layer_picks(), vec![2, 1, 1]);
    assert!(parse(&[("horn_layer", "on"), ("sine_layer", "on")]).is_err());
    assert!(parse(&[("horn_layer", "on"), ("layer_ratio", "1:2:3")]).is_err());
    assert!(parse(&[("layer_ratio", "1:1")]).is_err());
    assert!(parse(&[("horn_layer", "on"), ("layer_ratio", "0:0")]).is_err());
    // P(a), ~P(x) | Q(x), ~Q(a): every queue setting still finds the refutation.
    let clauses = vec![
        vec![pred(true, 0, vec![constant(0)])],
        vec![pred(false, 0, vec![var(0)]), pred(true, 1, vec![var(0)])],
        vec![pred(false, 1, vec![constant(0)])],
    ];
    for pairs in [
        &[("preset", "step5"), ("inputs_first", "on")][..],
        &[("preset", "step5"), ("horn_layer", "on")][..],
        &[
            ("preset", "step5"),
            ("horn_layer", "on"),
            ("layer_ratio", "3:1"),
        ][..],
        &[
            ("preset", "step5"),
            ("inputs_first", "on"),
            ("horn_layer", "on"),
        ][..],
    ] {
        let options = parse(pairs).expect("options");
        let mut search =
            Search::new(&clauses, &[0], &[1, 1], &options, Limits::default()).expect("valid input");
        assert!(
            matches!(search.run(), Stop::Proof(_)),
            "{pairs:?}: no refutation"
        );
    }
}

#[test]
fn sine_selects_premises_reached_from_the_goal() {
    use crate::sine::{Group, select};
    // Predicates p, q, r, s; constants a, b. Goal ~p(b); premises p(x) | q(x), ~q(x) | r(x), ~r(x) | q(x), s(a).
    // Premise occurrences: p 1, q 3, r 2, s 1, a 1 (b occurs only in the goal).
    let clauses = vec![
        vec![pred(false, 0, vec![constant(1)])],
        vec![pred(true, 0, vec![var(0)]), pred(true, 1, vec![var(0)])],
        vec![pred(false, 1, vec![var(0)]), pred(true, 2, vec![var(0)])],
        vec![pred(false, 2, vec![var(0)]), pred(true, 1, vec![var(0)])],
        vec![pred(true, 3, vec![constant(0)])],
    ];
    let groups: Vec<Group> = (0..clauses.len())
        .map(|index| Group {
            clauses: index..index + 1,
            goal: index == 0,
        })
        .collect();
    // Tolerance 1: p triggers the first premise; q, in three premises, triggers none of them.
    assert_eq!(
        select(&clauses, &groups, 1.0, None),
        vec![true, true, false, false, false]
    );
    // Tolerance 3: q also triggers, which reaches r; s is never reached.
    assert_eq!(
        select(&clauses, &groups, 3.0, None),
        vec![true, true, true, true, false]
    );
    // One round from the goal reaches only the first premise.
    assert_eq!(
        select(&clauses, &groups, 3.0, Some(1)),
        vec![true, true, false, false, false]
    );
    // Without a goal everything is kept.
    let premises: Vec<Group> = (0..clauses.len())
        .map(|index| Group {
            clauses: index..index + 1,
            goal: false,
        })
        .collect();
    assert_eq!(select(&clauses, &premises, 1.0, None), vec![true; 5]);
}
