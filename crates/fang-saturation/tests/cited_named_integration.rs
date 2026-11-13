// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Staged in the isolated saturation workspace only.
use fang_saturation::{cited, options::Options};
use fang_tptp_coverage_candidate::Root;
use fang_tptp_signed_bundle::{
    cited_inputs, premise_line, prepare_bundle_task_named, prepare_cited_task_named, sealed,
};
use fang_tptp_signed_roles::{Limits, Selection};
use std::time::{Duration, Instant};

#[test]
fn cited_named_bundle_replays_original_include_item_with_new_numbering() {
    let bundle = sealed(vec![
        (
            Root::Base,
            "input".into(),
            b"include('ax.ax').fof(g,conjecture,p(a)).".to_vec(),
        ),
        (
            Root::Base,
            "ax.ax".into(),
            b"fof(unused,axiom,![X,Y]:((u(X)&v(X)&w(X))|(x(Y)&y(Y)&z(Y)))).fof(needed,axiom,p(a))."
                .to_vec(),
        ),
    ]);
    let limits = Limits::default();
    let (flat, whole) = prepare_bundle_task_named(&bundle, Selection::Goal(0), &limits, 8).unwrap();
    assert!(whole.predicate_arities.len() > 2);
    let deadline = Instant::now() + Duration::from_secs(5);
    let candidate = cited::refute(
        whole,
        &Options::preset("step5").unwrap(),
        Some(deadline),
        Some(deadline),
        Some(512),
        |prepared, inputs| {
            cited_inputs(&flat, prepared, inputs).map_err(|error| format!("{error:?}"))
        },
        |items| {
            let (canonical, _, kept) =
                prepare_cited_task_named(&bundle, Selection::Goal(0), items, &limits, 8)
                    .map_err(|error| format!("{error:?}"))?;
            assert_eq!(canonical, items);
            assert_eq!(kept.predicate_arities, vec![1]);
            Ok(kept)
        },
    )
    .unwrap();
    assert_eq!(candidate.premises, vec![(1, 1)]);
    assert_eq!(premise_line(&candidate.premises), "(premises (item 1 1))");
    assert!(candidate.text.starts_with("(fang-proof 8"));
}

#[test]
fn cited_named_true_goal_replays_with_no_premises() {
    let bundle = sealed(vec![(
        Root::Base,
        "input".into(),
        b"fof(unused,axiom,![X,Y]:((u(X)&v(X)&w(X))|(x(Y)&y(Y)&z(Y)))).fof(g,conjecture,$true)."
            .to_vec(),
    )]);
    let limits = Limits::default();
    let (flat, whole) = prepare_bundle_task_named(&bundle, Selection::Goal(0), &limits, 8).unwrap();
    let deadline = Instant::now() + Duration::from_secs(5);
    let candidate = cited::refute(
        whole,
        &Options::preset("step5").unwrap(),
        Some(deadline),
        Some(deadline),
        Some(512),
        |prepared, inputs| {
            cited_inputs(&flat, prepared, inputs).map_err(|error| format!("{error:?}"))
        },
        |items| {
            prepare_cited_task_named(&bundle, Selection::Goal(0), items, &limits, 8)
                .map(|(_, _, prepared)| prepared)
                .map_err(|error| format!("{error:?}"))
        },
    )
    .unwrap();
    assert!(candidate.premises.is_empty());
    assert_eq!(premise_line(&candidate.premises), "(premises)");
}
