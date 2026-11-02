// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::ErrorKind;
use fang_quantified_fof_core::{Formula as CoreFormula, Limits as CoreLimits, Nnf};
use fang_tptp_full_frontend_candidate::{Encoded, EncodedBody, InputClass, Limits, Role, parse};

fn encoded(input: &str) -> Encoded {
    parse(input.as_bytes(), &Limits::default())
        .unwrap()
        .encode(100, 100)
        .unwrap()
}

#[test]
fn six_premise_roles_keep_original_role_and_body() {
    for (word, role) in [
        ("axiom", Role::Axiom),
        ("hypothesis", Role::Hypothesis),
        ("definition", Role::Definition),
        ("lemma", Role::Lemma),
        ("theorem", Role::Theorem),
        ("corollary", Role::Corollary),
    ] {
        let input = format!("fof(a,{word},p).");
        let parsed = parse(input.as_bytes(), &Limits::default()).unwrap();
        assert_eq!(parsed.declarations[0].role, role);
        assert_eq!(&input[parsed.declarations[0].role_bytes.clone()], word);
        assert_eq!(role.input_class(0).unwrap(), InputClass::Premise);
        let result = parsed.encode(100, 100).unwrap();
        let tasks: Vec<_> = result.obligations().unwrap().collect();
        assert_eq!(tasks.len(), 1);
        assert_eq!(tasks[0].goal_index(), None);
        assert!(
            tasks[0]
                .declarations()
                .all(|d| d.positive && d.original.role == role)
        );
    }
}

#[test]
fn unsupported_and_unknown_roles_are_distinct() {
    for role in ["assumption", "plain", "type", "interpretation", "logic"] {
        let input = format!("fof(a,{role},p).");
        assert_eq!(
            parse(input.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::Unsupported
        );
    }
    for role in [
        "unknown",
        "arbitrary",
        "question",
        "claim",
        "extensionality",
    ] {
        let input = format!("fof(a,{role},p).");
        assert_eq!(
            parse(input.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::InvalidInput
        );
    }
    assert!(parse(b"fof(a,axiom-extra,p).", &Limits::default()).is_err());
}

#[test]
fn cnf_conjecture_rejects_before_any_negation() {
    assert_eq!(
        parse(b"cnf(a,conjecture,p).", &Limits::default())
            .unwrap_err()
            .kind,
        ErrorKind::InvalidInput
    );
}

#[test]
fn conjecture_is_borrowed_with_negative_polarity() {
    let input = "fof('goal',conjecture,![X]:(p(X) => p(X))).";
    let parsed = parse(input.as_bytes(), &Limits::default()).unwrap();
    assert_eq!(
        &input[parsed.declarations[0].body_bytes.clone()],
        "![X]:(p(X) => p(X))"
    );
    let result = parsed.encode(100, 100).unwrap();
    let task = result.obligations().unwrap().next().unwrap();
    let signed = task.declarations().next().unwrap();
    assert_eq!(task.goal_index(), Some(0));
    assert!(!signed.positive);
    assert!(std::ptr::eq(signed.original, &result.declarations[0]));
    assert!(matches!(
        signed.original.body,
        EncodedBody::Fof(CoreFormula::Forall(..))
    ));
}

#[test]
fn actual_normalizer_negates_quantifiers_and_atoms() {
    let result = encoded("fof(goal,conjecture,![X]:p(X)).");
    let task = result.obligations().unwrap().next().unwrap();
    let signed = task.declarations().next().unwrap();
    let normal = signed
        .normalize_fof(&result.signature(), &CoreLimits::default())
        .unwrap()
        .unwrap();
    match normal.formula {
        Nnf::Exists(0, body) => {
            assert!(matches!(*body, Nnf::Literal(ref literal) if !literal.positive))
        }
        other => panic!("unexpected negative normal form: {other:?}"),
    }
    assert!(matches!(
        result.declarations[0].body,
        EncodedBody::Fof(CoreFormula::Forall(..))
    ));
}

#[test]
fn shadowed_binders_use_existing_rectifier() {
    let result = encoded("fof(goal,conjecture,![X]:(p(X) & ?[X]:q(X))).");
    let task = result.obligations().unwrap().next().unwrap();
    let signed = task.declarations().next().unwrap();
    let normal = signed
        .normalize_fof(&result.signature(), &CoreLimits::default())
        .unwrap()
        .unwrap();
    match normal.formula {
        Nnf::Exists(0, body) => match *body {
            Nnf::Or(_, right) => assert!(matches!(*right, Nnf::Forall(1, _))),
            other => panic!("unexpected body {other:?}"),
        },
        other => panic!("unexpected formula {other:?}"),
    }
}

#[test]
fn multiple_goals_have_separate_complete_obligations() {
    let result =
        encoded("fof(z,conjecture,p). cnf(a,axiom,p). fof(b,conjecture,q). fof(h,hypothesis,r).");
    let tasks: Vec<_> = result.obligations().unwrap().collect();
    assert_eq!(tasks.len(), 2);
    assert_eq!(tasks[0].goal_index(), Some(0));
    assert_eq!(tasks[1].goal_index(), Some(2));
    let views = tasks
        .iter()
        .map(|t| {
            t.declarations()
                .map(|d| (d.source_index, d.positive))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        views,
        vec![
            vec![(0, false), (1, true), (3, true)],
            vec![(1, true), (2, false), (3, true)]
        ]
    );
    // p alone does not entail both p and q. Negating both goals together would
    // conceal the countermodel of the second obligation.
    let values = [true, false, true];
    let countermodels: Vec<_> = tasks
        .iter()
        .map(|task| {
            task.declarations().all(|d| {
                let value = match &d.original.body {
                    EncodedBody::Fof(CoreFormula::Atom(id, _)) => values[*id as usize],
                    EncodedBody::Cnf(Some(clause)) => clause
                        .iter()
                        .any(|literal| values[literal.predicate as usize] == literal.positive),
                    other => panic!("unexpected fixture body {other:?}"),
                };
                value == d.positive
            })
        })
        .collect();
    assert_eq!(countermodels, vec![false, true]);
}

#[test]
fn already_negated_input_remains_positive_and_has_no_original_goal() {
    let result = encoded("fof(a,axiom,p). cnf(n,negated_conjecture,~p).");
    let tasks: Vec<_> = result.obligations().unwrap().collect();
    assert_eq!(tasks.len(), 1);
    assert_eq!(tasks[0].goal_index(), None);
    assert!(tasks[0].declarations().all(|d| d.positive));
}

#[test]
fn mixed_original_and_unlinked_negated_goals_reject() {
    for input in [
        "fof(g,conjecture,p). cnf(n,negated_conjecture,~p).",
        "cnf(n,negated_conjecture,~p). fof(g,conjecture,p).",
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
fn truth_and_empty_input_retain_satisfiability_task() {
    let empty = encoded("");
    let tasks: Vec<_> = empty.obligations().unwrap().collect();
    assert_eq!(tasks.len(), 1);
    assert_eq!(tasks[0].declarations().count(), 0);
    let result = encoded("cnf(z,lemma,$true). cnf(a,axiom,$false). fof(g,conjecture,$true).");
    let task = result.obligations().unwrap().next().unwrap();
    let declarations: Vec<_> = task.declarations().collect();
    assert_eq!(declarations.len(), 3);
    assert!(matches!(
        declarations[0].original.body,
        EncodedBody::Cnf(None)
    ));
    assert!(matches!(declarations[1].original.body, EncodedBody::Cnf(Some(ref c)) if c.is_empty()));
}

#[test]
fn entire_input_and_mutated_role_policy_are_checked() {
    assert!(
        parse(
            b"fof(a,axiom,$false). fof(g,conjecture,p(X)).",
            &Limits::default()
        )
        .is_err()
    );
    let mut result = encoded("cnf(a,axiom,p).");
    result.declarations[0].role = Role::Conjecture;
    assert!(result.obligations().is_err());
    result.declarations[0].role = Role::Plain;
    assert!(result.obligations().is_err());
}

#[test]
fn inherited_caps_still_apply_to_every_source_goal() {
    let mut limits = Limits::default();
    limits.input.max_clauses = 1;
    assert_eq!(
        parse(b"fof(a,conjecture,p). fof(b,conjecture,q).", &limits)
            .unwrap_err()
            .kind,
        ErrorKind::ResourceLimit
    );
    let result = encoded("fof(g,conjecture,![X]:p(X)).");
    let task = result.obligations().unwrap().next().unwrap();
    let core_limits = CoreLimits {
        max_operations: 0,
        ..CoreLimits::default()
    };
    assert!(
        task.declarations()
            .next()
            .unwrap()
            .normalize_fof(&result.signature(), &core_limits)
            .unwrap()
            .is_err()
    );
}
