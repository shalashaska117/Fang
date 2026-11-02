use fang::syntax::Term;
use fang_quantified_fof_core::{
    Error, Formula as F, Invalid, Limits, Nnf, Resource, Signature, Unsupported, VariableScope,
    normalize, preprocess, rectify_closed, rectify_normalize_closed, validate, validate_with_scope,
};

fn signature() -> Signature {
    Signature {
        functions: vec![0, 1, 2],
        predicates: vec![1, 2, 0],
    }
}

fn atom(id: u32) -> F {
    F::Atom(0, vec![Term::Var(id)])
}

fn constant() -> F {
    F::Atom(0, vec![Term::Fun(0, vec![])])
}

#[test]
fn shadowing_restores_outer_binding_and_preserves_unused_positions() {
    let source = F::Forall(
        9,
        Box::new(F::And(
            Box::new(F::Exists(9, Box::new(atom(9)))),
            Box::new(F::Forall(7, Box::new(atom(9)))),
        )),
    );
    let expected = F::Forall(
        0,
        Box::new(F::And(
            Box::new(F::Exists(1, Box::new(atom(1)))),
            Box::new(F::Forall(2, Box::new(atom(0)))),
        )),
    );
    let result = rectify_closed(&source, &signature(), &Limits::default()).unwrap();
    assert_eq!(result.formula, expected);
    assert_eq!(result.binder_count, 3);
    assert_eq!(result.statistics.input_binders, 3);
    assert_eq!(
        rectify_closed(&source, &signature(), &Limits::default()).unwrap(),
        result
    );
    assert_eq!(
        validate(&result.formula, &signature(), &Limits::default())
            .unwrap()
            .input_binders,
        3
    );
}

#[test]
fn separate_scopes_get_fresh_ids_and_do_not_capture_free_variables() {
    let source = F::And(
        Box::new(F::Forall(42, Box::new(atom(42)))),
        Box::new(F::Exists(42, Box::new(atom(42)))),
    );
    let result = rectify_closed(&source, &signature(), &Limits::default()).unwrap();
    assert_eq!(
        result.formula,
        F::And(
            Box::new(F::Forall(0, Box::new(atom(0)))),
            Box::new(F::Exists(1, Box::new(atom(1))))
        )
    );
    let escaped = F::And(
        Box::new(F::Forall(42, Box::new(atom(42)))),
        Box::new(atom(42)),
    );
    assert_eq!(
        rectify_closed(&escaped, &signature(), &Limits::default()),
        Err(Error::Invalid(Invalid::FreeVariable))
    );
    let bound = F::Forall(99, Box::new(F::And(Box::new(atom(99)), Box::new(atom(0)))));
    assert!(
        validate_with_scope(
            &bound,
            &signature(),
            VariableScope::Bound(1),
            &Limits::default()
        )
        .is_ok()
    );
    assert_eq!(
        rectify_closed(&bound, &signature(), &Limits::default()),
        Err(Error::Invalid(Invalid::FreeVariable))
    );
}

#[test]
fn negative_quantifiers_use_dual_quantifiers_and_literal_polarity() {
    let source = F::Forall(
        17,
        Box::new(F::Implies(
            Box::new(atom(17)),
            Box::new(F::Exists(17, Box::new(atom(17)))),
        )),
    );
    let actual =
        rectify_normalize_closed(&source, false, &signature(), &Limits::default()).unwrap();
    let lit = |positive, id| {
        Nnf::Literal(fang::syntax::Literal {
            positive,
            predicate: 0,
            arguments: vec![Term::Var(id)],
        })
    };
    assert_eq!(
        actual.formula,
        Nnf::Exists(
            0,
            Box::new(Nnf::And(
                Box::new(lit(true, 0)),
                Box::new(Nnf::Forall(1, Box::new(lit(false, 1)))),
            ))
        )
    );
}

#[test]
fn quantified_clausification_is_explicitly_unsupported() {
    for source in [
        F::Forall(0, Box::new(F::False)),
        F::Exists(0, Box::new(F::True)),
        F::Or(Box::new(F::True), Box::new(F::Forall(0, Box::new(atom(0))))),
    ] {
        assert_eq!(
            preprocess(&source, &signature(), &Limits::default()),
            Err(Error::Unsupported(
                Unsupported::QuantifiersRequireSkolemization
            ))
        );
    }
}

#[test]
fn binder_bounds_count_unused_and_shadowed_binders() {
    let source = F::Forall(u32::MAX, Box::new(F::Exists(u32::MAX, Box::new(F::True))));
    for cap in [0, 1] {
        let limits = Limits {
            max_binders: cap,
            ..Limits::default()
        };
        assert_eq!(
            rectify_closed(&source, &signature(), &limits),
            Err(Error::Resource(Resource::Binders))
        );
    }
    let limits = Limits {
        max_binders: 2,
        ..Limits::default()
    };
    assert_eq!(
        rectify_closed(&source, &signature(), &limits)
            .unwrap()
            .binder_count,
        2
    );
    assert!(
        rectify_closed(
            &F::True,
            &signature(),
            &Limits {
                max_binders: 0,
                ..limits
            }
        )
        .is_ok()
    );
}

#[test]
fn budgets_have_exact_success_boundary_and_expose_no_partial_result() {
    let source = F::Forall(5, Box::new(F::Exists(5, Box::new(atom(5)))));
    let baseline =
        rectify_normalize_closed(&source, true, &signature(), &Limits::default()).unwrap();
    let exact = Limits {
        max_operations: baseline.statistics.operations,
        max_stored_nodes: baseline.statistics.allocated_nodes,
        ..Limits::default()
    };
    assert_eq!(
        rectify_normalize_closed(&source, true, &signature(), &exact).unwrap(),
        baseline
    );
    assert_eq!(
        rectify_normalize_closed(
            &source,
            true,
            &signature(),
            &Limits {
                max_operations: exact.max_operations - 1,
                ..exact
            }
        ),
        Err(Error::Resource(Resource::Operations))
    );
    assert_eq!(
        rectify_normalize_closed(
            &source,
            true,
            &signature(),
            &Limits {
                max_stored_nodes: exact.max_stored_nodes - 1,
                ..exact
            }
        ),
        Err(Error::Resource(Resource::StoredNodes))
    );
    assert_eq!(
        rectify_normalize_closed(
            &source,
            true,
            &signature(),
            &Limits {
                max_formula_nodes: 0,
                ..exact
            }
        ),
        Err(Error::Resource(Resource::FormulaNodes))
    );
    assert_eq!(
        rectify_normalize_closed(&source, true, &signature(), &Limits::default()).unwrap(),
        baseline
    );
}

#[test]
fn validation_rejects_deep_and_malformed_source_before_copying() {
    let mut deep = F::True;
    for id in 0..65 {
        deep = F::Forall(id, Box::new(deep));
    }
    assert_eq!(
        rectify_closed(&deep, &signature(), &Limits::default()),
        Err(Error::Resource(Resource::FormulaDepth))
    );
    let wrong = F::Forall(0, Box::new(F::Atom(0, vec![Term::Fun(1, vec![])])));
    assert_eq!(
        rectify_closed(&wrong, &signature(), &Limits::default()),
        Err(Error::Invalid(Invalid::FunctionArity(1)))
    );
    let unknown = F::Forall(0, Box::new(F::Atom(3, vec![Term::Var(0)])));
    assert_eq!(
        rectify_closed(&unknown, &signature(), &Limits::default()),
        Err(Error::Invalid(Invalid::UnknownPredicate(3)))
    );
}

fn term_value(term: &Term, values: &[(u32, bool)], model: u32) -> bool {
    match term {
        Term::Var(id) => {
            values
                .iter()
                .rev()
                .find(|(name, _)| name == id)
                .expect("closed term")
                .1
        }
        Term::Fun(0, args) => {
            assert!(args.is_empty());
            model & 1 != 0
        }
        Term::Fun(1, args) => term_value(&args[0], values, model) ^ (model & 2 != 0),
        Term::Fun(2, args) => {
            term_value(&args[0], values, model) ^ term_value(&args[1], values, model)
        }
        _ => panic!("unknown test symbol"),
    }
}

fn predicate(pred: u32, args: &[Term], values: &[(u32, bool)], model: u32) -> bool {
    match pred {
        0 => term_value(&args[0], values, model) ^ (model & 4 != 0),
        1 => term_value(&args[0], values, model) == term_value(&args[1], values, model),
        2 => model & 8 != 0,
        _ => panic!("unknown test predicate"),
    }
}

fn formula_value(formula: &F, values: &mut Vec<(u32, bool)>, model: u32) -> bool {
    match formula {
        F::Atom(pred, args) => predicate(*pred, args, values, model),
        F::True => true,
        F::False => false,
        F::Not(body) => !formula_value(body, values, model),
        F::And(l, r) => formula_value(l, values, model) && formula_value(r, values, model),
        F::Or(l, r) => formula_value(l, values, model) || formula_value(r, values, model),
        F::Implies(l, r) => !formula_value(l, values, model) || formula_value(r, values, model),
        F::Forall(id, body) | F::Exists(id, body) => {
            values.push((*id, false));
            let left = formula_value(body, values, model);
            values.pop();
            values.push((*id, true));
            let right = formula_value(body, values, model);
            values.pop();
            if matches!(formula, F::Forall(_, _)) {
                left && right
            } else {
                left || right
            }
        }
    }
}

fn nnf_value(formula: &Nnf, values: &mut Vec<(u32, bool)>, model: u32) -> bool {
    match formula {
        Nnf::Literal(lit) => {
            predicate(lit.predicate, &lit.arguments, values, model) == lit.positive
        }
        Nnf::True => true,
        Nnf::False => false,
        Nnf::And(l, r) => nnf_value(l, values, model) && nnf_value(r, values, model),
        Nnf::Or(l, r) => nnf_value(l, values, model) || nnf_value(r, values, model),
        Nnf::Forall(id, body) | Nnf::Exists(id, body) => {
            values.push((*id, false));
            let left = nnf_value(body, values, model);
            values.pop();
            values.push((*id, true));
            let right = nnf_value(body, values, model);
            values.pop();
            if matches!(formula, Nnf::Forall(_, _)) {
                left && right
            } else {
                left || right
            }
        }
    }
}

fn next(seed: &mut u64) -> u32 {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    (*seed >> 32) as u32
}

fn generated_term(seed: &mut u64, scope: &[u32], depth: usize) -> Term {
    match next(seed) % if depth == 0 { 2 } else { 4 } {
        0 if !scope.is_empty() => Term::Var(scope[next(seed) as usize % scope.len()]),
        2 => Term::Fun(1, vec![generated_term(seed, scope, depth - 1)]),
        3 => Term::Fun(
            2,
            vec![
                generated_term(seed, scope, depth - 1),
                generated_term(seed, scope, depth - 1),
            ],
        ),
        _ => Term::Fun(0, vec![]),
    }
}

fn generated(seed: &mut u64, scope: &mut Vec<u32>, depth: usize) -> F {
    match next(seed) % if depth == 0 { 3 } else { 9 } {
        0 => F::True,
        1 => F::False,
        2 => {
            let pred = next(seed) % 3;
            F::Atom(
                pred,
                (0..[1, 2, 0][pred as usize])
                    .map(|_| generated_term(seed, scope, 2))
                    .collect(),
            )
        }
        3 => F::Not(Box::new(generated(seed, scope, depth - 1))),
        kind @ 4..=6 => {
            let left = Box::new(generated(seed, scope, depth - 1));
            let right = Box::new(generated(seed, scope, depth - 1));
            match kind {
                4 => F::And(left, right),
                5 => F::Or(left, right),
                _ => F::Implies(left, right),
            }
        }
        kind => {
            let id = next(seed) % 3;
            scope.push(id);
            let body = Box::new(generated(seed, scope, depth - 1));
            scope.pop();
            if kind == 7 {
                F::Forall(id, body)
            } else {
                F::Exists(id, body)
            }
        }
    }
}

fn binder_ids(formula: &F, ids: &mut Vec<u32>) {
    match formula {
        F::Forall(id, body) | F::Exists(id, body) => {
            ids.push(*id);
            binder_ids(body, ids);
        }
        F::Not(body) => binder_ids(body, ids),
        F::And(l, r) | F::Or(l, r) | F::Implies(l, r) => {
            binder_ids(l, ids);
            binder_ids(r, ids);
        }
        _ => {}
    }
}

#[test]
fn seeded_closed_scope_rectification_and_nnf_preserve_all_test_models() {
    let mut seed = 0x4641_4e47_5155_414e;
    for case in 0..1000 {
        let source = generated(&mut seed, &mut Vec::new(), 5);
        let result = rectify_closed(&source, &signature(), &Limits::default()).unwrap();
        let mut ids = Vec::new();
        binder_ids(&result.formula, &mut ids);
        assert_eq!(
            ids,
            (0..result.binder_count).collect::<Vec<_>>(),
            "case {case}"
        );
        validate(&result.formula, &signature(), &Limits::default()).unwrap();
        for positive in [false, true] {
            let nnf = rectify_normalize_closed(&source, positive, &signature(), &Limits::default())
                .unwrap();
            let direct = normalize(&source, positive, &signature(), &Limits::default()).unwrap();
            for model in 0..16 {
                let expected = formula_value(&source, &mut Vec::new(), model);
                assert_eq!(
                    formula_value(&result.formula, &mut Vec::new(), model),
                    expected,
                    "rectify {case}/{model}"
                );
                assert_eq!(
                    nnf_value(&nnf.formula, &mut Vec::new(), model),
                    expected == positive,
                    "nnf {case}/{model}/{positive}"
                );
                assert_eq!(
                    nnf_value(&direct.formula, &mut Vec::new(), model),
                    expected == positive,
                    "direct {case}/{model}/{positive}"
                );
            }
        }
    }
}

#[test]
fn zero_scope_keeps_quantifier_free_results_and_counters() {
    use universal_reference as old;
    let old_signature = old::Signature {
        functions: signature().functions,
        predicates: signature().predicates,
    };
    for cap in [0, 1, 2, 3, 4, 8, 32, 1000] {
        let formula = F::Or(
            Box::new(F::And(Box::new(constant()), Box::new(F::False))),
            Box::new(F::True),
        );
        let reference = old::Formula::Or(
            Box::new(old::Formula::And(
                Box::new(old::Formula::Atom(0, vec![Term::Fun(0, vec![])])),
                Box::new(old::Formula::False),
            )),
            Box::new(old::Formula::True),
        );
        for scope in [VariableScope::Ground, VariableScope::Bound(0)] {
            let actual = fang_quantified_fof_core::preprocess_with_scope(
                &formula,
                &signature(),
                scope,
                &Limits {
                    max_operations: cap,
                    ..Limits::default()
                },
            );
            let expected = old::preprocess(
                &reference,
                &old_signature,
                &old::Limits {
                    max_operations: cap,
                    ..old::Limits::default()
                },
            );
            match (actual, expected) {
                (Ok(a), Ok(b)) => {
                    assert_eq!(a.clauses, b.clauses);
                    assert_eq!(a.statistics.operations, b.statistics.operations);
                    assert_eq!(a.statistics.allocated_nodes, b.statistics.allocated_nodes);
                    assert_eq!(
                        a.statistics.input_formula_nodes,
                        b.statistics.input_formula_nodes
                    );
                    assert_eq!(a.statistics.input_term_nodes, b.statistics.input_term_nodes);
                    assert_eq!(a.statistics.output_literals, b.statistics.output_literals);
                    assert_eq!(
                        a.statistics.output_term_nodes,
                        b.statistics.output_term_nodes
                    );
                    assert_eq!(a.statistics.input_binders, 0);
                }
                (Err(a), Err(b)) => assert_eq!(format!("{a:?}"), format!("{b:?}")),
                other => panic!("old/new outcome differs: {other:?}"),
            }
        }
    }
}
