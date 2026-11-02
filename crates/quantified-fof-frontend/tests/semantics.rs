// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Finite-model tests are an independent specification oracle, not a proof.
use fang::syntax::Term;
use fang_quantified_fof_core::{Formula, Nnf, Signature, rectify_normalize_closed};
use fang_quantified_fof_frontend::{Body, Parsed, parse};

enum Named {
    Atom(&'static str, Option<&'static str>, bool),
    Truth(bool),
    Not(Box<Named>),
    Binary(u32, Box<Named>, Box<Named>),
    Quantified(bool, &'static str, Box<Named>),
}

fn next(seed: &mut u32) -> u32 {
    // Xorshift avoids the low-bit cycle that collapsed the first LCG corpus.
    *seed ^= *seed << 13;
    *seed ^= *seed >> 17;
    *seed ^= *seed << 5;
    *seed
}

fn generate(seed: &mut u32, depth: u32, scope: &mut Vec<&'static str>) -> Named {
    let choice = next(seed) % if depth == 0 { 2 } else { 8 };
    match choice {
        0 => {
            let predicate = if next(seed) & 1 == 0 { "p" } else { "q" };
            let name = if scope.is_empty() {
                None
            } else {
                Some(scope[next(seed) as usize % scope.len()])
            };
            Named::Atom(predicate, name, next(seed) & 1 == 0)
        }
        1 => Named::Truth(next(seed) & 1 == 0),
        2 => Named::Not(Box::new(generate(seed, depth - 1, scope))),
        3..=5 => Named::Binary(
            choice - 3,
            Box::new(generate(seed, depth - 1, scope)),
            Box::new(generate(seed, depth - 1, scope)),
        ),
        _ => {
            let name = ["X", "Y", "Z"][next(seed) as usize % 3];
            scope.push(name);
            let body = generate(seed, depth - 1, scope);
            scope.pop();
            Named::Quantified(choice == 6, name, Box::new(body))
        }
    }
}

fn render(value: &Named) -> String {
    match value {
        Named::Atom(p, v, nested) => {
            let term = v.unwrap_or("a");
            if *nested {
                format!("{p}(f({term}))")
            } else {
                format!("{p}({term})")
            }
        }
        Named::Truth(true) => "$true".into(),
        Named::Truth(false) => "$false".into(),
        Named::Not(a) => format!("~{}", render(a)),
        Named::Binary(op, a, b) => format!(
            "({} {} {})",
            render(a),
            ["&", "|", "=>"][*op as usize],
            render(b)
        ),
        Named::Quantified(all, name, body) => {
            format!("{}[{name}]:{}", if *all { "!" } else { "?" }, render(body))
        }
    }
}

// Two elements; all 128 interpretations of one constant, one unary function
// and two unary predicates. Bit positions identify their full truth tables.
fn bit(model: u32, pos: u32) -> bool {
    model & (1 << pos) != 0
}
fn function(model: u32, arg: bool) -> bool {
    bit(model, 1 + u32::from(arg))
}
fn predicate(model: u32, name: &str, arg: bool) -> bool {
    bit(model, (if name == "p" { 3 } else { 5 }) + u32::from(arg))
}

fn named(value: &Named, model: u32, env: &mut Vec<(&'static str, bool)>) -> bool {
    match value {
        Named::Atom(p, v, nested) => {
            let mut arg = v.map_or_else(
                || bit(model, 0),
                |v| env.iter().rev().find(|(n, _)| *n == v).unwrap().1,
            );
            if *nested {
                arg = function(model, arg);
            }
            predicate(model, p, arg)
        }
        Named::Truth(value) => *value,
        Named::Not(a) => !named(a, model, env),
        Named::Binary(op, a, b) => {
            let left = named(a, model, env);
            let right = named(b, model, env);
            match op {
                0 => left && right,
                1 => left || right,
                _ => !left || right,
            }
        }
        Named::Quantified(all, name, body) => {
            let values = [false, true].map(|value| {
                env.push((name, value));
                let truth = named(body, model, env);
                env.pop();
                truth
            });
            if *all {
                values[0] && values[1]
            } else {
                values[0] || values[1]
            }
        }
    }
}

fn term(value: &Term, model: u32, source: &Parsed, env: &[(u32, bool)]) -> bool {
    match value {
        Term::Var(id) => env.iter().rev().find(|(n, _)| n == id).unwrap().1,
        Term::Fun(id, args) => match source.functions[*id as usize].name.as_str() {
            "a" => {
                assert!(args.is_empty());
                bit(model, 0)
            }
            "f" => {
                assert_eq!(args.len(), 1);
                function(model, term(&args[0], model, source, env))
            }
            _ => panic!("unexpected function"),
        },
    }
}

fn formula(value: &Formula, model: u32, source: &Parsed, env: &mut Vec<(u32, bool)>) -> bool {
    match value {
        Formula::Atom(p, args) => {
            assert_eq!(args.len(), 1);
            predicate(
                model,
                &source.predicates[*p as usize].name,
                term(&args[0], model, source, env),
            )
        }
        Formula::True => true,
        Formula::False => false,
        Formula::Not(a) => !formula(a, model, source, env),
        Formula::And(a, b) => formula(a, model, source, env) && formula(b, model, source, env),
        Formula::Or(a, b) => formula(a, model, source, env) || formula(b, model, source, env),
        Formula::Implies(a, b) => !formula(a, model, source, env) || formula(b, model, source, env),
        Formula::Forall(id, body) | Formula::Exists(id, body) => {
            let values = [false, true].map(|v| {
                env.push((*id, v));
                let truth = formula(body, model, source, env);
                env.pop();
                truth
            });
            if matches!(value, Formula::Forall(..)) {
                values[0] && values[1]
            } else {
                values[0] || values[1]
            }
        }
    }
}

fn nnf(value: &Nnf, model: u32, source: &Parsed, env: &mut Vec<(u32, bool)>) -> bool {
    match value {
        Nnf::Literal(literal) => {
            assert_eq!(literal.arguments.len(), 1);
            let truth = predicate(
                model,
                &source.predicates[literal.predicate as usize].name,
                term(&literal.arguments[0], model, source, env),
            );
            truth == literal.positive
        }
        Nnf::True => true,
        Nnf::False => false,
        Nnf::And(a, b) => nnf(a, model, source, env) && nnf(b, model, source, env),
        Nnf::Or(a, b) => nnf(a, model, source, env) || nnf(b, model, source, env),
        Nnf::Forall(id, body) | Nnf::Exists(id, body) => {
            let values = [false, true].map(|v| {
                env.push((*id, v));
                let truth = nnf(body, model, source, env);
                env.pop();
                truth
            });
            if matches!(value, Nnf::Forall(..)) {
                values[0] && values[1]
            } else {
                values[0] || values[1]
            }
        }
    }
}

#[test]
fn original_named_meaning_matches_parsed_and_rectified_nnf_in_finite_models() {
    let mut seed = 0x36b1_7ec9;
    let mut binders = 0;
    let mut distinct = std::collections::BTreeSet::new();
    for _ in 0..512 {
        let original = generate(&mut seed, 5, &mut Vec::new());
        let bytes = format!("fof(a,axiom,{}).", render(&original));
        distinct.insert(bytes.clone());
        let source = parse(bytes.as_bytes(), &Default::default()).unwrap();
        binders += source.statistics.binders;
        let signature = Signature {
            functions: source.functions.iter().map(|s| s.arity).collect(),
            predicates: source.predicates.iter().map(|s| s.arity).collect(),
        };
        let Body::Fof(parsed) = &source.declarations[0].body else {
            panic!()
        };
        let positive =
            rectify_normalize_closed(parsed, true, &signature, &Default::default()).unwrap();
        let negative =
            rectify_normalize_closed(parsed, false, &signature, &Default::default()).unwrap();
        for model in 0..128 {
            let expected = named(&original, model, &mut Vec::new());
            assert_eq!(
                formula(parsed, model, &source, &mut Vec::new()),
                expected,
                "{bytes}, model={model}"
            );
            assert_eq!(
                nnf(&positive.formula, model, &source, &mut Vec::new()),
                expected,
                "{bytes}, positive, model={model}"
            );
            assert_eq!(
                nnf(&negative.formula, model, &source, &mut Vec::new()),
                !expected,
                "{bytes}, negative, model={model}"
            );
        }
    }
    assert!(binders > 100, "generator must cover quantified formulas");
    assert!(
        distinct.len() > 100,
        "generator must not collapse to a few cases"
    );
}
