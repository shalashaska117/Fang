// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::{
    ErrorKind,
    syntax::{Symbol, Term},
};
use fang_fof_core::{Formula, Signature, VariableScope, preprocess_with_scope};
use fang_fof_frontend::{Body, Limits, Parsed, parse};

fn parse_ok(text: &str) -> Parsed {
    parse(text.as_bytes(), &Limits::default()).unwrap()
}

fn signature(parsed: &Parsed) -> Signature {
    Signature {
        functions: parsed.functions.iter().map(|s| s.arity).collect(),
        predicates: parsed.predicates.iter().map(|s| s.arity).collect(),
    }
}

#[test]
fn prefix_positions_unused_binders_and_source_ranges_are_exact() {
    let text = " \tfof(rule,axiom, ! [ Unused , Y , X ] : (p(X,f(Y,X)) => q(Y)) ).\n";
    let parsed = parse_ok(text);
    let declaration = &parsed.declarations[0];
    assert_eq!(declaration.name, "rule");
    assert_eq!(declaration.variables, ["Unused", "Y", "X"]);
    assert_eq!(
        &text[declaration.bytes.clone()],
        "fof(rule,axiom, ! [ Unused , Y , X ] : (p(X,f(Y,X)) => q(Y)) )."
    );
    assert_eq!(
        &text[declaration.prefix_bytes.clone().unwrap()],
        "! [ Unused , Y , X ] :"
    );
    assert_eq!(
        &text[declaration.body_bytes.clone()],
        "(p(X,f(Y,X)) => q(Y))"
    );
    let Body::Universal(Formula::Implies(left, right)) = &declaration.body else {
        panic!()
    };
    assert_eq!(
        **left,
        Formula::Atom(
            0,
            vec![Term::Var(2), Term::Fun(0, vec![Term::Var(1), Term::Var(2)])]
        )
    );
    assert_eq!(**right, Formula::Atom(1, vec![Term::Var(1)]));
    let Body::Universal(formula) = &declaration.body else {
        panic!()
    };
    let result = preprocess_with_scope(
        formula,
        &signature(&parsed),
        VariableScope::Bound(3),
        &Default::default(),
    )
    .unwrap();
    assert_eq!(result.clauses.len(), 1);
    assert_eq!(result.clauses[0][0].arguments[0], Term::Var(2));
    assert_eq!(result.clauses[0][1].arguments, [Term::Var(1)]);
}

#[test]
fn mixed_declarations_keep_cnf_variables_clause_local() {
    let source = "cnf(c,axiom,(p(X,Y)|p(X,Y))).\nfof(u,axiom,![Y,X]:(p(X,Y)=>q(X))).\nfof(g,axiom,q(a)).\nfof(v,axiom,![X,Z]:p(X,Z)).\ncnf(d,axiom,(p(Y,X))).";
    let parsed = parse_ok(source);
    assert_eq!(
        parsed
            .declarations
            .iter()
            .map(|d| d.variables.clone())
            .collect::<Vec<_>>(),
        [
            vec!["X", "Y"],
            vec!["Y", "X"],
            vec![],
            vec!["X", "Z"],
            vec!["Y", "X"]
        ]
    );
    let Body::Cnf(first) = &parsed.declarations[0].body else {
        panic!()
    };
    assert_eq!(first.len(), 2);
    assert_eq!(first[0], first[1]);
    assert_eq!(first[0].arguments, [Term::Var(0), Term::Var(1)]);
    let Body::Universal(Formula::Implies(left, _)) = &parsed.declarations[1].body else {
        panic!()
    };
    assert_eq!(**left, Formula::Atom(0, vec![Term::Var(1), Term::Var(0)]));
    let Body::Cnf(last) = &parsed.declarations[4].body else {
        panic!()
    };
    assert_eq!(last[0].arguments, [Term::Var(0), Term::Var(1)]);
    for index in [0, 2, 4] {
        assert!(parsed.declarations[index].prefix_bytes.is_none());
    }
    assert_eq!(
        &source[parsed.declarations[0].body_bytes.clone()],
        "(p(X,Y)|p(X,Y))"
    );
    assert_eq!(&source[parsed.declarations[2].body_bytes.clone()], "q(a)");
}

#[test]
fn empty_duplicate_unbound_and_malformed_prefixes_are_invalid() {
    for source in [
        "fof(a,axiom,![]:p).",
        "fof(a,axiom,![X,X]:p(X)).",
        "fof(a,axiom,![x]:p(x)).",
        "fof(a,axiom,![X,]:p(X)).",
        "fof(a,axiom,![X Y]:p(X)).",
        "fof(a,axiom,![X]p(X)).",
        "fof(a,axiom,![X]:p(Y)).",
        "fof(a,axiom,![X]:($true | p(f(Y)))).",
        "fof(a,axiom,![X]:X).",
        "fof(a,axiom,![X]:).",
        "cnf(c,axiom,(p(X))).fof(a,axiom,![Y]:p(X)).",
        "fof(a,axiom,![X]:p(X)).fof(b,axiom,p(X)).",
        "fof(a,axiom,![X]:p(X)).fof(b,axiom,![Y]:p(X)).",
        "fof(a,axiom,![X]:p(X)).cnf(b,axiom,(p)).",
    ] {
        assert_eq!(
            parse(source.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::InvalidInput,
            "{source}"
        );
    }
}

#[test]
fn existential_nested_typed_equality_and_roles_are_unsupported() {
    for source in [
        "fof(a,axiom,?[X]:p(X)).",
        "fof(a,axiom,![X]:?[Y]:p(X,Y)).",
        "fof(a,axiom,![X]:![Y]:p(X,Y)).",
        "fof(a,axiom,~![X]:p(X)).",
        "fof(a,axiom,(![X]:p(X))).",
        "fof(a,axiom,(p & ![X]:q(X))).",
        "fof(a,axiom,![X:t]:p(X)).",
        "fof(a,axiom,![X]:X=a).",
        "fof(a,conjecture,![X]:p(X)).",
        "fof(a,hypothesis,![X]:p(X)).",
        "cnf(a,axiom,(![X]:p(X))).",
        "cnf(a,axiom,(~![X]:p(X))).",
        "fof(a,axiom,![X]:p(X),source).",
    ] {
        assert_eq!(
            parse(source.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::Unsupported,
            "{source}"
        );
    }
}

#[test]
fn binder_limit_counts_unused_names_and_is_declaration_local() {
    let text = b"fof(a,axiom,![Unused,X,Y]:p(X)).fof(b,axiom,![A,B,C]:$true).";
    for max_binders in 0..=3 {
        let limits = Limits {
            max_binders,
            ..Default::default()
        };
        let result = parse(text, &limits);
        if max_binders == 3 {
            assert_eq!(result.unwrap().declarations.len(), 2);
        } else {
            assert_eq!(result.unwrap_err().kind, ErrorKind::ResourceLimit);
        }
    }
    // Ground/CNF declarations do not consume the explicit-prefix budget.
    assert!(
        parse(
            b"cnf(c,axiom,(p(X))).fof(f,axiom,p(a)).",
            &Limits {
                max_binders: 0,
                ..Default::default()
            }
        )
        .is_ok()
    );
    for count in [4_096, 4_097] {
        let names = (0..count)
            .map(|id| format!("X{id}"))
            .collect::<Vec<_>>()
            .join(",");
        let source = format!("fof(a,axiom,![{names}]:$true).");
        let result = parse(source.as_bytes(), &Limits::default());
        if count == 4_096 {
            assert_eq!(result.unwrap().declarations[0].variables.len(), count);
        } else {
            assert_eq!(result.unwrap_err().kind, ErrorKind::ResourceLimit);
        }
    }
}

#[test]
fn prefix_bytes_tokens_and_body_resources_have_exact_boundaries() {
    let source = b"fof(a,axiom,![Unused,X,Y]:(p(f(X),Y) & ~$false)).";
    let complete = parse(source, &Limits::default()).unwrap();
    for cap in 0..=complete.statistics.operations {
        let limits = Limits {
            input: fang::Limits {
                max_operations: cap,
                ..Default::default()
            },
            ..Default::default()
        };
        let result = parse(source, &limits);
        if cap == complete.statistics.operations {
            assert_eq!(result.unwrap().declarations, complete.declarations);
        } else {
            assert_eq!(result.unwrap_err().kind, ErrorKind::ResourceLimit);
        }
    }
    for cap in [source.len() - 1, source.len()] {
        let limits = Limits {
            input: fang::Limits {
                max_input_bytes: cap,
                ..Default::default()
            },
            ..Default::default()
        };
        assert_eq!(parse(source, &limits).is_ok(), cap == source.len());
    }
    assert_eq!(
        (
            complete.statistics.formula_nodes,
            complete.statistics.term_nodes
        ),
        (4, 3)
    );
    for cap in 0..=3 {
        let limits = Limits {
            input: fang::Limits {
                max_term_nodes: cap,
                ..Default::default()
            },
            ..Default::default()
        };
        assert_eq!(parse(source, &limits).is_ok(), cap == 3);
    }
    for cap in 0..=4 {
        let limits = Limits {
            max_formula_nodes: cap,
            ..Default::default()
        };
        assert_eq!(parse(source, &limits).is_ok(), cap == 4);
    }
    for depth in [63, 64] {
        let source = format!(
            "fof(a,axiom,![X]:{}p(X){}).",
            "(".repeat(depth),
            ")".repeat(depth)
        );
        assert_eq!(
            parse(
                source.as_bytes(),
                &Limits {
                    max_formula_depth: usize::MAX,
                    ..Default::default()
                }
            )
            .is_ok(),
            depth == 63
        );
    }
}

// Named syntax is test data, not an alternative parser or preprocessing engine.
#[derive(Clone, Debug, PartialEq, Eq)]
enum NamedTerm {
    Var(String),
    Fun(String, Vec<NamedTerm>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum NamedFormula {
    Atom(String, Vec<NamedTerm>),
    True,
    False,
    Not(Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Implies(Box<Self>, Box<Self>),
}

fn term_text(term: &NamedTerm) -> String {
    match term {
        NamedTerm::Var(name) => name.clone(),
        NamedTerm::Fun(name, args) if args.is_empty() => name.clone(),
        NamedTerm::Fun(name, args) => format!(
            "{name}({})",
            args.iter().map(term_text).collect::<Vec<_>>().join(",")
        ),
    }
}
fn formula_text(formula: &NamedFormula) -> String {
    match formula {
        NamedFormula::Atom(name, args) if args.is_empty() => name.clone(),
        NamedFormula::Atom(name, args) => format!(
            "{name}({})",
            args.iter().map(term_text).collect::<Vec<_>>().join(",")
        ),
        NamedFormula::True => "$true".into(),
        NamedFormula::False => "$false".into(),
        NamedFormula::Not(body) => format!("~{}", formula_text(body)),
        NamedFormula::And(a, b) => format!("({} & {})", formula_text(a), formula_text(b)),
        NamedFormula::Or(a, b) => format!("({} | {})", formula_text(a), formula_text(b)),
        NamedFormula::Implies(a, b) => format!("({} => {})", formula_text(a), formula_text(b)),
    }
}
fn named_term(term: &Term, functions: &[Symbol], variables: &[String]) -> NamedTerm {
    match term {
        Term::Var(id) => NamedTerm::Var(variables[*id as usize].clone()),
        Term::Fun(id, args) => NamedTerm::Fun(
            functions[*id as usize].name.clone(),
            args.iter()
                .map(|t| named_term(t, functions, variables))
                .collect(),
        ),
    }
}
fn named_formula(formula: &Formula, parsed: &Parsed, variables: &[String]) -> NamedFormula {
    let recurse = |body| Box::new(named_formula(body, parsed, variables));
    match formula {
        Formula::Atom(id, args) => NamedFormula::Atom(
            parsed.predicates[*id as usize].name.clone(),
            args.iter()
                .map(|t| named_term(t, &parsed.functions, variables))
                .collect(),
        ),
        Formula::True => NamedFormula::True,
        Formula::False => NamedFormula::False,
        Formula::Not(body) => NamedFormula::Not(recurse(body)),
        Formula::And(a, b) => NamedFormula::And(recurse(a), recurse(b)),
        Formula::Or(a, b) => NamedFormula::Or(recurse(a), recurse(b)),
        Formula::Implies(a, b) => NamedFormula::Implies(recurse(a), recurse(b)),
    }
}
fn next(seed: &mut u64) -> u64 {
    *seed = seed
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    *seed
}
fn generated_term(seed: &mut u64, depth: usize) -> NamedTerm {
    let value = next(seed);
    if depth == 0 || value.is_multiple_of(3) {
        if value & 1 == 0 {
            NamedTerm::Var(["X", "Y", "Z"][(value as usize >> 2) % 3].into())
        } else {
            NamedTerm::Fun("a".into(), vec![])
        }
    } else if value & 1 == 0 {
        NamedTerm::Fun("f".into(), vec![generated_term(seed, depth - 1)])
    } else {
        NamedTerm::Fun(
            "g".into(),
            vec![
                generated_term(seed, depth - 1),
                generated_term(seed, depth - 1),
            ],
        )
    }
}
fn generated_formula(seed: &mut u64, depth: usize) -> NamedFormula {
    let value = next(seed);
    if depth == 0 || value.is_multiple_of(5) {
        match value % 4 {
            0 => NamedFormula::True,
            1 => NamedFormula::False,
            2 => NamedFormula::Atom("p".into(), vec![generated_term(seed, 3)]),
            _ => NamedFormula::Atom(
                "q".into(),
                vec![generated_term(seed, 3), generated_term(seed, 3)],
            ),
        }
    } else {
        let left = Box::new(generated_formula(seed, depth - 1));
        match value % 4 {
            0 => NamedFormula::Not(left),
            1 => NamedFormula::And(left, Box::new(generated_formula(seed, depth - 1))),
            2 => NamedFormula::Or(left, Box::new(generated_formula(seed, depth - 1))),
            _ => NamedFormula::Implies(left, Box::new(generated_formula(seed, depth - 1))),
        }
    }
}

#[test]
fn seeded_named_ast_roundtrips_preserve_binders_symbols_and_body_shape() {
    let binders = ["Unused", "Z", "Y", "X"].map(String::from).to_vec();
    let mut cases = 0;
    for initial in [0xfa16_b101, 0xfa16_b102, 0xfa16_b103, 0xfa16_b104] {
        let mut seed = initial;
        for _ in 0..256 {
            let expected = generated_formula(&mut seed, 4);
            let body = formula_text(&expected);
            // Preceding declarations change symbol IDs and local variable maps.
            let source = format!(
                "cnf(c,axiom,(q(V,U))).fof(g,axiom,p(a)).fof(u,axiom,![{}]:{body}).",
                binders.join(",")
            );
            let parsed = parse_ok(&source);
            let declaration = &parsed.declarations[2];
            assert_eq!(declaration.variables, binders);
            let Body::Universal(formula) = &declaration.body else {
                panic!()
            };
            assert_eq!(
                named_formula(formula, &parsed, &declaration.variables),
                expected
            );
            assert_eq!(&source[declaration.body_bytes.clone()], body);
            preprocess_with_scope(
                formula,
                &signature(&parsed),
                VariableScope::Bound(4),
                &Default::default(),
            )
            .unwrap();
            cases += 1;
        }
    }
    assert_eq!(cases, 1_024);
}
