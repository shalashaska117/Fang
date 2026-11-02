use fang::ErrorKind;
use fang::syntax::{Clause, Symbol, Term, deduplicate};
use fang_fof_core::{Formula, Signature, preprocess, validate};
use fang_fof_frontend::{Body, Limits, Parsed, parse};

fn parsed(text: &str) -> Parsed {
    parse(text.as_bytes(), &Limits::default()).unwrap()
}

fn signature(result: &Parsed) -> Signature {
    Signature {
        functions: result.functions.iter().map(|s| s.arity).collect(),
        predicates: result.predicates.iter().map(|s| s.arity).collect(),
    }
}

fn symbols(symbols: &[Symbol]) -> Vec<(&str, usize)> {
    symbols.iter().map(|s| (s.name.as_str(), s.arity)).collect()
}

fn kind(text: &str) -> ErrorKind {
    parse(text.as_bytes(), &Limits::default()).unwrap_err().kind
}

#[test]
fn mixed_declarations_preserve_tables_scopes_and_raw_duplicates() {
    let text = "  cnf(c,axiom,(p(X,a)|p(X,a))).\nfof(f,axiom,(p(f(a),a) => q(f(a)))).\ncnf(d,axiom,(q(Z))). ";
    let result = parsed(text);
    assert_eq!(symbols(&result.functions), vec![("a", 0), ("f", 1)]);
    assert_eq!(symbols(&result.predicates), vec![("p", 2), ("q", 1)]);
    assert_eq!(
        result
            .declarations
            .iter()
            .map(|d| d.name.as_str())
            .collect::<Vec<_>>(),
        ["c", "f", "d"]
    );
    assert_eq!(result.declarations[0].variables, ["X"]);
    assert!(result.declarations[1].variables.is_empty());
    assert_eq!(result.declarations[2].variables, ["Z"]);
    let Body::Cnf(first) = &result.declarations[0].body else {
        panic!()
    };
    assert_eq!(first.len(), 2);
    assert_eq!(first[0], first[1]);
    assert_eq!(first[0].arguments[0], Term::Var(0));
    let Body::Cnf(last) = &result.declarations[2].body else {
        panic!()
    };
    assert_eq!(last[0].arguments, [Term::Var(0)]);
    for (declaration, expected) in result.declarations.iter().zip([
        "cnf(c,axiom,(p(X,a)|p(X,a))).",
        "fof(f,axiom,(p(f(a),a) => q(f(a)))).",
        "cnf(d,axiom,(q(Z))).",
    ]) {
        assert_eq!(&text[declaration.bytes.clone()], expected);
    }
}

#[test]
fn functions_are_reserved_before_children_and_namespaces_are_separate() {
    let result = parsed("fof(x,axiom,f(f(g(a)))).");
    assert_eq!(symbols(&result.functions), [("f", 1), ("g", 1), ("a", 0)]);
    assert_eq!(symbols(&result.predicates), [("f", 1)]);
    let Body::Fof(formula) = &result.declarations[0].body else {
        panic!()
    };
    validate(formula, &signature(&result), &Default::default()).unwrap();
}

#[test]
fn exact_boolean_shape_and_distribution() {
    let result = parsed("fof(x,axiom,~((p & q) => (r | $false))).");
    let Body::Fof(formula) = &result.declarations[0].body else {
        panic!()
    };
    assert_eq!(
        *formula,
        Formula::Not(Box::new(Formula::Implies(
            Box::new(Formula::And(
                Box::new(Formula::Atom(0, vec![])),
                Box::new(Formula::Atom(1, vec![]))
            )),
            Box::new(Formula::Or(
                Box::new(Formula::Atom(2, vec![])),
                Box::new(Formula::False)
            )),
        )))
    );
    let clauses = preprocess(formula, &signature(&result), &Default::default())
        .unwrap()
        .clauses;
    assert_eq!(clauses.len(), 3);
    assert_eq!(
        clauses
            .iter()
            .map(|c| (c[0].positive, c[0].predicate))
            .collect::<Vec<_>>(),
        [(true, 0), (true, 1), (false, 2)]
    );
}

#[test]
fn true_false_and_empty_file_keep_their_meaning() {
    assert!(parsed("").declarations.is_empty());
    let result = parsed("fof(t,axiom,$true).fof(f,axiom,$false).cnf(c,axiom,($false)).");
    let sig = signature(&result);
    let Body::Fof(t) = &result.declarations[0].body else {
        panic!()
    };
    let Body::Fof(f) = &result.declarations[1].body else {
        panic!()
    };
    assert!(
        preprocess(t, &sig, &Default::default())
            .unwrap()
            .clauses
            .is_empty()
    );
    assert_eq!(
        preprocess(f, &sig, &Default::default()).unwrap().clauses,
        vec![Clause::new()]
    );
    assert_eq!(result.declarations[2].body, Body::Cnf(vec![]));
}

#[test]
fn all_six_ascii_whitespace_bytes_are_accepted() {
    let base = "fof ( x , axiom , ( p ( a ) => ~ q ) ) .";
    for byte in [b' ', 9, 10, 11, 12, 13] {
        let text: Vec<_> = base
            .bytes()
            .map(|b| if b == b' ' { byte } else { b })
            .collect();
        assert_eq!(
            parse(&text, &Limits::default()).unwrap().declarations.len(),
            1
        );
    }
}

#[test]
fn free_variables_are_invalid_even_in_discardable_formula_branches() {
    for text in [
        "fof(x,axiom,p(X)).",
        "fof(x,axiom,($true | p(f(X)))).",
        "fof(x,axiom,($false & p(X))).",
        "fof(x,axiom,X).",
        "cnf(c,axiom,(p(X))).fof(f,axiom,p(X)).",
    ] {
        assert_eq!(kind(text), ErrorKind::InvalidInput, "{text}");
    }
}

#[test]
fn duplicate_names_and_cross_language_arity_conflicts_are_invalid() {
    for text in [
        "cnf(x,axiom,(p)).fof(x,axiom,q).",
        "fof(x,axiom,p(a)).cnf(y,axiom,(p)).",
        "cnf(x,axiom,(p(f(a)))).fof(y,axiom,p(f)).",
        "fof(x,axiom,p(f(f))).",
    ] {
        assert_eq!(kind(text), ErrorKind::InvalidInput, "{text}");
    }
}

#[test]
fn unsupported_features_are_explicit() {
    for text in [
        "fof(x,axiom,?[X]:p(X)).",
        "fof(x,axiom,(a = b)).",
        "fof(x,axiom,(a != b)).",
        "fof(x,axiom,(p <=> q)).",
        "fof(x,axiom,(p <~> q)).",
        "fof(x,axiom,(p <= q)).",
        "fof(x,axiom,(p ~& q)).",
        "fof(x,axiom,(p ~| q)).",
        "fof(x,conjecture,p).",
        "fof(x,axiom,p,source).",
        "include('a.p').",
        "tff(x,axiom,p).",
        "thf(x,axiom,p).",
        "fof('x',axiom,p).",
        "fof(x,axiom,p(1)).",
        "% comment\nfof(x,axiom,p).",
        "fof(x,axiom,$ite(p,q,r)).",
        "cnf(x,axiom,($true)).",
        "cnf(x,axiom,(p & q)).",
        "cnf(x,axiom,(p => q)).",
    ] {
        assert_eq!(kind(text), ErrorKind::Unsupported, "{text}");
    }
}

#[test]
fn malformed_input_is_rejected_without_precedence_or_trailing_byte_recovery() {
    for text in [
        "fof(x,axiom,p & q).",
        "fof(x,axiom,(p & q | r)).",
        "fof(x,axiom,p()).",
        "fof(x,axiom,p(f())).",
        "fof(x,axiom,(p =>)).",
        "fof(x,axiom,(p = > q)).",
        "fof(x,axiom,p)",
        "fof(x,axiom,p).garbage",
        "fof(x,axiom,pA).",
        "fof(x,axiom,p)..",
        "fof(x,axiom,()).",
    ] {
        assert!(
            parse(text.as_bytes(), &Limits::default()).is_err(),
            "{text}"
        );
    }
    for text in [
        b"fof(x,axiom,p).\0".as_slice(),
        b"\xef\xbb\xbffof(x,axiom,p).",
        b"fof(x,axiom,p).\xff",
    ] {
        assert_eq!(
            parse(text, &Limits::default()).unwrap_err().kind,
            ErrorKind::InvalidInput
        );
    }
}

#[test]
fn resource_boundaries_are_exact_for_operations_bytes_nodes_and_depth() {
    let text = b"fof(x,axiom,(p(a) & ~q)).";
    let good = parse(text, &Limits::default()).unwrap();
    for cap in 0..=good.statistics.operations {
        let mut limits = Limits::default();
        limits.input.max_operations = cap;
        assert_eq!(
            parse(text, &limits).is_ok(),
            cap == good.statistics.operations
        );
    }
    let mut limits = Limits::default();
    limits.input.max_input_bytes = text.len() - 1;
    assert_eq!(
        parse(text, &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.input.max_input_bytes += 1;
    assert!(parse(text, &limits).is_ok());
    assert_eq!(good.statistics.formula_nodes, 4);
    for cap in 0..=4 {
        limits.max_formula_nodes = cap;
        assert_eq!(parse(text, &limits).is_ok(), cap == 4);
    }
    limits.max_formula_nodes = 4;
    limits.input.max_term_nodes = 0;
    assert_eq!(
        parse(text, &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.input.max_term_nodes = 1;
    assert!(parse(text, &limits).is_ok());
    limits.max_formula_depth = 2;
    assert_eq!(
        parse(text, &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.max_formula_depth = 3;
    assert!(parse(text, &limits).is_ok());
}

#[test]
fn grouping_and_term_recursion_are_bounded_even_with_maximal_configuration() {
    let limits = Limits {
        max_formula_depth: usize::MAX,
        input: fang::Limits {
            max_term_depth: usize::MAX,
            ..Default::default()
        },
        ..Default::default()
    };
    for depth in [63, 64] {
        let text = format!("fof(x,axiom,{}p{}).", "(".repeat(depth), ")".repeat(depth));
        assert_eq!(parse(text.as_bytes(), &limits).is_ok(), depth == 63);
        let text = format!(
            "fof(x,axiom,p({}a{})).",
            "f(".repeat(depth),
            ")".repeat(depth)
        );
        assert_eq!(parse(text.as_bytes(), &limits).is_ok(), depth == 63);
    }
}

#[test]
fn declaration_and_cnf_literal_caps_do_not_publish_a_prefix() {
    let mut limits = Limits::default();
    limits.input.max_clauses = 1;
    assert_eq!(
        parse(b"fof(a,axiom,p).cnf(b,axiom,(q)).", &limits)
            .unwrap_err()
            .kind,
        ErrorKind::ResourceLimit
    );
    limits.input.max_literals = 1;
    assert_eq!(
        parse(b"cnf(a,axiom,(p|p)).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    assert!(parse(b"cnf(a,axiom,(p)).", &limits).is_ok());
    limits.input.max_literals = 0;
    assert!(parse(b"cnf(a,axiom,($false)).", &limits).is_ok());
    assert_eq!(
        parse(b"cnf(a,axiom,(p)).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
}

#[test]
fn generated_cnf_matches_the_unchanged_frontend_after_declared_deduplication() {
    let atoms = ["p", "p(a)", "p(X)", "p(f(X))", "q(Y,a)"];
    let mut compared = 0;
    for (i, a) in atoms.iter().enumerate() {
        for (j, b) in atoms.iter().enumerate() {
            for signs in 0..4 {
                let source = format!(
                    "cnf(c,axiom,({}{}|{}{}|{}{})).cnf(d,axiom,(r(Z))).",
                    if signs & 1 == 0 { "" } else { "~" },
                    a,
                    if signs & 2 == 0 { "" } else { "~" },
                    b,
                    if signs & 1 == 0 { "" } else { "~" },
                    a
                );
                let old = fang::parser::parse(source.as_bytes(), &Default::default());
                let new = parse(source.as_bytes(), &Limits::default());
                match (old, new) {
                    (Ok(old), Ok(new)) => {
                        assert_eq!(symbols(&old.functions), symbols(&new.functions));
                        assert_eq!(symbols(&old.predicates), symbols(&new.predicates));
                        let clauses: Vec<_> = new
                            .declarations
                            .iter()
                            .map(|d| match &d.body {
                                Body::Cnf(c) => deduplicate(c),
                                _ => panic!(),
                            })
                            .collect();
                        assert_eq!(old.clauses, clauses);
                        compared += 1;
                    }
                    (Err(old), Err(new)) => assert_eq!(old.kind, new.kind, "{i}/{j}/{signs}"),
                    _ => panic!("different acceptance for {source}"),
                }
            }
        }
    }
    assert_eq!(compared, 76);
}

fn render(formula: &Formula, predicates: &[Symbol]) -> String {
    match formula {
        Formula::Atom(p, args) => {
            assert!(args.is_empty());
            predicates[*p as usize].name.clone()
        }
        Formula::True => "$true".into(),
        Formula::False => "$false".into(),
        Formula::Not(a) => format!("~{}", render(a, predicates)),
        Formula::And(a, b) => format!("({} & {})", render(a, predicates), render(b, predicates)),
        Formula::Or(a, b) => format!("({} | {})", render(a, predicates), render(b, predicates)),
        Formula::Implies(a, b) => {
            format!("({} => {})", render(a, predicates), render(b, predicates))
        }
    }
}

fn reference_formula(formula: &ground_core_reference::Formula) -> Formula {
    use ground_core_reference::Formula as Old;
    match formula {
        Old::Atom(id, args) => Formula::Atom(*id, args.clone()),
        Old::True => Formula::True,
        Old::False => Formula::False,
        Old::Not(body) => Formula::Not(Box::new(reference_formula(body))),
        Old::And(a, b) => Formula::And(
            Box::new(reference_formula(a)),
            Box::new(reference_formula(b)),
        ),
        Old::Or(a, b) => Formula::Or(
            Box::new(reference_formula(a)),
            Box::new(reference_formula(b)),
        ),
        Old::Implies(a, b) => Formula::Implies(
            Box::new(reference_formula(a)),
            Box::new(reference_formula(b)),
        ),
    }
}

fn compare_reference(source: &str, result: &Parsed) {
    let old = ground_reference::parse(source.as_bytes(), &Default::default()).unwrap();
    assert_eq!(symbols(&old.functions), symbols(&result.functions));
    assert_eq!(symbols(&old.predicates), symbols(&result.predicates));
    assert_eq!(old.statistics.operations, result.statistics.operations);
    assert_eq!(
        old.statistics.formula_nodes,
        result.statistics.formula_nodes
    );
    assert_eq!(old.statistics.term_nodes, result.statistics.term_nodes);
    assert_eq!(old.declarations.len(), result.declarations.len());
    for (old, new) in old.declarations.iter().zip(&result.declarations) {
        assert_eq!(old.name, new.name);
        assert_eq!(old.bytes, new.bytes);
        assert_eq!(old.variables, new.variables);
        assert!(new.prefix_bytes.is_none());
        match (&old.body, &new.body) {
            (ground_reference::Body::Cnf(old), Body::Cnf(new)) => assert_eq!(old, new),
            (ground_reference::Body::Fof(old), Body::Fof(new)) => {
                assert_eq!(reference_formula(old), *new)
            }
            _ => panic!("ground-language declaration kind changed"),
        }
    }
}

#[test]
fn exhaustive_small_formula_parses_preserve_connectives_and_operand_order() {
    let mut sizes = vec![
        Vec::<String>::new(),
        vec!["p".into(), "q".into(), "$true".into(), "$false".into()],
    ];
    for size in 2..=5 {
        let mut next: Vec<_> = sizes[size - 1].iter().map(|a| format!("~{a}")).collect();
        for left in 1..size - 1 {
            let right = size - 1 - left;
            for a in &sizes[left] {
                for b in &sizes[right] {
                    for op in ["&", "|", "=>"] {
                        next.push(format!("({a} {op} {b})"));
                    }
                }
            }
        }
        sizes.push(next);
    }
    assert_eq!(sizes.iter().map(Vec::len).sum::<usize>(), 1652);
    for body in sizes.iter().flatten() {
        let source = format!("fof(x,axiom,{body}).");
        let result = parsed(&source);
        compare_reference(&source, &result);
        let Body::Fof(formula) = &result.declarations[0].body else {
            panic!()
        };
        assert_eq!(render(formula, &result.predicates), *body);
        validate(formula, &signature(&result), &Default::default()).unwrap();
    }
}

#[test]
fn mixed_ground_reference_and_typed_failures_remain_compatible() {
    for source in [
        "cnf(c,axiom,(p(X,a)|p(X,a))).fof(f,axiom,(p(f(a),a) => q(f(a)))).cnf(d,axiom,(q(Z))).",
        "fof(t,axiom,$true).cnf(e,axiom,($false)).fof(f,axiom,~p(g(f(a),a))).",
    ] {
        compare_reference(source, &parsed(source));
    }
    for source in [
        "fof(a,axiom,p(X)).",
        "fof(a,axiom,p(f(f))).",
        "fof(a,conjecture,p).",
        "cnf(a,axiom,($true)).",
    ] {
        for max_operations in [0, 1, 5, 1000] {
            let new_limits = Limits {
                input: fang::Limits {
                    max_operations,
                    ..Default::default()
                },
                ..Default::default()
            };
            let old_limits = ground_reference::Limits {
                input: fang::Limits {
                    max_operations,
                    ..Default::default()
                },
                ..Default::default()
            };
            let old = ground_reference::parse(source.as_bytes(), &old_limits).unwrap_err();
            let new = parse(source.as_bytes(), &new_limits).unwrap_err();
            assert_eq!(
                (old.kind, old.offset),
                (new.kind, new.offset),
                "{source} at {max_operations}"
            );
        }
    }
}
