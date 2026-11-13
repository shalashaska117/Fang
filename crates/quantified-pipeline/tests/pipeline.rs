// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::search::{Outcome, prove};
use fang::syntax::{Literal, Term};
use fang_quantified_fof_core::Formula;
use fang_quantified_fof_frontend::Body;
use fang_quantified_pipeline::{Error, Limits, Origin, Prepared, prepare};

fn prepared(input: &str) -> Prepared {
    prepare(input.as_bytes(), &Limits::default()).unwrap()
}

#[test]
fn reserves_later_cnf_symbols_and_keeps_mixed_origins() {
    let value = prepared(
        "cnf(a,axiom,(s(c))). fof(b,axiom,?[X]:p(X)). cnf(c,axiom,(q(f(a)))). fof(d,axiom,?[Y]:~p(Y)).",
    );
    assert_eq!(value.problem.functions.len(), 5);
    assert_eq!(
        value
            .introduced
            .iter()
            .map(|row| row.function)
            .collect::<Vec<_>>(),
        [3, 4]
    );
    assert_eq!(
        value
            .introduced
            .iter()
            .map(|row| row.declaration)
            .collect::<Vec<_>>(),
        [1, 3]
    );
    assert_eq!(
        value.origins,
        (0..4)
            .map(|declaration| Origin {
                declaration,
                local_clause: 0
            })
            .collect::<Vec<_>>()
    );
    assert_eq!(
        value.problem.clause_names,
        ["a_0_0", "b_1_0", "c_2_0", "d_3_0"]
    );
}

#[test]
fn nested_alternation_keeps_ordered_universal_dependencies_and_holes() {
    let value = prepared("fof(a,axiom,![X]:?[Y]:![Z]:?[W]:p(X,Y,Z,W)).");
    assert_eq!(value.introduced.len(), 2);
    assert_eq!(value.introduced[0].universals, [0]);
    assert_eq!(value.introduced[1].universals, [0, 2]);
    assert_eq!(
        value
            .introduced
            .iter()
            .map(|row| row.binder)
            .collect::<Vec<_>>(),
        [1, 3]
    );
    assert_eq!(
        value
            .problem
            .functions
            .iter()
            .map(|symbol| symbol.arity)
            .collect::<Vec<_>>(),
        [1, 2]
    );
    assert_eq!(
        value.problem.clauses[0][0].arguments,
        [
            Term::Var(0),
            Term::Fun(0, vec![Term::Var(0)]),
            Term::Var(2),
            Term::Fun(1, vec![Term::Var(0), Term::Var(2)])
        ]
    );
}

#[test]
fn unused_universal_is_retained_in_skolem_arity() {
    let value = prepared("fof(a,axiom,![X]:?[Y]:p(Y)).");
    assert_eq!(value.introduced[0].universals, [0]);
    assert_eq!(value.problem.functions[0].arity, 1);
    assert_eq!(
        value.problem.clauses[0][0].arguments,
        [Term::Fun(0, vec![Term::Var(0)])]
    );
}

#[test]
fn disjoint_scopes_reusing_a_name_get_distinct_clause_variables() {
    let value = prepared("fof(a,axiom,((![X]:p(X)) | (![X]:q(X)))).");
    assert!(value.introduced.is_empty());
    assert_eq!(value.problem.clauses.len(), 1);
    assert_eq!(value.problem.clauses[0][0].arguments, [Term::Var(0)]);
    assert_eq!(value.problem.clauses[0][1].arguments, [Term::Var(1)]);
}

#[test]
fn independent_existential_witnesses_do_not_create_a_false_refutation() {
    let value = prepared("fof(a,axiom,?[X]:p(X)). fof(b,axiom,?[X]:~p(X)).");
    assert_eq!(value.introduced.len(), 2);
    assert!(matches!(
        prove(&value.problem, &fang::Limits::default()).unwrap(),
        Outcome::Unknown { .. }
    ));
}

#[test]
fn universal_and_existential_contradiction_produces_only_a_candidate() {
    let value = prepared("fof(a,axiom,![X]:p(X)). fof(b,axiom,?[Y]:~p(Y)).");
    assert!(matches!(
        prove(&value.problem, &fang::Limits::default()).unwrap(),
        Outcome::CandidateRefutation(_)
    ));
}

#[test]
fn fresh_names_avoid_original_functions_but_predicates_have_their_own_namespace() {
    let value = prepared("cnf(a,axiom,(p(fang_skolem_1))). fof(b,axiom,?[X]:p(X)).");
    assert_eq!(value.problem.functions[0].name, "fang_skolem_1");
    assert_eq!(value.problem.functions[1].name, "fang_skolem_1_");
    let other = prepared("fof(a,axiom,?[X]:fang_skolem_0(X)).");
    assert_eq!(other.problem.functions[0].name, "fang_skolem_0");
    assert_eq!(other.problem.predicates[0].name, "fang_skolem_0");
}

#[test]
fn source_order_raw_duplicates_and_empty_clause_are_distinct() {
    let value = prepared(
        "fof(t,axiom,$true). cnf(a,axiom,(p|p)). fof(b,axiom,(q&q)). fof(f,axiom,$false).",
    );
    assert_eq!(
        value.origins,
        [
            Origin {
                declaration: 1,
                local_clause: 0
            },
            Origin {
                declaration: 2,
                local_clause: 0
            },
            Origin {
                declaration: 2,
                local_clause: 1
            },
            Origin {
                declaration: 3,
                local_clause: 0
            }
        ]
    );
    assert_eq!(
        value
            .problem
            .clauses
            .iter()
            .map(Vec::len)
            .collect::<Vec<_>>(),
        [1, 1, 1, 0]
    );
    assert_eq!(value.statistics.raw_output_literals, 4);
    assert!(prepared("fof(t,axiom,$true).").problem.clauses.is_empty());
}

#[test]
fn invalid_and_unsupported_inputs_are_not_partial_successes() {
    for source in [
        "fof(a,conjecture,p).",
        "fof(a,axiom,a=b).",
        "tff(a,axiom,p).",
        "thf(a,axiom,p).",
        "include('x.p').",
    ] {
        assert!(
            matches!(
                prepare(source.as_bytes(), &Limits::default()),
                Err(Error::Input(fang::Error {
                    kind: fang::ErrorKind::Unsupported,
                    ..
                }))
            ),
            "{source}"
        );
    }
    for source in [
        "fof(a,axiom,p(X)).",
        "fof(a,axiom,p). junk",
        "fof(a,axiom,p). cnf(a,axiom,(q)).",
    ] {
        assert!(
            matches!(
                prepare(source.as_bytes(), &Limits::default()),
                Err(Error::Input(fang::Error {
                    kind: fang::ErrorKind::InvalidInput,
                    ..
                }))
            ),
            "{source}"
        );
    }
}

#[test]
fn global_clause_literal_and_declaration_caps_include_cnf_rows() {
    let mut limits = Limits::default();
    limits.preprocessing.core.max_clauses = 1;
    assert!(prepare(b"cnf(a,axiom,(p)). fof(b,axiom,q).", &limits).is_err());
    limits.preprocessing.core.max_clauses = 100;
    limits.preprocessing.core.max_literals = 1;
    assert!(prepare(b"cnf(a,axiom,(p|p)).", &limits).is_err());
    limits.preprocessing.core.max_literals = 100;
    limits.preprocessing.max_declarations = 1;
    assert!(matches!(
        prepare(b"cnf(a,axiom,(p)). cnf(b,axiom,(q)).", &limits),
        Err(Error::Resource("total source declaration cap"))
    ));
}

#[test]
fn cumulative_operation_and_storage_caps_are_exact_for_a_completed_run() {
    let input = b"cnf(a,axiom,(r)). fof(b,axiom,![X]:?[Y]:(p(X)|q(Y))).";
    let value = prepare(input, &Limits::default()).unwrap();
    let mut limits = Limits::default();
    limits.preprocessing.core.max_operations = value.statistics.preprocessing_operations;
    limits.preprocessing.core.max_stored_nodes = value.statistics.stored_nodes;
    assert_eq!(prepare(input, &limits).unwrap().problem, value.problem);
    limits.preprocessing.core.max_operations -= 1;
    assert!(prepare(input, &limits).is_err());
    limits.preprocessing.core.max_operations += 1;
    limits.preprocessing.core.max_stored_nodes -= 1;
    assert!(prepare(input, &limits).is_err());
}

#[test]
fn bookkeeping_and_name_caps_fail_without_returning_a_problem() {
    let input = b"cnf(a,axiom,(p(fang_skolem_1))). fof(b,axiom,?[X]:p(X)).";
    let mut limits = Limits {
        max_generated_name_bytes: "fang_skolem_1".len(),
        ..Limits::default()
    };
    assert!(matches!(
        prepare(input, &limits),
        Err(Error::Resource("generated function-name byte cap"))
    ));
    limits.max_generated_name_bytes = 100;
    limits.max_bookkeeping_operations = 0;
    assert!(matches!(
        prepare(input, &limits),
        Err(Error::Resource("bookkeeping operation cap"))
    ));
}

#[test]
fn repeated_preparation_is_exactly_deterministic() {
    let input = "fof(a,axiom,![X]:?[Y]:p(X,Y)). cnf(b,axiom,(~p(a,a))).";
    let first = prepared(input);
    let second = prepared(input);
    assert_eq!(first.problem, second.problem);
    assert_eq!(first.origins, second.origins);
    assert_eq!(first.introduced, second.introduced);
    assert_eq!(first.statistics, second.statistics);
}

// Independent finite-domain test interpreter. These checks are not proofs.
fn arguments(terms: &[Term], values: &[bool], functions: &[u16]) -> usize {
    terms.iter().enumerate().fold(0, |bits, (index, term)| {
        bits | (usize::from(term_value(term, values, functions)) << index)
    })
}

fn term_value(term: &Term, values: &[bool], functions: &[u16]) -> bool {
    match term {
        Term::Var(id) => values[*id as usize],
        Term::Fun(id, terms) => {
            functions[*id as usize] & (1 << arguments(terms, values, functions)) != 0
        }
    }
}

fn formula_value(formula: &Formula, values: &mut [bool], predicates: &[u16]) -> bool {
    match formula {
        Formula::Atom(id, terms) => {
            predicates[*id as usize] & (1 << arguments(terms, values, &[])) != 0
        }
        Formula::True => true,
        Formula::False => false,
        Formula::Not(body) => !formula_value(body, values, predicates),
        Formula::And(left, right) => {
            formula_value(left, values, predicates) && formula_value(right, values, predicates)
        }
        Formula::Or(left, right) => {
            formula_value(left, values, predicates) || formula_value(right, values, predicates)
        }
        Formula::Implies(left, right) => {
            !formula_value(left, values, predicates) || formula_value(right, values, predicates)
        }
        Formula::Forall(id, body) | Formula::Exists(id, body) => {
            let original = values[*id as usize];
            values[*id as usize] = false;
            let left = formula_value(body, values, predicates);
            values[*id as usize] = true;
            let right = formula_value(body, values, predicates);
            values[*id as usize] = original;
            if matches!(formula, Formula::Forall(..)) {
                left && right
            } else {
                left || right
            }
        }
    }
}

fn literal_value(
    literal: &Literal,
    values: &[bool],
    predicates: &[u16],
    functions: &[u16],
) -> bool {
    let atom = predicates[literal.predicate as usize]
        & (1 << arguments(&literal.arguments, values, functions))
        != 0;
    atom == literal.positive
}

fn tables(arities: &[usize]) -> Vec<Vec<u16>> {
    let mut result = vec![vec![]];
    for arity in arities {
        assert!(*arity <= 2, "finite test bound");
        let mut next = Vec::new();
        for prefix in result {
            for table in 0..(1u16 << (1 << arity)) {
                let mut row = prefix.clone();
                row.push(table);
                next.push(row);
            }
        }
        result = next;
    }
    result
}

#[test]
fn finite_models_preserve_quantifier_order_shadowing_and_negation() {
    let inputs = [
        "fof(a,axiom,?[X]:p(X)).",
        "fof(a,axiom,![X]:?[Y]:q(X,Y)).",
        "fof(a,axiom,?[Y]:![X]:q(X,Y)).",
        "fof(a,axiom,((![X]:p(X))|(?[Y]:~p(Y)))).",
        "fof(a,axiom,![X]:((?[X]:q(X,X))&p(X))).",
        "fof(a,axiom,~(?[X]:![Y]:q(X,Y))).",
        "fof(a,axiom,?[X]:p(X)). fof(b,axiom,?[Y]:~p(Y)).",
        "fof(a,axiom,![X]:p(X)). fof(b,axiom,?[Y]:~p(Y)).",
    ];
    let mut checked = 0;
    for input in inputs {
        let parsed =
            fang_quantified_fof_frontend::parse(input.as_bytes(), &Default::default()).unwrap();
        assert!(parsed.functions.is_empty());
        let value = prepared(input);
        let predicate_arities = value
            .problem
            .predicates
            .iter()
            .map(|symbol| symbol.arity)
            .collect::<Vec<_>>();
        let function_arities = value
            .problem
            .functions
            .iter()
            .map(|symbol| symbol.arity)
            .collect::<Vec<_>>();
        for predicates in tables(&predicate_arities) {
            let original = parsed
                .declarations
                .iter()
                .all(|declaration| match &declaration.body {
                    Body::Fof(formula) => formula_value(formula, &mut [false; 8], &predicates),
                    Body::Cnf(_) => panic!("finite control contains only FOF"),
                });
            let extended = tables(&function_arities).iter().any(|functions| {
                (0..256).all(|bits| {
                    let values = std::array::from_fn::<_, 8, _>(|index| bits & (1 << index) != 0);
                    value.problem.clauses.iter().all(|clause| {
                        clause
                            .iter()
                            .any(|literal| literal_value(literal, &values, &predicates, functions))
                    })
                })
            });
            assert_eq!(original, extended, "{input}: {predicates:?}");
            checked += 1;
        }
    }
    assert_eq!(checked, 128);
}
