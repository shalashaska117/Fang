use fang::syntax::{Literal, Term};
use fang_quantified_fof_core::{Error as CoreError, Formula as F, Invalid, Nnf as N, Signature};
use fang_skolem_core::{Declaration, Error, Introduced, Limits, Resource, skolemize_problem};

fn atom(arguments: Vec<Term>) -> F {
    F::Atom(0, arguments)
}
fn var(id: u32) -> Term {
    Term::Var(id)
}
fn fun(id: u32, arguments: Vec<Term>) -> Term {
    Term::Fun(id, arguments)
}
fn all(id: u32, body: F) -> F {
    F::Forall(id, Box::new(body))
}
fn exists(id: u32, body: F) -> F {
    F::Exists(id, Box::new(body))
}
fn declaration(formula: F) -> Declaration {
    Declaration {
        formula,
        positive: true,
    }
}
fn signature(functions: Vec<usize>, arity: usize) -> Signature {
    Signature {
        functions,
        predicates: vec![arity],
    }
}
fn lit(positive: bool, arguments: Vec<Term>) -> N {
    N::Literal(Literal {
        positive,
        predicate: 0,
        arguments,
    })
}

#[test]
fn empty_input_preserves_unused_original_signature() {
    let result = skolemize_problem(&[], &signature(vec![3, 0], 1), &Limits::default()).unwrap();
    assert!(result.formulas.is_empty());
    assert!(result.introduced.is_empty());
    assert_eq!(result.signature, signature(vec![3, 0], 1));
}

#[test]
fn reserves_symbols_used_only_by_later_declarations() {
    let input = [
        declaration(exists(7, atom(vec![var(7)]))),
        declaration(atom(vec![fun(1, vec![])])),
    ];
    let sig = signature(vec![0, 0], 1);
    let result = skolemize_problem(&input, &sig, &Limits::default()).unwrap();
    assert_eq!(result.signature.functions, vec![0, 0, 0]);
    assert_eq!(
        result.formulas,
        vec![
            lit(true, vec![fun(2, vec![])]),
            lit(true, vec![fun(1, vec![])])
        ]
    );
    assert_eq!(sig.functions, vec![0, 0]);
    assert_eq!(
        result.introduced,
        vec![Introduced {
            declaration: 0,
            binder: 0,
            function: 2,
            universals: vec![]
        }]
    );
}

#[test]
fn keeps_unused_universals_and_dependency_order() {
    let input = [declaration(all(
        90,
        all(2, exists(4, atom(vec![var(4), var(2)]))),
    ))];
    let result = skolemize_problem(&input, &signature(vec![], 2), &Limits::default()).unwrap();
    assert_eq!(result.introduced[0].universals, vec![0, 1]);
    assert_eq!(result.introduced[0].binder, 2);
    assert_eq!(result.signature.functions, vec![2]);
    assert_eq!(
        result.formulas[0],
        N::Forall(
            0,
            Box::new(N::Forall(
                1,
                Box::new(lit(true, vec![fun(0, vec![var(0), var(1)]), var(1)]))
            ))
        )
    );
}

#[test]
fn lexical_shadowing_and_sibling_stack_restore() {
    let body = F::And(
        Box::new(exists(7, atom(vec![var(7)]))),
        Box::new(exists(8, atom(vec![var(7)]))),
    );
    let input = [
        declaration(all(7, body)),
        declaration(exists(7, atom(vec![var(7)]))),
    ];
    let result = skolemize_problem(&input, &signature(vec![], 1), &Limits::default()).unwrap();
    assert_eq!(
        result.introduced,
        vec![
            Introduced {
                declaration: 0,
                binder: 1,
                function: 0,
                universals: vec![0]
            },
            Introduced {
                declaration: 0,
                binder: 2,
                function: 1,
                universals: vec![0]
            },
            Introduced {
                declaration: 1,
                binder: 0,
                function: 2,
                universals: vec![]
            },
        ]
    );
    assert_eq!(
        result.formulas[0],
        N::Forall(
            0,
            Box::new(N::And(
                Box::new(lit(true, vec![fun(0, vec![var(0)])])),
                Box::new(lit(true, vec![var(0)]))
            ))
        )
    );
    assert_eq!(result.formulas[1], lit(true, vec![fun(2, vec![])]));
}

#[test]
fn existential_replacements_carry_outer_dependencies() {
    let input = [declaration(all(
        9,
        exists(8, all(7, exists(6, atom(vec![var(8), var(6)])))),
    ))];
    let result = skolemize_problem(&input, &signature(vec![], 2), &Limits::default()).unwrap();
    assert_eq!(result.signature.functions, vec![1, 2]);
    assert_eq!(result.introduced[0].universals, vec![0]);
    assert_eq!(result.introduced[1].universals, vec![0, 2]);
    assert_eq!(
        result.formulas[0],
        N::Forall(
            0,
            Box::new(N::Forall(
                2,
                Box::new(lit(
                    true,
                    vec![fun(0, vec![var(0)]), fun(1, vec![var(0), var(2)])]
                ))
            ))
        )
    );
}

#[test]
fn negative_quantifiers_use_the_shared_normalizer() {
    let input = [Declaration {
        formula: all(9, exists(4, atom(vec![var(9), var(4)]))),
        positive: false,
    }];
    let result = skolemize_problem(&input, &signature(vec![], 2), &Limits::default()).unwrap();
    assert_eq!(result.introduced[0].binder, 0);
    assert_eq!(result.introduced[0].universals, vec![]);
    assert_eq!(
        result.formulas[0],
        N::Forall(1, Box::new(lit(false, vec![fun(0, vec![]), var(1)])))
    );
}

#[test]
fn unused_existentials_still_advance_the_global_counter() {
    let input = [
        declaration(exists(4, F::True)),
        declaration(exists(9, F::False)),
    ];
    let result = skolemize_problem(&input, &signature(vec![], 0), &Limits::default()).unwrap();
    assert_eq!(result.formulas, vec![N::True, N::False]);
    assert_eq!(result.signature.functions, vec![0, 0]);
    assert_eq!(
        result
            .introduced
            .iter()
            .map(|item| (item.declaration, item.binder, item.function))
            .collect::<Vec<_>>(),
        vec![(0, 0, 0), (1, 0, 1)]
    );
}

#[test]
fn all_input_validation_precedes_fresh_allocation() {
    let limits = Limits {
        max_skolem_symbols: 0,
        ..Default::default()
    };
    let input = [
        declaration(exists(0, F::True)),
        declaration(atom(vec![var(99)])),
    ];
    assert_eq!(
        skolemize_problem(&input, &signature(vec![], 1), &limits),
        Err(Error::Core(CoreError::Invalid(Invalid::FreeVariable)))
    );
    let malformed = [declaration(atom(vec![fun(0, vec![])]))];
    assert_eq!(
        skolemize_problem(&malformed, &signature(vec![1], 1), &Limits::default()),
        Err(Error::Core(CoreError::Invalid(Invalid::FunctionArity(0))))
    );
}

#[test]
fn declaration_function_and_skolem_caps_are_exact() {
    let input = [declaration(exists(0, F::True))];
    let sig = signature(vec![0], 0);
    for (limits, expected) in [
        (
            Limits {
                max_declarations: 0,
                ..Default::default()
            },
            Resource::Declarations,
        ),
        (
            Limits {
                max_functions: 1,
                ..Default::default()
            },
            Resource::Functions,
        ),
        (
            Limits {
                max_skolem_symbols: 0,
                ..Default::default()
            },
            Resource::SkolemSymbols,
        ),
    ] {
        assert_eq!(
            skolemize_problem(&input, &sig, &limits),
            Err(Error::Resource(expected))
        );
    }
    let limits = Limits {
        max_declarations: 1,
        max_functions: 2,
        max_skolem_symbols: 1,
        ..Default::default()
    };
    assert!(skolemize_problem(&input, &sig, &limits).is_ok());
}

#[test]
fn aggregate_operation_and_storage_boundaries_preserve_no_partial_result() {
    let input = [
        declaration(all(9, exists(4, atom(vec![var(4)])))),
        declaration(exists(1, F::True)),
    ];
    let sig = signature(vec![], 1);
    let accepted = skolemize_problem(&input, &sig, &Limits::default()).unwrap();
    let mut limits = Limits::default();
    limits.core.max_operations = accepted.statistics.operations;
    limits.core.max_stored_nodes = accepted.statistics.allocated_nodes;
    assert_eq!(skolemize_problem(&input, &sig, &limits).unwrap(), accepted);
    limits.core.max_operations -= 1;
    assert!(skolemize_problem(&input, &sig, &limits).is_err());
    limits.core.max_operations += 1;
    limits.core.max_stored_nodes -= 1;
    assert!(skolemize_problem(&input, &sig, &limits).is_err());
    assert_eq!(sig.functions, vec![]);
    assert_eq!(
        skolemize_problem(&input, &sig, &Limits::default()).unwrap(),
        accepted
    );
}

#[test]
fn replacement_term_depth_is_checked() {
    let input = [declaration(all(
        0,
        exists(1, atom(vec![fun(0, vec![var(1)])])),
    ))];
    let mut limits = Limits::default();
    limits.core.max_term_depth = 2;
    assert_eq!(
        skolemize_problem(&input, &signature(vec![1], 1), &limits),
        Err(Error::Resource(Resource::TermDepth))
    );
    limits.core.max_term_depth = 3;
    assert!(skolemize_problem(&input, &signature(vec![1], 1), &limits).is_ok());
}

fn term_value(term: &Term, valuation: &[usize], tables: &[Vec<usize>]) -> usize {
    match term {
        Term::Var(id) => valuation[*id as usize],
        Term::Fun(id, args) => {
            let index = args.iter().fold(0, |value, term| {
                value * 2 + term_value(term, valuation, tables)
            });
            tables[*id as usize][index]
        }
    }
}
fn formula_value(
    formula: &F,
    valuation: &mut [usize],
    tables: &[Vec<usize>],
    predicates: usize,
) -> bool {
    match formula {
        F::Atom(id, args) => {
            predicates & (1 << (2 * id + term_value(&args[0], valuation, tables) as u32)) != 0
        }
        F::True => true,
        F::False => false,
        F::Not(body) => !formula_value(body, valuation, tables, predicates),
        F::And(left, right) => {
            formula_value(left, valuation, tables, predicates)
                && formula_value(right, valuation, tables, predicates)
        }
        F::Or(left, right) => {
            formula_value(left, valuation, tables, predicates)
                || formula_value(right, valuation, tables, predicates)
        }
        F::Implies(left, right) => {
            !formula_value(left, valuation, tables, predicates)
                || formula_value(right, valuation, tables, predicates)
        }
        F::Forall(id, body) | F::Exists(id, body) => {
            let previous = valuation[*id as usize];
            valuation[*id as usize] = 0;
            let left = formula_value(body, valuation, tables, predicates);
            valuation[*id as usize] = 1;
            let right = formula_value(body, valuation, tables, predicates);
            valuation[*id as usize] = previous;
            if matches!(formula, F::Forall(..)) {
                left && right
            } else {
                left || right
            }
        }
    }
}
fn nnf_value(
    formula: &N,
    valuation: &mut [usize],
    tables: &[Vec<usize>],
    predicates: usize,
) -> bool {
    match formula {
        N::Literal(literal) => {
            let value = predicates
                & (1 << (2 * literal.predicate
                    + term_value(&literal.arguments[0], valuation, tables) as u32))
                != 0;
            value == literal.positive
        }
        N::True => true,
        N::False => false,
        N::And(left, right) => {
            nnf_value(left, valuation, tables, predicates)
                && nnf_value(right, valuation, tables, predicates)
        }
        N::Or(left, right) => {
            nnf_value(left, valuation, tables, predicates)
                || nnf_value(right, valuation, tables, predicates)
        }
        N::Forall(id, body) => {
            let previous = valuation[*id as usize];
            valuation[*id as usize] = 0;
            let left = nnf_value(body, valuation, tables, predicates);
            valuation[*id as usize] = 1;
            let right = nnf_value(body, valuation, tables, predicates);
            valuation[*id as usize] = previous;
            left && right
        }
        N::Exists(..) => panic!("existential survived"),
    }
}

#[test]
fn finite_models_check_original_extension_for_96_formulas_and_64_models() {
    let sig = Signature {
        functions: vec![1],
        predicates: vec![1, 1],
    };
    for case in 0..96 {
        let a = F::Atom(
            0,
            vec![if case & 1 == 0 {
                var(3)
            } else {
                fun(0, vec![var(3)])
            }],
        );
        let b = F::Atom(1, vec![if case & 2 == 0 { var(7) } else { var(3) }]);
        let body = match case % 3 {
            0 => F::And(Box::new(a), Box::new(b)),
            1 => F::Or(Box::new(a), Box::new(b)),
            _ => F::Implies(Box::new(a), Box::new(b)),
        };
        let body = if case & 4 == 0 {
            all(7, body)
        } else {
            exists(7, body)
        };
        let formula = if case & 8 == 0 {
            all(3, body)
        } else {
            exists(3, body)
        };
        let input = [Declaration {
            formula,
            positive: case & 16 == 0,
        }];
        let result = skolemize_problem(&input, &sig, &Limits::default()).unwrap();
        let bits: usize = result.signature.functions[1..]
            .iter()
            .map(|arity| 1 << arity)
            .sum();
        for original in 0..4 {
            let original_table = vec![vec![original & 1, (original >> 1) & 1]];
            for predicates in 0..16 {
                let original_truth =
                    formula_value(&input[0].formula, &mut [0; 8], &original_table, predicates)
                        == input[0].positive;
                let mut extension_exists = false;
                for extension in 0..(1 << bits) {
                    let mut tables = original_table.clone();
                    let mut shift = 0;
                    for arity in &result.signature.functions[1..] {
                        let count = 1 << arity;
                        tables.push(
                            (0..count)
                                .map(|index| (extension >> (shift + index)) & 1)
                                .collect(),
                        );
                        shift += count;
                    }
                    extension_exists |=
                        nnf_value(&result.formulas[0], &mut [0; 8], &tables, predicates);
                }
                assert_eq!(
                    original_truth, extension_exists,
                    "case={case} function={original} predicates={predicates}"
                );
            }
        }
    }
}
