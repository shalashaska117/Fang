use fang::syntax::{Clause, Literal, Term};
use fang_fof_core::naming::{Definition, name_nnf, name_then_clausify};
use fang_fof_core::nnf_entry::clausify_nnf_from;
use fang_fof_core::{Error, Limits, Nnf, Resource, Statistics};

fn literal(predicate: u32, positive: bool, arguments: Vec<Term>) -> Nnf {
    Nnf::Literal(Literal {
        positive,
        predicate,
        arguments,
    })
}

fn atom(predicate: u32) -> Nnf {
    literal(predicate, true, vec![])
}

fn and(left: Nnf, right: Nnf) -> Nnf {
    Nnf::And(Box::new(left), Box::new(right))
}

fn or(left: Nnf, right: Nnf) -> Nnf {
    Nnf::Or(Box::new(left), Box::new(right))
}

fn conjunction(predicates: &[u32]) -> Nnf {
    let mut formula = atom(predicates[0]);
    for predicate in &predicates[1..] {
        formula = and(formula, atom(*predicate));
    }
    formula
}

fn unlimited() -> Limits {
    Limits {
        max_clauses: 1_000_000,
        max_literals: 10_000_000,
        max_stored_nodes: 100_000_000,
        max_operations: 100_000_000,
        ..Limits::default()
    }
}

fn copy(formula: &Nnf) -> Nnf {
    match formula {
        Nnf::Literal(literal) => Nnf::Literal(literal.clone()),
        Nnf::True => Nnf::True,
        Nnf::False => Nnf::False,
        Nnf::And(left, right) => and(copy(left), copy(right)),
        Nnf::Or(left, right) => or(copy(left), copy(right)),
    }
}

#[test]
fn product_above_threshold_names_left_side_on_tie() {
    let formula = or(conjunction(&[0, 1, 2]), conjunction(&[3, 4, 5]));
    let renamed = name_nnf(&formula, 8, 10, &Limits::default(), Statistics::default()).unwrap();
    let guard = literal(10, false, vec![]);
    let expected = and(
        or(atom(10), conjunction(&[3, 4, 5])),
        or(guard, conjunction(&[0, 1, 2])),
    );
    assert_eq!(renamed.formula, expected);
    assert_eq!(
        renamed.definitions,
        vec![Definition {
            predicate: 10,
            arguments: vec![]
        }]
    );
    assert_eq!(renamed.next, 11);
}

#[test]
fn product_at_threshold_is_copied() {
    let formula = or(conjunction(&[0, 1, 2]), conjunction(&[3, 4, 5]));
    let renamed = name_nnf(&formula, 9, 10, &Limits::default(), Statistics::default()).unwrap();
    assert_eq!(renamed.formula, formula);
    assert!(renamed.definitions.is_empty());
    assert_eq!(renamed.next, 10);
}

#[test]
fn larger_side_is_named() {
    let formula = or(conjunction(&[0, 1]), conjunction(&[2, 3, 4]));
    let renamed = name_nnf(&formula, 2, 7, &Limits::default(), Statistics::default()).unwrap();
    let expected = and(
        or(conjunction(&[0, 1]), atom(7)),
        or(literal(7, false, vec![]), conjunction(&[2, 3, 4])),
    );
    assert_eq!(renamed.formula, expected);
}

#[test]
fn side_with_one_clause_is_never_named() {
    let formula = or(atom(0), conjunction(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
    let renamed = name_nnf(&formula, 0, 20, &Limits::default(), Statistics::default()).unwrap();
    assert_eq!(renamed.formula, formula);
    let falsity = or(Nnf::False, conjunction(&[1, 2]));
    let renamed = name_nnf(&falsity, 0, 20, &Limits::default(), Statistics::default()).unwrap();
    assert_eq!(renamed.formula, falsity);
    let truth = or(Nnf::True, conjunction(&[1, 2]));
    let renamed = name_nnf(&truth, 0, 20, &Limits::default(), Statistics::default()).unwrap();
    assert_eq!(renamed.formula, truth);
}

#[test]
fn arguments_are_the_increasing_distinct_variables_of_the_body() {
    let left = and(
        literal(
            0,
            true,
            vec![Term::Var(5), Term::Fun(1, vec![Term::Var(2)])],
        ),
        literal(1, false, vec![Term::Var(7), Term::Var(5)]),
    );
    let formula = or(left, and(atom(2), atom(3)));
    let renamed = name_nnf(&formula, 3, 4, &Limits::default(), Statistics::default()).unwrap();
    assert_eq!(
        renamed.definitions,
        vec![Definition {
            predicate: 4,
            arguments: vec![2, 5, 7]
        }]
    );
    let variables = vec![Term::Var(2), Term::Var(5), Term::Var(7)];
    let Nnf::And(renamed_root, definition) = renamed.formula else {
        panic!("one definition expected");
    };
    assert_eq!(
        *renamed_root,
        or(literal(4, true, variables.clone()), and(atom(2), atom(3)))
    );
    let Nnf::Or(guard, _) = *definition else {
        panic!("definition shape");
    };
    assert_eq!(*guard, literal(4, false, variables));
}

#[test]
fn nested_names_are_bottom_up_and_definitions_follow_in_order() {
    // ((a & b) | (c & d)) | (e & f), threshold 3: the inner disjunction names
    // its left side, then the outer one names the inner disjunction.
    let inner = or(conjunction(&[0, 1]), conjunction(&[2, 3]));
    let formula = or(inner, conjunction(&[4, 5]));
    let renamed = name_nnf(&formula, 3, 6, &Limits::default(), Statistics::default()).unwrap();
    assert_eq!(renamed.next, 8);
    let first = or(literal(6, false, vec![]), conjunction(&[0, 1]));
    let second = or(literal(7, false, vec![]), or(atom(6), conjunction(&[2, 3])));
    let expected = and(and(or(atom(7), conjunction(&[4, 5])), first), second);
    assert_eq!(renamed.formula, expected);
    let predicates: Vec<u32> = renamed.definitions.iter().map(|d| d.predicate).collect();
    assert_eq!(predicates, vec![6, 7]);
}

#[test]
fn deterministic() {
    let formula = sample(12345, 6, 4);
    let first = name_then_clausify(&formula, 4, 3, &unlimited(), Statistics::default()).unwrap();
    let second = name_then_clausify(&formula, 4, 3, &unlimited(), Statistics::default()).unwrap();
    assert_eq!(first, second);
}

#[test]
fn without_naming_the_clauses_and_counters_are_those_of_the_clausifier() {
    for seed in 0..50u64 {
        let formula = sample(seed, 5, 4);
        let named =
            name_then_clausify(&formula, usize::MAX, 4, &unlimited(), Statistics::default())
                .unwrap();
        let plain = clausify_nnf_from(&formula, &unlimited(), Statistics::default()).unwrap();
        assert!(named.definitions.is_empty());
        assert_eq!(named.next, 4);
        assert_eq!(named.clauses, plain.clauses);
        assert_eq!(named.statistics, plain.statistics);
    }
}

#[test]
fn clause_count_drops_below_distribution() {
    // Six disjuncts of five atoms: distribution gives 5^6 = 15625 clauses.
    let mut formula = conjunction(&[0, 1, 2, 3, 4]);
    for block in 1..6u32 {
        let start = block * 5;
        formula = or(
            formula,
            conjunction(&[start, start + 1, start + 2, start + 3, start + 4]),
        );
    }
    let named = name_then_clausify(&formula, 8, 30, &unlimited(), Statistics::default()).unwrap();
    assert!(named.clauses.len() < 100, "{} clauses", named.clauses.len());
    let plain = clausify_nnf_from(&formula, &unlimited(), Statistics::default()).unwrap();
    assert_eq!(plain.clauses.len(), 15625);
}

#[test]
fn predicate_index_overflow_is_a_resource_error() {
    let formula = or(conjunction(&[0, 1, 2]), conjunction(&[3, 4, 5]));
    let result = name_nnf(
        &formula,
        8,
        u32::MAX,
        &Limits::default(),
        Statistics::default(),
    );
    assert_eq!(result, Err(Error::Resource(Resource::Arithmetic)));
}

#[test]
fn counters_are_bounded() {
    let formula = or(conjunction(&[0, 1, 2]), conjunction(&[3, 4, 5]));
    let limits = Limits {
        max_operations: 10,
        ..unlimited()
    };
    assert_eq!(
        name_nnf(&formula, 4, 0, &limits, Statistics::default()),
        Err(Error::Resource(Resource::Operations))
    );
    let limits = Limits {
        max_stored_nodes: 5,
        ..unlimited()
    };
    assert_eq!(
        name_nnf(&formula, 4, 0, &limits, Statistics::default()),
        Err(Error::Resource(Resource::StoredNodes))
    );
}

// A small deterministic generator: predicates 0 to 2 over variables 0 to 2 and
// one unary function 0.
struct Generator(u64);

impl Generator {
    fn next(&mut self, bound: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) % bound
    }

    fn term(&mut self, depth: u32) -> Term {
        if depth == 0 || self.next(3) > 0 {
            Term::Var(self.next(3) as u32)
        } else {
            Term::Fun(0, vec![self.term(depth - 1)])
        }
    }

    fn formula(&mut self, depth: u32) -> Nnf {
        let choice = if depth == 0 { 0 } else { self.next(10) };
        match choice {
            0 => {
                let predicate = self.next(3) as u32;
                let arity = predicate as usize;
                let arguments = (0..arity).map(|_| self.term(1)).collect();
                literal(predicate, self.next(2) == 0, arguments)
            }
            1 => {
                if self.next(2) == 0 {
                    Nnf::True
                } else {
                    Nnf::False
                }
            }
            2..=5 => and(self.formula(depth - 1), self.formula(depth - 1)),
            _ => or(self.formula(depth - 1), self.formula(depth - 1)),
        }
    }
}

fn sample(seed: u64, depth: u32, _width: u32) -> Nnf {
    Generator(seed.wrapping_add(17)).formula(depth)
}

// Interpretations over the domain {0, 1}: function 0 is a table of two
// values; predicate p of arity k is a set of 2^k bits.
#[derive(Clone)]
struct Model {
    function: [u8; 2],
    predicates: Vec<u32>,
}

fn evaluate(term: &Term, model: &Model, valuation: &[u8; 3]) -> u8 {
    match term {
        Term::Var(id) => valuation[*id as usize],
        Term::Fun(_, arguments) => {
            model.function[evaluate(&arguments[0], model, valuation) as usize]
        }
    }
}

fn literal_holds(literal: &Literal, model: &Model, valuation: &[u8; 3]) -> bool {
    let mut index = 0usize;
    for argument in &literal.arguments {
        index = index * 2 + evaluate(argument, model, valuation) as usize;
    }
    let value = (model.predicates[literal.predicate as usize] >> index) & 1 == 1;
    value == literal.positive
}

fn holds(formula: &Nnf, model: &Model, valuation: &[u8; 3]) -> bool {
    match formula {
        Nnf::Literal(literal) => literal_holds(literal, model, valuation),
        Nnf::True => true,
        Nnf::False => false,
        Nnf::And(left, right) => holds(left, model, valuation) && holds(right, model, valuation),
        Nnf::Or(left, right) => holds(left, model, valuation) || holds(right, model, valuation),
    }
}

fn valuations() -> Vec<[u8; 3]> {
    (0..8u8)
        .map(|bits| [bits & 1, (bits >> 1) & 1, (bits >> 2) & 1])
        .collect()
}

fn clause_holds(clause: &Clause, model: &Model, valuation: &[u8; 3]) -> bool {
    clause
        .iter()
        .any(|literal| literal_holds(literal, model, valuation))
}

fn models_of_original() -> Vec<Model> {
    // Predicate 0 is nullary (1 bit), 1 unary (2 bits), 2 binary (4 bits).
    let mut models = Vec::new();
    for function in 0..4u8 {
        for bits in 0..(1u32 << 7) {
            models.push(Model {
                function: [function & 1, (function >> 1) & 1],
                predicates: vec![bits & 1, (bits >> 1) & 3, (bits >> 3) & 15],
            });
        }
    }
    models
}

/// Interpret each fresh predicate as the truth of its body, in naming order.
fn extend(model: &Model, definitions: &[Definition], bodies: &[Nnf]) -> Model {
    let mut extended = model.clone();
    for (definition, body) in definitions.iter().zip(bodies) {
        let arity = definition.arguments.len();
        assert!(arity <= 3);
        let mut bits = 0u32;
        for index in 0..(1usize << arity) {
            let mut valuation = [0u8; 3];
            for (position, id) in definition.arguments.iter().enumerate() {
                valuation[*id as usize] = ((index >> (arity - 1 - position)) & 1) as u8;
            }
            if holds(body, &extended, &valuation) {
                bits |= 1 << index;
            }
        }
        assert_eq!(extended.predicates.len(), definition.predicate as usize);
        extended.predicates.push(bits);
    }
    extended
}

fn definition_bodies(formula: &Nnf, count: usize) -> Vec<Nnf> {
    let mut bodies = Vec::new();
    let mut current = formula;
    for _ in 0..count {
        let Nnf::And(rest, definition) = current else {
            panic!("definition shape");
        };
        let Nnf::Or(_, body) = &**definition else {
            panic!("definition shape");
        };
        bodies.push(copy(body));
        current = rest;
    }
    bodies.reverse();
    bodies
}

#[test]
fn brute_force_models_extend_and_restrict() {
    let models = models_of_original();
    let mut named_cases = 0;
    let mut restricted_cases = 0;
    let mut satisfiable_cases = 0;
    for seed in 0..120u64 {
        let formula = sample(seed, 5, 4);
        for threshold in [1usize, 2, 4] {
            let named =
                name_then_clausify(&formula, threshold, 3, &unlimited(), Statistics::default())
                    .unwrap();
            let renamed =
                name_nnf(&formula, threshold, 3, &unlimited(), Statistics::default()).unwrap();
            let bodies = definition_bodies(&renamed.formula, renamed.definitions.len());
            if !renamed.definitions.is_empty() {
                named_cases += 1;
            }
            let mut input_satisfiable = false;
            let mut output_satisfiable = false;
            for model in &models {
                let model_of_input = valuations().iter().all(|v| holds(&formula, model, v));
                // Model extension: interpreting each fresh predicate as its body
                // turns a model of the input into a model of every clause.
                if model_of_input {
                    input_satisfiable = true;
                    let extended = extend(model, &renamed.definitions, &bodies);
                    for valuation in valuations() {
                        for clause in &named.clauses {
                            assert!(clause_holds(clause, &extended, &valuation), "seed {seed}");
                        }
                    }
                }
            }
            // Restriction: a model of the clauses, over every interpretation of
            // the fresh predicates, satisfies the input.
            let arities: Vec<usize> = renamed
                .definitions
                .iter()
                .map(|d| d.arguments.len())
                .collect();
            let choices: Vec<u64> = arities.iter().map(|a| 1u64 << (1u32 << a)).collect();
            let total: u64 = choices.iter().product();
            if total <= 64 && total > 1 {
                restricted_cases += 1;
                for model in &models {
                    for choice in 0..total {
                        let mut extended = model.clone();
                        let mut rest = choice;
                        for count in &choices {
                            extended.predicates.push((rest % count) as u32);
                            rest /= count;
                        }
                        let model_of_clauses = valuations()
                            .iter()
                            .all(|v| named.clauses.iter().all(|c| clause_holds(c, &extended, v)));
                        if model_of_clauses {
                            output_satisfiable = true;
                            assert!(
                                valuations().iter().all(|v| holds(&formula, model, v)),
                                "seed {seed}"
                            );
                        }
                    }
                }
                assert_eq!(input_satisfiable, output_satisfiable, "seed {seed}");
                if input_satisfiable {
                    satisfiable_cases += 1;
                }
            }
        }
    }
    assert!(named_cases > 50, "{named_cases} cases with a definition");
    assert!(restricted_cases > 20, "{restricted_cases} restricted cases");
    assert!(
        satisfiable_cases > 10,
        "{satisfiable_cases} satisfiable restricted cases"
    );
    println!("{named_cases} named, {restricted_cases} restricted, {satisfiable_cases} satisfiable");
}

#[test]
fn formula_depth_follows_the_limits_record() {
    use fang_fof_core::{Formula, Signature, VariableScope, validate_with_scope};
    let mut formula = Formula::True;
    for _ in 0..99 {
        formula = Formula::Not(Box::new(formula));
    }
    let signature = Signature {
        functions: vec![],
        predicates: vec![],
    };
    let deep = Limits {
        max_formula_depth: 100,
        ..Limits::default()
    };
    assert!(validate_with_scope(&formula, &signature, VariableScope::Ground, &deep).is_ok());
    let shallow = Limits {
        max_formula_depth: 99,
        ..Limits::default()
    };
    assert_eq!(
        validate_with_scope(&formula, &signature, VariableScope::Ground, &shallow),
        Err(Error::Resource(Resource::FormulaDepth))
    );
}

#[test]
fn renumbering_moves_the_slot_above_the_named_predicates() {
    use fang_fof_core::naming::renumber_predicate;
    // Original predicates 0..5, slot 6, named 7 and 8.
    let mapped: Vec<u32> = (0..10)
        .map(|p| renumber_predicate(p, 6, 2).unwrap())
        .collect();
    assert_eq!(mapped, vec![0, 1, 2, 3, 4, 5, 8, 6, 7, 9]);
    assert_eq!(renumber_predicate(6, 6, 0), Some(6));
    assert_eq!(renumber_predicate(u32::MAX - 1, u32::MAX - 1, 2), None);
}
