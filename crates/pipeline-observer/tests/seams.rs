use candidate::observer::{Event, ObservationError, Observer};
use fang::syntax::{Clause, Literal, Symbol, Term};
use fang_quantified_fof_frontend::{Body, parse};
use fang_quantified_pipeline_observer as candidate;

fn same(input: &[u8], limits: &candidate::Limits) {
    let reference_limits = fang_quantified_pipeline::Limits {
        input: limits.input.clone(),
        preprocessing: limits.preprocessing,
        max_bookkeeping_operations: limits.max_bookkeeping_operations,
        max_generated_name_bytes: limits.max_generated_name_bytes,
    };
    let original = fang_quantified_pipeline::prepare(input, &reference_limits);
    let observed = candidate::prepare(input, limits);
    match (original, observed) {
        (Ok(left), Ok(right)) => {
            assert_eq!(left.problem, right.problem);
            assert_eq!(
                format!("{:?}", left.origins),
                format!("{:?}", right.origins)
            );
            assert_eq!(
                format!("{:?}", left.introduced),
                format!("{:?}", right.introduced)
            );
            assert_eq!(
                format!("{:?}", left.statistics),
                format!("{:?}", right.statistics)
            );
        }
        (Err(left), Err(right)) => assert_eq!(format!("{left:?}"), format!("{right:?}")),
        other => panic!("outcome changed: {other:?}"),
    }
}

#[derive(Default)]
struct Recorder {
    names: Vec<&'static str>,
    origins: Vec<usize>,
    raw: Vec<Vec<Clause>>,
    remaining: Option<usize>,
    introduced: Vec<(usize, u32, u32, Vec<u32>)>,
}

impl Observer for Recorder {
    type Error = &'static str;
    fn observe(&mut self, event: Event<'_>) -> Result<(), Self::Error> {
        if let Some(remaining) = &mut self.remaining {
            if *remaining == 0 {
                return Err("test observation event cap");
            }
            *remaining -= 1;
        }
        match event {
            Event::Parsed(parsed) => {
                self.names.push("parsed");
                assert!(!parsed.declarations.is_empty());
            }
            Event::Skolemized {
                fof_origins,
                output,
            } => {
                self.names.push("skolem");
                self.origins = fof_origins.to_vec();
                assert_eq!(fof_origins.len(), output.formulas.len());
            }
            Event::Symbols {
                functions,
                predicates: _,
                introduced,
            } => {
                self.names.push("symbols");
                for symbol in introduced {
                    assert_eq!(
                        functions[symbol.function as usize].arity,
                        symbol.universals.len()
                    );
                    self.introduced.push((
                        symbol.declaration,
                        symbol.binder,
                        symbol.function,
                        symbol.universals.clone(),
                    ));
                }
            }
            Event::Removed {
                declaration: _,
                output: _,
            } => self.names.push("removed"),
            Event::ClauseBlock {
                declaration,
                clauses,
            } => {
                self.names.push("block");
                assert_eq!(declaration, self.raw.len());
                // Fixed small test fixtures only. Production recorders need a
                // separate byte/node cap before retaining borrowed values.
                self.raw.push(clauses.to_vec());
            }
            Event::Prepared(output) => {
                self.names.push("prepared");
                let expected: Vec<_> = self
                    .raw
                    .iter()
                    .flatten()
                    .map(fang::syntax::deduplicate)
                    .collect();
                assert_eq!(expected, output.problem.clauses);
            }
        }
        Ok(())
    }
}

#[test]
fn complete_event_order_and_raw_duplicate_blocks() {
    let input = b"fof(t,axiom,$true).cnf(a,axiom,(p|p)).fof(b,axiom,![Unused,X]:?[Y]:(q(X,Y)&q(X,Y))).cnf(c,axiom,($false)).";
    let mut recorder = Recorder::default();
    let output =
        candidate::prepare_observed(input, &candidate::Limits::default(), &mut recorder).unwrap();
    assert_eq!(
        recorder.names,
        [
            "parsed", "skolem", "symbols", "removed", "block", "block", "removed", "block",
            "block", "prepared"
        ]
    );
    assert_eq!(recorder.origins, [0, 2]);
    assert_eq!(
        recorder.raw.iter().map(Vec::len).collect::<Vec<_>>(),
        [0, 1, 2, 1]
    );
    assert_eq!(recorder.raw[1][0].len(), 2);
    assert!(recorder.raw[3][0].is_empty());
    assert_eq!(output.problem.clauses.len(), 4);
    assert_eq!(recorder.introduced, [(2, 2, 0, vec![0, 1])]);
    same(input, &candidate::Limits::default());
}

#[test]
fn actual_skolem_and_removed_formulas_are_exposed() {
    struct FormulaCheck;
    impl Observer for FormulaCheck {
        type Error = std::convert::Infallible;
        fn observe(&mut self, event: Event<'_>) -> Result<(), Self::Error> {
            let expected = Literal {
                positive: true,
                predicate: 0,
                arguments: vec![Term::Var(0), Term::Fun(0, vec![Term::Var(0)])],
            };
            match event {
                Event::Skolemized { output, .. } => {
                    let fang_quantified_fof_core::Nnf::Forall(0, body) = &output.formulas[0] else {
                        panic!()
                    };
                    assert_eq!(
                        body.as_ref(),
                        &fang_quantified_fof_core::Nnf::Literal(expected)
                    );
                }
                Event::Removed { output, .. } => {
                    assert_eq!(output.formula, fang_fof_core::Nnf::Literal(expected))
                }
                _ => (),
            }
            Ok(())
        }
    }
    candidate::prepare_observed(
        b"fof(a,axiom,![X]:?[Y]:p(X,Y)).",
        &candidate::Limits::default(),
        &mut FormulaCheck,
    )
    .unwrap();
}

#[test]
fn caller_parsed_entry_has_exact_byte_wrapper_output() {
    let input = b"fof(a,axiom,?[X]:(p(X)|q)).cnf(b,axiom,(r(c))).";
    let limits = candidate::Limits::default();
    let direct = candidate::prepare(input, &limits).unwrap();
    let parsed = parse(input, &limits.input).unwrap();
    let lowered = candidate::prepare_parsed(parsed, &limits).unwrap();
    assert_eq!(direct.problem, lowered.problem);
    assert_eq!(direct.origins, lowered.origins);
    assert_eq!(direct.introduced, lowered.introduced);
    assert_eq!(direct.statistics, lowered.statistics);
}

#[test]
fn numeric_reserved_slot_needs_no_text_roundtrip() {
    let limits = candidate::Limits::default();
    let mut parsed = parse(b"cnf(a,axiom,(p(c))).", &limits.input).unwrap();
    parsed.predicates.push(Symbol {
        name: "internal_equality".into(),
        arity: 2,
    });
    parsed.declarations[0].body = Body::Cnf(vec![Literal {
        positive: true,
        predicate: 1,
        arguments: vec![Term::Fun(0, vec![]), Term::Fun(0, vec![])],
    }]);
    // This tests a numeric seam only. The supplied predicate remains ordinary
    // here; the separate equality Reservation owns its built-in meaning.
    let output = candidate::prepare_parsed(parsed, &limits).unwrap();
    assert_eq!(output.problem.predicates[1].arity, 2);
    assert_eq!(output.problem.clauses[0][0].predicate, 1);
}

#[test]
fn observed_failures_are_separate_and_do_not_report_completion() {
    let mut recorder = Recorder {
        remaining: Some(3),
        ..Recorder::default()
    };
    let result = candidate::prepare_observed(
        b"fof(a,axiom,?[X]:p(X)).",
        &candidate::Limits::default(),
        &mut recorder,
    );
    assert!(matches!(
        result,
        Err(ObservationError::Observer("test observation event cap"))
    ));
    assert_eq!(recorder.names, ["parsed", "skolem", "symbols"]);
    assert!(!recorder.names.contains(&"prepared"));
}

#[test]
fn original_resource_failures_keep_partial_events_uncommitted() {
    let mut limits = candidate::Limits::default();
    limits.preprocessing.core.max_clauses = 1;
    let mut recorder = Recorder::default();
    let input = b"fof(a,axiom,(p&q)).";
    let result = candidate::prepare_observed(input, &limits, &mut recorder);
    assert!(matches!(result, Err(ObservationError::Preparation(_))));
    assert_eq!(recorder.names, ["parsed", "skolem", "symbols", "removed"]);
    same(input, &limits);
}

#[test]
fn every_stage_limit_keeps_the_disabled_outcome() {
    let input = b"fof(a,axiom,![X]:?[Y]:((p(X,Y)&q)|r)).cnf(b,axiom,(s(c))).";
    for choice in 0..9 {
        let mut limits = candidate::Limits::default();
        match choice {
            0 => limits.input.input.max_input_bytes = 1,
            1 => limits.preprocessing.max_declarations = 1,
            2 => limits.preprocessing.max_functions = 1,
            3 => limits.preprocessing.max_skolem_symbols = 0,
            4 => limits.preprocessing.core.max_operations = 5,
            5 => limits.preprocessing.core.max_stored_nodes = 5,
            6 => limits.preprocessing.core.max_literals_per_clause = 1,
            7 => limits.max_generated_name_bytes = 1,
            8 => limits.max_bookkeeping_operations = 1,
            _ => unreachable!(),
        }
        same(input, &limits);
    }
}

#[test]
fn rejected_input_has_no_observation_event() {
    for input in [
        b"fof(a,axiom,a=b).".as_slice(),
        b"fof(a,conjecture,p).",
        b"fof(a,axiom,p(X)).",
    ] {
        let mut recorder = Recorder::default();
        assert!(matches!(
            candidate::prepare_observed(input, &candidate::Limits::default(), &mut recorder),
            Err(ObservationError::Preparation(_))
        ));
        assert!(recorder.names.is_empty());
        same(input, &candidate::Limits::default());
    }
}

#[test]
fn prepared_entry_revalidates_closed_fof() {
    let limits = candidate::Limits::default();
    let mut parsed = parse(b"fof(a,axiom,p).", &limits.input).unwrap();
    parsed.declarations[0].body = Body::Fof(fang_quantified_fof_core::Formula::Atom(
        0,
        vec![Term::Var(0)],
    ));
    assert!(matches!(
        candidate::prepare_parsed(parsed, &limits),
        Err(candidate::Error::Skolem(_))
    ));
}

#[test]
fn generated_scopes_and_mixed_order_preserve_all_outputs_and_counters() {
    for bits in 0..128u32 {
        let mut formula = "p(X,Y)".to_string();
        for position in 0..4 {
            let quantifier = if bits & (1 << position) == 0 {
                '!'
            } else {
                '?'
            };
            let variable = if position % 2 == 0 { 'X' } else { 'Y' };
            formula = format!("{quantifier}[{variable}]:({formula})");
        }
        if bits & 16 != 0 {
            formula = format!("~({formula})");
        }
        if bits & 32 != 0 {
            formula = format!("({formula}&q)");
        }
        if bits & 64 != 0 {
            formula = format!("({formula}|r)");
        }
        let input = format!(
            "fof(t,axiom,$true).cnf(before,axiom,(s(c)|s(c))).fof(a,axiom,{formula}).cnf(after,axiom,($false))."
        );
        same(input.as_bytes(), &candidate::Limits::default());
        let mut recorder = Recorder::default();
        candidate::prepare_observed(
            input.as_bytes(),
            &candidate::Limits::default(),
            &mut recorder,
        )
        .unwrap();
        assert_eq!(recorder.origins, [0, 2]);
        assert_eq!(recorder.raw.len(), 4);
    }
}
