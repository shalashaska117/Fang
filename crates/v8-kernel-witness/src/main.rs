// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Untrusted version-8 equality witness suggestions from separate actual component calls.
// The expanded frontend replaces the version-7 frontend; everything after it is the
// version-7 witness unchanged. This is not an observation of one producer run.
#![forbid(unsafe_code)]
use fang::syntax::{Literal, Term};
use fang_quantified_fof_core::{Formula, Nnf};
use std::io::Read;

const SOURCE_BYTES: usize = 4096;
const CERTIFICATE_BYTES: usize = 65536;
const WITNESS_BYTES: usize = 16 << 20;

struct Json(String);
impl Json {
    fn raw(&mut self, text: &str) {
        assert!(
            text.len() <= WITNESS_BYTES - self.0.len(),
            "witness byte limit"
        );
        self.0.push_str(text);
    }
    fn number(&mut self, value: impl std::fmt::Display) {
        self.raw(&value.to_string());
    }
    fn string(&mut self, value: &str) {
        self.raw("\"");
        for byte in value.bytes() {
            match byte {
                b'"' => self.raw("\\\""),
                b'\\' => self.raw("\\\\"),
                32..=126 => self.raw(&(byte as char).to_string()),
                _ => self.raw(&format!("\\u{byte:04x}")),
            }
        }
        self.raw("\"");
    }
    fn list<T>(&mut self, values: &[T], emit: impl Fn(&mut Self, &T)) {
        self.raw("[");
        for (index, value) in values.iter().enumerate() {
            if index != 0 {
                self.raw(",");
            }
            emit(self, value);
        }
        self.raw("]");
    }
    fn term(&mut self, term: &Term) {
        match term {
            Term::Var(id) => {
                self.raw("[\"var\",");
                self.number(id);
                self.raw("]");
            }
            Term::Fun(id, args) => {
                self.raw("[\"fun\",");
                self.number(id);
                self.raw(",");
                self.list(args, Self::term);
                self.raw("]");
            }
        }
    }
    fn formula(&mut self, formula: &Formula) {
        match formula {
            Formula::Atom(id, args) => {
                self.raw("[\"atom\",");
                self.number(id);
                self.raw(",");
                self.list(args, Self::term);
                self.raw("]");
            }
            Formula::Not(body) => {
                self.raw("[\"not\",");
                self.formula(body);
                self.raw("]");
            }
            Formula::Forall(id, body) | Formula::Exists(id, body) => {
                self.raw(if matches!(formula, Formula::Forall(..)) {
                    "[\"all\","
                } else {
                    "[\"ex\","
                });
                self.number(id);
                self.raw(",");
                self.formula(body);
                self.raw("]");
            }
            Formula::True => self.raw("[\"truth\"]"),
            Formula::False => self.raw("[\"falsity\"]"),
            Formula::And(left, right)
            | Formula::Or(left, right)
            | Formula::Implies(left, right) => {
                self.raw(match formula {
                    Formula::And(..) => "[\"conj\",",
                    Formula::Or(..) => "[\"disj\",",
                    _ => "[\"implies\",",
                });
                self.formula(left);
                self.raw(",");
                self.formula(right);
                self.raw("]");
            }
        }
    }
    fn literal(&mut self, literal: &Literal) {
        self.raw("[");
        self.raw(if literal.positive { "true," } else { "false," });
        self.number(literal.predicate);
        self.raw(",");
        self.list(&literal.arguments, Self::term);
        self.raw("]");
    }
    fn equality_literal(&mut self, literal: &fang_equality_inference_core::Literal) {
        self.raw("[");
        self.raw(if literal.positive { "true," } else { "false," });
        match &literal.atom {
            fang_equality_inference_core::Atom::Predicate(id, args) => {
                self.raw("[\"predicate\",");
                self.number(id);
                self.raw(",");
                self.list(args, Self::term);
                self.raw("]");
            }
            fang_equality_inference_core::Atom::Equal(left, right) => {
                self.raw("[\"equal\",");
                self.term(left);
                self.raw(",");
                self.term(right);
                self.raw("]");
            }
        }
        self.raw("]");
    }
    fn nnf(&mut self, formula: &Nnf) {
        match formula {
            Nnf::Literal(literal) => {
                self.raw("[\"literal\",");
                self.literal(literal);
                self.raw("]");
            }
            Nnf::Forall(id, body) | Nnf::Exists(id, body) => {
                self.raw(if matches!(formula, Nnf::Forall(..)) {
                    "[\"all\","
                } else {
                    "[\"ex\","
                });
                self.number(id);
                self.raw(",");
                self.nnf(body);
                self.raw("]");
            }
            Nnf::True => self.raw("[\"truth\"]"),
            Nnf::False => self.raw("[\"falsity\"]"),
            Nnf::And(left, right) | Nnf::Or(left, right) => {
                self.raw(if matches!(formula, Nnf::And(..)) {
                    "[\"conj\","
                } else {
                    "[\"disj\","
                });
                self.nnf(left);
                self.raw(",");
                self.nnf(right);
                self.raw("]");
            }
        }
    }
    fn core_stats(&mut self, stats: &fang_quantified_fof_core::Statistics) {
        self.list(
            &[
                stats.operations,
                stats.input_formula_nodes,
                stats.input_term_nodes,
                stats.allocated_nodes,
                stats.output_clauses,
                stats.output_literals,
                stats.output_term_nodes,
                stats.input_binders,
            ],
            |out, value| out.number(value),
        );
    }
    fn bytes(&mut self, bytes: &[u8]) {
        self.raw("\"");
        for byte in bytes {
            self.raw(&format!("{byte:02x}"));
        }
        self.raw("\"");
    }
}

fn read_once(path: &std::ffi::OsStr, cap: usize) -> Vec<u8> {
    let file = std::fs::File::open(path).expect("open sealed file");
    assert!(
        file.metadata().expect("metadata").is_file(),
        "regular file required"
    );
    let mut bytes = Vec::new();
    file.take(cap as u64 + 1)
        .read_to_end(&mut bytes)
        .expect("read sealed file");
    assert!(bytes.len() <= cap, "sealed byte limit");
    bytes
}

fn main() {
    let paths: Vec<_> = std::env::args_os().skip(1).collect();
    assert_eq!(paths.len(), 2, "usage: witness INPUT CERTIFICATE");
    let source = read_once(&paths[0], SOURCE_BYTES);
    let certificate = read_once(&paths[1], CERTIFICATE_BYTES);
    assert!(
        source.is_ascii() && certificate.is_ascii(),
        "ASCII bytes required"
    );
    let parser_limits = fang_tptp_full_frontend_candidate::Limits::default();
    let parsed = fang_tptp_full_frontend_candidate::parse(&source, &parser_limits)
        .expect("source parses")
        .encode(100_000, 256)
        .expect("reserved equality encoding");
    // A true CNF row has no declaration in the Lean replay; names carry their kind as in taggedName.
    let active: Vec<_> = parsed
        .declarations
        .into_iter()
        .filter(|declaration| {
            !matches!(
                &declaration.body,
                fang_tptp_full_frontend_candidate::EncodedBody::Cnf(None)
            )
        })
        .collect();
    assert!(active.len() <= 16, "declaration witness limit");
    let tagged = |declaration: &fang_tptp_full_frontend_candidate::Declaration<
        fang_tptp_full_frontend_candidate::EncodedBody,
    >| {
        match declaration.name_kind {
            fang_tptp_full_frontend_candidate::NameKind::Atom => {
                format!("atom:{}", declaration.name)
            }
            fang_tptp_full_frontend_candidate::NameKind::Integer => {
                format!("integer:{}", declaration.name)
            }
        }
    };
    let mut json = Json(String::new());
    json.raw("{\"schema\":\"fang-equality-kernel-witness-1\",\"source_hex\":");
    json.bytes(&source);
    json.raw(",\"certificate_hex\":");
    json.bytes(&certificate);
    for (key, symbols) in [
        ("functions", &parsed.functions),
        ("original_predicates", &parsed.original_predicates),
    ] {
        json.raw(",");
        json.string(key);
        json.raw(":");
        json.list(symbols, |out, symbol| {
            out.raw("[");
            out.string(&symbol.name);
            out.raw(",");
            out.number(symbol.arity);
            out.raw("]");
        });
    }
    json.raw(",\"equality_id\":");
    json.number(parsed.reservation.equality_id());
    json.raw(",\"extended_predicates\":");
    json.list(&parsed.reservation.extended_arities(), |out, arity| {
        out.number(arity)
    });
    json.raw(",\"source_declarations\":");
    json.list(&active, |out, declaration| {
        out.raw("{\"name\":");
        out.string(&tagged(declaration));
        out.raw(",\"variables\":");
        out.list(&declaration.variables, |out, name| out.string(name));
        out.raw(",\"body\":");
        match &declaration.body {
            fang_tptp_full_frontend_candidate::EncodedBody::Fof(formula) => {
                out.raw("[\"fof\",");
                out.formula(formula);
                out.raw("]");
            }
            fang_tptp_full_frontend_candidate::EncodedBody::Cnf(Some(clause)) => {
                out.raw("[\"cnf\",");
                out.list(clause, Json::literal);
                out.raw("]");
            }
            fang_tptp_full_frontend_candidate::EncodedBody::Cnf(None) => {
                unreachable!("true rows filtered")
            }
        }
        out.raw("}");
    });
    json.raw(",\"declarations\":");
    let fof: Vec<_> = active
        .iter()
        .filter(|declaration| {
            matches!(
                &declaration.body,
                fang_tptp_full_frontend_candidate::EncodedBody::Fof(_)
            )
        })
        .collect();
    json.list(&fof, |out, declaration| {
        out.raw("{\"name\":");
        out.string(&tagged(declaration));
        out.raw(",\"variables\":");
        out.list(&declaration.variables, |out, name| out.string(name));
        out.raw(",\"formula\":");
        if let fang_tptp_full_frontend_candidate::EncodedBody::Fof(formula) = &declaration.body {
            out.formula(formula);
        } else {
            unreachable!("filtered FOF declaration");
        }
        out.raw("}");
    });
    let signature = fang_quantified_fof_core::Signature {
        functions: parsed.functions.iter().map(|symbol| symbol.arity).collect(),
        predicates: parsed.reservation.extended_arities(),
    };
    let core = fang_quantified_fof_core::Limits::default();
    let mut layout = Vec::new();
    let declarations: Vec<_> = active
        .into_iter()
        .filter_map(|declaration| match declaration.body {
            fang_tptp_full_frontend_candidate::EncodedBody::Fof(formula) => {
                layout.push(None);
                Some(fang_skolem_core::Declaration {
                    formula,
                    positive: true,
                })
            }
            fang_tptp_full_frontend_candidate::EncodedBody::Cnf(Some(clause)) => {
                layout.push(Some(clause));
                None
            }
            fang_tptp_full_frontend_candidate::EncodedBody::Cnf(None) => {
                unreachable!("true rows filtered")
            }
        })
        .collect();
    json.raw(",\"standalone\":");
    json.list(&declarations, |out, declaration| {
        let validated = fang_quantified_fof_core::validate(&declaration.formula, &signature, &core)
            .expect("validate");
        let rectified =
            fang_quantified_fof_core::rectify_closed(&declaration.formula, &signature, &core)
                .expect("rectify");
        let normalized = fang_quantified_fof_core::rectify_normalize_closed(
            &declaration.formula,
            true,
            &signature,
            &core,
        )
        .expect("normalize");
        out.raw("{\"validated\":");
        out.core_stats(&validated);
        out.raw(",\"rectified\":");
        out.formula(&rectified.formula);
        out.raw(",\"binder_count\":");
        out.number(rectified.binder_count);
        out.raw(",\"rectified_stats\":");
        out.core_stats(&rectified.statistics);
        out.raw(",\"normalized\":");
        out.nnf(&normalized.formula);
        out.raw(",\"normalized_stats\":");
        out.core_stats(&normalized.statistics);
        out.raw("}");
    });
    let transformed = fang_skolem_core::skolemize_problem(
        &declarations,
        &signature,
        &fang_skolem_core::Limits::default(),
    )
    .expect("Skolem preprocessing");
    json.raw(",\"skolem\":{\"formulas\":");
    json.list(&transformed.formulas, Json::nnf);
    json.raw(",\"functions\":");
    json.list(&transformed.signature.functions, |out, arity| {
        out.number(arity)
    });
    json.raw(",\"predicates\":");
    json.list(&transformed.signature.predicates, |out, arity| {
        out.number(arity)
    });
    json.raw(",\"introduced\":");
    json.list(&transformed.introduced, |out, introduced| {
        out.raw("[");
        out.number(introduced.declaration);
        out.raw(",");
        out.number(introduced.binder);
        out.raw(",");
        out.number(introduced.function);
        out.raw(",");
        out.list(&introduced.universals, |out, id| out.number(id));
        out.raw("]");
    });
    json.raw(",\"statistics\":");
    json.list(
        &[
            transformed.statistics.operations,
            transformed.statistics.allocated_nodes,
        ],
        |out, value| out.number(value),
    );
    json.raw("},\"blocks\":[");
    let mut blocks = Vec::new();
    for (index, formula) in transformed.formulas.into_iter().enumerate() {
        if index != 0 {
            json.raw(",");
        }
        let removed = fang_binder_removal_core::remove_universals(
            formula,
            &fang_binder_removal_core::Limits {
                max_formula_depth: 64,
                max_operations: 5_000_000,
                max_output_nodes: 1_000_000,
            },
        )
        .expect("remove universals");
        let clausified = fang_fof_core::nnf_entry::clausify_nnf_from(
            &removed.formula,
            &fang_fof_core::Limits::default(),
            fang_fof_core::Statistics::default(),
        )
        .expect("clausify");
        json.raw("{\"removal_stats\":");
        json.list(
            &[
                removed.statistics.operations,
                removed.statistics.output_nodes,
            ],
            |out, value| out.number(value),
        );
        json.raw(",\"clauses\":");
        json.list(&clausified.clauses, |out, clause| {
            out.list(clause, Json::literal)
        });
        json.raw(",\"clausifier_stats\":");
        let stats = clausified.statistics;
        json.list(
            &[
                stats.operations,
                stats.input_formula_nodes,
                stats.input_term_nodes,
                stats.allocated_nodes,
                stats.output_clauses,
                stats.output_literals,
                stats.output_term_nodes,
            ],
            |out, value| out.number(value),
        );
        json.raw("}");
        blocks.push(clausified.clauses);
    }
    // Assembly is only a witness suggestion. The emitted Lean assembly equation
    // must check this exact mixed order and each literal deduplication.
    let mut pending = blocks.into_iter();
    let mut ordinary = Vec::new();
    for declaration in layout {
        let clauses = match declaration {
            Some(clause) => vec![clause],
            None => pending.next().expect("one block per FOF declaration"),
        };
        ordinary.extend(clauses.iter().map(fang::syntax::deduplicate));
    }
    assert!(pending.next().is_none(), "unused FOF block");
    json.raw("],\"ordinary\":");
    json.list(&ordinary, |out, clause| out.list(clause, Json::literal));
    let equality: Vec<_> = ordinary
        .into_iter()
        .map(|clause| {
            parsed
                .reservation
                .decode_clause(clause, 256)
                .expect("actual equality conversion")
        })
        .collect();
    json.raw(",\"equality\":");
    json.list(&equality, |out, clause| {
        out.list(clause, Json::equality_literal)
    });
    json.raw("}");
    println!("{}", json.0);
}
