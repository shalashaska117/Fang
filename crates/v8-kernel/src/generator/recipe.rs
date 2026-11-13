// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! recipe/equality/generate-cnf.py and generate-quantified.py: the version-7 modules for one
//! sealed pair. The CNF recipe takes witnesses whose source declarations are all CNF; the
//! quantified recipe takes the rest. Both check the witness's suggestions against the
//! validated witness before emitting anything.

use std::collections::BTreeSet;

use fang_json::{Object, Value};

use super::certificate::checked_module;
use super::emit::{encoding_bounds, term, term_value, vec};
use super::validate::{SCHEMA, fields, validate};
use super::witness::{
    Body, Literal, Term, Witness, literal_value, natural_value, term_value as term_json,
};
use super::{
    Modules, Outcome, Refusal, clausifier, emit, join, json_string, list_text, py, rectify,
    rejected, removal, require, skolem, split,
};

pub(crate) const HEADER: &str = "/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Untrusted observations are checked against actual calls and sealed bytes. -/\n";
pub(crate) const INTRO: &str = "\nopen Aeneas Aeneas.Std\nnamespace EqInstance\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n";

/// `module(imports, body, audits)`.
pub(crate) fn module(imports: &[String], body: &str, audits: &[&str]) -> String {
    let mut text = HEADER.to_owned();
    for name in imports {
        text.push_str(&format!("import {name}\n"));
    }
    text.push_str(INTRO);
    text.push_str(body);
    for name in audits {
        text.push_str(&format!("#print axioms EqInstance.{name}\n"));
    }
    text.push_str("end EqInstance\n");
    text
}

fn names(items: &[&str]) -> Vec<String> {
    items.iter().map(|item| (*item).to_owned()).collect()
}

/// Which recipe.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Recipe {
    Cnf,
    Quantified,
}

/// The modules and the compile phases.
pub(crate) struct Built {
    pub(crate) modules: Modules,
    pub(crate) phases: Vec<Vec<String>>,
}

/// The checks both recipes make before and after validation, and the values they keep.
struct Checked {
    common: Witness,
    ordinary: Vec<Vec<Literal>>,
    equality: Vec<Value>,
    equality_id: Value,
    extended: Value,
}

fn witness_field<'a>(object: &'a Object, name: &str) -> &'a Value {
    static NULL: Value = Value::Null;
    object.get(name).unwrap_or(&NULL)
}

fn check(recipe: Recipe, source: &[u8], certificate: &[u8], w: &Value) -> Outcome<Checked> {
    let keys = [
        "schema",
        "source_hex",
        "certificate_hex",
        "functions",
        "original_predicates",
        "equality_id",
        "extended_predicates",
        "source_declarations",
        "declarations",
        "standalone",
        "skolem",
        "blocks",
        "ordinary",
        "equality",
    ];
    let w = fields(w, &keys, "unexpected witness fields")?;
    require(
        py::is_text(witness_field(w, "schema"), "fang-equality-kernel-witness-1"),
        "Equality witness schema",
    )?;
    let empty = Value::Array(Vec::new());
    if recipe == Recipe::Cnf {
        let cnf_only = py::equals(witness_field(w, "declarations"), &empty)
            && py::equals(witness_field(w, "blocks"), &empty)
            && py::equals(witness_field(w, "standalone"), &empty);
        require(
            cnf_only,
            "This first equality kernel slice supports CNF only",
        )?;
    }
    // The original predicates were rebuilt by the version-8 generator as [name, arity] pairs.
    let original = py::iterate(witness_field(w, "original_predicates"))?;
    let mut pairs = Vec::new();
    for item in &original {
        pairs.push(py::unpack_two(item)?);
    }
    let count = natural_value(pairs.len() as u64);
    require(
        py::equals(witness_field(w, "equality_id"), &count),
        "Reserved index suggestion",
    )?;
    let mut extended: Vec<Value> = pairs.iter().map(|(_, arity)| arity.clone()).collect();
    extended.push(natural_value(2));
    require(
        py::equals(
            witness_field(w, "extended_predicates"),
            &Value::Array(extended),
        ),
        "Extended table suggestion",
    )?;
    let mut spelling = "reserved_equality".to_owned();
    while pairs.iter().any(|(name, _)| py::is_text(name, &spelling)) {
        spelling.push('_');
    }
    let mut common = Object::new();
    for key in [
        "source_hex",
        "certificate_hex",
        "functions",
        "source_declarations",
        "declarations",
        "standalone",
        "skolem",
        "blocks",
    ] {
        common.set(key, witness_field(w, key).clone());
    }
    common.set("schema", SCHEMA);
    let mut predicates = original.clone();
    predicates.push(Value::Array(vec![
        Value::from(spelling.as_str()),
        natural_value(2),
    ]));
    common.set("predicates", Value::Array(predicates));
    let common = validate(&Value::Object(common), source, certificate)?;
    if recipe == Recipe::Cnf {
        require(
            common
                .source_declarations
                .iter()
                .all(|declaration| matches!(declaration.body, Body::Cnf(_))),
            "CNF declarations only",
        )?;
    }
    let mut ordinary: Vec<Vec<Literal>> = Vec::new();
    let mut block_index = 0;
    for declaration in &common.source_declarations {
        let clauses: Vec<Vec<Literal>> = match &declaration.body {
            Body::Cnf(literals) => vec![literals.clone()],
            Body::Fof(_) => {
                let Some(block) = common.blocks.get(block_index) else {
                    return Err(Refusal::Error("list index out of range".to_owned()));
                };
                block_index += 1;
                block.clauses.clone()
            }
        };
        for row in clauses {
            let mut clause: Vec<Literal> = Vec::new();
            for literal in row {
                if !clause.contains(&literal) {
                    clause.push(literal);
                }
            }
            ordinary.push(clause);
        }
    }
    if recipe == Recipe::Quantified {
        require(block_index == common.blocks.len(), "Mixed block count")?;
    }
    let ordinary_value = Value::Array(
        ordinary
            .iter()
            .map(|clause| Value::Array(clause.iter().map(literal_value).collect()))
            .collect(),
    );
    require(
        py::equals(witness_field(w, "ordinary"), &ordinary_value),
        "Observed ordinary assembly differs",
    )?;
    let equality_id = witness_field(w, "equality_id").clone();
    let mut expected = Vec::new();
    for clause in &ordinary {
        let mut row = Vec::new();
        for literal in clause {
            let atom = if py::equals(&natural_value(literal.predicate), &equality_id) {
                let (Some(left), Some(right)) =
                    (literal.arguments.first(), literal.arguments.get(1))
                else {
                    return Err(Refusal::Error("list index out of range".to_owned()));
                };
                Value::Array(vec![
                    Value::from("equal"),
                    term_json(left),
                    term_json(right),
                ])
            } else {
                Value::Array(vec![
                    Value::from("predicate"),
                    natural_value(literal.predicate),
                    Value::Array(literal.arguments.iter().map(term_json).collect()),
                ])
            };
            row.push(Value::Array(vec![Value::Bool(literal.positive), atom]));
        }
        expected.push(Value::Array(row));
    }
    require(
        py::equals(witness_field(w, "equality"), &Value::Array(expected)),
        "Observed equality conversion differs",
    )?;
    let equality = match witness_field(w, "equality") {
        Value::Array(rows) => rows.clone(),
        _ => Vec::new(),
    };
    Ok(Checked {
        common,
        ordinary,
        equality,
        equality_id,
        extended: witness_field(w, "extended_predicates").clone(),
    })
}

/// `clause(value)`: a numeric clause.
fn clause(value: &[Literal]) -> String {
    let literals = value.iter().map(|literal| {
        format!(
            "⟨{}, {}, [{}]⟩",
            literal.positive,
            literal.predicate,
            join(
                literal
                    .arguments
                    .iter()
                    .map(|argument| term(argument, true)),
                ", "
            )
        )
    });
    format!("[{}]", join(literals, ", "))
}

/// An item of a witness list that `==` already matched against the expected shape.
fn element(value: &Value, index: usize) -> Outcome<&Value> {
    match value {
        Value::Array(items) => items
            .get(index)
            .ok_or_else(|| Refusal::Error("list index out of range".to_owned())),
        other => Err(py::type_error(format!(
            "'{}' object is not subscriptable",
            py::type_name(other)
        ))),
    }
}

/// `input_literal(value, numeric)` on a witness equality literal.
fn input_literal(value: &Value, numeric: bool) -> Outcome<String> {
    let (positive, atom) = py::unpack_two(value)?;
    let body = if py::is_text(element(&atom, 0)?, "equal") {
        format!(
            "(.{} {} {})",
            if numeric { "equal" } else { "Equal" },
            term_value(element(&atom, 1)?, numeric)?,
            term_value(element(&atom, 2)?, numeric)?
        )
    } else {
        let mut rendered = Vec::new();
        for argument in py::iterate(element(&atom, 2)?)? {
            rendered.push(term_value(&argument, numeric)?);
        }
        let symbol = py::text(element(&atom, 1)?);
        if numeric {
            format!("(.predicate ⟨{symbol}, [{}]⟩)", rendered.join(", "))
        } else {
            format!("(.Predicate {symbol}#u32 {})", vec(&rendered))
        }
    };
    Ok(format!("⟨{}, {body}⟩", py::text(&positive).to_lowercase()))
}

/// The literals of one witness equality row.
fn row_literals(row: &Value) -> Outcome<Vec<Value>> {
    py::iterate(row)
}

fn symbols(table: &[super::witness::Symbol]) -> Outcome<String> {
    let mut entries = Vec::new();
    for symbol in table {
        entries.push(format!(
            "({}, {})",
            json_string(&symbol.name)?,
            symbol.arity
        ));
    }
    Ok(format!("[{}]", entries.join(", ")))
}

/// The bounds of one ordinary clause: its width, argument widths and identifiers.
fn clause_bounds(value: &[Literal]) -> (Vec<u64>, Vec<u64>) {
    let mut widths: BTreeSet<u64> = BTreeSet::from([value.len() as u64]);
    let mut identifiers: BTreeSet<u64> = BTreeSet::new();
    fn bounds(value: &Term, widths: &mut BTreeSet<u64>, identifiers: &mut BTreeSet<u64>) {
        match value {
            Term::Var(index) => {
                identifiers.insert(*index);
            }
            Term::Fun(symbol, arguments) => {
                identifiers.insert(*symbol);
                widths.insert(arguments.len() as u64);
                for child in arguments {
                    bounds(child, widths, identifiers);
                }
            }
        }
    }
    for literal in value {
        identifiers.insert(literal.predicate);
        widths.insert(literal.arguments.len() as u64);
        for argument in &literal.arguments {
            bounds(argument, &mut widths, &mut identifiers);
        }
    }
    widths.remove(&0);
    identifiers.remove(&0);
    (
        widths.into_iter().collect(),
        identifiers.into_iter().collect(),
    )
}

fn bound_lines(widths: &[u64], identifiers: &[u64]) -> (String, Vec<String>) {
    let mut lines = String::new();
    for n in widths {
        lines.push_str(&format!(
            "  have width{n} : {n} ≤ Usize.max := by scalar_tac\n"
        ));
    }
    for n in identifiers {
        lines.push_str(&format!(
            "  have identifier{n} : {n} ≤ U32.max := by scalar_tac\n"
        ));
    }
    let mut names: Vec<String> = widths.iter().map(|n| format!("width{n}")).collect();
    names.extend(identifiers.iter().map(|n| format!("identifier{n}")));
    (lines, names)
}

const CONVERSION: &str = r#"def ordinary@I@ : Fang.Clause := @CLAUSE@
def bridgeSource@I@ : alloc.vec.Vec FangEqualityBridge.OutputLiteral := @SOURCE@
def bridgeTarget@I@ : alloc.vec.Vec FangEqualityBridge.InputLiteral := @TARGET@
def equality@I@ : Fang.Equality.Clause := [@EQUALITY@]
set_option linter.unusedSimpArgs false
theorem encode_clause@I@_eq : FangQuantifiedEqualityReplay.Transport.encodeClause ordinary@I@ = .ok bridgeSource@I@ := by
@WIDTHS@  simp [@NAMES@ordinary@I@, bridgeSource@I@, FangQuantifiedKernel.vector,
    FangQuantifiedEqualityReplay.Transport.encodeClause, FangQuantifiedEqualityReplay.Transport.encodeLiterals,
    FangQuantifiedEqualityReplay.Transport.encodeLiteral, FangQuantifiedEqualityReplay.Transport.encodeTerms,
    FangQuantifiedEqualityReplay.Transport.encodeTerm, FangQuantifiedTransport.checkedVec,
    FangQuantifiedTransport.checkedU32, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  all_goals rfl
theorem clause_relation@I@ : List.Forall₂ (FangEqualityBridge.EncodesLiteral reservation)
    bridgeTarget@I@.val bridgeSource@I@.val := by
  simp [bridgeTarget@I@, bridgeSource@I@, reservation, FangQuantifiedKernel.vector, alloc.vec.Vec.val,
    FangEqualityBridge.EncodesLiteral, FangEqualityBridge.LiteralValid, FangEqualityBridge.OrdinaryAnswer]
theorem decode_clause@I@_eq : fang_fof_equality_bridge.Reservation.decode_clause reservation bridgeSource@I@ 256#usize =
    .ok (.Ok bridgeTarget@I@) := by
  apply FangEqualityKernelGenerator.decode_clause_eq
  · rfl
  · simp [bridgeSource@I@, FangQuantifiedKernel.vector, alloc.vec.Vec.val]
  · exact clause_relation@I@
theorem conversion@I@_eq : FangQuantifiedEqualityReplay.Conversion.clause reservation 256#usize ordinary@I@ = .ok equality@I@ := by
  exact FangEqualityKernelGenerator.conversion_clause_eq reservation 256#usize ordinary@I@
    bridgeSource@I@ bridgeTarget@I@ encode_clause@I@_eq decode_clause@I@_eq
"#;

/// The conversion module of each ordinary clause.
fn conversions(checked: &Checked) -> Outcome<(Modules, Vec<String>)> {
    let mut modules = Modules::new();
    let mut names_list = Vec::new();
    for (i, (ordinary_clause, explicit)) in
        checked.ordinary.iter().zip(&checked.equality).enumerate()
    {
        let (widths, identifiers) = clause_bounds(ordinary_clause);
        let (width_lines, width_names) = bound_lines(&widths, &identifiers);
        let source_literals: Vec<String> = ordinary_clause
            .iter()
            .map(|literal| {
                let arguments: Vec<String> = literal
                    .arguments
                    .iter()
                    .map(|argument| term(argument, false))
                    .collect();
                format!(
                    "⟨{}, {}#u32, {}⟩",
                    literal.positive,
                    literal.predicate,
                    vec(&arguments)
                )
            })
            .collect();
        let literals = row_literals(explicit)?;
        let mut targets = Vec::new();
        for literal in &literals {
            targets.push(input_literal(literal, false)?);
        }
        let mut equalities = Vec::new();
        for literal in &literals {
            equalities.push(input_literal(literal, true)?);
        }
        let prefix: String = width_names.iter().map(|name| format!("{name}, ")).collect();
        let body = CONVERSION
            .replace("@CLAUSE@", &clause(ordinary_clause))
            .replace("@SOURCE@", &vec(&source_literals))
            .replace("@TARGET@", &vec(&targets))
            .replace("@EQUALITY@", &equalities.join(", "))
            .replace("@WIDTHS@", &width_lines)
            .replace("@NAMES@", &prefix)
            .replace("@I@", &i.to_string());
        let name = format!("EqInstanceConversion{i}");
        let audits = [
            format!("encode_clause{i}_eq"),
            format!("clause_relation{i}"),
            format!("decode_clause{i}_eq"),
            format!("conversion{i}_eq"),
        ];
        let audit_names: Vec<&str> = audits.iter().map(String::as_str).collect();
        modules.set(
            name.clone(),
            module(&names(&["EqInstanceEncoded"]), &body, &audit_names),
        );
        names_list.push(name);
    }
    Ok((modules, names_list))
}

/// The recipe's Decoded module.
fn decoded(
    checked: &Checked,
    source: &[u8],
    certificate: &[u8],
    recipe: Recipe,
) -> Outcome<String> {
    let common = &checked.common;
    let mut rows = Vec::new();
    for declaration in &common.source_declarations {
        let name = json_string(&declaration.name)?;
        rows.push(match (&declaration.body, recipe) {
            (Body::Cnf(literals), _) => format!("(.cnf {name} {})", clause(literals)),
            (Body::Fof(formula), Recipe::Quantified) => {
                format!("(.fof {name} {})", emit::formula(formula, true)?)
            }
            (Body::Fof(_), Recipe::Cnf) => return Err(rejected("CNF declarations only")),
        });
    }
    let original = &common.predicates[..common.predicates.len().saturating_sub(1)];
    let body = format!(
        "def input : String := {}\ndef certificateBytes : String := {}\ndef decoded : Fang.QuantifiedEqualityFrontend.Encoding.Encoded := {{\n  functions := {}\n  originalPredicates := {}\n  equalityId := {}\n  predicateArities := {}\n  declarations := [{}] }}\ntheorem decode_eq : Fang.QuantifiedEqualityFrontend.decode input = .ok decoded := by cbv\n",
        json_string(&String::from_utf8_lossy(source))?,
        json_string(&String::from_utf8_lossy(certificate))?,
        symbols(&common.functions)?,
        symbols(original)?,
        py::text(&checked.equality_id),
        py::text(&checked.extended),
        rows.join(", ")
    );
    Ok(
        module(&names(&["EqualityQuantifiedBytes"]), &body, &["decode_eq"])
            .replace("open Aeneas Aeneas.Std\n", ""),
    )
}

const CNF_ENCODED: &str = r#"
def originalSignature : fang_skolem_core.fang_quantified_fof_core.Signature := @ORIGINAL@
def reservation : fang_fof_equality_bridge.Reservation := @RESERVATION@
def declarations : Slice fang_skolem_core.Declaration := Slice.from [] (by simp)
def encoded : FangQuantifiedEqualityInput.Prepared := ⟨decoded, declarations, signature, reservation⟩
theorem original_signature_eq : FangQuantifiedTransport.encodeSignature
    (decoded.functions.map Prod.snd) (decoded.originalPredicates.map Prod.snd) = .ok originalSignature := by cbv
theorem reservation_eq : fang_fof_equality_bridge.Reservation.new originalSignature.predicates 100000#usize =
    .ok (.Ok reservation) := by
  apply FangEqualityKernelGenerator.reservation_eq
  · simp [originalSignature, FangQuantifiedKernel.vector, alloc.vec.Vec.val]
  · rfl
theorem extended_eq : fang_fof_equality_bridge.Reservation.extended_arities reservation = .ok signature.predicates := by
  apply FangEqualityKernelGenerator.extended_arities_eq
  · simp [reservation, FangQuantifiedKernel.vector, alloc.vec.Vec.val]; scalar_tac
  · rfl
theorem axioms_eq : FangOriginalInput.encodeAxioms
    (Fang.QuantifiedCertificate.formulas (FangQuantifiedEqualityInput.numericDeclarations decoded.declarations)) = .ok [] := by cbv
theorem transport_eq : FangQuantifiedEqualityInput.transport decoded 100000#usize = .ok encoded := by
  unfold FangQuantifiedEqualityInput.transport
  rw [original_signature_eq]
  simp only [FangQuantifiedEqualityInput.liftTransport, FangOriginalInput.liftWidth, Except.mapError,
    Bind.bind, Except.bind, FangQuantifiedEqualityInput.reserve, reservation_eq,
    FangQuantifiedEqualityInput.observe, Result.match.ok, extended_eq, axioms_eq,
    FangOriginalInput.checkedSlice, List.length_nil, Nat.zero_le, ↓reduceDIte, Pure.pure, Except.pure]
  rfl
theorem input_eq : FangQuantifiedEqualityInput.prepareInput input 100000#usize = .ok encoded := by
  simp [FangQuantifiedEqualityInput.prepareInput, decode_eq, transport_eq, Except.mapError, Bind.bind, Except.bind]
"#;

const QUANTIFIED_ENCODED: &str = r#"
set_option linter.unusedSimpArgs false
def originalSignature : fang_skolem_core.fang_quantified_fof_core.Signature := @ORIGINAL@
def reservation : fang_fof_equality_bridge.Reservation := @RESERVATION@
def declarations : Slice fang_skolem_core.Declaration := Slice.from [@VALUES@] (by simp; scalar_tac)
def encoded : FangQuantifiedEqualityInput.Prepared := ⟨decoded, declarations, signature, reservation⟩
theorem original_signature_eq : FangQuantifiedTransport.encodeSignature
    (decoded.functions.map Prod.snd) (decoded.originalPredicates.map Prod.snd) = .ok originalSignature := by cbv
theorem reservation_eq : fang_fof_equality_bridge.Reservation.new originalSignature.predicates 100000#usize =
    .ok (.Ok reservation) := by
  apply FangEqualityKernelGenerator.reservation_eq
  · simp [originalSignature, FangQuantifiedKernel.vector, alloc.vec.Vec.val]
  · rfl
theorem extended_eq : fang_fof_equality_bridge.Reservation.extended_arities reservation = .ok signature.predicates := by
  apply FangEqualityKernelGenerator.extended_arities_eq
  · simp [reservation, FangQuantifiedKernel.vector, alloc.vec.Vec.val]; scalar_tac
  · rfl
theorem axioms_eq : FangOriginalInput.encodeAxioms
    (Fang.QuantifiedCertificate.formulas (FangQuantifiedEqualityInput.numericDeclarations decoded.declarations)) = .ok declarations.val := by
@BOUNDS@  simp [@NAMES@decoded, declarations,
    FangQuantifiedEqualityInput.numericDeclarations, FangQuantifiedEqualityInput.numericDeclaration,
    Fang.QuantifiedCertificate.formulas, FangOriginalInput.encodeAxioms, FangOriginalInput.liftWidth,
    FangQuantifiedTransport.encodeDeclaration, FangQuantifiedTransport.encodeFormula,
    FangQuantifiedTransport.encodeTerm, FangQuantifiedTransport.encodeTerms,
    FangQuantifiedTransport.checkedU32, FangQuantifiedTransport.checkedVec,
    FangQuantifiedKernel.vector, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  all_goals (repeat' (first | rfl | constructor))
theorem slice_eq : FangOriginalInput.checkedSlice declarations.val = .ok declarations := by
  unfold FangOriginalInput.checkedSlice
  rw [dite_eq_left declarations.property]
  rfl
theorem transport_eq : FangQuantifiedEqualityInput.transport decoded 100000#usize = .ok encoded := by
  unfold FangQuantifiedEqualityInput.transport
  rw [original_signature_eq]
  simp only [FangQuantifiedEqualityInput.liftTransport, FangOriginalInput.liftWidth, Except.mapError,
    Bind.bind, Except.bind, FangQuantifiedEqualityInput.reserve, reservation_eq,
    FangQuantifiedEqualityInput.observe, Result.match.ok, extended_eq, axioms_eq,
    slice_eq, Pure.pure, Except.pure]
  rfl
theorem input_eq : FangQuantifiedEqualityInput.prepareInput input 100000#usize = .ok encoded := by
  simp [FangQuantifiedEqualityInput.prepareInput, decode_eq, transport_eq, Except.mapError, Bind.bind, Except.bind]
"#;

/// The recipe's Encoded module.
fn encoded(checked: &Checked, recipe: Recipe) -> Outcome<String> {
    let common = &checked.common;
    let original_predicates = &common.predicates[..common.predicates.len().saturating_sub(1)];
    let usize_vector = |values: &[super::witness::Symbol]| {
        vec(&values
            .iter()
            .map(|symbol| format!("{}#usize", symbol.arity))
            .collect::<Vec<_>>())
    };
    let reservation = format!(
        "⟨{}, {}#u32⟩",
        usize_vector(original_predicates),
        py::text(&checked.equality_id)
    );
    let original = format!(
        "⟨{}, {}⟩",
        usize_vector(&common.functions),
        usize_vector(original_predicates)
    );
    let imports = names(&[
        "EqInstanceData",
        "EqInstanceDecoded",
        "EqualityBridgeKernel",
    ]);
    Ok(match recipe {
        Recipe::Cnf => {
            let body = CNF_ENCODED
                .replace("@ORIGINAL@", &original)
                .replace("@RESERVATION@", &reservation);
            let audits = [
                "original_signature_eq",
                "reservation_eq",
                "extended_eq",
                "axioms_eq",
                "transport_eq",
                "input_eq",
            ];
            module(&imports, &body, &audits)
        }
        Recipe::Quantified => {
            let values = join(
                (0..common.declarations.len()).map(|i| format!("⟨formula{i}, true⟩")),
                ", ",
            );
            let (widths, identifiers) = encoding_bounds(common)?;
            let (lines, mut bound_names) = bound_lines(&widths, &identifiers);
            bound_names.extend((0..common.declarations.len()).map(|i| format!("formula{i}")));
            let prefix: String = bound_names.iter().map(|name| format!("{name}, ")).collect();
            let body = QUANTIFIED_ENCODED
                .replace("@ORIGINAL@", &original)
                .replace("@RESERVATION@", &reservation)
                .replace("@VALUES@", &values)
                .replace("@BOUNDS@", &lines)
                .replace("@NAMES@", &prefix);
            let audits = [
                "original_signature_eq",
                "reservation_eq",
                "extended_eq",
                "axioms_eq",
                "slice_eq",
                "transport_eq",
                "input_eq",
            ];
            module(&imports, &body, &audits)
        }
    })
}

const CNF_PREPARED: &str = r#"def replayLimits : FangOriginalReplay.Limits := {
  skolem := FangOriginalKernelProbe.skolemLimits
  removal := ⟨64#usize, 5000000#usize, 1000000#usize⟩
  clausification := {
    max_formula_depth := 64#usize, max_formula_nodes := 10000#usize,
    max_term_depth := 64#usize, max_input_term_nodes := 100000#usize,
    max_clauses := 1000#usize, max_literals_per_clause := 256#usize,
    max_literals := 100000#usize, max_stored_nodes := 1000000#usize, max_operations := 5000000#usize } }
"#;

const CNF_PREPARED_TAIL: &str = r#"theorem blocks_eq : FangOriginalReplay.replayBlocks replayLimits skolemized.formulas.val = .ok [] := rfl
theorem assembly_eq : FangOriginalReplay.assemble (FangQuantifiedEqualityInput.numericDeclarations decoded.declarations) [] = .ok ordinary := by cbv
theorem conversion_eq : FangQuantifiedEqualityReplay.Conversion.problem reservation 256#usize ordinary = .ok prepared.problem := by
  simp only [ordinary, prepared, FangQuantifiedEqualityReplay.Conversion.problem,
    @CONVERSIONS@Bind.bind, Except.bind, Pure.pure, Except.pure]
theorem prepare_eq : FangQuantifiedEqualityReplay.prepare input replayLimits 100000#usize 256#usize = .ok prepared := by
  unfold FangQuantifiedEqualityReplay.prepare
  rw [input_eq]
  simp only [Except.mapError, Bind.bind, Except.bind]
  change (do
    let transformed ← (FangOriginalReplay.observe (fang_skolem_core.skolemize_problem declarations signature FangOriginalKernelProbe.skolemLimits) .skolem).mapError FangQuantifiedEqualityReplay.Error.preprocessing
    let blocks ← (FangOriginalReplay.replayBlocks replayLimits transformed.formulas.val).mapError FangQuantifiedEqualityReplay.Error.preprocessing
    let ordinary ← (FangOriginalReplay.assemble (FangQuantifiedEqualityInput.numericDeclarations decoded.declarations) blocks).mapError FangQuantifiedEqualityReplay.Error.preprocessing
    let equality ← (FangQuantifiedEqualityReplay.Conversion.problem reservation 256#usize ordinary).mapError FangQuantifiedEqualityReplay.Error.conversion
    pure (⟨equality, transformed.signature.functions.val.map (fun (value : Usize) => value.val), decoded.originalPredicates.map Prod.snd⟩ : FangQuantifiedEqualityReplay.Prepared)) = .ok prepared
  rw [skolemize_eq]
  simp only [FangOriginalReplay.observe, Result.match.ok, Except.mapError, Bind.bind, Except.bind,
    blocks_eq, assembly_eq, conversion_eq, Pure.pure, Except.pure]
  rfl
"#;

const QUANTIFIED_LIMITS: &str = r#"def replayLimits : FangOriginalReplay.Limits := {
  skolem := FangOriginalKernelProbe.skolemLimits
  removal := FangKernelGenerator.removalLimits
  clausification := FangQuantifiedKernel.Clausifier.limits }
"#;

const QUANTIFIED_PREPARED_TAIL: &str = r#"theorem assembly_eq : FangOriginalReplay.assemble (FangQuantifiedEqualityInput.numericDeclarations decoded.declarations) clauseBlocks = .ok ordinary := by cbv
theorem conversion_eq : FangQuantifiedEqualityReplay.Conversion.problem reservation 256#usize ordinary = .ok prepared.problem := by
  simp only [ordinary, prepared, FangQuantifiedEqualityReplay.Conversion.problem,
    @CONVERSIONS@Bind.bind, Except.bind, Pure.pure, Except.pure]
theorem prepare_eq : FangQuantifiedEqualityReplay.prepare input replayLimits 100000#usize 256#usize = .ok prepared := by
  have result := FangEqualityKernelGenerator.prepare_of_parts (limits := replayLimits) input_eq skolemize_eq blocks_eq assembly_eq conversion_eq
  exact result
"#;

/// The definitions of `ordinary` and `prepared`.
fn ordinary_and_prepared(checked: &Checked) -> String {
    let common = &checked.common;
    let count = checked.ordinary.len();
    let original: Vec<u64> = common.predicates[..common.predicates.len().saturating_sub(1)]
        .iter()
        .map(|symbol| symbol.arity)
        .collect();
    format!(
        "def ordinary : Fang.Problem := [{}]\ndef prepared : FangQuantifiedEqualityReplay.Prepared := ⟨[{}], {}, {}⟩\n",
        join((0..count).map(|i| format!("ordinary{i}")), ", "),
        join((0..count).map(|i| format!("equality{i}")), ", "),
        list_text(&common.skolem.functions),
        list_text(&original)
    )
}

fn conversion_names(count: usize) -> String {
    (0..count).map(|i| format!("conversion{i}_eq, ")).collect()
}

const CNF_CERTIFICATE: &str = r#"
theorem certificate_checked : FangQuantifiedEqualityCertificate.checkPrepared
    prepared.problem prepared.functionArities prepared.predicateArities certificateBytes = .ok () := checked_bytes
#print axioms EqInstance.certificate_checked
"#;

const QUANTIFIED_CERTIFICATE: &str = r#"
theorem certificate_checked : FangQuantifiedEqualityCertificate.checkPrepared
    prepared.problem prepared.functionArities prepared.predicateArities certificateBytes = .ok () := by
  dsimp only [prepared, @EQUALITIES@certificateBytes]
  exact checked_bytes
#print axioms EqInstance.certificate_checked
"#;

const CERTIFICATE_TAIL: &str = r#"theorem certificate_accepts : FangQuantifiedEqualityCertificate.accepts input certificateBytes replayLimits 100000#usize 256#usize = .ok () := by
  unfold FangQuantifiedEqualityCertificate.accepts
  rw [prepare_eq]
  change (FangQuantifiedEqualityCertificate.checkPrepared prepared.problem prepared.functionArities prepared.predicateArities certificateBytes).mapError FangQuantifiedEqualityCertificate.Error.prepared = .ok ()
  rw [certificate_checked]
  rfl
#print axioms EqInstance.certificate_accepts
theorem original_bytes_unsat : ¬ Fang.NamedQuantifiedEquality.Grammar.BytesSatisfiable
    (Fang.Source.Grammar.spelling input) := FangQuantifiedEqualityCertificate.accepts_original_unsat certificate_accepts
#print axioms EqInstance.original_bytes_unsat
"#;

/// `build(source, certificate, raw, emitters)` of either recipe, on the parsed witness.
pub(crate) fn build(
    recipe: Recipe,
    source: &[u8],
    certificate: &[u8],
    w: &Value,
) -> Outcome<Built> {
    let checked = check(recipe, source, certificate, w)?;
    let common = &checked.common;
    let mut result = emit::emit(common, source, certificate, "EqInstance")?;
    result.set(
        "EqInstanceDecoded",
        decoded(&checked, source, certificate, recipe)?,
    );
    result.set("EqInstanceEncoded", encoded(&checked, recipe)?);
    let input_names = result.names();
    let mut phases: Vec<Vec<String>> = vec![input_names];
    let mut clausification_names = Vec::new();
    match recipe {
        Recipe::Cnf => {
            let preparation = skolem::preparation(common, "EqInstance")?;
            phases.push(preparation.names());
            result.update(preparation);
            // There are no FOF formulas in this slice. Keep the zero-declaration bridge explicit
            // without importing an unused Boolean transformer module.
            let mut transform = Modules::new();
            transform.set(
                "EqInstanceTransformData",
                module(&names(&["EqInstancePreparation"]), "", &[]),
            );
            phases.push(transform.names());
            result.update(transform);
            let declarations = split::declarations(common, "EqInstance")?;
            phases.push(declarations.names());
            result.update(declarations);
        }
        Recipe::Quantified => {
            let rectification = rectify::emit(common, "EqInstance")?;
            phases.push(rectification.names());
            result.update(rectification);
            let preparation = skolem::preparation(common, "EqInstance")?;
            phases.push(preparation.names());
            result.update(preparation);
            let transform = split::transform_modules(common, "EqInstance")?;
            phases.push(transform.names());
            result.update(transform);
            let declarations = split::declarations(common, "EqInstance")?;
            phases.push(declarations.names());
            result.update(declarations);
            let removed = removal::emit(common, "EqInstance")?;
            phases.push(removed.names());
            result.update(removed);
            let clausification = clausifier::emit(common, "EqInstance")?;
            clausification_names = clausification.names();
            phases.push(clausification.names());
            result.update(clausification);
        }
    }
    let (conversion_modules, conversion_list) = conversions(&checked)?;
    result.update(conversion_modules);
    phases.push(conversion_list.clone());
    let count = checked.ordinary.len();
    let prepared = match recipe {
        Recipe::Cnf => {
            let mut body = CNF_PREPARED.to_owned();
            body.push_str(&ordinary_and_prepared(&checked));
            body.push_str(&CNF_PREPARED_TAIL.replace("@CONVERSIONS@", &conversion_names(count)));
            let mut imports = names(&["EqInstanceSkolem", "EqualityOriginalCertificate"]);
            imports.extend(conversion_list.iter().cloned());
            module(
                &imports,
                &body,
                &["blocks_eq", "assembly_eq", "conversion_eq", "prepare_eq"],
            )
        }
        Recipe::Quantified => {
            let block_rows: Vec<String> = common
                .blocks
                .iter()
                .map(|block| {
                    format!(
                        "[{}]",
                        join(block.clauses.iter().map(|row| clause(row)), ", ")
                    )
                })
                .collect();
            let mut body = format!(
                "def clauseBlocks : List Fang.Problem := [{}]\n",
                block_rows.join(", ")
            );
            body.push_str(QUANTIFIED_LIMITS);
            body.push_str(&ordinary_and_prepared(&checked));
            body.push_str("theorem blocks_eq : FangOriginalReplay.replayBlocks replayLimits skolemized.formulas.val = .ok clauseBlocks := by\n");
            let blocks = common.blocks.len();
            let outputs = join((0..blocks).map(|i| format!("skolemOutput{i}")), ", ");
            let decoded_blocks = join(
                (0..blocks).map(|i| format!("FangScopedFof.decodeClauses block{i}.clauses.val")),
                ", ",
            );
            body.push_str(&format!("  change FangOriginalReplay.replayBlocks replayLimits [{outputs}] = .ok [{decoded_blocks}]\n"));
            for i in 0..blocks {
                body.push_str(&format!("  apply FangEqualityKernelGenerator.replay_blocks_cons remove{i}_eq clausify{i}_eq\n"));
            }
            body.push_str("  rfl\n");
            body.push_str(
                &QUANTIFIED_PREPARED_TAIL.replace("@CONVERSIONS@", &conversion_names(count)),
            );
            let mut imports = names(&[
                "EqInstanceSkolem",
                "EqualityReplayKernel",
                "BooleanClausifierPrimitives",
                "RemovalPrimitives",
            ]);
            imports.extend(clausification_names.iter().cloned());
            imports.extend(conversion_list.iter().cloned());
            module(
                &imports,
                &body,
                &["blocks_eq", "assembly_eq", "conversion_eq", "prepare_eq"],
            )
        }
    };
    result.set("EqInstancePrepared", prepared);
    let mut rows = Vec::new();
    for row in &checked.equality {
        let mut literals = Vec::new();
        for literal in row_literals(row)? {
            literals.push(input_literal(&literal, true)?);
        }
        rows.push(format!("[{}]", literals.join(", ")));
    }
    let original: Vec<u64> = common.predicates[..common.predicates.len().saturating_sub(1)]
        .iter()
        .map(|symbol| symbol.arity)
        .collect();
    result.set(
        "EqInstanceChecked",
        checked_module(
            certificate,
            &format!("[{}]", rows.join(", ")),
            &list_text(&common.skolem.functions),
            &list_text(&original),
        )?,
    );
    result.set(
        "EqInstanceJoined",
        format!("{HEADER}import EqInstancePrepared\nimport EqInstanceChecked\n"),
    );
    let mut certificate_body = match recipe {
        Recipe::Cnf => CNF_CERTIFICATE.to_owned(),
        Recipe::Quantified => {
            let mut equalities: String = join((0..count).map(|i| format!("equality{i}")), ", ");
            if count > 0 {
                equalities.push_str(", ");
            }
            QUANTIFIED_CERTIFICATE.replace("@EQUALITIES@", &equalities)
        }
    };
    certificate_body.push_str(CERTIFICATE_TAIL);
    result.set(
        "EqInstanceCertificate",
        module(&names(&["EqInstanceJoined"]), &certificate_body, &[]),
    );
    let text = json_string(&String::from_utf8_lossy(source))?;
    let proof = json_string(&String::from_utf8_lossy(certificate))?;
    let audit = format!(
        "theorem actual_sealed_acceptance : FangQuantifiedEqualityCertificate.accepts {text} {proof} replayLimits 100000#usize 256#usize = .ok () := certificate_accepts\ntheorem actual_original_bytes_unsat : ¬ Fang.NamedQuantifiedEquality.Grammar.BytesSatisfiable\n    (Fang.Source.Grammar.spelling {text}) := original_bytes_unsat\n"
    );
    result.set(
        "EqInstanceFixedAudit",
        module(
            &names(&["EqInstanceCertificate"]),
            &audit,
            &["actual_sealed_acceptance", "actual_original_bytes_unsat"],
        ),
    );
    for name in [
        "EqInstancePrepared",
        "EqInstanceChecked",
        "EqInstanceJoined",
        "EqInstanceCertificate",
        "EqInstanceFixedAudit",
    ] {
        phases.push(vec![name.to_owned()]);
    }
    let total: usize = result.iter().map(|(_, code)| code.len()).sum();
    require(
        total <= 16 << 20 && result.len() <= 256,
        "Generated size/module cap",
    )?;
    phases.retain(|phase| !phase.is_empty());
    Ok(Built {
        modules: result,
        phases,
    })
}
