// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The renderers and `emit` of recipe/mixed/generate.py: the Data, Decoded, Encoded and
//! Validate modules of the input phase.

use std::collections::BTreeSet;

use fang_json::Value;

use super::py;
use super::witness::{Body, Formula, Term, Witness};
use super::{
    Modules, Outcome, Refusal, join, json_dumps, json_string, rejected, require_namespace,
};

/// `vec(values)`: a bounded vector literal with its length proof.
pub(crate) fn vec(values: &[String]) -> String {
    let proof = if values.is_empty() {
        "by simp"
    } else {
        "by simp; scalar_tac"
    };
    format!(
        "(FangQuantifiedKernel.vector [{}] ({proof}))",
        values.join(", ")
    )
}

/// `term(value, numeric)` on a validated term.
pub(crate) fn term(value: &Term, numeric: bool) -> String {
    match (value, numeric) {
        (Term::Var(index), true) => format!("(.var {index})"),
        (Term::Fun(symbol, arguments), true) => {
            format!(
                "(.app {symbol} [{}])",
                join(arguments.iter().map(|argument| term(argument, true)), ", ")
            )
        }
        (Term::Var(index), false) => format!("(.Var {index}#u32)"),
        (Term::Fun(symbol, arguments), false) => {
            let rendered: Vec<String> = arguments
                .iter()
                .map(|argument| term(argument, false))
                .collect();
            format!("(.Fun {symbol}#u32 {})", vec(&rendered))
        }
    }
}

/// `term(value, numeric)` on a witness value that revision 7 only compared with `==`: the
/// identifier is printed with Python's `str`, whatever its number type.
pub(crate) fn term_value(value: &Value, numeric: bool) -> Outcome<String> {
    let items = py::iterate(value)?;
    if items.len() < 2 {
        return Err(rejected(format!(
            "not enough values to unpack (expected at least 2, got {})",
            items.len()
        )));
    }
    let identifier = py::text(&items[1]);
    let var = py::is_text(&items[0], "var");
    if var {
        return Ok(if numeric {
            format!("(.var {identifier})")
        } else {
            format!("(.Var {identifier}#u32)")
        });
    }
    let Some(arguments) = items.get(2) else {
        return Err(Refusal::Error("list index out of range".to_owned()));
    };
    let mut rendered = Vec::new();
    for argument in py::iterate(arguments)? {
        rendered.push(term_value(&argument, numeric)?);
    }
    Ok(if numeric {
        format!("(.app {identifier} [{}])", rendered.join(", "))
    } else {
        format!("(.Fun {identifier}#u32 {})", vec(&rendered))
    })
}

/// `formula(value, numeric)`. A `literal` node is not a formula here; Python fails to unpack it.
pub(crate) fn formula(value: &Formula, numeric: bool) -> Outcome<String> {
    Ok(match value {
        Formula::Truth => (if numeric { "(.truth)" } else { "(.True)" }).to_owned(),
        Formula::Falsity => (if numeric { "(.falsity)" } else { "(.False)" }).to_owned(),
        Formula::Conj(left, right) | Formula::Disj(left, right) | Formula::Implies(left, right) => {
            let constructor = match (value, numeric) {
                (_, true) => value.tag(),
                (Formula::Conj(..), false) => "And",
                (Formula::Disj(..), false) => "Or",
                _ => "Implies",
            };
            format!(
                "(.{constructor} {} {})",
                formula(left, numeric)?,
                formula(right, numeric)?
            )
        }
        Formula::Atom(symbol, terms) => {
            if numeric {
                format!(
                    "(.atom ⟨{symbol}, [{}]⟩)",
                    join(terms.iter().map(|argument| term(argument, true)), ", ")
                )
            } else {
                let rendered: Vec<String> =
                    terms.iter().map(|argument| term(argument, false)).collect();
                format!("(.Atom {symbol}#u32 {})", vec(&rendered))
            }
        }
        Formula::Not(body) => format!(
            "(.{} {})",
            if numeric { "neg" } else { "Not" },
            formula(body, numeric)?
        ),
        Formula::All(binder, body) | Formula::Ex(binder, body) => {
            let constructor = match (value, numeric) {
                (Formula::All(..), true) => "all",
                (Formula::All(..), false) => "Forall",
                (_, true) => "ex",
                _ => "Exists",
            };
            let suffix = if numeric { "" } else { "#u32" };
            format!(
                "(.{constructor} {binder}{suffix} {})",
                formula(body, numeric)?
            )
        }
        Formula::Literal(_) => {
            return Err(rejected("not enough values to unpack (expected 2, got 1)"));
        }
    })
}

/// `source_declaration(value)`: the decoded body of one source declaration.
fn source_declaration(body: &Body) -> Outcome<String> {
    Ok(match body {
        Body::Fof(value) => format!(".fof {}", formula(value, true)?),
        Body::Cnf(literals) => {
            let rendered = literals.iter().map(|literal| {
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
            format!(".cnf [{}]", join(rendered, ", "))
        }
    })
}

/// `encoding_bounds(witness)`: the widths and identifiers the Encoded proof needs as facts.
pub(crate) fn encoding_bounds(witness: &Witness) -> Outcome<(Vec<u64>, Vec<u64>)> {
    let mut widths: BTreeSet<u64> = BTreeSet::new();
    widths.insert(witness.declarations.len() as u64);
    widths.insert(witness.functions.len() as u64);
    widths.insert(witness.predicates.len() as u64);
    let mut identifiers: BTreeSet<u64> = BTreeSet::new();
    for symbol in witness.functions.iter().chain(&witness.predicates) {
        widths.insert(symbol.arity);
    }
    fn visit_term(value: &Term, widths: &mut BTreeSet<u64>, identifiers: &mut BTreeSet<u64>) {
        match value {
            Term::Var(index) => {
                identifiers.insert(*index);
            }
            Term::Fun(symbol, arguments) => {
                identifiers.insert(*symbol);
                widths.insert(arguments.len() as u64);
                for argument in arguments {
                    visit_term(argument, widths, identifiers);
                }
            }
        }
    }
    fn visit(
        value: &Formula,
        widths: &mut BTreeSet<u64>,
        identifiers: &mut BTreeSet<u64>,
    ) -> Outcome<()> {
        match value {
            Formula::Truth | Formula::Falsity => {}
            Formula::Conj(left, right)
            | Formula::Disj(left, right)
            | Formula::Implies(left, right) => {
                visit(left, widths, identifiers)?;
                visit(right, widths, identifiers)?;
            }
            Formula::Not(body) => visit(body, widths, identifiers)?,
            Formula::All(binder, body) | Formula::Ex(binder, body) => {
                identifiers.insert(*binder);
                visit(body, widths, identifiers)?;
            }
            Formula::Atom(symbol, arguments) => {
                identifiers.insert(*symbol);
                widths.insert(arguments.len() as u64);
                for argument in arguments {
                    visit_term(argument, widths, identifiers);
                }
            }
            // A literal's second item is a list, which a set cannot hold.
            Formula::Literal(_) => {
                return Err(Refusal::Error("unhashable type: 'list'".to_owned()));
            }
        }
        Ok(())
    }
    for declaration in &witness.declarations {
        visit(&declaration.formula, &mut widths, &mut identifiers)?;
    }
    widths.remove(&0);
    identifiers.remove(&0);
    Ok((
        widths.into_iter().collect(),
        identifiers.into_iter().collect(),
    ))
}

const COMMON: &str = "/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Generated from untrusted witness data. Equations must be checked by Lean. -/\n";

/// `emit(witness, source, certificate, namespace)`.
pub(crate) fn emit(
    witness: &Witness,
    source: &[u8],
    certificate: &[u8],
    namespace: &str,
) -> Outcome<Modules> {
    require_namespace(namespace, "Lean namespace/module spelling")?;
    let intro = format!(
        "\nnamespace {namespace}\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n"
    );
    let mut data = format!("{COMMON}import TransformPrimitives\nopen Aeneas Aeneas.Std\n{intro}");
    let functions: Vec<String> = witness
        .functions
        .iter()
        .map(|symbol| format!("{}#usize", symbol.arity))
        .collect();
    let predicates: Vec<String> = witness
        .predicates
        .iter()
        .map(|symbol| format!("{}#usize", symbol.arity))
        .collect();
    data.push_str(&format!(
        "def signature : fang_skolem_core.fang_quantified_fof_core.Signature :=\n  ⟨{}, {}⟩\n",
        vec(&functions),
        vec(&predicates)
    ));
    for (index, declaration) in witness.declarations.iter().enumerate() {
        data.push_str(&format!(
            "def formula{index} : fang_skolem_core.fang_quantified_fof_core.Formula :=\n  {}\n",
            formula(&declaration.formula, false)?
        ));
    }
    data.push_str(&format!("end {namespace}\n"));
    let mut modules = Modules::new();
    modules.set(format!("{namespace}Data"), data);

    let mut decoded = format!("{COMMON}import QuantifiedInput\n{intro}");
    decoded.push_str(&format!(
        "def input : String := {}\n",
        json_string(&String::from_utf8_lossy(source))?
    ));
    decoded.push_str(&format!(
        "def certificateBytes : String := {}\n",
        json_string(&String::from_utf8_lossy(certificate))?
    ));
    let mut bodies = Vec::new();
    for declaration in &witness.source_declarations {
        bodies.push(source_declaration(&declaration.body)?);
    }
    let names = Value::Array(
        witness
            .source_declarations
            .iter()
            .map(|item| Value::from(item.name.as_str()))
            .collect(),
    );
    let last_variables = witness
        .source_declarations
        .last()
        .map(|item| {
            item.variables
                .iter()
                .map(|name| Value::from(name.as_str()))
                .collect()
        })
        .unwrap_or_default();
    decoded.push_str(&format!(
        "def decoded : Fang.QuantifiedFrontend.Decoded := {{\n  declarations := [{}]\n  state := {{\n    tokens := []\n    endOffset := {}\n    clauseNames := {}\n    «variables» := {}\n",
        bodies.join(", "),
        source.len(),
        json_dumps(&names)?,
        json_dumps(&Value::Array(last_variables))?
    ));
    for (key, table) in [
        ("functions", &witness.functions),
        ("predicates", &witness.predicates),
    ] {
        let mut entries = Vec::new();
        for symbol in table {
            entries.push(format!(
                "⟨{}, some {}⟩",
                json_string(&symbol.name)?,
                symbol.arity
            ));
        }
        decoded.push_str(&format!("    {key} := [{}]\n", entries.join(", ")));
    }
    decoded.push_str(
        "  } }\ntheorem decode_eq : Fang.QuantifiedFrontend.decode input = .ok decoded := by cbv\n",
    );
    decoded.push_str(&format!(
        "#print axioms {namespace}.decode_eq\nend {namespace}\n"
    ));
    modules.set(format!("{namespace}Decoded"), decoded);

    let mut encoded = format!(
        "{COMMON}import OriginalInput\nimport {namespace}Data\nimport {namespace}Decoded\nopen Aeneas Aeneas.Std\n{intro}"
    );
    let proof = if witness.declarations.is_empty() {
        "by simp"
    } else {
        "by simp; scalar_tac"
    };
    let values = join(
        (0..witness.declarations.len()).map(|index| format!("⟨formula{index}, true⟩")),
        ", ",
    );
    encoded.push_str(&format!("def declarations : Slice fang_skolem_core.Declaration :=\n  Slice.from [{values}] ({proof})\n"));
    encoded.push_str("def encoded : FangOriginalInput.Encoded := ⟨declarations, signature⟩\n");
    // This fixed structural simp set includes constructors absent from some inputs.
    encoded.push_str("set_option linter.unusedSimpArgs false\n");
    encoded.push_str(
        "theorem encode_eq : FangOriginalInput.encodeInput decoded = .ok encoded := by\n",
    );
    let (widths, identifiers) = encoding_bounds(witness)?;
    for value in &widths {
        encoded.push_str(&format!(
            "  have width{value} : {value} ≤ Usize.max := by scalar_tac\n"
        ));
    }
    for value in &identifiers {
        encoded.push_str(&format!(
            "  have identifier{value} : {value} ≤ U32.max := by scalar_tac\n"
        ));
    }
    let mut optional: Vec<String> = widths.iter().map(|value| format!("width{value}")).collect();
    optional.extend(identifiers.iter().map(|value| format!("identifier{value}")));
    optional.extend((0..witness.declarations.len()).map(|index| format!("formula{index}")));
    let prefix: String = optional.iter().map(|name| format!("{name}, ")).collect();
    encoded.push_str(&format!(
        "  simp [{prefix}FangOriginalInput.encodeInput, decoded, encoded, declarations, signature,\n    FangQuantifiedKernel.vector,\n    FangOriginalInput.readArities, FangOriginalInput.liftWidth, FangOriginalInput.checkedSlice,\n    FangOriginalInput.encodeAxioms, Fang.QuantifiedCertificate.formulas,\n    FangQuantifiedTransport.encodeSignature, FangQuantifiedTransport.encodeArities,\n    FangQuantifiedTransport.checkedVec, FangQuantifiedTransport.encodeDeclaration,\n    FangQuantifiedTransport.encodeFormula, FangQuantifiedTransport.encodeTerm,\n    FangQuantifiedTransport.encodeTerms, FangQuantifiedTransport.checkedU32,\n    FangQuantifiedTransport.checkedUsize, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]\n  all_goals (constructor <;> rfl)\n"
    ));
    let finish = "  all_goals (constructor <;> rfl)\n";
    encoded = if !witness.functions.is_empty() || !witness.predicates.is_empty() {
        let closing = if witness.declarations.is_empty() {
            "  rfl\n"
        } else {
            "  repeat' (first | rfl | constructor)\n"
        };
        encoded.replace(finish, closing)
    } else {
        encoded.replace(finish, "")
    };
    encoded.push_str(&format!(
        "#print axioms {namespace}.encode_eq\nend {namespace}\n"
    ));
    modules.set(format!("{namespace}Encoded"), encoded);

    for (index, observed) in witness.standalone.iter().enumerate() {
        let theorem = format!("validate{index}_eq");
        let mut code = format!(
            "{COMMON}import {namespace}Data\nopen Aeneas Aeneas.Std\nopen FangOriginalKernelProbe\nopen fang_skolem_core.fang_quantified_fof_core\n{intro}"
        );
        let validated = join(
            observed
                .validated
                .iter()
                .map(|value| format!("{value}#usize")),
            ", ",
        );
        code.push_str(&format!(
            "theorem {theorem} : validate formula{index} signature skolemLimits.core =\n  .ok (.Ok ⟨{validated}⟩) := by\n"
        ));
        code.push_str(&format!(
            "  simp only [formula{index}, signature, validate, validate_with_scope, Work.new,\n    core_statistics_eq, Bindings.new, bind_ok]\n  generated_transform\n"
        ));
        code.push_str(&format!(
            "#print axioms {namespace}.{theorem}\nend {namespace}\n"
        ));
        modules.set(format!("{namespace}Validate{index}"), code);
    }
    Ok(modules)
}
