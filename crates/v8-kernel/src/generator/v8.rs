// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! generator/generate-v8.py, version 4, and the recipe choice of entry/check.py.
//!
//! The version-7 recipe emits the modules for the extracted calls unchanged. This replaces only
//! the front, where the version-8 decoder and legacyInput reach the version-7 transport input,
//! and the back, where V8ReplayKernel composes prepare and accepts and the version-8 envelope
//! check runs. Witness values remain untrusted suggestions; Lean checks every equation on the
//! sealed bytes. The recipe receives a copy of the witness with synthetic names, since it only
//! needs distinct lower-case spellings; the Decoded module is rebuilt from the real tables and
//! names, which Lean checks against the actual decoder.

use fang_json::{Object, ParseLimits, Value};

use super::certificate::{
    certificate_constructor, exact_string, frontend_tokens, lexer_parts, node_equations, quote,
};
use super::emit::term_value;
use super::recipe::{HEADER, Recipe, build as recipe_build, module};
use super::validate::hex;
use super::{Modules, Outcome, Refusal, json_string, list_text, py, rejected, require};

const INTEGRATION: &str = "Fang.TptpCandidate.FullFof.Integration";
const SATISFIABLE: &str = "Fang.TptpCandidate.FullFof.CnfBoolean.BytesSatisfiable";
const MAXIMUM_BYTES: &str = "1048576";
const RECIPE_FINISH: &str = "  all_goals (repeat' (first | rfl | constructor))\n";
const FINISH: &str = "  all_goals (repeat' constructor)\n";
const SUPPORT: &str = "namespace FangV8CertificateKernel
theorem size_ofList (characters : List Char) :
    (String.ofList characters).utf8ByteSize = (characters.map Char.utf8Size).sum := by
  induction characters with
  | nil => rfl
  | cons c cs ih =>
    change (String.ofList ([c] ++ cs)).utf8ByteSize = _
    rw [String.ofList_append, String.utf8ByteSize_append,
      ← String.singleton_eq_ofList, String.utf8ByteSize_singleton, ih]
    rfl

theorem frontend_tokenizes (input : String) (characters : List Char)
    (tokens : List Fang.Frontend.Token) (fuel : Nat)
    (spelling : input.toList = characters)
    (ascii : characters.findIdx? (fun c => c.toNat > 127) = none)
    (length : characters.length + 1 = fuel)
    (lexed : Fang.Frontend.lexAux fuel characters 0 = .ok tokens) :
    Fang.Frontend.tokenize input = .ok tokens := by
  unfold Fang.Frontend.tokenize
  rw [spelling]
  dsimp only
  rw [ascii, length]
  exact lexed

theorem v8_decodes (input : String) (tokens : List Fang.Frontend.Token)
    (size fuel : Nat) (certificate : Fang.Equality.Ordered.Certificate) (state : Fang.Frontend.State)
    (tokenized : Fang.Frontend.tokenize input = .ok tokens)
    (bytes : input.utf8ByteSize = size) (length : tokens.length + 1 = fuel)
    (parsed : Fang.TptpCandidate.FullFof.Integration.v8Certificate fuel { tokens, endOffset := size } = .ok (certificate, state)) :
    Fang.TptpCandidate.FullFof.Integration.decodeV8 input = .ok certificate := by
  simp [Fang.TptpCandidate.FullFof.Integration.decodeV8, tokenized, bytes, length, parsed, Bind.bind, Except.bind]
  rfl
end FangV8CertificateKernel

";

/// The generated modules in compile order of definition, and the compile phases.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Generated {
    pub modules: Vec<(String, Vec<u8>)>,
    pub phases: Vec<Vec<String>>,
    /// `generate-cnf.py` or `generate-quantified.py`, as check.py records it.
    pub recipe: &'static str,
}

/// The witness parse of check.py and generate-v8.py: duplicate keys refused, and every other
/// fang-json refusal, as Python's ValueError and RecursionError were, is an invalid witness.
fn parse_witness(raw: &[u8]) -> Outcome<Value> {
    let limits = ParseLimits {
        max_bytes: 16 << 20,
        max_depth: 512,
    };
    fang_json::parse(raw, &limits).map_err(|_| rejected("Invalid witness JSON"))
}

/// `generator_name(raw)` of check.py: the CNF recipe when every source declaration is CNF.
/// This selects a construction recipe, never an acceptance result.
fn select(witness: &Value) -> Recipe {
    let declarations = match witness {
        Value::Object(object) => object.get("source_declarations"),
        _ => None,
    };
    let cnf = match declarations {
        Some(Value::Array(items)) if !items.is_empty() => items.iter().all(|item| match item {
            Value::Object(entry) => match entry.get("body") {
                Some(Value::Array(body)) => body.len() == 2 && py::is_text(&body[0], "cnf"),
                _ => false,
            },
            _ => false,
        }),
        _ => false,
    };
    if cnf { Recipe::Cnf } else { Recipe::Quantified }
}

/// `remove_theorem(text, name)`: drop one version-7 composition theorem and its audit line.
fn remove_theorem(text: &str, name: &str) -> Outcome<String> {
    let mut lines: Vec<&str> = text.split('\n').collect();
    let prefix = format!("theorem {name} ");
    let starts: Vec<usize> = lines
        .iter()
        .enumerate()
        .filter(|(_, line)| line.starts_with(&prefix))
        .map(|(i, _)| i)
        .collect();
    require(
        starts.len() == 1,
        &format!("Expected one version-7 theorem {name}"),
    )?;
    let start = starts[0];
    let mut end = start + 1;
    while end < lines.len() && lines[end].starts_with(' ') {
        end += 1;
    }
    lines.drain(start..end);
    let audit = format!("#print axioms EqInstance.{name}");
    require(
        lines.iter().filter(|line| **line == audit).count() == 1,
        &format!("Expected one audit for {name}"),
    )?;
    if let Some(position) = lines.iter().position(|line| *line == audit) {
        lines.remove(position);
    }
    Ok(lines.join("\n"))
}

/// `endpoint(source, certificate)`: the exact sealed bytes and the native checker's parameters.
fn endpoint(source: &str, certificate: &str) -> Outcome<String> {
    let text = json_string(source)?;
    let proof = json_string(certificate)?;
    let body = format!(
        "theorem actual_sealed_acceptance : {INTEGRATION}.accepts {text}.toUTF8.data.toList {MAXIMUM_BYTES} {proof} replayLimits 100000#usize 256#usize = .ok () := certificate_accepts\ntheorem actual_original_bytes_unsat : ¬ {SATISFIABLE}\n    {text}.toUTF8.data.toList {MAXIMUM_BYTES} := original_bytes_unsat\n"
    );
    Ok(module(
        &["EqInstanceCertificate".to_owned()],
        &body,
        &["actual_sealed_acceptance", "actual_original_bytes_unsat"],
    ))
}

/// `checked_v8(...)`: the reviewed version-7 decomposition with the version-8 parser and envelope.
fn checked_v8(
    certificate: &[u8],
    problem: &str,
    functions: &str,
    predicates: &str,
) -> Outcome<String> {
    let (expression, steps, last) = certificate_constructor(certificate)?;
    let mut body = exact_string("proofBytes", certificate);
    let cut = body
        .find("theorem exact_proofBytes_bytes :")
        .ok_or_else(|| rejected("substring not found"))?;
    body.truncate(cut);
    body.push_str(&format!(
        "def parsedCertificate : Fang.Equality.Ordered.Certificate := {expression}\n\n"
    ));
    body.push_str(&lexer_parts("proofBytes", certificate)?.concat());
    body.push_str(&node_equations(certificate, &steps, &last)?.concat());
    let tokens = frontend_tokens(certificate);
    let spelling: Vec<String> = tokens
        .iter()
        .map(|(word, offset, _)| format!("{{ text := {}, offset := {offset} }}", quote(word)))
        .collect();
    let spelling = format!("[{}]", spelling.join(", "));
    let size = certificate.len();
    let fuel = tokens.len() + 1;
    body.push_str(&format!(
        "theorem certificate_parses :\n    {INTEGRATION}.v8Certificate {fuel}\n      {{ tokens := {spelling}, endOffset := {size} }} =\n      .ok (parsedCertificate, {{ tokens := [], endOffset := {size} }}) := by cbv\n\n@[cbv_eval] theorem exact_certificate_decodes : {INTEGRATION}.decodeV8 proofBytes = .ok parsedCertificate :=\n  FangV8CertificateKernel.v8_decodes proofBytes _ {size} {fuel}\n"
    ));
    body.push_str("    parsedCertificate _ proofBytes_tokenizes proofBytes_size (by decide +kernel) certificate_parses\n\n");
    body.push_str(&format!(
        "def checkedProblem : Fang.Equality.Problem := {problem}\n"
    ));
    body.push_str(&format!(
        "theorem checked : {INTEGRATION}.checkProblem checkedProblem {functions} {predicates} certificateBytes = .ok () := by\n  change {INTEGRATION}.checkProblem _ _ _ proofBytes = .ok ()\n  unfold {INTEGRATION}.checkProblem\n"
    ));
    body.push_str("  rw [exact_certificate_decodes]\n  cbv\n\n");
    body.push_str("#print axioms EqInstance.exact_certificate_decodes\n#print axioms EqInstance.checked\nend EqInstance\n");
    let body = body.replace("FangEqualityCertificateKernel.", "FangV8CertificateKernel.");
    Ok(format!(
        "/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Untrusted observations are checked against actual calls and sealed bytes. -/\nimport EqInstanceDecoded\nimport ExpandedEnvelope\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats 4000000\nset_option cbv.maxSteps 20000000\n\n{SUPPORT}namespace EqInstance\n{body}"
    ))
}

/// `re.search(r'def decoded : ... := (\{.*?\})\ntheorem', text, re.S)`: the decoded literal.
fn decoded_literal(text: &str) -> Option<&str> {
    let prefix = "def decoded : Fang.QuantifiedEqualityFrontend.Encoding.Encoded := ";
    let start = text.find(&format!("{prefix}{{"))? + prefix.len();
    let close = text[start + 1..].find("}\ntheorem")? + start + 1;
    Some(&text[start..=close])
}

/// `re.subn(r'\((\.(?:cnf|fof)) "(d[0-9]+)"', ...)`: put the real declaration names back.
fn rename_declarations(
    literal: &str,
    original_names: &[(String, String)],
) -> Outcome<(String, usize)> {
    let bytes = literal.as_bytes();
    let mut result = String::new();
    let mut count = 0;
    let mut position = 0;
    let mut copied = 0;
    while position < bytes.len() {
        let rest = &literal[position..];
        let kind = ["(.cnf \"d", "(.fof \"d"]
            .iter()
            .find(|pattern| rest.starts_with(**pattern));
        if let Some(pattern) = kind {
            let digits_start = position + pattern.len();
            let mut digits_end = digits_start;
            while digits_end < bytes.len() && bytes[digits_end].is_ascii_digit() {
                digits_end += 1;
            }
            if digits_end > digits_start && bytes.get(digits_end) == Some(&b'"') {
                let synthetic = &literal[digits_start - 1..digits_end];
                let Some((_, name)) = original_names.iter().find(|(value, _)| value == synthetic)
                else {
                    return Err(py::key_error(&Value::from(synthetic)));
                };
                result.push_str(&literal[copied..position]);
                result.push('(');
                result.push_str(&literal[position + 1..position + 5]);
                result.push(' ');
                result.push_str(&json_string(name)?);
                count += 1;
                position = digits_end + 1;
                copied = position;
                continue;
            }
        }
        position += rest.chars().next().map_or(1, char::len_utf8);
    }
    result.push_str(&literal[copied..]);
    Ok((result, count))
}

/// `re.subn(r'^  KEY := .*$', ..., flags=re.M)`: replace every line that starts with the key.
fn replace_table_line(literal: &str, key: &str, replacement: &str) -> (String, usize) {
    let prefix = format!("  {key} := ");
    let mut count = 0;
    let lines: Vec<String> = literal
        .split('\n')
        .map(|line| {
            if line.starts_with(&prefix) {
                count += 1;
                replacement.to_owned()
            } else {
                line.to_owned()
            }
        })
        .collect();
    (lines.join("\n"), count)
}

/// `re.search(r'^def ordinary[0-9]+ : Fang\.Clause := \[\]$', text, re.M)`.
fn has_empty_ordinary(text: &str) -> bool {
    text.split('\n').any(|line| {
        line.strip_prefix("def ordinary").is_some_and(|rest| {
            let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
            digits > 0 && &rest[digits..] == " : Fang.Clause := []"
        })
    })
}

/// A real symbol table of the witness: a list of [name, arity] pairs, or an empty string or dict.
fn table(value: &Value) -> Outcome<Vec<(Value, Value)>> {
    let mut pairs = Vec::new();
    for item in py::iterate(value)? {
        pairs.push(py::unpack_two(&item)?);
    }
    Ok(pairs)
}

/// `symbols(table)`.
fn symbols(pairs: &[(Value, Value)]) -> Outcome<String> {
    let mut entries = Vec::new();
    for (name, arity) in pairs {
        entries.push(format!(
            "({}, {})",
            super::json_dumps(name)?,
            py::text(arity)
        ));
    }
    Ok(format!("[{}]", entries.join(", ")))
}

/// The recipe check.py records as `selected_generator` before generating: none when the witness
/// is not JSON, since generator_name refuses it first.
pub fn selected_recipe(raw: &[u8]) -> Option<&'static str> {
    let witness = parse_witness(raw).ok()?;
    Some(match select(&witness) {
        Recipe::Cnf => "generate-cnf.py",
        Recipe::Quantified => "generate-quantified.py",
    })
}

/// Exact-instance modules for one sealed input, certificate and witness, or the refusal with
/// revision 7's class.
pub fn generate(source: &[u8], certificate: &[u8], raw: &[u8]) -> Result<Generated, Refusal> {
    let witness = parse_witness(raw)?;
    let recipe = select(&witness);
    let (modules, phases) = build(source, certificate, witness, recipe)?;
    Ok(Generated {
        modules: modules
            .into_entries()
            .into_iter()
            .map(|(name, text)| (name, text.into_bytes()))
            .collect(),
        phases,
        recipe: match recipe {
            Recipe::Cnf => "generate-cnf.py",
            Recipe::Quantified => "generate-quantified.py",
        },
    })
}

/// `build(source, certificate, raw, emitters, recipe)` on the parsed witness.
fn build(
    source: &[u8],
    certificate: &[u8],
    witness: Value,
    recipe: Recipe,
) -> Outcome<(Modules, Vec<Vec<String>>)> {
    require(
        source.is_ascii() && certificate.is_ascii(),
        "ASCII pair required",
    )?;
    // Only a structural guard: the version and marker are checked by decodeV8 inside Lean.
    require(
        certificate.starts_with(b"(fang-proof "),
        "Certificate envelope required",
    )?;
    let source_hex = Value::String(hex(source));
    let mut witness = match witness {
        Value::Object(object)
            if object
                .get("source_hex")
                .is_some_and(|value| py::equals(value, &source_hex)) =>
        {
            object
        }
        _ => return Err(rejected("Witness detached from the source")),
    };
    // The version-7 recipe binds the certificate bytes it embeds; give it the version-8 bytes,
    // and synthetic names that satisfy its spelling rules. Names are not used by its equations.
    witness.set("certificate_hex", hex(certificate));
    let real_functions = key(&witness, "functions")?.clone();
    let real_predicates = key(&witness, "original_predicates")?.clone();
    let source_declarations = key(&witness, "source_declarations")?.clone();
    let mut declared = Vec::new();
    for item in py::iterate(&source_declarations)? {
        declared.push(py::item(&item, "name")?.clone());
    }
    let names_printable = declared
        .iter()
        .all(|name| matches!(name, Value::String(text) if py::printable_ascii(text)));
    require(names_printable, "Witness names must be printable ASCII")?;
    for table_value in [&real_functions, &real_predicates] {
        for symbol in py::iterate(table_value)? {
            let good = match &symbol {
                Value::Array(items) if items.len() == 2 => {
                    matches!(&items[0], Value::String(text) if py::printable_ascii(text))
                }
                _ => false,
            };
            require(good, "Witness names must be printable ASCII")?;
        }
    }
    let real_function_pairs = table(&real_functions)?;
    let real_predicate_pairs = table(&real_predicates)?;
    let mut sanitized = witness.clone();
    let synthetic_table = |pairs: &[(Value, Value)], letter: &str| {
        Value::Array(
            pairs
                .iter()
                .enumerate()
                .map(|(index, (_, arity))| {
                    Value::Array(vec![Value::from(format!("{letter}{index}")), arity.clone()])
                })
                .collect(),
        )
    };
    sanitized.set("functions", synthetic_table(&real_function_pairs, "f"));
    sanitized.set(
        "original_predicates",
        synthetic_table(&real_predicate_pairs, "p"),
    );
    // Declared names are distinct printable strings here; a repeated one leaves fewer entries.
    let declared_names: Vec<String> = declared.iter().map(py::text).collect();
    let mut synthetic: Vec<(String, String)> = Vec::new();
    for (index, name) in declared_names.iter().enumerate() {
        match synthetic.iter_mut().find(|(existing, _)| existing == name) {
            Some(entry) => entry.1 = format!("d{index}"),
            None => synthetic.push((name.clone(), format!("d{index}"))),
        }
    }
    require(
        synthetic.len() == declared_names.len(),
        "Duplicate declaration name",
    )?;
    rename_sanitized(&mut sanitized, &synthetic)?;
    let built = recipe_build(recipe, source, certificate, &Value::Object(sanitized))?;
    let mut modules = built.modules;
    let names = modules.names();
    for required in [
        "EqInstanceDecoded",
        "EqInstanceEncoded",
        "EqInstancePrepared",
        "EqInstanceChecked",
        "EqInstanceJoined",
        "EqInstanceCertificate",
        "EqInstanceFixedAudit",
    ] {
        require(
            modules.contains(required),
            &format!("Version-7 recipe module missing: {required}"),
        )?;
    }
    // Front: the version-8 decoder, then legacyInput, reaches the version-7 transport input.
    let recipe_decoded = modules
        .get("EqInstanceDecoded")
        .cloned()
        .unwrap_or_default();
    let Some(literal) = decoded_literal(&recipe_decoded) else {
        return Err(rejected("Version-7 decoded value missing"));
    };
    let original_names: Vec<(String, String)> = synthetic
        .iter()
        .map(|(name, value)| (value.clone(), name.clone()))
        .collect();
    let (literal, renamed) = rename_declarations(literal, &original_names)?;
    require(
        renamed == declared.len(),
        "Every source declaration must be renamed once",
    )?;
    let (literal, tables) = replace_table_line(
        &literal,
        "functions",
        &format!("  functions := {}", symbols(&real_function_pairs)?),
    );
    let (literal, more) = replace_table_line(
        &literal,
        "originalPredicates",
        &format!(
            "  originalPredicates := {}",
            symbols(&real_predicate_pairs)?
        ),
    );
    require(
        tables == 1 && more == 1,
        "Decoded table lines differ from the version-7 shape",
    )?;
    let front = format!(
        "set_option cbv.maxSteps 200000000\ndef bytes : List UInt8 := {}.toUTF8.data.toList\ndef certificateBytes : String := {}\ndef decoded : Fang.QuantifiedEqualityFrontend.Encoding.Encoded := {literal}\ntheorem front_map : ({INTEGRATION}.decodeNumeric bytes {MAXIMUM_BYTES}).map {INTEGRATION}.legacyInput = .ok decoded := by cbv\ntheorem front : ∃ numeric, {INTEGRATION}.decodeNumeric bytes {MAXIMUM_BYTES} = .ok numeric ∧\n    {INTEGRATION}.legacyInput numeric = decoded := by\n  have mapped := front_map\n  cases run : {INTEGRATION}.decodeNumeric bytes {MAXIMUM_BYTES} with\n  | error failure => simp [run, Except.map] at mapped\n  | ok numeric => exact ⟨numeric, rfl, by simpa [run, Except.map] using mapped⟩\n",
        json_string(&String::from_utf8_lossy(source))?,
        json_string(&String::from_utf8_lossy(certificate))?
    );
    modules.set(
        "EqInstanceDecoded",
        module(
            &["ExpandedCertificate".to_owned()],
            &front,
            &["front_map", "front"],
        )
        .replace("open Aeneas Aeneas.Std\n", ""),
    );
    // Nonempty symbol tables: the recipe's cbv proof stops at the bounded-vector check.
    let arities: Vec<&Value> = real_function_pairs
        .iter()
        .chain(&real_predicate_pairs)
        .map(|(_, arity)| arity)
        .collect();
    let mut encoded = modules
        .get("EqInstanceEncoded")
        .cloned()
        .unwrap_or_default();
    if !arities.is_empty() {
        let old = "    (decoded.functions.map Prod.snd) (decoded.originalPredicates.map Prod.snd) = .ok originalSignature := by cbv\n";
        require(
            encoded.matches(old).count() == 1,
            "Version-7 signature equation shape differs",
        )?;
        let mut bounds: Vec<u64> = Vec::new();
        for value in arities {
            bounds.push(natural_arity(value)?);
        }
        bounds.push(real_function_pairs.len() as u64);
        bounds.push(real_predicate_pairs.len() as u64);
        bounds.sort_unstable();
        bounds.dedup();
        bounds.retain(|&value| value != 0);
        let facts: String = bounds
            .iter()
            .map(|n| format!("  have width{n} : {n} \u{2264} Usize.max := by scalar_tac\n"))
            .collect();
        let widths: String = bounds.iter().map(|n| format!("width{n}, ")).collect();
        let new = format!(
            "    (decoded.functions.map Prod.snd) (decoded.originalPredicates.map Prod.snd) = .ok originalSignature := by\n{facts}  simp [{widths}decoded, originalSignature, FangQuantifiedTransport.encodeSignature,\n    FangQuantifiedTransport.encodeArities, FangQuantifiedTransport.checkedUsize, FangQuantifiedTransport.checkedVec,\n    FangQuantifiedKernel.vector, Bind.bind, Except.bind, Pure.pure, Except.pure]\n{FINISH}"
        );
        encoded = encoded.replace(old, &new);
    }
    encoded = encoded.replace(RECIPE_FINISH, FINISH);
    modules.set("EqInstanceEncoded", encoded);
    // An empty clause encodes by simp alone; the recipe's finishing rfl would only add a linter warning.
    for name in modules.names() {
        let Some(text) = modules.get(&name).cloned() else {
            continue;
        };
        if name.starts_with("EqInstanceConversion") && has_empty_ordinary(&text) {
            require(
                text.matches("  all_goals rfl\n").count() == 1,
                "Version-7 empty clause encoding shape differs",
            )?;
            modules.set(name, text.replace("  all_goals rfl\n", ""));
        }
    }
    // The version-7 compositions name the version-7 decoder and prepare; version 8 composes its own.
    let encoded = remove_theorem(
        modules.get("EqInstanceEncoded").map_or("", String::as_str),
        "input_eq",
    )?;
    modules.set("EqInstanceEncoded", encoded);
    let prepared = remove_theorem(
        modules.get("EqInstancePrepared").map_or("", String::as_str),
        "prepare_eq",
    )?;
    modules.set("EqInstancePrepared", prepared);
    let skolem_functions = skolem_functions(&witness)?;
    let original_arities: Vec<u64> = real_predicate_pairs
        .iter()
        .map(|(_, arity)| natural_arity(arity))
        .collect::<Outcome<_>>()?;
    let functions = list_text(&skolem_functions);
    let predicates = list_text(&original_arities);
    let mut rows = Vec::new();
    let equality = key(&witness, "equality")?.clone();
    for row in py::iterate(&equality)? {
        let mut literals = Vec::new();
        for literal in py::iterate(&row)? {
            let (positive, atom) = py::unpack_two(&literal)?;
            require(
                matches!(positive, Value::Bool(_)) && matches!(atom, Value::Array(_)),
                "Equality literal shape",
            )?;
            let Value::Array(atom) = atom else {
                return Err(rejected("Equality literal shape"));
            };
            let item = |index: usize| {
                atom.get(index)
                    .ok_or_else(|| Refusal::Error("list index out of range".to_owned()))
            };
            let body = if py::is_text(item(0)?, "equal") {
                format!(
                    "(.equal {} {})",
                    term_value(item(1)?, true)?,
                    term_value(item(2)?, true)?
                )
            } else {
                let mut arguments = Vec::new();
                for argument in py::iterate(item(2)?)? {
                    arguments.push(term_value(&argument, true)?);
                }
                format!(
                    "(.predicate ⟨{}, [{}]⟩)",
                    py::text(item(1)?),
                    arguments.join(", ")
                )
            };
            literals.push(format!("⟨{}, {body}⟩", py::text(&positive).to_lowercase()));
        }
        rows.push(format!("[{}]", literals.join(", ")));
    }
    modules.set(
        "EqInstanceChecked",
        checked_v8(
            certificate,
            &format!("[{}]", rows.join(", ")),
            &functions,
            &predicates,
        )?,
    );
    modules.set(
        "EqInstanceJoined",
        format!(
            "{HEADER}import EqInstancePrepared\nimport EqInstanceChecked\nimport V8ReplayKernel\n"
        ),
    );
    let accepts = format!(
        "theorem certificate_accepts : {INTEGRATION}.accepts bytes {MAXIMUM_BYTES} certificateBytes replayLimits 100000#usize 256#usize = .ok () := by\n  obtain ⟨numeric, decodeRun, legacy⟩ := front\n  have predicates : numeric.predicates.map Prod.snd = {predicates} :=\n    congrArg (List.map Prod.snd) (congrArg Fang.QuantifiedEqualityFrontend.Encoding.Encoded.originalPredicates legacy)\n  apply FangV8KernelGenerator.accepts_of_parts (FangV8KernelGenerator.prepare_of_parts (limits := replayLimits)\n    decodeRun (FangV8KernelGenerator.transport_of_legacy legacy transport_eq) skolemize_eq blocks_eq\n    (FangV8KernelGenerator.assembly_of_legacy legacy assembly_eq) conversion_eq)\n  dsimp only\n  rw [predicates]\n  exact checked\ntheorem original_bytes_unsat : ¬ {SATISFIABLE} bytes {MAXIMUM_BYTES} :=\n  {INTEGRATION}.accepts_original_unsat certificate_accepts\n"
    );
    modules.set(
        "EqInstanceCertificate",
        module(
            &["EqInstanceJoined".to_owned()],
            &accepts,
            &["certificate_accepts", "original_bytes_unsat"],
        ),
    );
    modules.set(
        "EqInstanceFixedAudit",
        endpoint(
            &String::from_utf8_lossy(source),
            &String::from_utf8_lossy(certificate),
        )?,
    );
    require(modules.names() == names, "Module order changed")?;
    Ok((modules, built.phases))
}

/// Rename every source and FOF declaration of the sanitized copy to its synthetic name, as
/// `for item in sanitized['source_declarations'] + sanitized['declarations']` does.
fn rename_sanitized(sanitized: &mut Object, synthetic: &[(String, String)]) -> Outcome<()> {
    let sources = key(sanitized, "source_declarations")?.clone();
    let declarations = key(sanitized, "declarations")?.clone();
    // List + list concatenates; str + str concatenates characters, which have no 'name'; any
    // other pair is a TypeError.
    match (&sources, &declarations) {
        (Value::Array(_), Value::Array(_)) => {}
        (Value::String(left), Value::String(right)) => {
            return if left.is_empty() && right.is_empty() {
                Ok(())
            } else {
                Err(py::type_error("string indices must be integers, not 'str'"))
            };
        }
        (left, right) => {
            return Err(py::type_error(format!(
                "can only concatenate {} (not \"{}\") to {}",
                py::type_name(left),
                py::type_name(right),
                py::type_name(left)
            )));
        }
    }
    for key in ["source_declarations", "declarations"] {
        let Some(Value::Array(items)) = sanitized.get_mut(key) else {
            continue;
        };
        for item in items.iter_mut() {
            let name = py::item(item, "name")?.clone();
            let Value::String(name) = &name else {
                return Err(match name {
                    Value::Array(_) | Value::Object(_) => {
                        py::type_error(format!("unhashable type: '{}'", py::type_name(&name)))
                    }
                    other => py::key_error(&other),
                });
            };
            let Some((_, value)) = synthetic.iter().find(|(existing, _)| existing == name) else {
                return Err(py::key_error(&Value::String(name.clone())));
            };
            if let Value::Object(entry) = item {
                entry.set("name", value.clone());
            }
        }
    }
    Ok(())
}

/// `object[name]` on a witness dict; KeyError when missing.
fn key<'a>(object: &'a Object, name: &str) -> Outcome<&'a Value> {
    object
        .get(name)
        .ok_or_else(|| py::key_error(&Value::from(name)))
}

/// A validated arity: the recipe checked it as a natural, so it is an integer.
fn natural_arity(value: &Value) -> Outcome<u64> {
    value
        .as_u64()
        .ok_or_else(|| Refusal::Error(format!("unexpected arity {}", py::repr(value))))
}

/// `witness['skolem']['functions']`, validated by the recipe as naturals.
fn skolem_functions(witness: &Object) -> Outcome<Vec<u64>> {
    let skolem = key(witness, "skolem")?;
    let functions = py::item(skolem, "functions")?;
    py::iterate(functions)?.iter().map(natural_arity).collect()
}
