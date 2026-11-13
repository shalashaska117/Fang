// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The engine, checker, replay exporter and fixed-audit contracts of the CNF profile: a port of
//! tools/fang_szs/protocol.py. Its refusals are Failures with protocol.py's texts and stages.

use fang_json::Object;
use fang_supervisor::{Fault, StageOutput};

use crate::older::{contract, error, value};

pub const ACCEPTED: &[u8] =
    b"accepted-refutation (compiled checker; no per-instance kernel replay performed)\n";
/// The fixed audit's theorems, sorted.
pub const REQUIRED_AUDITS: [&str; 4] = [
    "exact_certificate_decodes",
    "exact_checker_acceptance",
    "exact_original_bytes_unsat",
    "exact_source_decodes",
];
const ALLOWED_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];
const UNSUPPORTED: [&str; 5] = [
    "interpreted symbols and $true are unsupported",
    "token is outside the supported TPTP CNF fragment",
    "only cnf statements are supported",
    "only the axiom role is supported",
    "TPTP annotations are unsupported",
];
const INVALID: [&str; 12] = [
    "uppercase character in a lowercase identifier",
    "input must contain ASCII bytes only",
    "invalid character",
    "inconsistent symbol arity",
    "expected a lowercase identifier",
    "expected a term",
    "duplicate clause name",
    "only cnf statements are supported",
    "expected '('",
    "expected ')'",
    "expected ','",
    "expected '.'",
];
const ESTABLISHED_INPUT_ERROR: [&str; 2] = ["inconsistent symbol arity", "duplicate clause name"];

/// `completed_contract`: the exit code of a normally completed child.
pub fn completed_contract(output: &StageOutput) -> Result<i64, Fault> {
    crate::older::normal_code(output).ok_or_else(|| {
        error(
            "Child did not satisfy its normal-exit contract",
            output.record.stage.clone(),
        )
    })
}

/// Python's `bytes.decode("ascii")`, with its error text as a ValueError.
fn ascii_text(data: &[u8]) -> Result<String, Fault> {
    match data.iter().position(|byte| !byte.is_ascii()) {
        None => Ok(String::from_utf8_lossy(data).to_string()),
        Some(position) => Err(value(format!(
            "'ascii' codec can't decode byte 0x{:02x} in position {position}: ordinal not in range(128)",
            data[position]
        ))),
    }
}

/// `engine_outcome`: candidate, or a final status with its reason.
pub fn engine_outcome(output: &StageOutput, source: &[u8]) -> Result<(String, String), Fault> {
    let code = completed_contract(output)?;
    let (stdout, stderr) = (&output.stdout[..], &output.stderr[..]);
    if code == 0 && stdout == b"candidate-refutation\n" && contract::candidate_stderr(stderr) {
        return Ok((
            "candidate".into(),
            "Rust candidate requires independent checking".into(),
        ));
    }
    if code == 2 && stdout == b"unknown\n" && contract::unknown_stderr(stderr) {
        return Ok((
            "GaveUp".into(),
            "Search exhausted its queue without a certified result".into(),
        ));
    }
    if stdout.is_empty() {
        if let Some(found) = contract::diagnostic(stderr) {
            let message = ascii_text(found.message)?;
            if code == 4 && found.kind == "Unsupported" && UNSUPPORTED.contains(&message.as_str()) {
                return Ok(("Inappropriate".into(), message));
            }
            if code == 3 && found.kind == "InvalidInput" && INVALID.contains(&message.as_str()) {
                let offset = found.offset_value();
                if message == "invalid character" && offset < source.len() as u128 {
                    let byte = source[offset as usize];
                    if byte == 127 || (byte < 32 && !b"\t\n\x0b\x0c\r".contains(&byte)) {
                        return Ok((
                            "InputError".into(),
                            "Invalid control byte in the declared ASCII syntax".into(),
                        ));
                    }
                }
                let status = if ESTABLISHED_INPUT_ERROR.contains(&message.as_str()) {
                    "InputError"
                } else {
                    "Inappropriate"
                };
                return Ok((status.into(), message));
            }
        }
        if code == 5 && contract::resource_stderr(stderr) {
            return Ok((
                "ResourceOut".into(),
                String::from_utf8_lossy(&stderr[..stderr.len() - 1]).to_string(),
            ));
        }
    }
    Err(error(
        "Malformed, unrecognized or failed engine contract",
        "search",
    ))
}

/// `checker_acceptance`.
pub fn checker_acceptance(output: &StageOutput) -> Result<(), Fault> {
    if completed_contract(output)? != 0 || output.stdout != ACCEPTED || !output.stderr.is_empty() {
        return Err(error(
            "Independent compiled checker did not accept the captured certificate",
            "checker",
        ));
    }
    Ok(())
}

/// `exact_axioms`: the four fixed reports, one each, nothing else, standard axioms only. Returns theorem ->
/// sorted axioms in report order. A ValueError of the shared parser becomes a Failure at stage "audit", as
/// kernel.py raised it.
pub fn exact_axioms(text: &str) -> Result<Object, Fault> {
    let reports = fang_axiom_audit::audit_axioms(text, &REQUIRED_AUDITS)
        .map_err(|failure| error(failure.0, "audit"))?;
    let matches = fang_axiom_audit::reports(text);
    let mut names: Vec<&str> = matches.iter().map(|report| report.name.as_str()).collect();
    names.sort_unstable();
    names.dedup();
    if matches.len() != REQUIRED_AUDITS.len() || names != REQUIRED_AUDITS {
        return Err(error("Extra or duplicate fixed-audit report", "audit"));
    }
    if !fang_axiom_audit::python_strip(&fang_axiom_audit::strip_reports(text)).is_empty() {
        return Err(error("Unexpected fixed-audit output", "audit"));
    }
    let mut found: Vec<&str> = reports.iter().map(|(name, _)| name.as_str()).collect();
    found.sort_unstable();
    let allowed = reports.iter().all(|(_, axioms)| {
        axioms
            .iter()
            .all(|axiom| ALLOWED_AXIOMS.contains(&axiom.as_str()))
    });
    if found != REQUIRED_AUDITS || !allowed {
        return Err(error("Fixed-audit theorem or axiom set differs", "audit"));
    }
    let mut result = Object::new();
    for (name, axioms) in reports {
        result.set(
            name.as_str(),
            fang_json::Value::Array(axioms.into_iter().map(fang_json::Value::String).collect()),
        );
    }
    Ok(result)
}

pub const HEADER: &str = "/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
The kernel checks exact decoder computations and checker acceptance, then
applies general source soundness to the original input byte value.
The compiled exporter is untrusted. Source acceptance completeness is separate.
-/
import Fang.CertificateInput
import Fang.FrontendSoundness
import Lean.Elab.Tactic.Cbv

namespace Fang.InstanceReplay

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 10000000

";

pub const FOOTER: &str =
    "theorem source_decodes : decodeProblem originalInput = .ok problem := by cbv

theorem certificate_decodes : decodeCertificate originalCertificate = .ok certificate := by cbv

theorem accepted : check (preprocess problem) certificate = true := by decide +kernel

theorem parsed_ast_unsat : \u{ac} Satisfiable problem :=
  check_preprocessed_sound problem certificate accepted

theorem original_input_unsat : \u{ac} Source.Grammar.BytesSatisfiable
    (Source.Grammar.spelling originalInput) :=
  decoded_refutation_unsat source_decodes certificate accepted

#print axioms source_decodes
#print axioms certificate_decodes
#print axioms accepted
#print axioms parsed_ast_unsat
#print axioms original_input_unsat

end Fang.InstanceReplay
";

/// `quote` of protocol.py and source_witness.py on ASCII text: a Lean string literal whose escapes are
/// `json.dumps`'s, except form feed and backspace, which Lean only accepts as `\u` escapes.
pub fn quote(text: &str) -> String {
    let mut result = String::from("\"");
    for character in text.chars() {
        match character {
            '\u{c}' => result.push_str("\\u000c"),
            '\u{8}' => result.push_str("\\u0008"),
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            character if (character as u32) < 0x20 || (character as u32) > 0x7e => {
                let mut units = [0u16; 2];
                for unit in character.encode_utf16(&mut units) {
                    result.push_str(&format!("\\u{unit:04x}"));
                }
            }
            character => result.push(character),
        }
    }
    result.push('"');
    result
}

/// `literal_value`: the bytes of a Lean string literal with only ordinary ASCII escapes, never an expression.
fn literal_value(text: &str) -> Result<Vec<u8>, Fault> {
    let characters: Vec<char> = text.chars().collect();
    if characters.len() < 2 || characters[0] != '"' || characters[characters.len() - 1] != '"' {
        return Err(error("Exporter string is not a string literal", "export"));
    }
    let end = characters.len() - 1;
    let mut result = Vec::new();
    let mut index = 1;
    while index < end {
        let mut character = characters[index];
        index += 1;
        if character == '\\' {
            if index >= end {
                return Err(error("Incomplete exporter escape", "export"));
            }
            let escape = characters[index];
            index += 1;
            character = match escape {
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                '\\' => '\\',
                '"' => '"',
                '0' => '\0',
                'u' | 'x' => {
                    let width = if escape == 'u' { 4 } else { 2 };
                    let digits: String = characters[index..(index + width).min(characters.len())]
                        .iter()
                        .collect();
                    if digits.chars().count() != width
                        || !digits.chars().all(|digit| digit.is_ascii_hexdigit())
                    {
                        return Err(error("Invalid exporter escape", "export"));
                    }
                    index += width;
                    char::from_u32(u32::from_str_radix(&digits, 16).unwrap_or(0xd800))
                        .unwrap_or('\u{fffd}')
                }
                _ => return Err(error("Unsupported exporter escape", "export")),
            };
        } else if character == '"' || (character as u32) < 32 {
            return Err(error("Invalid raw exporter string character", "export"));
        }
        if (character as u32) > 127 {
            return Err(error(
                "Exporter string changed the ASCII source boundary",
                "export",
            ));
        }
        result.push(character as u8);
    }
    Ok(result)
}

/// Python's `\b` after a keyword: the next character is not a word character.
fn word_end(text: &str, end: usize) -> bool {
    text[end..]
        .chars()
        .next()
        .is_none_or(|next| !(next.is_alphanumeric() || next == '_'))
}

/// One token of protocol.py's DATA_TOKEN at the start of `text`; returns its length.
fn data_token(text: &str) -> Option<usize> {
    let spaces: usize = text
        .chars()
        .take_while(|character| fang_axiom_audit::is_python_space(*character))
        .map(char::len_utf8)
        .sum();
    if spaces > 0 {
        return Some(spaces);
    }
    if text.starts_with("Certificate.mk") {
        return Some("Certificate.mk".len());
    }
    for word in [
        ".var", ".app", ".input", ".factor", ".resolve", "positive", "atom", "pred", "args",
        "true", "false",
    ] {
        if text.starts_with(word) && word_end(text, word.len()) {
            return Some(word.len());
        }
    }
    let digits = text.bytes().take_while(u8::is_ascii_digit).count();
    if digits > 0 {
        return Some(digits);
    }
    if text.starts_with(":=") {
        return Some(2);
    }
    text.chars()
        .next()
        .filter(|character| "[](){},".contains(*character))
        .map(|_| 1)
}

/// `fixed_replay`: check the exporter's template, keep only its constructor data, and rebuild the module with
/// the captured bytes quoted here.
pub fn fixed_replay(exported: &[u8], source: &[u8], certificate: &[u8]) -> Result<String, Fault> {
    let text = crate::older::python_utf8(exported)?;
    let differs = || error("Exporter imports or proof template differs", "export");
    if !text.starts_with(HEADER) || !text.ends_with(FOOTER) {
        return Err(differs());
    }
    let embedded = || {
        error(
            "Exporter did not embed the captured input and certificate",
            "export",
        )
    };
    let body = text
        .get(HEADER.len()..text.len().saturating_sub(FOOTER.len()))
        .ok_or_else(embedded)?;
    let rest = body
        .strip_prefix("def originalInput : String := ")
        .ok_or_else(embedded)?;
    let line = |rest: &'_ str| -> Option<usize> { rest.find('\n').filter(|&end| end > 0) };
    let first = line(rest).ok_or_else(embedded)?;
    let (input, rest) = rest.split_at(first);
    let rest = rest
        .strip_prefix("\n\ndef originalCertificate : String := ")
        .ok_or_else(embedded)?;
    let second = line(rest).ok_or_else(embedded)?;
    let (certificate_text, rest) = rest.split_at(second);
    let rest = rest
        .strip_prefix("\n\ndef problem : Problem := ")
        .ok_or_else(embedded)?;
    const SEPARATOR: &str = "\n\ndef certificate : Certificate := ";
    let split = rest.find(SEPARATOR).ok_or_else(embedded)?;
    let problem = &rest[..split];
    let rest = &rest[split + SEPARATOR.len()..];
    let parsed = rest.strip_suffix("\n\n").ok_or_else(embedded)?;
    if literal_value(input)? != source || literal_value(certificate_text)? != certificate {
        return Err(embedded());
    }
    for expression in [problem, parsed] {
        let mut cursor = 0;
        while cursor < expression.len() {
            let length = data_token(&expression[cursor..])
                .ok_or_else(|| error("Exporter contains non-constructor data", "export"))?;
            cursor += length;
        }
    }
    let source_text = String::from_utf8_lossy(source);
    let certificate_text = String::from_utf8_lossy(certificate);
    Ok(format!(
        "{HEADER}def originalInput : String := {}\n\ndef originalCertificate : String := {}\n\ndef problem : Problem := {problem}\n\ndef certificate : Certificate := {parsed}\n\n{FOOTER}",
        quote(&source_text),
        quote(&certificate_text)
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quote_follows_json_dumps_with_lean_escapes() {
        assert_eq!(
            quote("a\"b\\c\n\t\u{c}\u{8}\u{1}\u{7f}"),
            "\"a\\\"b\\\\c\\n\\t\\u000c\\u0008\\u0001\\u007f\""
        );
    }

    #[test]
    fn literal_values_take_ordinary_escapes_only() {
        assert_eq!(literal_value("\"a\\n\\x41\\u0042\"").unwrap(), b"a\nAB");
        assert!(literal_value("\"a\\q\"").is_err());
        assert!(literal_value("\"\\u00e9\"").is_err());
        assert!(literal_value("abc").is_err());
    }

    #[test]
    fn the_replay_template_is_rebuilt_around_the_captured_bytes() {
        let exported = format!(
            "{HEADER}def originalInput : String := \"cnf(a,axiom,p).\"\n\ndef originalCertificate : String := \"(c)\"\n\ndef problem : Problem := [{{ positive := true, atom := {{ pred := 0, args := [] }} }}]\n\ndef certificate : Certificate := Certificate.mk [.input 0] 0\n\n{FOOTER}"
        );
        let rebuilt = fixed_replay(exported.as_bytes(), b"cnf(a,axiom,p).", b"(c)").unwrap();
        assert_eq!(rebuilt, exported);
        assert!(fixed_replay(exported.as_bytes(), b"cnf(b,axiom,p).", b"(c)").is_err());
        let smuggled = exported.replace(
            "Certificate.mk [.input 0] 0",
            "Certificate.mk [.input (by sorry)] 0",
        );
        assert_eq!(
            fixed_replay(smuggled.as_bytes(), b"cnf(a,axiom,p).", b"(c)")
                .unwrap_err()
                .python_str(),
            "Exporter contains non-constructor data"
        );
    }

    // The controls of tools/tests/test_fang_szs.py `ProtocolTests` and `AxiomTests` that concern this module,
    // each named after the Python test it replaces.

    const INPUT: &[u8] = b"cnf(a,axiom,(p)).cnf(b,axiom,(~p)).\n";
    const PROOF: &[u8] =
        b"(fang-proof 1 (input 0 0) (input 1 1) (resolve 2 0 0 1 0 (subst) (clause)) (final 2))\n";

    fn output(exit_code: i32, classification: &str, stdout: &[u8], stderr: &[u8]) -> StageOutput {
        let record = fang_supervisor::StageRecord {
            stage: "search".into(),
            classification: classification.into(),
            exit_code: Some(exit_code),
            ..Default::default()
        };
        StageOutput {
            record,
            stdout: stdout.to_vec(),
            stderr: stderr.to_vec(),
        }
    }

    #[test]
    fn metadata_inconsistency() {
        assert!(engine_outcome(&output(2, "completed", b"unknown\n", b""), b"").is_err());
    }

    #[test]
    fn higher_order_at_and_lambda_are_outside_scope() {
        for source in [
            &b"thf(c,axiom,(f @ X))."[..],
            b"thf(c,axiom,(^ [X]: p(X))).",
        ] {
            let position = source.iter().position(|byte| b"@^".contains(byte)).unwrap();
            let stderr = format!("InvalidInput at byte {position}: invalid character\n");
            let (status, _) =
                engine_outcome(&output(3, "nonzero-exit", b"", stderr.as_bytes()), source).unwrap();
            assert_eq!(status, "Inappropriate");
        }
    }

    #[test]
    fn control_byte_is_established_input_error() {
        let (status, _) = engine_outcome(
            &output(
                3,
                "nonzero-exit",
                b"",
                b"InvalidInput at byte 0: invalid character\n",
            ),
            b"\0",
        )
        .unwrap();
        assert_eq!(status, "InputError");
    }

    fn fixture() -> String {
        format!(
            "{HEADER}def originalInput : String := {}\n\ndef originalCertificate : String := {}\n\ndef problem : Problem := []\n\ndef certificate : Certificate := Certificate.mk [] 0\n\n{FOOTER}",
            quote(std::str::from_utf8(INPUT).unwrap()),
            quote(std::str::from_utf8(PROOF).unwrap())
        )
    }

    #[test]
    fn fixed_template_retains_only_constructor_data() {
        assert!(
            fixed_replay(fixture().as_bytes(), INPUT, PROOF)
                .unwrap()
                .contains("def problem : Problem := []")
        );
    }

    #[test]
    fn export_cannot_select_imports() {
        let exported = fixture().replace("import Fang.CertificateInput", "import Malicious");
        assert!(fixed_replay(exported.as_bytes(), INPUT, PROOF).is_err());
    }

    #[test]
    fn export_cannot_inject_commands() {
        let exported = fixture().replace(
            "def problem : Problem := []",
            "def problem : Problem := by exact []",
        );
        assert!(fixed_replay(exported.as_bytes(), INPUT, PROOF).is_err());
    }

    #[test]
    fn export_cannot_substitute_input() {
        assert!(fixed_replay(fixture().as_bytes(), &[INPUT, b" "].concat(), PROOF).is_err());
    }

    #[test]
    fn export_cannot_substitute_certificate() {
        assert!(fixed_replay(fixture().as_bytes(), INPUT, &[PROOF, b" "].concat()).is_err());
    }

    #[test]
    fn export_cannot_select_axiom() {
        let exported = fixture().replace("by cbv", "by exact sorry");
        assert!(fixed_replay(exported.as_bytes(), INPUT, PROOF).is_err());
    }

    fn reports() -> String {
        REQUIRED_AUDITS
            .iter()
            .map(|name| {
                format!("'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]")
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    #[test]
    fn exact_reports() {
        let found = exact_axioms(&reports()).unwrap();
        let names: Vec<&str> = found.iter().map(|(name, _)| name).collect();
        let mut sorted = names.clone();
        sorted.sort_unstable();
        assert_eq!(sorted, REQUIRED_AUDITS);
    }

    #[test]
    fn missing() {
        let text = reports();
        assert!(exact_axioms(&text.lines().skip(1).collect::<Vec<_>>().join("\n")).is_err());
    }

    #[test]
    fn extra() {
        assert!(
            exact_axioms(&format!(
                "{}\n'Other' does not depend on any axioms",
                reports()
            ))
            .is_err()
        );
    }

    #[test]
    fn duplicate() {
        let text = reports();
        assert!(exact_axioms(&format!("{text}\n{}", text.lines().next().unwrap())).is_err());
    }

    #[test]
    fn custom_axiom() {
        assert!(exact_axioms(&reports().replace("propext", "Invented.fact")).is_err());
    }

    #[test]
    fn spoofing_comment() {
        assert!(exact_axioms(&format!("unexpected\n{}", reports())).is_err());
    }
}
