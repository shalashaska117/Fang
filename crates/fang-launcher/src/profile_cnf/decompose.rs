// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The CNF profile's proof generators: a port of tools/replay/decomposed_replay_probe.py in the one mode the
//! profile runs (`--grouped --full --emit-only`), and of generic_source_replay.py `fixed_audit`.
//!
//! Both are untrusted: the decomposition's equations are checked by the kernel, and the fixed audit is built
//! by the parent from the captured bytes alone. Their output must equal the Python generators' bytes.

use crate::profile_cnf::protocol::quote;

/// The generated modules, in import order.
pub const MODULES: [&str; 11] = [
    "ReplayDefs",
    "CertificateCharacters",
    "LexerProofs",
    "CertificateTokens",
    "NodeProofs",
    "CertificateDecoded",
    "SourceCharacters",
    "SourceLexer",
    "SourceDecoded",
    "CertificateAccepted",
    "CompleteReplay",
];
/// The scope line of `emitted.json`.
pub const SCOPE: &str = "Untrusted generated proof sources; no compilation performed";
/// What `emitted.json` names as its generator, in place of the Python generator's hash.
pub const GENERATOR: &str = "fang-launcher --fang-internal cnf-decompose";

const OPTIONS: &str = "\nnamespace Fang.InstanceReplay\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\nset_option cbv.maxSteps 10000000\n\n";
const ENDING: &str = "\nend Fang.InstanceReplay\n";
const SIZE_LEMMA: &str = "theorem size_ofList (characters : List Char) :
    (String.ofList characters).utf8ByteSize = (characters.map Char.utf8Size).sum := by
  induction characters with
  | nil => rfl
  | cons c cs ih =>
    change (String.ofList ([c] ++ cs)).utf8ByteSize = _
    rw [String.ofList_append, String.utf8ByteSize_append,
      \u{2190} String.singleton_eq_ofList, String.utf8ByteSize_singleton, ih]
    rfl
";

/// Python's `repr` of one character.
pub fn char_repr(character: char) -> String {
    match character {
        '\'' => "\"'\"".to_string(),
        '\\' => "'\\\\'".to_string(),
        '\n' => "'\\n'".to_string(),
        '\r' => "'\\r'".to_string(),
        '\t' => "'\\t'".to_string(),
        character
            if (character as u32) < 0x20
                || (0x7f..0xa1).contains(&(character as u32))
                || character == '\u{ad}' =>
        {
            format!("'\\x{:02x}'", character as u32)
        }
        character => format!("'{character}'"),
    }
}

fn chars_source(text: &str) -> String {
    let items: Vec<String> = text.chars().map(char_repr).collect();
    format!("[{}]", items.join(", "))
}

fn token_source(items: &[(&str, usize)]) -> String {
    let items: Vec<String> = items
        .iter()
        .map(|(text, offset)| format!("{{ text := \"{text}\", offset := {offset} }}"))
        .collect();
    format!("[{}]", items.join(", "))
}

fn is_word(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'$' | b'-')
}

fn is_punctuation(byte: u8) -> bool {
    matches!(byte, b'(' | b')' | b',' | b'.' | b'|' | b'~')
}

fn is_space(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | b'\r' | b'\x0c' | b'\x0b')
}

/// `re.finditer(r"[A-Za-z0-9_$-]+|[(),.|~]", text)`: each token with its offset.
fn tokens(text: &str) -> Vec<(&str, usize)> {
    let bytes = text.as_bytes();
    let mut result = Vec::new();
    let mut position = 0;
    while position < bytes.len() {
        if is_word(bytes[position]) {
            let start = position;
            while position < bytes.len() && is_word(bytes[position]) {
                position += 1;
            }
            result.push((&text[start..position], start));
        } else {
            if is_punctuation(bytes[position]) {
                result.push((&text[position..position + 1], position));
            }
            position += 1;
        }
    }
    result
}

/// Whether the text holds only tokens and the lexer's whitespace (the generator's `assert re.sub(...) == ""`).
fn lexical_only(text: &str) -> bool {
    text.bytes()
        .all(|byte| is_word(byte) || is_punctuation(byte) || is_space(byte))
}

/// `len(re.findall(token | whitespace, prefix))`: the lexer steps that consume `prefix`.
fn steps(prefix: &str) -> usize {
    let bytes = prefix.as_bytes();
    let mut count = 0;
    let mut position = 0;
    while position < bytes.len() {
        if is_word(bytes[position]) {
            while position < bytes.len() && is_word(bytes[position]) {
                position += 1;
            }
            count += 1;
        } else {
            if is_punctuation(bytes[position]) || is_space(bytes[position]) {
                count += 1;
            }
            position += 1;
        }
    }
    count
}

fn character_equations(label: &str, text: &str, include_size_lemma: bool) -> String {
    let (literal, characters) = (quote(text), chars_source(text));
    let length = text.chars().count();
    let mut result = format!(
        "@[cbv_eval] theorem {label}_characters : String.toList {literal} = {characters} := by\n  exact String.toList_ofList\n"
    );
    if include_size_lemma {
        result.push_str(SIZE_LEMMA);
    }
    result.push_str(&format!(
        "@[cbv_eval] theorem {label}_size : {literal}.utf8ByteSize = {length} := by\n  change (String.ofList {characters}).utf8ByteSize = {length}\n  rw [size_ofList]\n  decide +kernel\n#print axioms {label}_size\n#print axioms {label}_characters\n"
    ));
    result
}

fn after<'a>(text: &'a str, marker: &str) -> Option<&'a str> {
    text.find(marker).map(|start| &text[start + marker.len()..])
}

fn before<'a>(text: &'a str, marker: &str) -> &'a str {
    text.find(marker).map_or(text, |start| &text[..start])
}

/// The decomposed modules of the replay module `original`, for the captured certificate `proof` and input
/// `source`. Every refusal of the Python generator (a non-ASCII pair, a byte outside the lexer's alphabet, a
/// certificate without its final step, a replay without its template theorems) is an error here.
pub fn decompose(
    original: &str,
    proof: &[u8],
    source: &[u8],
) -> Result<Vec<(String, String)>, &'static str> {
    let proof = std::str::from_utf8(proof)
        .ok()
        .filter(|text| text.is_ascii())
        .ok_or("certificate is not ASCII")?;
    let source_text = std::str::from_utf8(source)
        .ok()
        .filter(|text| text.is_ascii())
        .ok_or("input is not ASCII")?;
    let definition = before(original, "theorem source_decodes").replace(
        "import Fang.CertificateInput",
        "import Fang.DecoderComposition",
    );
    let tokens = tokens(proof);
    if !lexical_only(proof) {
        return Err("certificate holds a byte outside the lexer's alphabet");
    }
    let mut starts = Vec::new();
    let mut depth: i64 = 0;
    for (index, (token, _)) in tokens.iter().enumerate() {
        if *token == "(" {
            if depth == 1 {
                starts.push(index);
            }
            depth += 1;
        } else if *token == ")" {
            depth -= 1;
        }
    }
    let last = *starts.last().ok_or("certificate has no step")?;
    if tokens.get(last + 1).map(|(token, _)| *token) != Some("final") {
        return Err("certificate does not end with its final step");
    }
    let state_source = |index: usize| {
        format!(
            "({{ tokens := {}, endOffset := {} }} : Frontend.State)",
            token_source(&tokens[index..]),
            proof.len()
        )
    };
    let mut modules = vec![("ReplayDefs".to_string(), format!("{definition}{ENDING}"))];
    modules.push((
        "CertificateCharacters".to_string(),
        format!(
            "import ReplayDefs\n{OPTIONS}{}{ENDING}",
            character_equations("certificate", proof, true)
        ),
    ));
    let mut boundaries: Vec<usize> = std::iter::once(0)
        .chain(starts.iter().map(|&index| tokens[index].1))
        .collect();
    boundaries.sort_unstable();
    boundaries.dedup();
    let mut lexer_bodies = Vec::new();
    for (number, &offset) in boundaries.iter().enumerate().rev() {
        let consumed = steps(&proof[..offset]);
        let remaining: Vec<(&str, usize)> = tokens
            .iter()
            .copied()
            .filter(|(_, position)| *position >= offset)
            .collect();
        lexer_bodies.push(format!(
            "@[cbv_eval] theorem lex_suffix_{number} : Frontend.lexAux {} {} {offset} = .ok {} := by cbv\n#print axioms lex_suffix_{number}\n",
            proof.len() + 1 - consumed,
            chars_source(&proof[offset..]),
            token_source(&remaining)
        ));
    }
    modules.push((
        "LexerProofs".to_string(),
        format!(
            "import CertificateCharacters\n{OPTIONS}{}{ENDING}",
            lexer_bodies.join("\n")
        ),
    ));
    let body = format!(
        "@[cbv_eval] theorem certificate_tokenizes : Frontend.tokenize {} = .ok {} :=\n  tokenize_of_characters _ _ _ certificate_characters (by decide +kernel) lex_suffix_0\n#print axioms certificate_tokenizes\n",
        quote(proof),
        token_source(&tokens)
    );
    modules.push((
        "CertificateTokens".to_string(),
        format!("import LexerProofs\n{OPTIONS}{body}{ENDING}"),
    ));
    let end_state = state_source(tokens.len() - 1);
    let mut node_bodies = Vec::new();
    for (number, &token_index) in starts.iter().enumerate().rev() {
        node_bodies.push(format!(
            "@[cbv_eval] theorem node_suffix_{number} : CertificateInput.nodes {} {number} {} = .ok ((certificate.steps.drop {number}, certificate.final), {end_state}) := by cbv\n#print axioms node_suffix_{number}\n",
            tokens.len() + 1 - number,
            state_source(token_index)
        ));
    }
    modules.push((
        "NodeProofs".to_string(),
        format!(
            "import CertificateTokens\n{OPTIONS}{}{ENDING}",
            node_bodies.join("\n")
        ),
    ));
    let body = format!(
        "theorem certificate_decodes : decodeCertificate originalCertificate = .ok certificate :=\n  decodeCertificate_of_tokens _ _ _ {{ tokens := [], endOffset := {} }} certificate_tokenizes (by cbv)\n#print axioms certificate_decodes\n",
        proof.len()
    );
    modules.push((
        "CertificateDecoded".to_string(),
        format!("import NodeProofs\n{OPTIONS}{body}{ENDING}"),
    ));
    let source_proof = format!(
        "theorem source_decodes{}",
        before(
            after(original, "theorem source_decodes").ok_or("replay lacks source_decodes")?,
            "theorem certificate_decodes"
        )
    );
    let accepted_proof = format!(
        "theorem accepted{}",
        after(original, "theorem accepted").ok_or("replay lacks accepted")?
    );
    modules.push((
        "SourceCharacters".to_string(),
        format!(
            "import CertificateDecoded\n{OPTIONS}{}{ENDING}",
            character_equations("source", source_text, false)
        ),
    ));
    let source_tokens = self::tokens(source_text);
    if !lexical_only(source_text) {
        return Err("input holds a byte outside the lexer's alphabet");
    }
    let mut source_boundaries: Vec<usize> = std::iter::once(0)
        .chain(
            source_tokens
                .iter()
                .filter(|(token, _)| *token == "cnf")
                .map(|(_, offset)| *offset),
        )
        .collect();
    source_boundaries.sort_unstable();
    source_boundaries.dedup();
    let mut source_lexer = Vec::new();
    for (number, &offset) in source_boundaries.iter().enumerate().rev() {
        let consumed = steps(&source_text[..offset]);
        let remaining: Vec<(&str, usize)> = source_tokens
            .iter()
            .copied()
            .filter(|(_, position)| *position >= offset)
            .collect();
        source_lexer.push(format!(
            "@[cbv_eval] theorem source_lex_{number} : Frontend.lexAux {} {} {offset} = .ok {} := by cbv\n#print axioms source_lex_{number}\n",
            source_text.len() + 1 - consumed,
            chars_source(&source_text[offset..]),
            token_source(&remaining)
        ));
    }
    source_lexer.push(format!(
        "@[cbv_eval] theorem source_tokenizes : Frontend.tokenize {} = .ok {} :=\n  tokenize_of_characters _ _ _ source_characters (by decide +kernel) source_lex_0\n#print axioms source_tokenizes\n",
        quote(source_text),
        token_source(&source_tokens)
    ));
    modules.push((
        "SourceLexer".to_string(),
        format!(
            "import SourceCharacters\n{OPTIONS}{}{ENDING}",
            source_lexer.join("\n")
        ),
    ));
    modules.push((
        "SourceDecoded".to_string(),
        format!(
            "import SourceLexer\n{OPTIONS}{source_proof}#print axioms source_decodes\n{ENDING}"
        ),
    ));
    let (accepted, consequences) = accepted_proof
        .split_once("theorem parsed_ast_unsat")
        .ok_or("replay lacks parsed_ast_unsat")?;
    modules.push((
        "CertificateAccepted".to_string(),
        format!("import SourceDecoded\n{OPTIONS}{accepted}#print axioms accepted\n{ENDING}"),
    ));
    modules.push((
        "CompleteReplay".to_string(),
        format!("import CertificateAccepted\n{OPTIONS}theorem parsed_ast_unsat{consequences}"),
    ));
    Ok(modules)
}

/// The `emitted.json` the decomposition writes: `json.dumps(..., indent=2)` of its scope, its generator and the
/// module names.
pub fn emitted_json(modules: &[(String, String)]) -> String {
    let names: Vec<String> = modules
        .iter()
        .map(|(name, _)| format!("    \"{name}\""))
        .collect();
    format!(
        "{{\n  \"scope\": \"{SCOPE}\",\n  \"generator\": \"{GENERATOR}\",\n  \"modules\": [\n{}\n  ]\n}}\n",
        names.join(",\n")
    )
}

/// `fixed_audit` of generic_source_replay.py: only fixed theorem templates and the captured bytes, read
/// independently of the generated modules. `None` when a byte is not ASCII, where Python raised.
pub fn fixed_audit(module: &str, source: &[u8], certificate: &[u8]) -> Option<String> {
    if !matches!(module, "Replay" | "CompleteReplay")
        || !source.is_ascii()
        || !certificate.is_ascii()
    {
        return None;
    }
    let bytes: Vec<String> = source.iter().map(u8::to_string).collect();
    let byte_list = format!("[{}]", bytes.join(", "));
    let source_literal = quote(std::str::from_utf8(source).ok()?);
    let certificate_literal = quote(std::str::from_utf8(certificate).ok()?);
    let characters: Vec<String> = source
        .iter()
        .map(|&byte| char_repr(char::from(byte)))
        .collect();
    let source_characters = format!("[{}]", characters.join(", "));
    Some(format!(
        "import {module}\nimport Fang.SourceAscii\n\n\
set_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n\n\
theorem exact_input_value : Fang.InstanceReplay.originalInput = {source_literal} := by rfl\n\n\
theorem exact_certificate_value : Fang.InstanceReplay.originalCertificate = {certificate_literal} := by rfl\n\n\
theorem exact_input_bytes : Fang.Source.Grammar.spelling {source_literal} = {byte_list} := by\n\
\x20 change Fang.Source.Grammar.spelling (String.ofList {source_characters}) = _\n\
\x20 rw [Fang.Source.Grammar.spelling_ofList_ascii _ (by decide +kernel)]\n\
\x20 rfl\n\n\
theorem exact_original_bytes_unsat : \u{ac} Fang.Source.Grammar.BytesSatisfiable {byte_list} := by\n\
\x20 have proved : \u{ac} Fang.Source.Grammar.BytesSatisfiable\n\
\x20     (Fang.Source.Grammar.spelling Fang.InstanceReplay.originalInput) :=\n\
\x20   Fang.InstanceReplay.original_input_unsat\n\
\x20 simpa only [exact_input_value, exact_input_bytes] using proved\n\n\
theorem exact_source_decodes : Fang.decodeProblem {source_literal} = .ok Fang.InstanceReplay.problem := by\n\
\x20 rw [\u{2190} exact_input_value]\n\
\x20 exact Fang.InstanceReplay.source_decodes\n\n\
theorem exact_certificate_decodes : Fang.decodeCertificate {certificate_literal} = .ok Fang.InstanceReplay.certificate := by\n\
\x20 rw [\u{2190} exact_certificate_value]\n\
\x20 exact Fang.InstanceReplay.certificate_decodes\n\n\
theorem exact_checker_acceptance : Fang.check (Fang.preprocess Fang.InstanceReplay.problem) Fang.InstanceReplay.certificate = true := Fang.InstanceReplay.accepted\n\n\
#print axioms exact_original_bytes_unsat\n#print axioms exact_source_decodes\n\
#print axioms exact_certificate_decodes\n#print axioms exact_checker_acceptance\n"
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn characters_print_as_python_reprs() {
        assert_eq!(char_repr('a'), "'a'");
        assert_eq!(char_repr('\''), "\"'\"");
        assert_eq!(char_repr('\\'), "'\\\\'");
        assert_eq!(char_repr('\n'), "'\\n'");
        assert_eq!(char_repr('\u{b}'), "'\\x0b'");
        assert_eq!(char_repr('\u{7f}'), "'\\x7f'");
    }

    #[test]
    fn lexer_steps_count_tokens_and_single_spaces() {
        assert_eq!(steps("(fang-proof 1\n  ("), 8);
        assert_eq!(
            tokens("(a b)"),
            vec![("(", 0), ("a", 1), ("b", 3), (")", 4)]
        );
    }

    #[test]
    fn a_certificate_without_its_final_step_is_refused() {
        let original = "x theorem source_decodes y theorem certificate_decodes z theorem accepted w theorem parsed_ast_unsat v";
        assert!(decompose(original, b"(fang-proof 1 (input 0 0))", b"cnf(a,axiom,p).").is_err());
        let modules = decompose(
            original,
            b"(fang-proof 1 (input 0 0) (final 0))",
            b"cnf(a,axiom,p).",
        )
        .unwrap();
        let names: Vec<&str> = modules.iter().map(|(name, _)| name.as_str()).collect();
        assert_eq!(names, MODULES);
        assert!(emitted_json(&modules).starts_with("{\n  \"scope\": "));
    }

    /// Equivalence with the Python generators on cases they prepared: each directory under
    /// `FANG_DECOMPOSE_CASES` holds `Replay.lean`, `input.p`, `proof.fang`, `python-outcome.txt`, `python/` (the
    /// current decomposer's modules) and `python-audit.lean`; `export.stdout` (the retained exporter output, whose
    /// `fixed_replay` must give `Replay.lean`) and `retained/` (the modules the retained run compiled, reported
    /// but not required) when the run kept them.
    #[test]
    #[ignore = "needs the cases the Python generators prepared"]
    fn python_equivalence() {
        let root = std::path::PathBuf::from(
            std::env::var_os("FANG_DECOMPOSE_CASES").expect("FANG_DECOMPOSE_CASES"),
        );
        let mut cases: Vec<std::path::PathBuf> = std::fs::read_dir(&root)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect();
        cases.sort();
        let (mut differences, mut retained_differences) = (Vec::new(), 0usize);
        let mut counts = std::collections::BTreeMap::new();
        for case in &cases {
            let read = |name: &str| std::fs::read(case.join(name)).unwrap();
            let original = String::from_utf8(read("Replay.lean")).unwrap();
            let (source, proof) = (read("input.p"), read("proof.fang"));
            let expected = String::from_utf8(read("python-outcome.txt")).unwrap();
            let generated = decompose(&original, &proof, &source);
            let outcome = if generated.is_ok() { "ok" } else { "refused" };
            *counts
                .entry(format!("{} -> {outcome}", expected.trim_end()))
                .or_insert(0usize) += 1;
            if outcome != expected.trim_end() {
                differences.push(format!(
                    "{}: python {}, rust {outcome}",
                    case.display(),
                    expected.trim_end()
                ));
            }
            if let Ok(modules) = &generated {
                for (name, contents) in modules {
                    if std::fs::read(case.join("python").join(format!("{name}.lean")))
                        .ok()
                        .as_deref()
                        != Some(contents.as_bytes())
                    {
                        differences.push(format!("{}: module {name} differs", case.display()));
                    }
                    if case.join("retained").is_dir()
                        && std::fs::read(case.join("retained").join(format!("{name}.lean")))
                            .ok()
                            .as_deref()
                            != Some(contents.as_bytes())
                    {
                        retained_differences += 1;
                    }
                }
            }
            let audit = fixed_audit("CompleteReplay", &source, &proof);
            match std::fs::read(case.join("python-audit.lean")) {
                Ok(reference) if audit.as_deref().map(str::as_bytes) == Some(&reference[..]) => {}
                Err(_) if audit.is_none() => {}
                _ => differences.push(format!("{}: audit differs", case.display())),
            }
            if let Ok(exported) = std::fs::read(case.join("export.stdout")) {
                match crate::profile_cnf::protocol::fixed_replay(&exported, &source, &proof) {
                    Ok(replay) if replay.as_bytes() == original.as_bytes() => {}
                    _ => differences.push(format!("{}: fixed_replay differs", case.display())),
                }
            }
        }
        println!(
            "cases {}; outcomes {counts:?}; retained module differences {retained_differences}",
            cases.len()
        );
        for difference in &differences {
            println!("{difference}");
        }
        assert!(
            !cases.is_empty() && differences.is_empty(),
            "{} differences",
            differences.len()
        );
    }
}
