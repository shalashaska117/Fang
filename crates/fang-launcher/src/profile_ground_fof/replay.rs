// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Untrusted witnesses for the ground-FOF kernel replay; Lean must check every generated equation.
//!
//! A port of tools/replay/fof_replay.py with the certificate constructor of tools/replay/source_witness.py
//! (`certificate_source`). The generated modules and the audit source are byte-identical to the Python
//! generator's. Errors keep the Python distinction that matters to the caller: a profile bound
//! (`Error::Limit`, the Python `ReplayLimit`) or any other refusal (`Error::Invalid`, a Python ValueError).

/// The namespace of the generated modules.
pub const NAMESPACE: &str = "Fang.FOFKernelReplay.Instance";
/// The generated modules, in import order.
pub const MODULES: [&str; 4] = [
    "FofInstanceData",
    "FofInstanceInput",
    "FofInstanceCertificate",
    "FofInstanceProof",
];
/// The theorems of the fixed audit, sorted.
pub const AUDITS: [&str; 5] = [
    "exact_acceptance",
    "exact_certificate_bytes",
    "exact_certificate_decodes",
    "exact_input_bytes",
    "exact_original_bytes_unsat",
];
pub const MAX_INPUT_BYTES: usize = 4096;
pub const MAX_CERTIFICATE_BYTES: usize = 65536;
pub const MAX_CERTIFICATE_NODES: usize = 100;
pub const MAX_GENERATED_BYTES: usize = 16 << 20;
/// Python's limit on the digits `int()` converts.
const MAX_INT_DIGITS: usize = 4300;
/// Nesting the certificate reader accepts. Python's recursive reader stops at its interpreter's recursion
/// limit (1,000 frames) and reports a profile bound; a compiled-checker-accepted certificate never nests near
/// either value.
const MAX_NESTING: usize = 900;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// The bounded replay profile cannot process the data (Python `ReplayLimit`).
    Limit(&'static str),
    /// The data is outside what the generator reads (a Python ValueError).
    Invalid(&'static str),
}

/// The generated modules and the replay's metadata.
#[derive(Debug, PartialEq, Eq)]
pub struct Replay {
    pub modules: Vec<(String, String)>,
    pub input_bytes: usize,
    pub certificate_bytes: usize,
    pub certificate_nodes: usize,
}

fn ascii(data: &[u8]) -> Result<&str, Error> {
    if data.is_ascii() {
        // ASCII is valid UTF-8.
        std::str::from_utf8(data).map_err(|_| Error::Invalid("non-ASCII byte"))
    } else {
        Err(Error::Invalid("non-ASCII byte"))
    }
}

/// `quote` of fof_replay.py: control characters as \uXXXX, `"` and `\` escaped.
fn quote(text: &str) -> String {
    let mut result = String::with_capacity(text.len() + 2);
    result.push('"');
    for character in text.chars() {
        if (character as u32) < 32 {
            result.push_str(&format!("\\u{:04x}", character as u32));
        } else if character == '"' || character == '\\' {
            result.push('\\');
            result.push(character);
        } else {
            result.push(character);
        }
    }
    result.push('"');
    result
}

fn byte_list(data: &[u8]) -> String {
    let items: Vec<String> = data.iter().map(|byte| byte.to_string()).collect();
    format!("[{}]", items.join(", "))
}

fn characters(data: &[u8]) -> String {
    let items: Vec<String> = data
        .iter()
        .map(|byte| format!("Char.ofNat {byte}"))
        .collect();
    format!("[{}]", items.join(", "))
}

fn exact_string(label: &str, data: &[u8], text: &str) -> String {
    let chars = characters(data);
    format!(
        "def {label} : String := {quoted}\n\n\
@[cbv_eval] theorem {label}_characters : {label}.toList = {chars} := by\n  exact String.toList_ofList\n\n\
@[cbv_eval] theorem {label}_size : {label}.utf8ByteSize = {length} := by\n  change (String.ofList {chars}).utf8ByteSize = _\n  rw [Fang.FOFKernelReplay.size_ofList]\n  decide +kernel\n\n\
theorem exact_{label}_bytes : Fang.Source.Grammar.spelling {label} = {bytes} := by\n  change Fang.Source.Grammar.spelling (String.ofList {chars}) = _\n  rw [Fang.Source.Grammar.spelling_ofList_ascii _ (by decide +kernel)]\n  rfl\n\n",
        quoted = quote(text),
        length = data.len(),
        bytes = byte_list(data),
    )
}

fn is_word_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'$' | b'-')
}

/// `[ \t\n\r\f\v]`.
fn is_lexer_space(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | b'\r' | 0x0c | 0x0b)
}

/// The tokens of `pattern` in fof_replay.py `lexer_equations`, with the check that nothing but tokens and
/// `[ \t\n\r\f\v]` occurs. `formulas` selects the FOFFrontend vocabulary (`=>` and `&` besides the CNF
/// punctuation).
fn lexer_tokens(text: &[u8], formulas: bool) -> Result<Vec<(usize, usize)>, Error> {
    let punctuation: &[u8] = if formulas { b"(),.|~&" } else { b"(),.|~" };
    let mut tokens = Vec::new();
    let mut position = 0;
    while position < text.len() {
        let byte = text[position];
        if is_word_byte(byte) {
            let start = position;
            while position < text.len() && is_word_byte(text[position]) {
                position += 1;
            }
            tokens.push((start, position));
        } else if formulas && byte == b'=' && text.get(position + 1) == Some(&b'>') {
            tokens.push((position, position + 2));
            position += 2;
        } else if punctuation.contains(&byte) {
            tokens.push((position, position + 1));
            position += 1;
        } else if is_lexer_space(byte) {
            position += 1;
        } else {
            return Err(Error::Invalid(
                "Character outside the declared replay token vocabulary",
            ));
        }
    }
    Ok(tokens)
}

fn token_list(text: &[u8], items: &[(usize, usize)]) -> String {
    let rendered: Vec<String> = items
        .iter()
        .map(|&(start, end)| {
            // Token bytes are ASCII; the slice is valid UTF-8.
            let word = std::str::from_utf8(&text[start..end]).unwrap_or_default();
            format!("{{ text := {}, offset := {start} }}", quote(word))
        })
        .collect();
    format!("[{}]", rendered.join(", "))
}

fn lexer_equations(label: &str, data: &[u8], namespace: &str) -> Result<String, Error> {
    let formulas = namespace == "FOFFrontend";
    let tokens = lexer_tokens(data, formulas)?;
    // Every tenth token's offset, and 0, sorted and without repeats.
    let mut boundaries: Vec<usize> = tokens.iter().step_by(10).map(|&(start, _)| start).collect();
    boundaries.push(0);
    boundaries.sort_unstable();
    boundaries.dedup();
    let mut result = String::new();
    for (number, &offset) in boundaries.iter().enumerate().rev() {
        // Tokens and whitespace characters before the offset.
        let steps = tokens.iter().filter(|&&(start, _)| start < offset).count()
            + data[..offset]
                .iter()
                .filter(|&&byte| is_lexer_space(byte))
                .count();
        let after: Vec<(usize, usize)> = tokens
            .iter()
            .copied()
            .filter(|&(start, _)| start >= offset)
            .collect();
        result.push_str(&format!(
            "@[cbv_eval] theorem {label}_lex_{number} : Fang.{namespace}.lexAux {} {} {offset} = .ok {} := by cbv\n\n",
            data.len() + 1 - steps,
            characters(&data[offset..]),
            token_list(data, &after),
        ));
        if result.len() > MAX_GENERATED_BYTES {
            return Err(Error::Limit(
                "Generated lexer witness exceeds the replay byte cap",
            ));
        }
    }
    result.push_str(&format!(
        "@[cbv_eval] theorem {label}_tokenizes : Fang.{namespace}.tokenize {label} = .ok {} := by cbv\n\n",
        token_list(data, &tokens)
    ));
    Ok(result)
}

/// `[ \t\r\n\f\v]` of the header pattern.
fn header_space(byte: u8) -> bool {
    is_lexer_space(byte)
}

/// The end of the version-2 envelope header `( fang-proof 2 ( preprocessing ground-fof-distributive-v1 )`,
/// matched at the start as fof_replay.py's HEADER does.
fn header_end(data: &[u8]) -> Option<usize> {
    let mut position = 0;
    let skip = |position: &mut usize| {
        while *position < data.len() && header_space(data[*position]) {
            *position += 1;
        }
    };
    let skip_some = |position: &mut usize| -> bool {
        let start = *position;
        while *position < data.len() && header_space(data[*position]) {
            *position += 1;
        }
        *position > start
    };
    let literal = |position: &mut usize, text: &[u8]| -> bool {
        if data[*position..].starts_with(text) {
            *position += text.len();
            true
        } else {
            false
        }
    };
    skip(&mut position);
    if !literal(&mut position, b"(") {
        return None;
    }
    skip(&mut position);
    if !literal(&mut position, b"fang-proof")
        || !skip_some(&mut position)
        || !literal(&mut position, b"2")
    {
        return None;
    }
    if !skip_some(&mut position) || !literal(&mut position, b"(") {
        return None;
    }
    skip(&mut position);
    if !literal(&mut position, b"preprocessing")
        || !skip_some(&mut position)
        || !literal(&mut position, b"ground-fof-distributive-v1")
    {
        return None;
    }
    skip(&mut position);
    if !literal(&mut position, b")") {
        return None;
    }
    Some(position)
}

/// Python's `\s` on str, restricted to ASCII: `[\t\n\v\f\r\x1c-\x1f ]`.
fn python_space(byte: u8) -> bool {
    matches!(
        byte,
        b'\t' | b'\n' | 0x0b | 0x0c | b'\r' | 0x1c..=0x1f | b' '
    )
}

fn python_word(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

/// A parsed certificate s-expression.
enum Node {
    Atom(String),
    List(Vec<Node>),
}

impl Node {
    fn is(&self, text: &str) -> bool {
        matches!(self, Node::Atom(atom) if atom == text)
    }
    fn list(&self) -> Option<&[Node]> {
        match self {
            Node::List(items) => Some(items),
            Node::Atom(_) => None,
        }
    }
}

/// `re.findall(r"\(|\)|[^\s()]+", text)`.
fn certificate_words(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let mut words = Vec::new();
    let mut position = 0;
    while position < bytes.len() {
        let byte = bytes[position];
        if byte == b'(' || byte == b')' {
            words.push(&text[position..position + 1]);
            position += 1;
        } else if python_space(byte) {
            position += 1;
        } else {
            let start = position;
            while position < bytes.len()
                && !python_space(bytes[position])
                && bytes[position] != b'('
                && bytes[position] != b')'
            {
                position += 1;
            }
            words.push(&text[start..position]);
        }
    }
    words
}

fn read_expression(words: &[&str], position: &mut usize, depth: usize) -> Result<Node, Error> {
    if depth > MAX_NESTING {
        return Err(Error::Limit(
            "Certificate nesting exceeds the witness generator's stack limit",
        ));
    }
    let value = *words
        .get(*position)
        .ok_or(Error::Invalid("Truncated certificate"))?;
    *position += 1;
    if value == "(" {
        let mut values = Vec::new();
        while *position < words.len() && words[*position] != ")" {
            values.push(read_expression(words, position, depth + 1)?);
        }
        if *position >= words.len() {
            return Err(Error::Invalid("Unterminated certificate list"));
        }
        *position += 1;
        return Ok(Node::List(values));
    }
    if value == ")" {
        return Err(Error::Invalid("Unexpected certificate closing delimiter"));
    }
    Ok(Node::Atom(value.to_string()))
}

/// `natural` of source_witness.py: digits only, written as `str(int(value))`.
fn natural(value: &Node) -> Result<String, Error> {
    let Node::Atom(text) = value else {
        return Err(Error::Invalid("Expected certificate natural number"));
    };
    if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(Error::Invalid("Expected certificate natural number"));
    }
    if text.len() > MAX_INT_DIGITS {
        return Err(Error::Invalid(
            "Exceeds the limit for integer string conversion",
        ));
    }
    let trimmed = text.trim_start_matches('0');
    Ok(if trimmed.is_empty() {
        "0".to_string()
    } else {
        trimmed.to_string()
    })
}

fn lean_list(items: &[String]) -> String {
    format!("[{}]", items.join(", "))
}

fn term(value: &Node, depth: usize) -> Result<String, Error> {
    if depth > MAX_NESTING {
        return Err(Error::Limit(
            "Certificate nesting exceeds the witness generator's stack limit",
        ));
    }
    if let Some(items) = value.list() {
        if items.len() == 2 && items[0].is("v") {
            return Ok(format!("(.var {})", natural(&items[1])?));
        }
        if items.len() >= 2 && items[0].is("f") {
            let children = items[2..]
                .iter()
                .map(|child| term(child, depth + 1))
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(format!(
                "(.app {} {})",
                natural(&items[1])?,
                lean_list(&children)
            ));
        }
    }
    Err(Error::Invalid("Invalid certificate term"))
}

fn substitution(value: &Node) -> Result<String, Error> {
    let Some(items) = value
        .list()
        .filter(|items| !items.is_empty() && items[0].is("subst"))
    else {
        return Err(Error::Invalid("Invalid substitution"));
    };
    let mut bindings = Vec::new();
    for entry in &items[1..] {
        let Some(pair) = entry.list().filter(|pair| pair.len() == 2) else {
            return Err(Error::Invalid("Invalid binding"));
        };
        bindings.push(format!("({}, {})", natural(&pair[0])?, term(&pair[1], 1)?));
    }
    Ok(lean_list(&bindings))
}

fn clause(value: &Node) -> Result<String, Error> {
    let Some(items) = value
        .list()
        .filter(|items| !items.is_empty() && items[0].is("clause"))
    else {
        return Err(Error::Invalid("Invalid clause"));
    };
    let mut result = Vec::new();
    for literal in &items[1..] {
        let Some(parts) = literal
            .list()
            .filter(|parts| parts.len() >= 2 && (parts[0].is("pos") || parts[0].is("neg")))
        else {
            return Err(Error::Invalid("Invalid certificate literal"));
        };
        let arguments = parts[2..]
            .iter()
            .map(|child| term(child, 1))
            .collect::<Result<Vec<_>, _>>()?;
        result.push(format!(
            "{{ positive := {}, atom := {{ pred := {}, args := {} }} }}",
            if parts[0].is("pos") { "true" } else { "false" },
            natural(&parts[1])?,
            lean_list(&arguments)
        ));
    }
    Ok(lean_list(&result))
}

/// `certificate_source` of source_witness.py: the Lean constructor expression of a version-1 certificate.
pub fn certificate_source(text: &str) -> Result<String, Error> {
    let words = certificate_words(text);
    let mut position = 0;
    let parsed = read_expression(&words, &mut position, 0)?;
    let header = match &parsed {
        Node::List(items)
            if position == words.len()
                && items.len() >= 2
                && items[0].is("fang-proof")
                && items[1].is("1") =>
        {
            items
        }
        _ => {
            return Err(Error::Invalid(
                "Invalid certificate header or trailing input",
            ));
        }
    };
    let mut steps: Vec<String> = Vec::new();
    let mut last = None;
    let count = header.len();
    for (node_index, node) in header.iter().enumerate().skip(2) {
        let Some(items) = node.list().filter(|items| items.len() >= 2) else {
            return Err(Error::Invalid("Invalid certificate node"));
        };
        if items[0].is("final") {
            if items.len() != 2 || node_index != count - 1 {
                return Err(Error::Invalid("Invalid final node"));
            }
            last = Some(natural(&items[1])?);
            continue;
        }
        let identifier = natural(&items[1])?;
        if identifier != steps.len().to_string() {
            return Err(Error::Invalid("Non-sequential node ID"));
        }
        let numbers = |range: std::ops::Range<usize>| -> Result<String, Error> {
            Ok(items[range]
                .iter()
                .map(natural)
                .collect::<Result<Vec<_>, _>>()?
                .join(" "))
        };
        if items[0].is("input") && items.len() == 3 {
            steps.push(format!(".input {}", natural(&items[2])?));
        } else if items[0].is("factor") && items.len() == 7 {
            steps.push(format!(
                ".factor {} {} {}",
                numbers(2..5)?,
                substitution(&items[5])?,
                clause(&items[6])?
            ));
        } else if items[0].is("resolve") && items.len() == 8 {
            steps.push(format!(
                ".resolve {} {} {}",
                numbers(2..6)?,
                substitution(&items[6])?,
                clause(&items[7])?
            ));
        } else {
            return Err(Error::Invalid("Unsupported certificate node"));
        }
    }
    let Some(last) = last else {
        return Err(Error::Invalid("Missing final node"));
    };
    let wrapped: Vec<String> = steps.iter().map(|step| format!("({step})")).collect();
    Ok(format!("Certificate.mk {} {last}", lean_list(&wrapped)))
}

/// One token of fof_replay.py's CONSTRUCTOR_TOKEN at `position`, or None.
fn constructor_token(text: &[u8], position: usize) -> Option<usize> {
    let rest = &text[position..];
    let boundary = |length: usize| rest.get(length).is_none_or(|&byte| !python_word(byte));
    if python_space(rest[0]) {
        return Some(position + rest.iter().take_while(|&&byte| python_space(byte)).count());
    }
    if rest.starts_with(b"Certificate.mk") {
        return Some(position + "Certificate.mk".len());
    }
    if rest[0] == b'.' {
        for word in ["var", "app", "input", "factor", "resolve"] {
            if rest[1..].starts_with(word.as_bytes()) && boundary(1 + word.len()) {
                return Some(position + 1 + word.len());
            }
        }
    }
    for word in ["positive", "atom", "pred", "args", "true", "false"] {
        if rest.starts_with(word.as_bytes()) && boundary(word.len()) {
            return Some(position + word.len());
        }
    }
    if rest[0].is_ascii_digit() {
        return Some(position + rest.iter().take_while(|byte| byte.is_ascii_digit()).count());
    }
    if rest.starts_with(b":=") {
        return Some(position + 2);
    }
    if b"[](){},".contains(&rest[0]) {
        return Some(position + 1);
    }
    None
}

/// `len(re.findall(r"\.(?:input|factor|resolve)\b", expression))`.
fn node_count(text: &[u8]) -> usize {
    let mut count = 0;
    let mut position = 0;
    while position < text.len() {
        if text[position] == b'.' {
            let rest = &text[position + 1..];
            if let Some(word) = ["input", "factor", "resolve"].iter().find(|word| {
                rest.starts_with(word.as_bytes())
                    && rest.get(word.len()).is_none_or(|&byte| !python_word(byte))
            }) {
                count += 1;
                position += 1 + word.len();
                continue;
            }
        }
        position += 1;
    }
    count
}

/// `generate` of fof_replay.py with `certificate_source` as the constructor.
pub fn generate(source: &[u8], certificate: &[u8]) -> Result<Replay, Error> {
    if source.len() > MAX_INPUT_BYTES || certificate.len() > MAX_CERTIFICATE_BYTES {
        return Err(Error::Limit(
            "Input or certificate exceeds this kernel replay profile's byte cap",
        ));
    }
    let source_text = ascii(source)?;
    let certificate_text = ascii(certificate)?;
    let end = header_end(certificate).ok_or(Error::Invalid(
        "Expected version-2 ground-FOF certificate envelope",
    ))?;
    let legacy = format!("(fang-proof 1\n{}", &certificate_text[end..]);
    let expression = certificate_source(&legacy)?;
    let bytes = expression.as_bytes();
    let mut cursor = 0;
    while cursor < bytes.len() {
        cursor = constructor_token(bytes, cursor).ok_or(Error::Invalid(
            "Certificate emitter returned non-constructor syntax",
        ))?;
    }
    let nodes = node_count(bytes);
    if nodes > MAX_CERTIFICATE_NODES {
        return Err(Error::Limit(
            "Certificate exceeds this kernel replay profile's node cap",
        ));
    }
    let bodies = [
        format!(
            "{}{}def parsedCertificate : Fang.Certificate := {expression}\n\n",
            exact_string("input", source, source_text),
            exact_string("certificate", certificate, certificate_text)
        ),
        lexer_equations("input", source, "FOFFrontend")?,
        lexer_equations("certificate", certificate, "Frontend")?
            + "@[cbv_eval] theorem exact_certificate_decodes :\n    Fang.FOFVersioned.decodeCertificate certificate = .ok parsedCertificate := by cbv\n\n",
        format!(
            "theorem exact_acceptance :\n    Fang.FOFVersioned.accepts input certificate = .ok true := by\n  unfold Fang.FOFVersioned.accepts\n  rw [exact_certificate_decodes]\n  cbv\n\ntheorem exact_original_bytes_unsat :\n    \u{ac} Fang.FOFGrammar.BytesSatisfiable {} := by\n  have proved := Fang.FOFVersioned.accepts_original_unsat exact_acceptance\n  simpa only [exact_input_bytes] using proved\n\n",
            byte_list(source)
        ),
    ];
    let mut modules = Vec::new();
    let mut previous = "Fang.FOF.Replay".to_string();
    for (name, body) in MODULES.iter().zip(bodies) {
        let contents = format!(
            "import {previous}\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats 4000000\nset_option cbv.maxSteps 20000000\n\nnamespace {NAMESPACE}\n\n{body}end {NAMESPACE}\n"
        );
        modules.push((name.to_string(), contents));
        previous = name.to_string();
    }
    if modules.iter().map(|(_, text)| text.len()).sum::<usize>() > MAX_GENERATED_BYTES {
        return Err(Error::Limit("Generated modules exceed the replay byte cap"));
    }
    Ok(Replay {
        modules,
        input_bytes: source.len(),
        certificate_bytes: certificate.len(),
        certificate_nodes: nodes,
    })
}

/// `audit_source` of fof_replay.py: the fixed audit, bound to the captured bytes independently of the
/// generated modules.
pub fn audit_source(source: &[u8], certificate: &[u8]) -> String {
    let source_value = byte_list(source);
    let certificate_value = byte_list(certificate);
    let n = NAMESPACE;
    let mut text = format!(
        "import FofInstanceProof\n\nnamespace Fang.FOFKernelAudit\n\n\
theorem exact_original_bytes_unsat : \u{ac} Fang.FOFGrammar.BytesSatisfiable {source_value} := {n}.exact_original_bytes_unsat\n\n\
theorem exact_input_bytes : Fang.Source.Grammar.spelling {n}.input = {source_value} := {n}.exact_input_bytes\n\n\
theorem exact_certificate_bytes : Fang.Source.Grammar.spelling {n}.certificate = {certificate_value} := {n}.exact_certificate_bytes\n\n\
theorem exact_certificate_decodes : Fang.FOFVersioned.decodeCertificate {n}.certificate = .ok {n}.parsedCertificate := {n}.exact_certificate_decodes\n\n\
theorem exact_acceptance : Fang.FOFVersioned.accepts {n}.input {n}.certificate = .ok true := {n}.exact_acceptance\n\nend Fang.FOFKernelAudit\n\n"
    );
    for name in AUDITS {
        text.push_str(&format!("#print axioms Fang.FOFKernelAudit.{name}\n"));
    }
    text
}

/// The `emitted.json` the replay child writes, as Python's `json.dumps` of the same dictionary.
pub fn emitted_json(replay: &Replay) -> String {
    let names: Vec<String> = replay
        .modules
        .iter()
        .map(|(name, _)| format!("\"{name}\""))
        .collect();
    format!(
        "{{\"modules\": [{}], \"input_bytes\": {}, \"certificate_bytes\": {}, \"certificate_nodes\": {}}}\n",
        names.join(", "),
        replay.input_bytes,
        replay.certificate_bytes,
        replay.certificate_nodes
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quote_escapes_controls_quotes_and_backslashes() {
        assert_eq!(quote("a\"b\\c\n\x7f"), "\"a\\\"b\\\\c\\u000a\x7f\"");
    }

    #[test]
    fn certificate_source_reads_a_version_one_certificate() {
        let text = "(fang-proof 1\n(input 0 0)\n(input 1 01)\n(resolve 2 0 0 1 0 (subst) (clause))\n(final 2))";
        assert_eq!(
            certificate_source(text).unwrap(),
            "Certificate.mk [(.input 0), (.input 1), (.resolve 0 0 1 0 [] [])] 2"
        );
        assert!(matches!(
            certificate_source("(fang-proof 1 (input 1 0) (final 0))"),
            Err(Error::Invalid(_))
        ));
    }

    #[test]
    fn nesting_past_the_bound_is_a_profile_limit() {
        let deep = format!(
            "{}{}",
            "(".repeat(MAX_NESTING + 2),
            ")".repeat(MAX_NESTING + 2)
        );
        assert!(matches!(certificate_source(&deep), Err(Error::Limit(_))));
    }

    #[test]
    fn lexer_counts_whitespace_and_tokens_before_each_boundary() {
        let tokens = lexer_tokens(b"fof(a,axiom,p=>q).", true).unwrap();
        assert_eq!(tokens.len(), 11);
        assert!(lexer_tokens(b"p = q", true).is_err());
        assert!(lexer_tokens(b"(a & b)", false).is_err());
    }

    #[test]
    fn header_matches_the_version_two_envelope_only() {
        assert_eq!(
            header_end(b" ( fang-proof 2 (preprocessing ground-fof-distributive-v1) rest"),
            Some(58)
        );
        assert_eq!(
            header_end(b"(fang-proof 1 (preprocessing ground-fof-distributive-v1)"),
            None
        );
        assert_eq!(
            header_end(b"(fang-proof2 (preprocessing ground-fof-distributive-v1)"),
            None
        );
    }

    #[test]
    fn audit_lists_the_five_theorems_sorted() {
        let audit = audit_source(b"p", b"q");
        assert!(audit.ends_with("#print axioms Fang.FOFKernelAudit.exact_original_bytes_unsat\n"));
        assert_eq!(audit.matches("#print axioms").count(), 5);
    }

    /// Equivalence with the Python generator (fof_replay.py with source_witness.py) on cases it prepared:
    /// each directory under `FANG_REPLAY_CASES` holds `source.p`, `certificate.fang`, `python-outcome.txt`,
    /// `python-audit.lean` and, for an accepted pair, `python/` with the modules and `emitted.json`.
    #[test]
    #[ignore = "needs the cases the Python generator prepared"]
    fn python_equivalence() {
        let root = std::path::PathBuf::from(
            std::env::var_os("FANG_REPLAY_CASES").expect("FANG_REPLAY_CASES"),
        );
        let mut cases: Vec<std::path::PathBuf> = std::fs::read_dir(&root)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect();
        cases.sort();
        let mut differences = Vec::new();
        let mut counts = std::collections::BTreeMap::new();
        for case in &cases {
            let read = |name: &str| std::fs::read(case.join(name)).unwrap();
            let (source, certificate) = (read("source.p"), read("certificate.fang"));
            let expected = String::from_utf8(read("python-outcome.txt")).unwrap();
            let expected = expected.trim_end();
            let generated = generate(&source, &certificate);
            let outcome = match &generated {
                Ok(_) => "ok",
                Err(Error::Limit(_)) => "limit",
                Err(Error::Invalid(_)) => "invalid",
            };
            let same =
                outcome == expected || (outcome == "invalid" && expected.starts_with("other:"));
            *counts
                .entry(format!("{expected} -> {outcome}"))
                .or_insert(0usize) += 1;
            if !same {
                differences.push(format!(
                    "{}: python {expected}, rust {outcome}",
                    case.display()
                ));
            }
            if let Ok(replay) = &generated {
                for (name, contents) in &replay.modules {
                    if std::fs::read(case.join("python").join(format!("{name}.lean")))
                        .ok()
                        .as_deref()
                        != Some(contents.as_bytes())
                    {
                        differences.push(format!("{}: module {name} differs", case.display()));
                    }
                }
                if read("python/emitted.json") != emitted_json(replay).into_bytes() {
                    differences.push(format!("{}: emitted.json differs", case.display()));
                }
            }
            if read("python-audit.lean") != audit_source(&source, &certificate).into_bytes() {
                differences.push(format!("{}: audit differs", case.display()));
            }
        }
        println!("cases {}; outcomes {counts:?}", cases.len());
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
