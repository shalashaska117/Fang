// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! recipe/equality/generate-certificate.py: the certificate's exact string, its lexer and node
//! equations, and the constructor read from the certificate's own tokens. Envelope validity and
//! trailing tokens are left to Lean.

use super::{Outcome, Refusal, join, rejected};

const MAX_CERTIFICATE_NODES: usize = 100;

/// `quote(data)`: a Lean string literal of ASCII bytes.
pub(crate) fn quote(text: &str) -> String {
    let mut result = String::from("\"");
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
    format!("[{}]", join(data, ", "))
}

fn characters(data: &[u8]) -> String {
    format!(
        "[{}]",
        join(data.iter().map(|byte| format!("Char.ofNat {byte}")), ", ")
    )
}

/// `exact_string(label, data)`.
pub(crate) fn exact_string(label: &str, data: &[u8]) -> String {
    let chars = characters(data);
    let text = String::from_utf8_lossy(data);
    format!(
        "def {label} : String := {}\n\n@[cbv_eval] theorem {label}_characters : {label}.toList = {chars} := by\n  exact String.toList_ofList\n\n@[cbv_eval] theorem {label}_size : {label}.utf8ByteSize = {} := by\n  change (String.ofList {chars}).utf8ByteSize = _\n  rw [FangEqualityCertificateKernel.size_ofList]\n  decide +kernel\n\ntheorem {label}_ascii : ({chars}).findIdx? (fun c => c.toNat > 127) = none := by\n  decide +kernel\n\ntheorem exact_{label}_bytes : Fang.Source.Grammar.spelling {label} = {} := by\n  change Fang.Source.Grammar.spelling (String.ofList {chars}) = _\n  rw [Fang.Source.Grammar.spelling_ofList_ascii _ (by decide +kernel)]\n  rfl\n\n",
        quote(&text),
        data.len(),
        byte_list(data)
    )
}

fn word_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'$' || byte == b'-'
}

/// `re.finditer(r"[A-Za-z0-9_$-]+|[(),.|~]", text)`: each token with its start and end.
pub(crate) fn frontend_tokens(text: &[u8]) -> Vec<(String, usize, usize)> {
    let mut tokens = Vec::new();
    let mut position = 0;
    while position < text.len() {
        let byte = text[position];
        if word_byte(byte) {
            let start = position;
            while position < text.len() && word_byte(text[position]) {
                position += 1;
            }
            tokens.push((
                String::from_utf8_lossy(&text[start..position]).into_owned(),
                start,
                position,
            ));
        } else if b"(),.|~".contains(&byte) {
            tokens.push(((byte as char).to_string(), position, position + 1));
            position += 1;
        } else {
            position += 1;
        }
    }
    tokens
}

/// `[ \t\n\r\f\v]`.
fn lexer_space(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | b'\r' | 0x0c | 0x0b)
}

fn token_list(items: &[(String, usize)]) -> String {
    let rendered = items
        .iter()
        .map(|(word, offset)| format!("{{ text := {}, offset := {offset} }}", quote(word)));
    format!("[{}]", join(rendered, ", "))
}

/// `lexer_parts(label, data, "Frontend")`: suffix definitions and lexer equations, four to a
/// part, then the tokenizer equation.
pub(crate) fn lexer_parts(label: &str, data: &[u8]) -> Outcome<Vec<String>> {
    let namespace = "Frontend";
    if !data
        .iter()
        .all(|&byte| word_byte(byte) || b"(),.|~".contains(&byte) || lexer_space(byte))
    {
        return Err(rejected("Outside this replay token vocabulary"));
    }
    let tokens: Vec<(String, usize)> = frontend_tokens(data)
        .into_iter()
        .map(|(word, start, _)| (word, start))
        .collect();
    let mut boundaries: Vec<usize> = vec![0];
    boundaries.extend(tokens.iter().step_by(10).map(|(_, offset)| *offset));
    boundaries.sort_unstable();
    boundaries.dedup();
    let mut result = Vec::new();
    for (number, &offset) in boundaries.iter().enumerate().rev() {
        // Tokens and whitespace characters before the offset, as re.findall counts them.
        let prefix = &data[..offset];
        let steps = frontend_tokens(prefix).len()
            + prefix.iter().filter(|&&byte| lexer_space(byte)).count();
        let end = boundaries.get(number + 1).copied().unwrap_or(data.len());
        let more = end < data.len();
        let tail = if more {
            format!(" ++ {label}_suffix_characters_{}", number + 1)
        } else {
            String::new()
        };
        let token_tail = if more {
            format!(" ++ {label}_suffix_tokens_{}", number + 1)
        } else {
            String::new()
        };
        let suffix: Vec<(String, usize)> = tokens
            .iter()
            .filter(|(_, position)| offset <= *position && *position < end)
            .cloned()
            .collect();
        let fuel = data.len() as i64 + 1 - steps as i64;
        result.push(format!(
            "def {label}_suffix_characters_{number} : List Char := {}{tail}\n\ndef {label}_suffix_tokens_{number} : List Fang.Frontend.Token := {}{token_tail}\n\n@[cbv_eval] theorem {label}_lex_{number} : Fang.{namespace}.lexAux {fuel} {label}_suffix_characters_{number} {offset} = .ok {label}_suffix_tokens_{number} := by rfl\n\n",
            characters(&data[offset..end]),
            token_list(&suffix)
        ));
    }
    let mut parts: Vec<String> = result.chunks(4).map(|chunk| chunk.concat()).collect();
    parts.push(format!(
        "@[cbv_eval] theorem {label}_tokenizes : Fang.{namespace}.tokenize {label} = .ok {} :=\n  FangEqualityCertificateKernel.frontend_tokenizes {label} _ _ {}\n    {label}_characters {label}_ascii (by decide +kernel) {label}_lex_0\n\n",
        token_list(&tokens),
        data.len() + 1
    ));
    Ok(parts)
}

/// A parsed certificate expression: a token or a parenthesized list.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Expression {
    Atom(String),
    List(Vec<Expression>),
}

impl Expression {
    fn is(&self, text: &str) -> bool {
        matches!(self, Expression::Atom(atom) if atom == text)
    }

    /// `value[0]` with Python's behaviour on a string (its first character) and an empty list.
    fn first_is(&self, text: &str) -> Outcome<bool> {
        match self {
            Expression::Atom(atom) => Ok(atom
                .chars()
                .next()
                .is_some_and(|character| text == character.to_string())),
            Expression::List(items) => match items.first() {
                Some(first) => Ok(first.is(text)),
                None => Err(Refusal::Error("list index out of range".to_owned())),
            },
        }
    }

    /// `len(value)`: characters of a string, items of a list.
    fn length(&self) -> usize {
        match self {
            Expression::Atom(atom) => atom.chars().count(),
            Expression::List(items) => items.len(),
        }
    }
}

/// Python's `\s` on ASCII text: 0x09 to 0x0d, 0x1c to 0x1f and the space.
fn python_space(byte: u8) -> bool {
    matches!(byte, 0x09..=0x0d | 0x1c..=0x1f | b' ')
}

/// `re.findall(r"\(|\)|[^\s()]+", text)`.
fn sexpression_tokens(text: &[u8]) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut position = 0;
    while position < text.len() {
        let byte = text[position];
        if byte == b'(' || byte == b')' {
            tokens.push((byte as char).to_string());
            position += 1;
        } else if python_space(byte) {
            position += 1;
        } else {
            let start = position;
            while position < text.len()
                && !python_space(text[position])
                && text[position] != b'('
                && text[position] != b')'
            {
                position += 1;
            }
            tokens.push(String::from_utf8_lossy(&text[start..position]).into_owned());
        }
    }
    tokens
}

struct Reader {
    tokens: Vec<String>,
    cursor: usize,
}

impl Reader {
    fn expression(&mut self, depth: usize) -> Outcome<Expression> {
        if depth > 128 || self.cursor >= self.tokens.len() {
            return Err(rejected("Witness nesting/length limit"));
        }
        let token = self.tokens[self.cursor].clone();
        self.cursor += 1;
        if token != "(" {
            if token == ")" {
                return Err(rejected("Unexpected closing parenthesis"));
            }
            return Ok(Expression::Atom(token));
        }
        let mut result = Vec::new();
        while self.cursor < self.tokens.len() && self.tokens[self.cursor] != ")" {
            result.push(self.expression(depth + 1)?);
        }
        if self.cursor == self.tokens.len() {
            return Err(rejected("Missing closing parenthesis"));
        }
        self.cursor += 1;
        Ok(Expression::List(result))
    }
}

fn natural(value: &Expression) -> Outcome<String> {
    match value {
        Expression::Atom(text)
            if !text.is_empty()
                && text.len() <= 10
                && text.bytes().all(|byte| byte.is_ascii_digit()) =>
        {
            let number: u64 = text
                .parse()
                .map_err(|_| rejected("Expected bounded natural data"))?;
            Ok(number.to_string())
        }
        _ => Err(rejected("Expected bounded natural data")),
    }
}

fn sequence(values: Vec<String>) -> String {
    format!("[{}]", values.join(", "))
}

fn term(value: &Expression) -> Outcome<String> {
    let Expression::List(items) = value else {
        return Err(rejected("Expected term data"));
    };
    if items.len() < 2 {
        return Err(rejected("Expected term data"));
    }
    if items[0].is("v") && items.len() == 2 {
        return Ok(format!("(.var {})", natural(&items[1])?));
    }
    if items[0].is("f") {
        let symbol = natural(&items[1])?;
        let mut arguments = Vec::new();
        for argument in &items[2..] {
            arguments.push(term(argument)?);
        }
        return Ok(format!("(.app {symbol} {})", sequence(arguments)));
    }
    Err(rejected("Unknown term tag"))
}

fn literal(value: &Expression) -> Outcome<String> {
    // `polarity, atom = value`: a string unpacks into its characters.
    let (polarity, atom) = match value {
        Expression::List(items) if items.len() == 2 => (items[0].clone(), items[1].clone()),
        Expression::Atom(text) if text.chars().count() == 2 => {
            let mut characters = text.chars();
            let first = characters.next().map(String::from).unwrap_or_default();
            let second = characters.next().map(String::from).unwrap_or_default();
            (Expression::Atom(first), Expression::Atom(second))
        }
        _ => return Err(rejected("Expected two values to unpack")),
    };
    if !(polarity.is("pos") || polarity.is("neg")) {
        return Err(rejected("Unknown literal polarity"));
    }
    let encoded = if atom.first_is("eq")? && atom.length() == 3 {
        let Expression::List(items) = &atom else {
            return Err(rejected("Unknown atom data"));
        };
        format!(".equal {} {}", term(&items[1])?, term(&items[2])?)
    } else if atom.first_is("pred")? && atom.length() >= 2 {
        let Expression::List(items) = &atom else {
            return Err(rejected("Unknown atom data"));
        };
        let symbol = natural(&items[1])?;
        let mut arguments = Vec::new();
        for argument in &items[2..] {
            arguments.push(term(argument)?);
        }
        format!(".predicate ⟨{symbol}, {}⟩", sequence(arguments))
    } else {
        return Err(rejected("Unknown atom data"));
    };
    Ok(format!("⟨{}, {encoded}⟩", polarity.is("pos")))
}

fn clause(value: &Expression) -> Outcome<String> {
    match value {
        Expression::List(items) if !items.is_empty() && items[0].is("clause") => {
            let mut literals = Vec::new();
            for item in &items[1..] {
                literals.push(literal(item)?);
            }
            Ok(sequence(literals))
        }
        _ => Err(rejected("Expected clause data")),
    }
}

fn substitution(value: &Expression) -> Outcome<String> {
    let Expression::List(items) = value else {
        return Err(rejected("Expected substitution data"));
    };
    if items.is_empty() || !items[0].is("subst") {
        return Err(rejected("Expected substitution data"));
    }
    if items[1..]
        .iter()
        .any(|entry| !matches!(entry, Expression::List(pair) if pair.len() == 2))
    {
        return Err(rejected("Expected substitution entry"));
    }
    let mut entries = Vec::new();
    for entry in &items[1..] {
        if let Expression::List(pair) = entry {
            entries.push(format!("({}, {})", natural(&pair[0])?, term(&pair[1])?));
        }
    }
    Ok(sequence(entries))
}

/// `node[0] == tag and len(node) == count` for one certificate node.
fn node_is(node: &Expression, tag: &str, count: usize) -> Outcome<bool> {
    Ok(node.first_is(tag)? && node.length() == count)
}

/// `certificate_constructor(data)`: the parsed certificate, its steps and its final index.
pub(crate) fn certificate_constructor(data: &[u8]) -> Outcome<(String, Vec<String>, String)> {
    let mut reader = Reader {
        tokens: sexpression_tokens(data),
        cursor: 0,
    };
    let root = reader.expression(0)?;
    let nodes = match &root {
        Expression::List(items) if items.len() >= 4 && items[0].is("fang-proof") => {
            items[3..].to_vec()
        }
        _ => return Err(rejected("Expected proof data")),
    };
    let mut steps = Vec::new();
    let mut last = None;
    for node in &nodes {
        let item = |index: usize| match node {
            Expression::List(items) => items[index].clone(),
            Expression::Atom(_) => Expression::Atom(String::new()),
        };
        if node_is(node, "input", 3)? {
            steps.push(format!("(.input {})", natural(&item(2))?));
        } else if node_is(node, "eq-resolve", 9)? {
            let mut step = format!("(.equalityResolution {} ", natural(&item(2))?);
            step.push_str(&format!("{} {} ", clause(&item(3))?, clause(&item(4))?));
            step.push_str(&format!("{} {} ", term(&item(5))?, term(&item(6))?));
            step.push_str(&format!(
                "{} {})",
                substitution(&item(7))?,
                clause(&item(8))?
            ));
            steps.push(step);
        } else if node_is(node, "factor", 7)? {
            let mut step = format!("(.factor {} {} ", natural(&item(2))?, natural(&item(3))?);
            step.push_str(&format!(
                "{} {} {})",
                natural(&item(4))?,
                substitution(&item(5))?,
                clause(&item(6))?
            ));
            steps.push(step);
        } else if node_is(node, "resolve", 8)? {
            let mut step = format!(
                "(.resolution {} {} ",
                natural(&item(2))?,
                natural(&item(3))?
            );
            step.push_str(&format!("{} {} ", natural(&item(4))?, natural(&item(5))?));
            step.push_str(&format!(
                "{} {})",
                substitution(&item(6))?,
                clause(&item(7))?
            ));
            steps.push(step);
        } else if node_is(node, "paramodulate", 11)? {
            let (root, path, direction) = (item(6), item(7), item(8));
            let selected_root = if root
                == Expression::List(vec![Expression::Atom("equality-left".to_owned())])
            {
                ".equalityLeft".to_owned()
            } else if root == Expression::List(vec![Expression::Atom("equality-right".to_owned())])
            {
                ".equalityRight".to_owned()
            } else {
                match &root {
                    Expression::List(items) if items.len() == 2 && items[0].is("argument") => {
                        format!(".argument {}", natural(&items[1])?)
                    }
                    _ => return Err(rejected("Unknown root data")),
                }
            };
            let Expression::List(path_items) = &path else {
                return Err(rejected("Expected path data"));
            };
            if path_items.is_empty() || !path_items[0].is("path") {
                return Err(rejected("Expected path data"));
            }
            if !(direction.is("forward") || direction.is("reverse")) {
                return Err(rejected("Expected direction data"));
            }
            let mut witness = format!(
                "{{ sourcePivot := {}, targetLiteral := {}",
                natural(&item(4))?,
                natural(&item(5))?
            );
            let mut positions = Vec::new();
            for position in &path_items[1..] {
                positions.push(natural(position)?);
            }
            witness.push_str(&format!(
                ", root := {selected_root}, path := {}",
                sequence(positions)
            ));
            witness.push_str(&format!(
                ", reverse := {}, substitution := {} }}",
                direction.is("reverse"),
                substitution(&item(9))?
            ));
            let mut step = format!(
                "(.paramodulation {} {} ",
                natural(&item(2))?,
                natural(&item(3))?
            );
            step.push_str(&format!("{witness} {})", clause(&item(10))?));
            steps.push(step);
        } else if node_is(node, "final", 2)? {
            last = Some(natural(&item(1))?);
        } else {
            return Err(rejected("Unsupported witness step"));
        }
    }
    let Some(last) = last else {
        return Err(rejected("Missing final or too many nodes"));
    };
    if steps.len() > MAX_CERTIFICATE_NODES {
        return Err(rejected("Missing final or too many nodes"));
    }
    Ok((
        format!("⟨{}, {last}⟩", sequence(steps.clone())),
        steps,
        last,
    ))
}

/// `\((?:input|eq-resolve|factor|resolve|paramodulate|final)\b`: the start of each node.
fn node_starts(text: &[u8]) -> Vec<usize> {
    let keywords: [&[u8]; 6] = [
        b"input",
        b"eq-resolve",
        b"factor",
        b"resolve",
        b"paramodulate",
        b"final",
    ];
    let mut starts = Vec::new();
    for position in 0..text.len() {
        if text[position] != b'(' {
            continue;
        }
        let rest = &text[position + 1..];
        let matched = keywords.iter().any(|keyword| {
            rest.starts_with(keyword)
                && rest
                    .get(keyword.len())
                    .is_none_or(|&next| !(next.is_ascii_alphanumeric() || next == b'_'))
        });
        if matched {
            starts.push(position);
        }
    }
    starts
}

/// `node_equations(certificate, steps, final)`: one nodes equation per suffix, last first.
pub(crate) fn node_equations(
    certificate: &[u8],
    steps: &[String],
    last: &str,
) -> Outcome<Vec<String>> {
    let tokens = frontend_tokens(certificate);
    let starts = node_starts(certificate);
    if starts.len() != steps.len() + 1 {
        return Err(rejected("Expected one position per certificate node"));
    }
    let final_start = starts[starts.len() - 1];
    let Some(position) = tokens
        .iter()
        .position(|(_, offset, _)| *offset == final_start)
    else {
        return Err(Refusal::Error("StopIteration".to_owned()));
    };
    // The final parser consumes four tokens: (, final, index, ).
    let remaining: Vec<(String, usize, usize)> =
        tokens.iter().skip(position + 4).cloned().collect();
    let state = |items: &[(String, usize, usize)]| {
        let rendered = items
            .iter()
            .map(|(word, offset, _)| format!("{{ text := {}, offset := {offset} }}", quote(word)));
        format!(
            "{{ tokens := [{}], endOffset := {} }}",
            join(rendered, ", "),
            certificate.len()
        )
    };
    let mut modules = Vec::new();
    for index in (0..starts.len()).rev() {
        let input: Vec<(String, usize, usize)> = tokens
            .iter()
            .filter(|(_, offset, _)| *offset >= starts[index])
            .cloned()
            .collect();
        let output = format!("([{}], {last})", steps[index..].join(", "));
        modules.push(format!(
            "@[cbv_eval] theorem certificate_nodes_{index} : Fang.EqualityOrderedCertificateInput.nodes {} {index} {} = .ok ({output}, {}) := by cbv\n\n",
            tokens.len() + 1 - index,
            state(&input),
            state(&remaining)
        ));
    }
    Ok(modules)
}

const SUPPORT: &str = "/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EqualityOriginalCertificateInput

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 20000000

namespace FangEqualityCertificateKernel
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

theorem certificate_decodes (input : String) (tokens : List Fang.Frontend.Token)
    (size fuel : Nat) (certificate : Fang.Equality.Ordered.Certificate) (state : Fang.Frontend.State)
    (tokenized : Fang.Frontend.tokenize input = .ok tokens)
    (bytes : input.utf8ByteSize = size) (length : tokens.length + 1 = fuel)
    (parsed : FangQuantifiedEqualityCertificate.certificate fuel { tokens, endOffset := size } =
      .ok (certificate, state)) :
    FangQuantifiedEqualityCertificate.decodeCertificate input = .ok certificate := by
  simp [FangQuantifiedEqualityCertificate.decodeCertificate, tokenized, bytes, length, parsed,
    Bind.bind, Except.bind]
  rfl
end FangEqualityCertificateKernel

namespace EqInstance
";

/// `checked_module(certificate, problem, functions, predicates)`: the version-7 Checked module.
pub(crate) fn checked_module(
    certificate: &[u8],
    problem: &str,
    functions: &str,
    predicates: &str,
) -> Outcome<String> {
    let (expression, steps, last) = certificate_constructor(certificate)?;
    let mut body = exact_string("proofBytes", certificate);
    body.push_str(&format!(
        "def parsedCertificate : Fang.Equality.Ordered.Certificate := {expression}\n\n"
    ));
    body.push_str(&lexer_parts("proofBytes", certificate)?.concat());
    body.push_str(&node_equations(certificate, &steps, &last)?.concat());
    let tokens = frontend_tokens(certificate);
    let spelling = format!(
        "[{}]",
        join(
            tokens.iter().map(|(word, offset, _)| format!(
                "{{ text := {}, offset := {offset} }}",
                quote(word)
            )),
            ", "
        )
    );
    let size = certificate.len();
    let fuel = tokens.len() + 1;
    let text = String::from_utf8_lossy(certificate);
    body.push_str(&format!(
        "theorem certificate_parses :\n    FangQuantifiedEqualityCertificate.certificate {fuel}\n      {{ tokens := {spelling}, endOffset := {size} }} =\n      .ok (parsedCertificate, {{ tokens := [], endOffset := {size} }}) := by cbv\n\n@[cbv_eval] theorem exact_certificate_decodes :\n    FangQuantifiedEqualityCertificate.decodeCertificate proofBytes = .ok parsedCertificate :=\n  FangEqualityCertificateKernel.certificate_decodes proofBytes _ {size} {fuel}\n    parsedCertificate _ proofBytes_tokenizes proofBytes_size (by decide +kernel) certificate_parses\n\ntheorem checked_bytes : FangQuantifiedEqualityCertificate.checkPrepared\n    {problem} {functions} {predicates} {} = .ok () := by\n  change FangQuantifiedEqualityCertificate.checkPrepared _ _ _ proofBytes = .ok ()\n  unfold FangQuantifiedEqualityCertificate.checkPrepared\n  rw [exact_certificate_decodes]\n  cbv\n\n#print axioms EqInstance.exact_certificate_decodes\n#print axioms EqInstance.checked_bytes\nend EqInstance\n",
        quote(&text)
    ));
    // spelling_ofList_ascii is outside the lightweight imported closure and not needed here:
    // the final endpoint repeats the exact proof string.
    let start = body
        .find("theorem exact_proofBytes_bytes :")
        .ok_or_else(|| rejected("substring not found"))?;
    let end = body[start..]
        .find("def parsedCertificate")
        .ok_or_else(|| rejected("substring not found"))?
        + start;
    body.replace_range(start..end, "");
    Ok(format!("{SUPPORT}{body}"))
}
