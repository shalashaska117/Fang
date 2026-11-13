// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The text scanners of the build scripts, written out by hand in place of their Python regular expressions:
//! the import scanner of build-v8-lean.py, and the comment blanking, forbidden-construct search, import findall and
//! audit count of check-suite.py, with Python's `str.splitlines`, `\s` and path order. Standard library only, so
//! they can be compared with the Python functions on their own.

use std::path::{Component, Path};

/// Python's `str.isspace()`, which `\s` matches in a str pattern.
pub fn py_space(character: char) -> bool {
    matches!(character, '\t' | '\n' | '\x0b' | '\x0c' | '\r' | '\x1c'..='\x1f' | ' ' | '\u{85}' | '\u{a0}' | '\u{1680}'
                        | '\u{2000}'..='\u{200a}' | '\u{2028}' | '\u{2029}' | '\u{202f}' | '\u{205f}' | '\u{3000}')
}

/// `\w` in a str pattern: alphanumeric or underscore. Rust's Unicode classes; they differ from Python's only
/// on combining marks, which no pinned source puts after an `import` keyword.
pub fn py_word(character: char) -> bool {
    character.is_alphanumeric() || character == '_'
}

/// Python's `str.splitlines()`.
pub fn splitlines(text: &str) -> Vec<&str> {
    let mut lines = Vec::new();
    let mut start = 0;
    let mut characters = text.char_indices().peekable();
    while let Some((index, character)) = characters.next() {
        let boundary = matches!(
            character,
            '\n' | '\r'
                | '\x0b'
                | '\x0c'
                | '\x1c'
                | '\x1d'
                | '\x1e'
                | '\u{85}'
                | '\u{2028}'
                | '\u{2029}'
        );
        if boundary {
            lines.push(&text[start..index]);
            let mut end = index + character.len_utf8();
            if character == '\r'
                && let Some(&(next, '\n')) = characters.peek()
            {
                characters.next();
                end = next + 1;
            }
            start = end;
        }
    }
    if start < text.len() {
        lines.push(&text[start..]);
    }
    lines
}

/// `re.fullmatch(r"(?:public )?import ([A-Za-z0-9_. ]+)", line)`: the imported names.
pub fn import_names(line: &str) -> Option<Vec<String>> {
    let candidates = line
        .strip_prefix("public ")
        .into_iter()
        .chain(std::iter::once(line));
    for candidate in candidates {
        if let Some(names) = candidate.strip_prefix("import ")
            && !names.is_empty()
            && names
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | ' '))
        {
            return Some(
                names
                    .split(' ')
                    .filter(|name| !name.is_empty())
                    .map(str::to_string)
                    .collect(),
            );
        }
    }
    None
}

/// `re.match(r"\s*(?:public\s+)?import\b", line)`.
pub fn import_like(line: &str) -> bool {
    let start = line.trim_start_matches(py_space);
    let after_public = start
        .strip_prefix("public")
        .filter(|rest| rest.starts_with(py_space))
        .map(|rest| rest.trim_start_matches(py_space));
    after_public
        .into_iter()
        .chain(std::iter::once(start))
        .any(|candidate| {
            candidate
                .strip_prefix("import")
                .is_some_and(|rest| rest.chars().next().is_none_or(|next| !py_word(next)))
        })
}

pub fn word(character: char) -> bool {
    character.is_alphanumeric() || character == '_'
}

/// `re.match(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\r\n])'", text[cursor:])`: the literal's length.
fn char_literal(text: &[char], cursor: usize) -> Option<usize> {
    let at = |offset: usize| text.get(cursor + offset).copied();
    if at(0) != Some('\'') {
        return None;
    }
    let body = match at(1)? {
        '\\' => {
            let hex = |from: usize, count: usize| {
                (0..count).all(|k| at(from + k).is_some_and(|c| c.is_ascii_hexdigit()))
            };
            // Alternatives in order: x with two hex digits, u with four, then any character but a newline.
            if at(2) == Some('x') && hex(3, 2) && at(5) == Some('\'') {
                4
            } else if at(2) == Some('u') && hex(3, 4) && at(7) == Some('\'') {
                6
            } else if at(2).is_some_and(|c| c != '\n') {
                2
            } else {
                return None;
            }
        }
        '\'' | '\r' | '\n' => return None,
        _ => 1,
    };
    (at(1 + body) == Some('\'')).then_some(body + 2)
}

/// `lean_code(text)`: nested comments and strings blanked, newlines kept, and `axiom` after `.` or `|` blanked.
pub fn lean_code(text: &str) -> Result<String, String> {
    let text: Vec<char> = text.chars().collect();
    let mut output: Vec<char> = Vec::with_capacity(text.len());
    let (mut cursor, mut depth, mut string) = (0usize, 0usize, false);
    let blank = |character: char| if character == '\n' { '\n' } else { ' ' };
    while cursor < text.len() {
        let character = text[cursor];
        let pair = (character, text.get(cursor + 1).copied());
        if depth > 0 {
            if pair == ('/', Some('-')) {
                depth += 1;
                cursor += 2;
            } else if pair == ('-', Some('/')) {
                depth -= 1;
                cursor += 2;
            } else {
                output.push(blank(character));
                cursor += 1;
            }
        } else if string {
            if character == '\\' {
                cursor += 2;
            } else if character == '"' {
                string = false;
                output.push(' ');
                cursor += 1;
            } else {
                output.push(blank(character));
                cursor += 1;
            }
        } else if pair == ('/', Some('-')) {
            depth = 1;
            cursor += 2;
        } else if pair == ('-', Some('-')) {
            cursor = text[cursor..]
                .iter()
                .position(|c| *c == '\n')
                .map_or(text.len(), |offset| cursor + offset);
        } else if let Some(length) = (character == '\'')
            .then(|| char_literal(&text, cursor))
            .flatten()
        {
            output.push(' ');
            cursor += length;
        } else if character == '«' {
            let end = text[cursor + 1..]
                .iter()
                .position(|c| *c == '»')
                .map(|offset| cursor + 1 + offset)
                .ok_or_else(|| "Unterminated Lean escaped identifier".to_string())?;
            output.push(' ');
            output.extend(std::iter::repeat_n(
                '\n',
                text[cursor..=end].iter().filter(|c| **c == '\n').count(),
            ));
            cursor = end + 1;
        } else if character == '"' {
            string = true;
            output.push(' ');
            cursor += 1;
        } else {
            output.push(character);
            cursor += 1;
        }
    }
    Ok(blank_member_axioms(&output))
}

/// `re.sub(r"(?P<head>[.|]\s*)\baxiom\b", lambda m: m["head"] + " " * 5, code)`.
fn blank_member_axioms(code: &[char]) -> String {
    let mut result: Vec<char> = Vec::with_capacity(code.len());
    let mut index = 0;
    while index < code.len() {
        if matches!(code[index], '.' | '|') {
            let mut end = index + 1;
            while end < code.len() && py_space(code[end]) {
                end += 1;
            }
            // \b before `axiom`: the head ends in '.', '|' or whitespace, none of them word characters.
            let word_at = |k: usize| code.get(k).is_some_and(|c| word(*c));
            if code[end..].starts_with(&['a', 'x', 'i', 'o', 'm']) && !word_at(end + 5) {
                result.extend_from_slice(&code[index..end]);
                result.extend([' '; 5]);
                index = end + 5;
                continue;
            }
        }
        result.push(code[index]);
        index += 1;
    }
    result.into_iter().collect()
}

fn starts_word(code: &[char], at: usize, word_text: &str) -> Option<usize> {
    let pattern: Vec<char> = word_text.chars().collect();
    code[at..]
        .starts_with(&pattern)
        .then_some(at + pattern.len())
}

fn boundary_after(code: &[char], at: usize) -> bool {
    !code.get(at).is_some_and(|c| word(*c))
}

/// `re.search(r"\b(sorry|admit|axiom|native_decide)\b|\bdecide\s*\+\s*native\b|\bdebug\.skipKernelTC\b", code)`.
pub fn forbidden(code: &str) -> Option<String> {
    let code: Vec<char> = code.chars().collect();
    for start in 0..code.len() {
        if start > 0 && word(code[start - 1]) {
            continue;
        }
        for name in ["sorry", "admit", "axiom", "native_decide"] {
            if let Some(end) =
                starts_word(&code, start, name).filter(|end| boundary_after(&code, *end))
            {
                return Some(code[start..end].iter().collect());
            }
        }
        if let Some(mut end) = starts_word(&code, start, "decide") {
            while end < code.len() && py_space(code[end]) {
                end += 1;
            }
            if code.get(end) == Some(&'+') {
                end += 1;
                while end < code.len() && py_space(code[end]) {
                    end += 1;
                }
                if let Some(end) =
                    starts_word(&code, end, "native").filter(|end| boundary_after(&code, *end))
                {
                    return Some(code[start..end].iter().collect());
                }
            }
        }
        if let Some(end) = starts_word(&code, start, "debug.skipKernelTC")
            .filter(|end| boundary_after(&code, *end))
        {
            return Some(code[start..end].iter().collect());
        }
    }
    None
}

/// `re.findall(r"^\s*(?:public\s+)?import\s+([\w.]+)", code, re.M)`.
pub fn imports(code: &str) -> Vec<String> {
    let code: Vec<char> = code.chars().collect();
    let skip = |mut at: usize| {
        while at < code.len() && py_space(code[at]) {
            at += 1;
        }
        at
    };
    let attempt = |line: usize| -> Option<(String, usize)> {
        let start = skip(line);
        let after_public = starts_word(&code, start, "public")
            .filter(|end| code.get(*end).is_some_and(|c| py_space(*c)))
            .map(skip);
        for candidate in after_public.into_iter().chain(std::iter::once(start)) {
            if let Some(end) = starts_word(&code, candidate, "import")
                .filter(|end| code.get(*end).is_some_and(|c| py_space(*c)))
            {
                let name_start = skip(end);
                let mut name_end = name_start;
                while name_end < code.len() && (word(code[name_end]) || code[name_end] == '.') {
                    name_end += 1;
                }
                if name_end > name_start {
                    return Some((code[name_start..name_end].iter().collect(), name_end));
                }
            }
        }
        None
    };
    // Candidate positions are the line starts; a match moves the search past its end.
    let line_starts = std::iter::once(0).chain(
        code.iter()
            .enumerate()
            .filter(|(_, c)| **c == '\n')
            .map(|(index, _)| index + 1),
    );
    let mut found = Vec::new();
    let mut search = 0;
    for line in line_starts {
        if line < search {
            continue;
        }
        if let Some((name, end)) = attempt(line) {
            found.push(name);
            search = end;
        }
    }
    found
}

/// `len(re.findall(r"#print\s+axioms\s+", code))`.
pub fn audit_count(code: &str) -> usize {
    let code: Vec<char> = code.chars().collect();
    let (mut count, mut at) = (0, 0);
    while at < code.len() {
        let matched = starts_word(&code, at, "#print")
            .and_then(|end| {
                let spaced = (end..code.len()).take_while(|k| py_space(code[*k])).count();
                (spaced > 0).then_some(end + spaced)
            })
            .and_then(|end| starts_word(&code, end, "axioms"))
            .and_then(|end| {
                let spaced = (end..code.len()).take_while(|k| py_space(code[*k])).count();
                (spaced > 0).then_some(end + spaced)
            });
        match matched {
            Some(end) => {
                count += 1;
                at = end;
            }
            None => at += 1,
        }
    }
    count
}

/// Python's ordering of paths: by components, not by the joined text.
pub fn path_key(path: &Path) -> Vec<String> {
    path.components()
        .filter_map(|component| match component {
            Component::Normal(name) => Some(name.to_string_lossy().into_owned()),
            _ => None,
        })
        .collect()
}

/// The text `Path.read_text()` gives: universal newlines, so "\r\n" and a lone "\r" become "\n".
pub fn universal_newlines(text: &str) -> String {
    text.replace("\r\n", "\n").replace('\r', "\n")
}
