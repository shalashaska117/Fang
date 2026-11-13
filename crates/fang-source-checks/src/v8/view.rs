// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The code view of v8_dependencies.py: a file with every comment body removed, keeping
//! delimiters, comment kinds, line breaks, strings and code. The scanner works on characters,
//! as Python's str indexes do.

use crate::error::Error;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Suffix {
    Lean,
    Rust,
    Toml,
}

impl Suffix {
    /// `Path(name).suffix` for the three kinds the maps rewrite.
    pub fn of(name: &str) -> Option<Suffix> {
        let file = name.rsplit('/').next().unwrap_or(name);
        let index = file.rfind('.').filter(|index| *index > 0)?;
        match &file[index..] {
            ".lean" => Some(Suffix::Lean),
            ".rs" => Some(Suffix::Rust),
            ".toml" => Some(Suffix::Toml),
            _ => None,
        }
    }

    fn syntax(self) -> (&'static str, Option<(&'static str, &'static str)>) {
        match self {
            Suffix::Lean => ("--", Some(("/-", "-/"))),
            Suffix::Rust => ("//", Some(("/*", "*/"))),
            Suffix::Toml => ("#", None),
        }
    }

    /// COMMENT_KINDS: the characters after an opener that make a doc or module comment.
    fn kinds(self) -> (&'static str, &'static str) {
        match self {
            Suffix::Lean => ("", "-!"),
            Suffix::Rust => ("/!", "*!"),
            Suffix::Toml => ("", ""),
        }
    }
}

/// Python's `str.isalnum` for one character, through Rust's Unicode tables.
fn alnum(character: char) -> bool {
    character.is_alphanumeric()
}

struct Text<'a> {
    characters: &'a [char],
}

impl Text<'_> {
    fn len(&self) -> usize {
        self.characters.len()
    }

    fn starts_with(&self, word: &str, position: usize) -> bool {
        let mut index = position;
        for character in word.chars() {
            if self.characters.get(index) != Some(&character) {
                return false;
            }
            index += 1;
        }
        true
    }

    /// `text[start:end]` (clamped).
    fn slice(&self, start: usize, end: usize) -> String {
        self.characters[start.min(self.len())..end.min(self.len())]
            .iter()
            .collect()
    }

    fn find(&self, word: &str, from: usize) -> Option<usize> {
        (from..self.len()).find(|index| self.starts_with(word, *index))
    }

    fn find_char(&self, target: char, from: usize) -> Option<usize> {
        (from..self.len()).find(|index| self.characters[*index] == target)
    }

    /// `_RAW_STRING.match(text, position)`: b?r(#*)"; returns the hashes and the end.
    fn raw_string(&self, position: usize) -> Option<(usize, usize)> {
        let mut index = position;
        if self.characters.get(index) == Some(&'b') {
            index += 1;
        }
        if self.characters.get(index) != Some(&'r') {
            return None;
        }
        index += 1;
        let start = index;
        while self.characters.get(index) == Some(&'#') {
            index += 1;
        }
        if self.characters.get(index) != Some(&'"') {
            return None;
        }
        Some((index - start, index + 1))
    }

    /// `_CHARACTER.match(text, position)`: '(?:\\[^'\n]{1,10}|[^\\'\n])'; returns the end.
    fn character_literal(&self, position: usize) -> Option<usize> {
        if self.characters.get(position) != Some(&'\'') {
            return None;
        }
        let first = *self.characters.get(position + 1)?;
        if first == '\\' {
            let mut count = 0;
            while count < 10 {
                match self.characters.get(position + 2 + count) {
                    Some(&character) if character != '\'' && character != '\n' => count += 1,
                    _ => break,
                }
            }
            if count >= 1 && self.characters.get(position + 2 + count) == Some(&'\'') {
                return Some(position + 3 + count);
            }
            return None;
        }
        if first == '\'' || first == '\n' {
            return None;
        }
        (self.characters.get(position + 2) == Some(&'\'')).then_some(position + 3)
    }
}

fn string_end(
    text: &Text<'_>,
    start: usize,
    suffix: Suffix,
    view: &mut String,
) -> Result<usize, Error> {
    let mut position = start + 1;
    let interpolated = suffix == Suffix::Lean && start > 0 && text.characters[start - 1] == '!';
    while position < text.len() {
        let character = text.characters[position];
        if character == '\\' {
            position += 2;
        } else if character == '"' {
            view.push_str(&text.slice(start, position + 1));
            return Ok(position + 1);
        } else if interpolated && character == '{' {
            let mut inner = String::new();
            let mut spans = Vec::new();
            position = scan(text, position + 1, suffix, &mut inner, true, &mut spans)? + 1;
        } else {
            position += 1;
        }
    }
    Err(Error::value("Unclosed string literal"))
}

fn scan(
    text: &Text<'_>,
    mut position: usize,
    suffix: Suffix,
    view: &mut String,
    interpolation: bool,
    spans: &mut Vec<(usize, usize)>,
) -> Result<usize, Error> {
    let (line, block) = suffix.syntax();
    let (line_kinds, block_kinds) = suffix.kinds();
    let mut braces = 0usize;
    while position < text.len() {
        let character = text.characters[position];
        if interpolation && character == '{' {
            braces += 1;
        } else if interpolation && character == '}' {
            if braces == 0 {
                return Ok(position);
            }
            braces -= 1;
        }
        if text.starts_with(line, position) {
            let kind = text.slice(position + 2, position + 3);
            let end = text.find_char('\n', position).unwrap_or(text.len());
            view.push_str(line);
            if !kind.is_empty() && line_kinds.contains(kind.as_str()) {
                view.push_str(&kind);
            }
            spans.push((position, end));
            position = end;
            continue;
        }
        if let Some((opener, closer)) = block
            && text.starts_with(opener, position)
        {
            let kind = text.slice(position + 2, position + 3);
            let kind = if !kind.is_empty()
                && block_kinds.contains(kind.as_str())
                && !text.starts_with(closer, position + 2)
            {
                kind
            } else {
                String::new()
            };
            view.push_str(opener);
            view.push_str(&kind);
            let start = position;
            let mut depth = 1;
            position += 2 + kind.chars().count();
            while depth > 0 {
                if position >= text.len() {
                    return Err(Error::value("Unclosed block comment"));
                }
                if text.starts_with(opener, position) {
                    depth += 1;
                    position += 2;
                } else if text.starts_with(closer, position) {
                    depth -= 1;
                    position += 2;
                } else {
                    if text.characters[position] == '\n' {
                        view.push('\n');
                    }
                    position += 1;
                }
            }
            view.push_str(closer);
            spans.push((start, position));
            continue;
        }
        let previous = if position > 0 {
            Some(text.characters[position - 1])
        } else {
            None
        };
        if (character == 'b' || character == 'r')
            && suffix != Suffix::Toml
            && let Some((hashes, raw_end)) = text.raw_string(position)
            && !previous.is_some_and(|previous| alnum(previous) || previous == '_')
        {
            let mut terminator = String::from("\"");
            terminator.extend(std::iter::repeat_n('#', hashes));
            let Some(end) = text.find(&terminator, raw_end) else {
                return Err(Error::value("Unclosed raw string literal"));
            };
            let stop = end + terminator.chars().count();
            view.push_str(&text.slice(position, stop));
            position = stop;
            continue;
        }
        if character == '"' {
            position = string_end(text, position, suffix, view)?;
            continue;
        }
        if character == '\'' && suffix == Suffix::Toml {
            let end = text.find_char('\'', position + 1);
            match end {
                Some(end) if !text.characters[position..end].contains(&'\n') => {
                    view.push_str(&text.slice(position, end + 1));
                    position = end + 1;
                    continue;
                }
                _ => return Err(Error::value("Unclosed literal string")),
            }
        }
        if character == '\''
            && let Some(end) = text.character_literal(position)
        {
            // Python: `previous in "_'!?"` holds for the empty string at the start of the text.
            let blocked = suffix == Suffix::Lean
                && previous.is_none_or(|previous| alnum(previous) || "_'!?".contains(previous));
            if !blocked {
                view.push_str(&text.slice(position, end));
                position = end;
                continue;
            }
        }
        if suffix == Suffix::Lean && character == '\u{ab}' {
            let Some(end) = text.find_char('\u{bb}', position) else {
                return Err(Error::value("Unclosed escaped identifier"));
            };
            view.push_str(&text.slice(position, end + 1));
            position = end + 1;
            continue;
        }
        view.push(character);
        position += 1;
    }
    if interpolation {
        return Err(Error::value("Unclosed interpolation"));
    }
    Ok(position)
}

/// The code view and the (start, end) character span of every comment.
pub fn view_and_spans(text: &str, suffix: Suffix) -> Result<(String, Vec<(usize, usize)>), Error> {
    let characters: Vec<char> = text.chars().collect();
    let text = Text {
        characters: &characters,
    };
    let mut view = String::new();
    let mut spans = Vec::new();
    scan(&text, 0, suffix, &mut view, false, &mut spans)?;
    Ok((view, spans))
}

/// `code_view(text, suffix)`.
pub fn code_view(text: &str, suffix: Suffix) -> Result<String, Error> {
    Ok(view_and_spans(text, suffix)?.0)
}

/// `code_view_sha256(text, suffix)`.
pub fn code_view_sha256(text: &str, suffix: Suffix) -> Result<String, Error> {
    Ok(fang_hash::sha256_hex(code_view(text, suffix)?.as_bytes()))
}
