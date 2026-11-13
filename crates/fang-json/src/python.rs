// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Python's `repr` of a str and of a list of str, for messages that must read as Python's.

/// Non-ASCII characters Python's repr escapes: controls, separators and format characters in
/// the ranges that occur in practice. Other non-ASCII characters are kept, as Python keeps
/// every printable one; a character outside these ranges that Python does not consider
/// printable is the one known difference.
fn escaped_non_ascii(code: u32) -> bool {
    matches!(
        code,
        0x80..=0xa0
            | 0xad
            | 0x34f
            | 0x61c
            | 0x1680
            | 0x180e
            | 0x2000..=0x200f
            | 0x2028..=0x202f
            | 0x205f..=0x206f
            | 0x3000
            | 0xd800..=0xf8ff
            | 0xfeff
            | 0xfff0..=0xfffb
            | 0xfffe..=0xffff
            | 0xe0000..=0xe0fff
            | 0xf0000..=0x10ffff
    )
}

/// `repr(text)` for a Python str.
pub fn python_repr_str(text: &str) -> String {
    let quote = if text.contains('\'') && !text.contains('"') {
        '"'
    } else {
        '\''
    };
    let mut output = String::with_capacity(text.len() + 2);
    output.push(quote);
    for character in text.chars() {
        let code = u32::from(character);
        match character {
            _ if character == quote || character == '\\' => {
                output.push('\\');
                output.push(character);
            }
            '\t' => output.push_str("\\t"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            _ if code < 0x20 || code == 0x7f => output.push_str(&format!("\\x{code:02x}")),
            _ if code < 0x7f => output.push(character),
            _ if !escaped_non_ascii(code) => output.push(character),
            _ if code <= 0xff => output.push_str(&format!("\\x{code:02x}")),
            _ if code <= 0xffff => output.push_str(&format!("\\u{code:04x}")),
            _ => output.push_str(&format!("\\U{code:08x}")),
        }
    }
    output.push(quote);
    output
}

/// `repr(items)` for a Python list of str, as `str(sorted(...))` prints it in error messages.
pub fn python_repr_list<'a>(items: impl IntoIterator<Item = &'a str>) -> String {
    let parts: Vec<String> = items.into_iter().map(python_repr_str).collect();
    format!("[{}]", parts.join(", "))
}
