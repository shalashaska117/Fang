// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! A small regular-expression matcher for the child contracts, so that the patterns of the earlier Python
//! adapter can be kept verbatim.
//!
//! It implements the subset those patterns use, with Python's `re.fullmatch` semantics on bytes: literal bytes,
//! the escapes `\\`, `\.`, `\(` and the like, `\n`, `\r`, `\t`, character classes with ranges and negation,
//! `.` (any byte but a newline), capturing groups and `(?:...)`, alternation, and the greedy quantifiers `*`,
//! `+` and `?`. Matching backtracks; the patterns and the streams they read are short.

/// A compiled pattern.
#[derive(Clone, Debug)]
pub struct Pattern {
    node: Node,
    groups: usize,
}

#[derive(Clone, Debug)]
enum Node {
    Byte(u8),
    Any,
    Class(Vec<(u8, u8)>, bool),
    Group(Option<usize>, Vec<Vec<Node>>),
    Repeat(Box<Node>, usize, Option<usize>),
}

struct Compiler<'a> {
    text: &'a [u8],
    position: usize,
    groups: usize,
}

impl Compiler<'_> {
    fn peek(&self) -> Option<u8> {
        self.text.get(self.position).copied()
    }

    fn next(&mut self) -> Result<u8, String> {
        let byte = self.peek().ok_or("pattern ends early")?;
        self.position += 1;
        Ok(byte)
    }

    fn escape(byte: u8) -> u8 {
        match byte {
            b'n' => b'\n',
            b'r' => b'\r',
            b't' => b'\t',
            other => other,
        }
    }

    fn alternatives(&mut self) -> Result<Vec<Vec<Node>>, String> {
        let mut alternatives = vec![Vec::new()];
        while let Some(byte) = self.peek() {
            match byte {
                b')' => break,
                b'|' => {
                    self.position += 1;
                    alternatives.push(Vec::new());
                }
                _ => {
                    let atom = self.atom()?;
                    let atom = self.quantified(atom)?;
                    alternatives.last_mut().ok_or("no alternative")?.push(atom);
                }
            }
        }
        Ok(alternatives)
    }

    fn quantified(&mut self, atom: Node) -> Result<Node, String> {
        Ok(match self.peek() {
            Some(b'*') => {
                self.position += 1;
                Node::Repeat(Box::new(atom), 0, None)
            }
            Some(b'+') => {
                self.position += 1;
                Node::Repeat(Box::new(atom), 1, None)
            }
            Some(b'?') => {
                self.position += 1;
                Node::Repeat(Box::new(atom), 0, Some(1))
            }
            _ => atom,
        })
    }

    fn atom(&mut self) -> Result<Node, String> {
        match self.next()? {
            b'(' => {
                let index = if self.text[self.position..].starts_with(b"?:") {
                    self.position += 2;
                    None
                } else {
                    self.groups += 1;
                    Some(self.groups)
                };
                let alternatives = self.alternatives()?;
                if self.next()? != b')' {
                    return Err("unbalanced group".to_string());
                }
                Ok(Node::Group(index, alternatives))
            }
            b'[' => self.class(),
            b'.' => Ok(Node::Any),
            b'\\' => Ok(Node::Byte(Self::escape(self.next()?))),
            byte => Ok(Node::Byte(byte)),
        }
    }

    fn class(&mut self) -> Result<Node, String> {
        let negated = if self.peek() == Some(b'^') {
            self.position += 1;
            true
        } else {
            false
        };
        let mut ranges = Vec::new();
        let mut first = true;
        loop {
            let byte = self.next()?;
            if byte == b']' && !first {
                break;
            }
            first = false;
            let low = if byte == b'\\' {
                Self::escape(self.next()?)
            } else {
                byte
            };
            if self.peek() == Some(b'-')
                && self
                    .text
                    .get(self.position + 1)
                    .is_some_and(|&next| next != b']')
            {
                self.position += 1;
                let high = self.next()?;
                let high = if high == b'\\' {
                    Self::escape(self.next()?)
                } else {
                    high
                };
                ranges.push((low, high));
            } else {
                ranges.push((low, low));
            }
        }
        Ok(Node::Class(ranges, negated))
    }
}

/// Captured groups of one match: start and end of each group, `None` when it did not take part.
pub type Captures = Vec<Option<(usize, usize)>>;

impl Pattern {
    /// Compile `text`; a pattern outside the supported subset is an error.
    pub fn new(text: &str) -> Result<Pattern, String> {
        let mut compiler = Compiler {
            text: text.as_bytes(),
            position: 0,
            groups: 0,
        };
        let alternatives = compiler.alternatives()?;
        if compiler.position != compiler.text.len() {
            return Err("unbalanced group".to_string());
        }
        Ok(Pattern {
            node: Node::Group(Some(0), alternatives),
            groups: compiler.groups,
        })
    }

    /// Compile a pattern that is part of the program; it is known to be valid.
    pub fn of(text: &str) -> Pattern {
        Pattern::new(text).expect("a built-in pattern compiles")
    }

    /// `re.fullmatch`: the captures when the whole of `input` matches.
    pub fn fullmatch(&self, input: &[u8]) -> Option<Captures> {
        let mut captures = vec![None; self.groups + 1];
        let mut end_ok = |position: usize, _: &mut Captures| position == input.len();
        if matches(&self.node, input, 0, &mut captures, &mut end_ok) {
            Some(captures)
        } else {
            None
        }
    }

    /// Whether the whole of `input` matches.
    pub fn is_full(&self, input: &[u8]) -> bool {
        self.fullmatch(input).is_some()
    }
}

/// The bytes of group `index` in a match.
pub fn group<'a>(input: &'a [u8], captures: &Captures, index: usize) -> Option<&'a [u8]> {
    captures
        .get(index)
        .copied()
        .flatten()
        .map(|(start, end)| &input[start..end])
}

type Continuation<'c> = dyn FnMut(usize, &mut Captures) -> bool + 'c;

fn matches(
    node: &Node,
    input: &[u8],
    position: usize,
    captures: &mut Captures,
    rest: &mut Continuation,
) -> bool {
    match node {
        Node::Byte(byte) => input.get(position) == Some(byte) && rest(position + 1, captures),
        Node::Any => {
            input.get(position).is_some_and(|&byte| byte != b'\n') && rest(position + 1, captures)
        }
        Node::Class(ranges, negated) => match input.get(position) {
            Some(&byte) => {
                let inside = ranges
                    .iter()
                    .any(|&(low, high)| low <= byte && byte <= high);
                inside != *negated && rest(position + 1, captures)
            }
            None => false,
        },
        Node::Group(index, alternatives) => {
            let index = *index;
            for alternative in alternatives {
                let saved = captures.clone();
                let start = position;
                let mut close = |end: usize, captures: &mut Captures| {
                    let previous = index.map(|index| captures[index]);
                    if let Some(index) = index {
                        captures[index] = Some((start, end));
                    }
                    if rest(end, captures) {
                        return true;
                    }
                    if let (Some(index), Some(previous)) = (index, previous) {
                        captures[index] = previous;
                    }
                    false
                };
                if sequence(alternative, input, position, captures, &mut close) {
                    return true;
                }
                *captures = saved;
            }
            false
        }
        Node::Repeat(inner, minimum, maximum) => repeat(
            inner, *minimum, *maximum, 0, input, position, captures, rest,
        ),
    }
}

fn sequence(
    nodes: &[Node],
    input: &[u8],
    position: usize,
    captures: &mut Captures,
    rest: &mut Continuation,
) -> bool {
    match nodes.split_first() {
        None => rest(position, captures),
        Some((first, others)) => {
            let mut next = |position: usize, captures: &mut Captures| {
                sequence(others, input, position, captures, rest)
            };
            matches(first, input, position, captures, &mut next)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn repeat(
    inner: &Node,
    minimum: usize,
    maximum: Option<usize>,
    count: usize,
    input: &[u8],
    position: usize,
    captures: &mut Captures,
    rest: &mut Continuation,
) -> bool {
    // Greedy: one more repetition first, then stop. A repetition that consumed nothing ends the loop.
    if maximum.is_none_or(|maximum| count < maximum) {
        let mut again = |next: usize, captures: &mut Captures| {
            next != position
                && repeat(
                    inner,
                    minimum,
                    maximum,
                    count + 1,
                    input,
                    next,
                    captures,
                    rest,
                )
        };
        let saved = captures.clone();
        if matches(inner, input, position, captures, &mut again) {
            return true;
        }
        *captures = saved;
    }
    count >= minimum && rest(position, captures)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subset_behaves_like_python_re() {
        let unknown = Pattern::of(r"unknown: processed=[0-9]+ attempted=[0-9]+\n");
        assert!(unknown.is_full(b"unknown: processed=3 attempted=12\n"));
        assert!(!unknown.is_full(b"unknown: processed= attempted=12\n"));
        let text = Pattern::of(r#""(?:[^"\\\r\n]|\\.)*""#);
        assert!(text.is_full(br#""a \"quoted\" word""#));
        assert!(!text.is_full(b"\"line\nbreak\""));
        let input = Pattern::of(
            r#"adapter: Input\(Error \{ kind: (InvalidInput|Unsupported|ResourceLimit), offset: (None|Some\(([0-9]+)\)), message: ("(?:[^"\\\r\n]|\\.)*") \}\)\n"#,
        );
        let line = br#"adapter: Input(Error { kind: InvalidInput, offset: Some(14), message: "free variable" })
"#;
        let captures = input.fullmatch(line).expect("matches");
        assert_eq!(group(line, &captures, 1), Some(&b"InvalidInput"[..]));
        assert_eq!(group(line, &captures, 3), Some(&b"14"[..]));
        assert_eq!(group(line, &captures, 4), Some(&br#""free variable""#[..]));
        let none = br#"adapter: Input(Error { kind: Unsupported, offset: None, message: "x" })
"#;
        let captures = input.fullmatch(none).expect("matches");
        assert_eq!(group(none, &captures, 3), None);
        let optional = Pattern::of(r"io-error: [ -~]+\n(?:  [ -~]+\n)*");
        assert!(optional.is_full(b"io-error: no such file\n  file: /tmp/x\n"));
        assert!(!optional.is_full(b"io-error: no such file\n file: /tmp/x\n"));
        assert!(Pattern::of(r"a(?:b|bc)d").is_full(b"abcd"));
        assert!(Pattern::of(r"[a-z][A-Za-z0-9_]*").is_full(b"aNaturalNumber0"));
        assert!(!Pattern::of(r"[^-]x").is_full(b"-x"));
    }
}
