// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The engine lines both older profiles read, as exact matchers of the Python regular expressions in
//! tools/fang_szs/protocol.py and tools/fof_szs/protocol.py (`re.fullmatch` on the whole stream).

/// `[1-9][0-9]* recorded search nodes; serialized proof keeps only refutation dependencies; independent
/// checking required\n`.
pub fn candidate_stderr(stderr: &[u8]) -> bool {
    const TAIL: &[u8] = b" recorded search nodes; serialized proof keeps only refutation dependencies; independent checking required\n";
    let digits = stderr
        .iter()
        .take_while(|byte| byte.is_ascii_digit())
        .count();
    digits >= 1 && stderr[0] != b'0' && &stderr[digits..] == TAIL
}

/// `queue exhausted after [0-9]+ clauses and [0-9]+ inference attempts\n`.
pub fn unknown_stderr(stderr: &[u8]) -> bool {
    let Some(rest) = stderr.strip_prefix(b"queue exhausted after ") else {
        return false;
    };
    let first = rest.iter().take_while(|byte| byte.is_ascii_digit()).count();
    if first == 0 {
        return false;
    }
    let Some(rest) = rest[first..].strip_prefix(b" clauses and ") else {
        return false;
    };
    let second = rest.iter().take_while(|byte| byte.is_ascii_digit()).count();
    second >= 1 && &rest[second..] == b" inference attempts\n"
}

/// A diagnostic `(InvalidInput|Unsupported) at byte ([0-9]+): ([^\r\n]+)\n`.
pub struct Diagnostic<'a> {
    pub kind: &'a str,
    /// The offset digits as written.
    pub offset: &'a [u8],
    pub message: &'a [u8],
}

impl Diagnostic<'_> {
    /// The offset as Python's `int()` gives it, saturated: an offset past u128 is past any input.
    pub fn offset_value(&self) -> u128 {
        let mut value: u128 = 0;
        for &digit in self.offset {
            value = value
                .saturating_mul(10)
                .saturating_add(u128::from(digit - b'0'));
        }
        value
    }
}

pub fn diagnostic(stderr: &[u8]) -> Option<Diagnostic<'_>> {
    let (kind, rest) = if let Some(rest) = stderr.strip_prefix(b"InvalidInput at byte ") {
        ("InvalidInput", rest)
    } else if let Some(rest) = stderr.strip_prefix(b"Unsupported at byte ") {
        ("Unsupported", rest)
    } else {
        return None;
    };
    let digits = rest.iter().take_while(|byte| byte.is_ascii_digit()).count();
    if digits == 0 {
        return None;
    }
    let rest = rest[digits..].strip_prefix(b": ")?;
    let message = rest.strip_suffix(b"\n")?;
    if message.is_empty() || message.iter().any(|&byte| byte == b'\r' || byte == b'\n') {
        return None;
    }
    Some(Diagnostic {
        kind,
        offset: &stderr[stderr.len() - rest.len() - 2 - digits..stderr.len() - rest.len() - 2],
        message,
    })
}

/// `ResourceLimit: [\x20-\x7e]+\n`.
pub fn resource_stderr(stderr: &[u8]) -> bool {
    let Some(rest) = stderr.strip_prefix(b"ResourceLimit: ") else {
        return false;
    };
    let Some(text) = rest.strip_suffix(b"\n") else {
        return false;
    };
    !text.is_empty() && text.iter().all(|&byte| (0x20..=0x7e).contains(&byte))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matchers_follow_the_python_patterns() {
        assert!(candidate_stderr(
            b"12 recorded search nodes; serialized proof keeps only refutation dependencies; independent checking required\n"
        ));
        assert!(!candidate_stderr(
            b"012 recorded search nodes; serialized proof keeps only refutation dependencies; independent checking required\n"
        ));
        assert!(unknown_stderr(
            b"queue exhausted after 3 clauses and 0 inference attempts\n"
        ));
        assert!(!unknown_stderr(
            b"queue exhausted after  clauses and 0 inference attempts\n"
        ));
        let found = diagnostic(b"InvalidInput at byte 17: invalid character\n").unwrap();
        assert_eq!(
            (found.kind, found.offset, found.message),
            ("InvalidInput", &b"17"[..], &b"invalid character"[..])
        );
        assert_eq!(found.offset_value(), 17);
        assert!(diagnostic(b"Unsupported at byte 3: \n").is_none());
        assert!(resource_stderr(b"ResourceLimit: search step limit\n"));
        assert!(!resource_stderr(b"ResourceLimit: \n"));
    }
}
