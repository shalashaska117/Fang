// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! A command-line parser with the behaviour and the texts of Python's argparse, for the parsers the `fang`
//! profiles declare: one positional argument, options that take one value (with an optional set of choices),
//! store-true flags and -h/--help.
//!
//! Parsing follows argparse: long options may be abbreviated to a unique prefix, `--option=value` is
//! accepted, `--` ends the options, a value that looks like a negative number is a value, and the last
//! occurrence of an option wins. Errors carry argparse's messages, without the "usage:" block, since the
//! profiles turn them into run-record reasons. Help is laid out as argparse's HelpFormatter lays it out for a
//! non-terminal: the width is COLUMNS when set, otherwise 80, less two.

use std::collections::BTreeMap;

/// The type of an argument's value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Text,
    Path,
    Int,
    Float,
    /// A store-true flag: no value, true when given.
    Flag,
}

/// A parsed value.
#[derive(Clone, Debug, PartialEq)]
pub enum Parsed {
    None,
    Text(String),
    Int(i64),
    /// An integer Python accepts that does not fit in 64 bits; every range check refuses it.
    Large,
    Float(f64),
    Bool(bool),
}

/// A default: the value the argument takes when absent, and the text `%(default)s` shows in its help.
#[derive(Clone, Debug, PartialEq)]
pub struct Default {
    pub value: Parsed,
    pub display: String,
}

impl Default {
    pub fn none() -> Self {
        Default {
            value: Parsed::None,
            display: "None".to_string(),
        }
    }
    pub fn int(value: i64) -> Self {
        Default {
            value: Parsed::Int(value),
            display: value.to_string(),
        }
    }
    /// A float option whose default was written as an integer in Python (for example `default=60`): the
    /// value is that integer, shown without a fraction.
    pub fn int_for_float(value: i64) -> Self {
        Default {
            value: Parsed::Int(value),
            display: value.to_string(),
        }
    }
    pub fn text(value: &str) -> Self {
        Default {
            value: Parsed::Text(value.to_string()),
            display: value.to_string(),
        }
    }
    pub fn flag() -> Self {
        Default {
            value: Parsed::Bool(false),
            display: "False".to_string(),
        }
    }
}

/// One declared argument.
#[derive(Clone, Debug)]
pub struct Argument {
    /// Where the value is stored, and the positional's name.
    pub dest: String,
    /// The option string, for example `--check`; empty for the positional.
    pub flag: String,
    pub kind: Kind,
    pub choices: Option<Vec<String>>,
    pub default: Default,
    pub required: bool,
    pub help: String,
}

impl Argument {
    fn positional(&self) -> bool {
        self.flag.is_empty()
    }

    /// The name argparse uses in error messages.
    fn name(&self) -> String {
        if self.positional() {
            self.dest.clone()
        } else {
            self.flag.clone()
        }
    }

    /// The metavar of the value: `{a,b,c}` for choices, otherwise the dest in upper case (the dest itself for
    /// the positional).
    fn metavar(&self) -> String {
        if let Some(choices) = &self.choices {
            format!("{{{}}}", choices.join(","))
        } else if self.positional() {
            self.dest.clone()
        } else {
            self.dest.to_uppercase()
        }
    }

    /// The help column's text: `-h, --help` for help, the option and its metavar for an option with a value.
    fn invocation(&self) -> String {
        if self.positional() {
            self.metavar()
        } else if self.dest == "help" {
            "-h, --help".to_string()
        } else if self.kind == Kind::Flag {
            self.flag.clone()
        } else {
            format!("{} {}", self.flag, self.metavar())
        }
    }

    /// The usage text: the first option string only, in brackets unless required.
    fn usage_part(&self) -> String {
        let invocation = if self.positional() || self.kind == Kind::Flag {
            if self.positional() {
                self.metavar()
            } else {
                self.flag.clone()
            }
        } else {
            format!("{} {}", self.flag, self.metavar())
        };
        if self.positional() || self.required {
            invocation
        } else {
            format!("[{invocation}]")
        }
    }
}

/// What parsing gives: the values, or a request for help, or an error message.
#[derive(Debug)]
pub enum Outcome {
    Values(Values),
    /// `-h` or `--help` was given: the help text, to print to standard output before exiting 0.
    Help(String),
    /// An argparse error message, for example "the following arguments are required: input".
    Error(String),
}

/// Parsed values by dest.
#[derive(Clone, Debug, Default)]
pub struct Values {
    values: BTreeMap<String, Parsed>,
}

impl Values {
    pub fn get(&self, dest: &str) -> &Parsed {
        self.values.get(dest).unwrap_or(&Parsed::None)
    }
    pub fn text(&self, dest: &str) -> Option<&str> {
        match self.get(dest) {
            Parsed::Text(text) => Some(text),
            _ => None,
        }
    }
    pub fn int(&self, dest: &str) -> Option<i64> {
        match self.get(dest) {
            Parsed::Int(value) => Some(*value),
            _ => None,
        }
    }
    /// A float option's value; an integer default counts as its float value.
    pub fn float(&self, dest: &str) -> Option<f64> {
        match self.get(dest) {
            Parsed::Float(value) => Some(*value),
            Parsed::Int(value) => Some(*value as f64),
            _ => None,
        }
    }
    pub fn flag(&self, dest: &str) -> bool {
        matches!(self.get(dest), Parsed::Bool(true))
    }
}

/// How `classify` sees one string: `None` for a value; otherwise the matched argument (`None` for help),
/// whether it is the help option, and an explicit value after `=`.
type Classified<'a> = Option<(Option<&'a Argument>, bool, Option<String>)>;

/// A parser: the program name, the texts and the declared arguments, in declaration order.
#[derive(Clone, Debug)]
pub struct Parser {
    pub prog: String,
    pub description: String,
    pub epilog: String,
    arguments: Vec<Argument>,
}

impl Parser {
    /// A parser with -h/--help declared first, as argparse does.
    pub fn new(prog: &str) -> Self {
        Parser {
            prog: prog.to_string(),
            description: String::new(),
            epilog: String::new(),
            arguments: Vec::new(),
        }
    }

    pub fn description(mut self, text: &str) -> Self {
        self.description = text.to_string();
        self
    }

    pub fn epilog(mut self, text: &str) -> Self {
        self.epilog = text.to_string();
        self
    }

    /// The positional argument.
    pub fn positional(mut self, dest: &str, kind: Kind, help: &str) -> Self {
        self.arguments.push(Argument {
            dest: dest.to_string(),
            flag: String::new(),
            kind,
            choices: None,
            default: Default::none(),
            required: true,
            help: help.to_string(),
        });
        self
    }

    /// An option `--name` with one value (or a flag, for `Kind::Flag`); its dest is the name without the
    /// leading dashes and with `-` replaced by `_`.
    pub fn option(mut self, flag: &str, kind: Kind, default: Default, help: &str) -> Self {
        let dest = flag.trim_start_matches('-').replace('-', "_");
        let default = if kind == Kind::Flag {
            Default::flag()
        } else {
            default
        };
        self.arguments.push(Argument {
            dest,
            flag: flag.to_string(),
            kind,
            choices: None,
            default,
            required: false,
            help: help.to_string(),
        });
        self
    }

    /// Restrict the last declared option to `choices`.
    pub fn choices(mut self, choices: &[&str]) -> Self {
        if let Some(last) = self.arguments.last_mut() {
            last.choices = Some(choices.iter().map(|choice| choice.to_string()).collect());
        }
        self
    }

    /// Make the last declared option required.
    pub fn required(mut self, required: bool) -> Self {
        if let Some(last) = self.arguments.last_mut() {
            last.required = required;
        }
        self
    }

    fn help_argument() -> Argument {
        Argument {
            dest: "help".to_string(),
            flag: "-h".to_string(),
            kind: Kind::Flag,
            choices: None,
            default: Default::flag(),
            required: false,
            help: "show this help message and exit".to_string(),
        }
    }

    /// Parse `arguments` (without the program name).
    pub fn parse(&self, arguments: &[String]) -> Outcome {
        match self.parse_inner(arguments) {
            Ok(Some(values)) => Outcome::Values(values),
            Ok(None) => Outcome::Help(self.help()),
            Err(message) => Outcome::Error(message),
        }
    }

    fn long_options(&self) -> Vec<&Argument> {
        self.arguments
            .iter()
            .filter(|argument| !argument.positional())
            .collect()
    }

    /// argparse's classification of one string: an option (with an explicit value after `=`), or a value.
    fn classify<'a>(&'a self, item: &str) -> Result<Classified<'a>, String> {
        // Returns None for a value; Some((argument or None for help, is_help, explicit value)).
        if item.is_empty() || !item.starts_with('-') {
            return Ok(None);
        }
        if item == "-h" || item == "--help" {
            return Ok(Some((None, true, None)));
        }
        if let Some(argument) = self
            .long_options()
            .into_iter()
            .find(|argument| argument.flag == item)
        {
            return Ok(Some((Some(argument), false, None)));
        }
        if item.len() == 1 {
            return Ok(None);
        }
        if let Some((prefix, value)) = item.split_once('=') {
            if prefix == "--help" || prefix == "-h" {
                return Ok(Some((None, true, Some(value.to_string()))));
            }
            if let Some(argument) = self
                .long_options()
                .into_iter()
                .find(|argument| argument.flag == prefix)
            {
                return Ok(Some((Some(argument), false, Some(value.to_string()))));
            }
        }
        if item.starts_with("--") {
            let (prefix, explicit) = match item.split_once('=') {
                Some((prefix, value)) => (prefix, Some(value.to_string())),
                None => (item, None),
            };
            let mut flags: Vec<&str> = vec!["--help"];
            flags.extend(
                self.long_options()
                    .iter()
                    .map(|argument| argument.flag.as_str()),
            );
            let matches: Vec<&str> = flags
                .into_iter()
                .filter(|flag| flag.starts_with(prefix))
                .collect();
            if matches.len() > 1 {
                return Err(format!(
                    "ambiguous option: {item} could match {}",
                    matches.join(", ")
                ));
            }
            if let Some(&flag) = matches.first() {
                if flag == "--help" {
                    return Ok(Some((None, true, explicit)));
                }
                let argument = self
                    .long_options()
                    .into_iter()
                    .find(|argument| argument.flag == flag);
                return Ok(Some((argument, false, explicit)));
            }
        }
        if is_negative_number(item) || item.contains(' ') {
            return Ok(None);
        }
        Err(format!("\u{0}unrecognized\u{0}{item}"))
    }

    fn parse_inner(&self, arguments: &[String]) -> Result<Option<Values>, String> {
        let mut values = Values::default();
        let mut seen: Vec<&str> = Vec::new();
        let mut extras: Vec<String> = Vec::new();
        let positional = self.arguments.iter().find(|argument| argument.positional());
        let mut positional_taken = false;
        let mut index = 0;
        let mut options_ended = false;
        while index < arguments.len() {
            let item = &arguments[index];
            index += 1;
            if !options_ended && item == "--" {
                options_ended = true;
                continue;
            }
            let classified = if options_ended {
                Ok(None)
            } else {
                self.classify(item)
            };
            let classified = match classified {
                Ok(classified) => classified,
                Err(message) if message.starts_with("\u{0}unrecognized\u{0}") => {
                    extras.push(item.clone());
                    continue;
                }
                Err(message) => return Err(message),
            };
            match classified {
                None => match positional {
                    Some(argument) if !positional_taken => {
                        values
                            .values
                            .insert(argument.dest.clone(), convert(argument, item)?);
                        seen.push(argument.dest.as_str());
                        positional_taken = true;
                    }
                    _ => extras.push(item.clone()),
                },
                Some((_, true, explicit)) => {
                    if let Some(value) = explicit {
                        return Err(format!(
                            "argument -h/--help: ignored explicit argument {}",
                            python_repr(&value)
                        ));
                    }
                    return Ok(None);
                }
                Some((Some(argument), false, explicit)) => {
                    if argument.kind == Kind::Flag {
                        if let Some(value) = explicit {
                            return Err(format!(
                                "argument {}: ignored explicit argument {}",
                                argument.flag,
                                python_repr(&value)
                            ));
                        }
                        values
                            .values
                            .insert(argument.dest.clone(), Parsed::Bool(true));
                    } else {
                        let value = match explicit {
                            Some(value) => value,
                            None => {
                                let next = arguments.get(index);
                                let usable = match next {
                                    Some(next) if next == "--" => false,
                                    Some(next) => {
                                        options_ended || matches!(self.classify(next), Ok(None))
                                    }
                                    None => false,
                                };
                                if !usable {
                                    return Err(format!(
                                        "argument {}: expected one argument",
                                        argument.flag
                                    ));
                                }
                                index += 1;
                                next.cloned().unwrap_or_default()
                            }
                        };
                        values
                            .values
                            .insert(argument.dest.clone(), convert(argument, &value)?);
                    }
                    seen.push(argument.dest.as_str());
                }
                Some((None, false, _)) => unreachable!("an option match always names an argument"),
            }
        }
        let missing: Vec<String> = self
            .arguments
            .iter()
            .filter(|argument| argument.required && !seen.contains(&argument.dest.as_str()))
            .map(Argument::name)
            .collect();
        if !missing.is_empty() {
            return Err(format!(
                "the following arguments are required: {}",
                missing.join(", ")
            ));
        }
        if !extras.is_empty() {
            return Err(format!("unrecognized arguments: {}", extras.join(" ")));
        }
        for argument in &self.arguments {
            if !values.values.contains_key(&argument.dest) {
                let value = match (&argument.default.value, argument.kind) {
                    // argparse converts a string default with the argument's type.
                    (Parsed::Text(text), Kind::Int | Kind::Float) => convert(argument, text)?,
                    (value, _) => value.clone(),
                };
                values.values.insert(argument.dest.clone(), value);
            }
        }
        Ok(Some(values))
    }

    /// The width argparse formats to: COLUMNS when set to an integer, otherwise 80, less two.
    fn width() -> usize {
        let columns = std::env::var("COLUMNS")
            .ok()
            .and_then(|text| text.trim().parse::<i64>().ok())
            .unwrap_or(80);
        (columns - 2).max(0) as usize
    }

    /// The help text, as argparse's `format_help`.
    pub fn help(&self) -> String {
        let width = Self::width();
        let mut all = vec![Self::help_argument()];
        all.extend(self.arguments.iter().cloned());
        let positionals: Vec<&Argument> = all
            .iter()
            .filter(|argument| argument.positional())
            .collect();
        let optionals: Vec<&Argument> = all
            .iter()
            .filter(|argument| !argument.positional())
            .collect();
        let mut output = String::new();
        output.push_str(&self.usage(width, &optionals, &positionals));
        output.push_str("\n\n");
        if !self.description.is_empty() {
            output.push_str(&fill(&collapse(&self.description), width.max(11)));
            output.push_str("\n\n");
        }
        let max_help_position = 24usize.min(width.saturating_sub(20).max(4));
        let action_max_length = all
            .iter()
            .map(|argument| argument.invocation().len() + 2)
            .max()
            .unwrap_or(0);
        let help_position = (action_max_length + 2).min(max_help_position);
        let help_width = width.saturating_sub(help_position).max(11);
        for (title, group) in [
            ("positional arguments", &positionals),
            ("options", &optionals),
        ] {
            if group.is_empty() {
                continue;
            }
            output.push_str(title);
            output.push_str(":\n");
            for argument in group.iter() {
                let invocation = argument.invocation();
                let action_width = help_position.saturating_sub(2 + 2);
                let help = expand_help(argument);
                let lines = if help.trim().is_empty() {
                    Vec::new()
                } else {
                    wrap(&collapse(&help), help_width)
                };
                if lines.is_empty() {
                    output.push_str(&format!("  {invocation}\n"));
                    continue;
                }
                if invocation.len() <= action_width {
                    output.push_str(&format!("  {invocation:<action_width$}  {}\n", lines[0]));
                } else {
                    output.push_str(&format!(
                        "  {invocation}\n{:help_position$}{}\n",
                        "", lines[0]
                    ));
                }
                for line in &lines[1..] {
                    output.push_str(&format!("{:help_position$}{line}\n", ""));
                }
            }
            output.push('\n');
        }
        if !self.epilog.is_empty() {
            output.push_str(&fill(&collapse(&self.epilog), width.max(11)));
            output.push_str("\n\n");
        }
        // argparse joins sections with blank lines, collapses longer breaks and ends with one newline.
        let mut collapsed = String::new();
        let mut newlines = 0;
        for character in output.chars() {
            if character == '\n' {
                newlines += 1;
                if newlines <= 2 {
                    collapsed.push(character);
                }
            } else {
                newlines = 0;
                collapsed.push(character);
            }
        }
        format!("{}\n", collapsed.trim_matches('\n'))
    }

    /// The usage block, as argparse's `_format_usage` for a non-terminal.
    fn usage(&self, width: usize, optionals: &[&Argument], positionals: &[&Argument]) -> String {
        let prefix = "usage: ";
        let opt_parts: Vec<String> = optionals
            .iter()
            .map(|argument| argument.usage_part())
            .collect();
        let pos_parts: Vec<String> = positionals
            .iter()
            .map(|argument| argument.usage_part())
            .collect();
        let mut all = vec![self.prog.clone()];
        all.extend(opt_parts.iter().cloned());
        all.extend(pos_parts.iter().cloned());
        let flat = all.join(" ");
        let text_width = width;
        if prefix.len() + flat.len() <= text_width {
            return format!("{prefix}{flat}");
        }
        let get_lines = |parts: &[String], indent: &str, with_prefix: bool| -> Vec<String> {
            let mut lines = Vec::new();
            let mut line: Vec<String> = Vec::new();
            let mut line_len = if with_prefix {
                prefix.len() - 1
            } else {
                indent.len() - 1
            };
            for part in parts {
                if line_len + 1 + part.len() > text_width && !line.is_empty() {
                    lines.push(format!("{indent}{}", line.join(" ")));
                    line.clear();
                    line_len = indent.len() - 1;
                }
                line.push(part.clone());
                line_len += part.len() + 1;
            }
            if !line.is_empty() {
                lines.push(format!("{indent}{}", line.join(" ")));
            }
            if with_prefix && let Some(first) = lines.first_mut() {
                *first = first[indent.len()..].to_string();
            }
            lines
        };
        let lines = if (prefix.len() + self.prog.len()) as f64 <= 0.75 * text_width as f64 {
            let indent = " ".repeat(prefix.len() + self.prog.len() + 1);
            if !opt_parts.is_empty() {
                let mut first = vec![self.prog.clone()];
                first.extend(opt_parts.iter().cloned());
                let mut lines = get_lines(&first, &indent, true);
                lines.extend(get_lines(&pos_parts, &indent, false));
                lines
            } else if !pos_parts.is_empty() {
                let mut first = vec![self.prog.clone()];
                first.extend(pos_parts.iter().cloned());
                get_lines(&first, &indent, true)
            } else {
                vec![self.prog.clone()]
            }
        } else {
            let indent = " ".repeat(prefix.len());
            let mut parts = opt_parts.clone();
            parts.extend(pos_parts.iter().cloned());
            let mut lines = get_lines(&parts, &indent, false);
            if lines.len() > 1 {
                lines = get_lines(&opt_parts, &indent, false);
                lines.extend(get_lines(&pos_parts, &indent, false));
            }
            let mut result = vec![self.prog.clone()];
            result.extend(lines);
            result
        };
        format!("{prefix}{}", lines.join("\n"))
    }
}

/// Convert one value with the argument's type, then check its choices, with argparse's messages.
fn convert(argument: &Argument, text: &str) -> Result<Parsed, String> {
    let value = match argument.kind {
        Kind::Text | Kind::Path => Parsed::Text(text.to_string()),
        Kind::Int => match python_int(text) {
            Some(value) => Parsed::Int(value),
            // Python's int has no bound: such a value parses, and the range checks after parsing refuse it.
            None if python_int_digits(text).is_some() => Parsed::Large,
            None => {
                return Err(format!(
                    "argument {}: invalid int value: {}",
                    argument.name(),
                    python_repr(text)
                ));
            }
        },
        Kind::Float => match python_float(text) {
            Some(value) => Parsed::Float(value),
            None => {
                return Err(format!(
                    "argument {}: invalid float value: {}",
                    argument.name(),
                    python_repr(text)
                ));
            }
        },
        Kind::Flag => Parsed::Bool(true),
    };
    if let (Some(choices), Parsed::Text(chosen)) = (&argument.choices, &value)
        && !choices.contains(chosen)
    {
        // argparse 3.14: the value in repr, the choices as str, joined with ", ".
        return Err(format!(
            "argument {}: invalid choice: {} (choose from {})",
            argument.name(),
            python_repr(chosen),
            choices.join(", ")
        ));
    }
    Ok(value)
}

/// `%(default)s` and `%%` in a help text.
fn expand_help(argument: &Argument) -> String {
    argument
        .help
        .replace("%(default)s", &argument.default.display)
        .replace("%%", "%")
}

/// argparse's negative-number test: `-` then digits, or `-` digits `.` digits.
fn is_negative_number(text: &str) -> bool {
    let Some(rest) = text.strip_prefix('-') else {
        return false;
    };
    let (whole, fraction) = match rest.split_once('.') {
        Some((whole, fraction)) => (whole, Some(fraction)),
        None => (rest, None),
    };
    match fraction {
        None => !whole.is_empty() && whole.bytes().all(|byte| byte.is_ascii_digit()),
        Some(fraction) => {
            whole.bytes().all(|byte| byte.is_ascii_digit())
                && !fraction.is_empty()
                && fraction.bytes().all(|byte| byte.is_ascii_digit())
        }
    }
}

/// The sign and digits of Python's `int(text)` for decimal text: surrounding whitespace, an optional sign,
/// digits with single underscores between them. None where Python refuses the text.
fn python_int_digits(text: &str) -> Option<(bool, String)> {
    let trimmed = text.trim();
    let (negative, digits) = match trimmed.as_bytes().first() {
        Some(b'+') => (false, &trimmed[1..]),
        Some(b'-') => (true, &trimmed[1..]),
        _ => (false, trimmed),
    };
    if digits.is_empty()
        || digits.starts_with('_')
        || digits.ends_with('_')
        || digits.contains("__")
    {
        return None;
    }
    if !digits
        .bytes()
        .all(|byte| byte.is_ascii_digit() || byte == b'_')
    {
        return None;
    }
    Some((negative, digits.replace('_', "")))
}

/// Python's `int(text)` for decimal text, when the value fits in 64 bits.
pub fn python_int(text: &str) -> Option<i64> {
    let (negative, digits) = python_int_digits(text)?;
    let magnitude: i128 = digits.parse().ok()?;
    i64::try_from(if negative { -magnitude } else { magnitude }).ok()
}

/// Python's `float(text)`: surrounding whitespace, decimal or exponent forms with single underscores between
/// digits, and `inf`, `infinity` and `nan` in any case with an optional sign.
pub fn python_float(text: &str) -> Option<f64> {
    let trimmed = text.trim();
    let unsigned = trimmed.trim_start_matches(['+', '-']);
    if trimmed.len() - unsigned.len() > 1 {
        return None;
    }
    let lower = unsigned.to_ascii_lowercase();
    if lower == "inf" || lower == "infinity" || lower == "nan" {
        return trimmed.to_ascii_lowercase().parse::<f64>().ok();
    }
    if unsigned.is_empty()
        || !unsigned
            .bytes()
            .all(|byte| byte.is_ascii_digit() || b"._eE+-".contains(&byte))
    {
        return None;
    }
    let bytes = unsigned.as_bytes();
    for (index, byte) in bytes.iter().enumerate() {
        if *byte == b'_' {
            let before = index > 0 && bytes[index - 1].is_ascii_digit();
            let after = index + 1 < bytes.len() && bytes[index + 1].is_ascii_digit();
            if !before || !after {
                return None;
            }
        }
    }
    trimmed.replace('_', "").parse::<f64>().ok()
}

/// Python's repr of a str, for the messages that quote a value.
pub fn python_repr(text: &str) -> String {
    let quote = if text.contains('\'') && !text.contains('"') {
        '"'
    } else {
        '\''
    };
    let mut result = String::new();
    result.push(quote);
    for character in text.chars() {
        match character {
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            c if c == quote => {
                result.push('\\');
                result.push(c);
            }
            c if (c as u32) < 0x20 || c as u32 == 0x7f => {
                result.push_str(&format!("\\x{:02x}", c as u32))
            }
            c => result.push(c),
        }
    }
    result.push(quote);
    result
}

/// argparse collapses every run of whitespace to one space and strips the ends.
fn collapse(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn fill(text: &str, width: usize) -> String {
    wrap(text, width).join("\n")
}

fn is_letter(character: char) -> bool {
    (character.is_alphanumeric() || character == '_') && !character.is_numeric()
}

fn is_word(character: char) -> bool {
    character.is_alphanumeric() || character == '_'
}

fn is_word_or_punctuation(character: char) -> bool {
    is_word(character) || "!\"'&.,?".contains(character)
}

/// textwrap's chunks: whitespace runs, and words split after the hyphens of hyphenated words and before
/// em-dashes, as TextWrapper.wordsep_re splits them.
fn chunks(text: &str) -> Vec<String> {
    let characters: Vec<char> = text.chars().collect();
    let length = characters.len();
    let mut result = Vec::new();
    let mut start = 0;
    let dashes_then_word = |at: usize| -> bool {
        let mut end = at;
        while end < length && characters[end] == '-' {
            end += 1;
        }
        end - at >= 2 && end < length && is_word(characters[end])
    };
    while start < length {
        if characters[start].is_whitespace() {
            let mut end = start;
            while end < length && characters[end].is_whitespace() {
                end += 1;
            }
            result.push(characters[start..end].iter().collect());
            start = end;
            continue;
        }
        if start > 0 && is_word_or_punctuation(characters[start - 1]) && dashes_then_word(start) {
            let mut end = start;
            while end < length && characters[end] == '-' {
                end += 1;
            }
            result.push(characters[start..end].iter().collect());
            start = end;
            continue;
        }
        let mut end = start + 1;
        loop {
            if end >= length || characters[end].is_whitespace() {
                break;
            }
            if characters[end] == '-' {
                let after = end + 1;
                let two_letters =
                    end >= 2 && is_letter(characters[end - 1]) && is_letter(characters[end - 2]);
                let letter_hyphen_letter = end >= 3
                    && is_letter(characters[end - 1])
                    && characters[end - 2] == '-'
                    && is_letter(characters[end - 3]);
                let ahead = after < length
                    && is_letter(characters[after])
                    && ((after + 1 < length && is_letter(characters[after + 1]))
                        || (after + 2 < length
                            && characters[after + 1] == '-'
                            && is_letter(characters[after + 2])));
                if (two_letters || letter_hyphen_letter) && ahead {
                    end += 1;
                    break;
                }
            }
            if is_word_or_punctuation(characters[end - 1]) && dashes_then_word(end) {
                break;
            }
            end += 1;
        }
        result.push(characters[start..end].iter().collect());
        start = end;
    }
    result
}

/// Where textwrap breaks a word longer than the line: after the last hyphen that fits, when something other
/// than hyphens precedes it, otherwise at the space left.
fn long_word_end(characters: &[char], space_left: usize) -> usize {
    if characters.len() > space_left
        && let Some(hyphen) = characters[..space_left]
            .iter()
            .rposition(|&character| character == '-')
        && hyphen > 0
        && characters[..hyphen]
            .iter()
            .any(|&character| character != '-')
    {
        hyphen + 1
    } else {
        space_left
    }
}

/// textwrap.wrap(text, width) with its defaults: long words broken, preferring a hyphen; whitespace dropped
/// at line ends and at the start of every line but the first.
pub fn wrap(text: &str, width: usize) -> Vec<String> {
    let mut pending: Vec<String> = chunks(text);
    pending.reverse();
    let mut lines: Vec<String> = Vec::new();
    while !pending.is_empty() {
        let mut line: Vec<String> = Vec::new();
        let mut line_length = 0usize;
        if !lines.is_empty() && pending.last().is_some_and(|chunk| chunk.trim().is_empty()) {
            pending.pop();
        }
        while let Some(chunk) = pending.last() {
            let size = chunk.chars().count();
            if line_length + size <= width {
                line_length += size;
                line.push(pending.pop().unwrap_or_default());
            } else {
                break;
            }
        }
        if let Some(chunk) = pending.last().cloned()
            && chunk.chars().count() > width
        {
            let space_left = if width < 1 { 1 } else { width - line_length };
            let characters: Vec<char> = chunk.chars().collect();
            let end = long_word_end(&characters, space_left);
            line.push(characters[..end].iter().collect());
            let rest: String = characters[end..].iter().collect();
            if let Some(last) = pending.last_mut() {
                *last = rest;
            }
        }
        if line.last().is_some_and(|chunk| chunk.trim().is_empty()) {
            line.pop();
        }
        if !line.is_empty() {
            lines.push(line.concat());
        }
    }
    lines
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(items: &[&str]) -> Vec<String> {
        items.iter().map(|item| item.to_string()).collect()
    }

    fn parser() -> Parser {
        Parser::new("fang")
            .positional("input", Kind::Path, "TPTP problem file to read and capture")
            .option("--check", Kind::Text, Default::none(), "verification mode")
            .choices(&["compiled", "kernel", "none"])
            .option(
                "--wall-seconds",
                Kind::Float,
                Default::int_for_float(60),
                "deadline (default: %(default)s)",
            )
            .option(
                "--memory-mib",
                Kind::Int,
                Default::int(2048),
                "memory (default: %(default)s)",
            )
            .option(
                "--self-check",
                Kind::Flag,
                Default::flag(),
                "hash everything",
            )
    }

    fn error(items: &[&str]) -> String {
        match parser().parse(&strings(items)) {
            Outcome::Error(message) => message,
            other => panic!("expected an error, got {other:?}"),
        }
    }

    fn values(items: &[&str]) -> Values {
        match parser().parse(&strings(items)) {
            Outcome::Values(values) => values,
            other => panic!("expected values, got {other:?}"),
        }
    }

    #[test]
    fn argparse_messages() {
        assert_eq!(error(&[]), "the following arguments are required: input");
        assert_eq!(
            error(&["p.p", "--check", "x"]),
            "argument --check: invalid choice: 'x' (choose from compiled, kernel, none)"
        );
        assert_eq!(
            error(&["p.p", "--wall-seconds", "abc"]),
            "argument --wall-seconds: invalid float value: 'abc'"
        );
        assert_eq!(
            error(&["p.p", "--memory-mib", "1.5"]),
            "argument --memory-mib: invalid int value: '1.5'"
        );
        assert_eq!(
            error(&["p.p", "--check"]),
            "argument --check: expected one argument"
        );
        assert_eq!(error(&["p.p", "q.p"]), "unrecognized arguments: q.p");
        assert_eq!(
            error(&["p.p", "--bogus"]),
            "unrecognized arguments: --bogus"
        );
        assert_eq!(
            error(&["p.p", "--self-check=1"]),
            "argument --self-check: ignored explicit argument '1'"
        );
    }

    #[test]
    fn argparse_values() {
        let parsed = values(&[
            "p.p",
            "--wall",
            "5",
            "--check=kernel",
            "--memory-mib",
            "1_024",
        ]);
        assert_eq!(parsed.text("input"), Some("p.p"));
        assert_eq!(parsed.float("wall_seconds"), Some(5.0));
        assert_eq!(parsed.text("check"), Some("kernel"));
        assert_eq!(parsed.int("memory_mib"), Some(1024));
        assert!(!parsed.flag("self_check"));
        assert_eq!(values(&["p.p"]).float("wall_seconds"), Some(60.0));
        assert_eq!(
            values(&["--wall-seconds", "-5", "p.p"]).float("wall_seconds"),
            Some(-5.0)
        );
        assert_eq!(values(&["--", "-p.p"]).text("input"), Some("-p.p"));
    }

    #[test]
    fn help_requests() {
        assert!(matches!(
            parser().parse(&strings(&["--help"])),
            Outcome::Help(_)
        ));
        assert!(matches!(
            parser().parse(&strings(&["-h", "--check", "x"])),
            Outcome::Help(_)
        ));
        assert!(matches!(
            parser().parse(&strings(&["--he"])),
            Outcome::Help(_)
        ));
    }

    #[test]
    fn wrapping_follows_textwrap() {
        assert_eq!(wrap("aa bb cc", 5), ["aa bb", "cc"]);
        assert_eq!(
            chunks("compiler-and runtime"),
            ["compiler-", "and", " ", "runtime"]
        );
        assert_eq!(chunks("--max-input-bytes"), ["--max-", "input-", "bytes"]);
        assert_eq!(wrap("abcdefghij", 4), ["abcd", "efgh", "ij"]);
    }

    #[test]
    fn python_numbers() {
        assert_eq!(python_int(" 12 "), Some(12));
        assert_eq!(python_int("1__2"), None);
        assert_eq!(python_int("-9223372036854775808"), Some(i64::MIN));
        assert_eq!(python_int("9223372036854775808"), None);
        assert!(python_int_digits("9223372036854775808").is_some());
        assert!(python_int_digits("1e3").is_none());
        assert_eq!(python_float("1e3"), Some(1000.0));
        assert!(python_float("nan").unwrap().is_nan());
        assert_eq!(python_float("abc"), None);
    }
}
