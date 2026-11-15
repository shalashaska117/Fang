// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Search counters and a small JSON writer for the `--stats` file. Nothing here reaches standard output or
//! standard error.

use std::fmt::Write;

#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub input_clauses: u64,
    pub inputs_dropped: u64,
    pub inputs_unselected: u64,
    pub given: u64,
    pub attempts: u64,
    pub generated: u64,
    pub passive_added: u64,
    pub passive_peak: u64,
    pub active_final: u64,
    pub duplicates: u64,
    pub tautologies: u64,
    pub cleanup_steps: u64,
    pub forward_subsumed: u64,
    pub unit_join_attempts: u64,
    pub unit_join_redundant: u64,
    pub unit_join_refused: u64,
    pub subsumption_resolutions: u64,
    pub pruned: u64,
    pub orphaned: u64,
    pub passive_limit_dropped: u64,
    pub backward_subsumed: u64,
    pub forward_rewrites: u64,
    pub backward_rewrites: u64,
    pub dropped_depth: u64,
    pub dropped_literals: u64,
    pub dropped_weight: u64,
    pub resolutions: u64,
    pub superpositions: u64,
    pub equality_resolutions: u64,
    pub factorings: u64,
    pub equality_factorings: u64,
    pub clauses_stored: u64,
    pub terms_stored: u64,
    pub search_ms: u64,
    pub extract_ms: u64,
    pub proof_nodes: u64,
    pub proof_rules: Vec<(String, u64)>,
    pub unchecked_nodes: u64,
}

/// A JSON object written field by field.
pub struct Json {
    text: String,
    first: bool,
}

pub fn quote(value: &str) -> String {
    let mut output = String::from("\"");
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            c if (c as u32) < 0x20 || (c as u32) > 0x7e => {
                let _ = write!(output, "\\u{:04x}", c as u32);
            }
            c => output.push(c),
        }
    }
    output.push('"');
    output
}

impl Json {
    pub fn new() -> Self {
        Self {
            text: String::from("{"),
            first: true,
        }
    }

    fn key(&mut self, key: &str) {
        if !self.first {
            self.text.push(',');
        }
        self.first = false;
        self.text.push_str(&quote(key));
        self.text.push(':');
    }

    pub fn string(&mut self, key: &str, value: &str) -> &mut Self {
        self.key(key);
        self.text.push_str(&quote(value));
        self
    }

    pub fn number(&mut self, key: &str, value: u64) -> &mut Self {
        self.key(key);
        let _ = write!(self.text, "{value}");
        self
    }

    pub fn float(&mut self, key: &str, value: f64) -> &mut Self {
        self.key(key);
        let _ = write!(self.text, "{value:.3}");
        self
    }

    pub fn raw(&mut self, key: &str, value: &str) -> &mut Self {
        self.key(key);
        self.text.push_str(value);
        self
    }

    pub fn finish(&mut self) -> String {
        self.text.push('}');
        std::mem::take(&mut self.text)
    }
}

impl Default for Json {
    fn default() -> Self {
        Self::new()
    }
}

impl Stats {
    pub fn json(&self) -> String {
        let mut json = Json::new();
        let fields: [(&str, u64); 38] = [
            ("input_clauses", self.input_clauses),
            ("inputs_dropped", self.inputs_dropped),
            ("inputs_unselected", self.inputs_unselected),
            ("given", self.given),
            ("attempts", self.attempts),
            ("generated", self.generated),
            ("passive_added", self.passive_added),
            ("passive_peak", self.passive_peak),
            ("active_final", self.active_final),
            ("duplicates", self.duplicates),
            ("tautologies", self.tautologies),
            ("cleanup_steps", self.cleanup_steps),
            ("forward_subsumed", self.forward_subsumed),
            ("unit_join_attempts", self.unit_join_attempts),
            ("unit_join_redundant", self.unit_join_redundant),
            ("unit_join_refused", self.unit_join_refused),
            ("subsumption_resolutions", self.subsumption_resolutions),
            ("pruned", self.pruned),
            ("orphaned", self.orphaned),
            ("passive_limit_dropped", self.passive_limit_dropped),
            ("backward_subsumed", self.backward_subsumed),
            ("forward_rewrites", self.forward_rewrites),
            ("backward_rewrites", self.backward_rewrites),
            ("dropped_depth", self.dropped_depth),
            ("dropped_literals", self.dropped_literals),
            ("dropped_weight", self.dropped_weight),
            ("resolutions", self.resolutions),
            ("superpositions", self.superpositions),
            ("equality_resolutions", self.equality_resolutions),
            ("factorings", self.factorings),
            ("equality_factorings", self.equality_factorings),
            ("clauses_stored", self.clauses_stored),
            ("terms_stored", self.terms_stored),
            ("search_ms", self.search_ms),
            ("extract_ms", self.extract_ms),
            ("proof_nodes", self.proof_nodes),
            ("unchecked_nodes", self.unchecked_nodes),
            ("rules_in_proof", self.proof_rules.len() as u64),
        ];
        for (key, value) in fields {
            json.number(key, value);
        }
        let mut rules = Json::new();
        for (name, count) in &self.proof_rules {
            rules.number(name, *count);
        }
        json.raw("proof_by_rule", &rules.finish());
        json.finish()
    }
}
