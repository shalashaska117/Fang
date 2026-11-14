// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Search options, set from `--set key=value`. A preset names the configuration of one measured step of the search's development;
//! keys given after it override it.

use crate::kbo::{OrderKind, Precedence};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Selection {
    None,
    /// The heaviest negative literal, the first one on ties.
    HeaviestNegative,
    /// The lightest negative literal, the first one on ties.
    LightestNegative,
    /// The negative literal with the fewest inference partners among the active clauses (lookahead selection).
    Lookahead,
    /// Prefer ground negative literals, then weight, then the first occurrence.
    GroundNegative,
    /// Prefer negative equalities, then weight, then the first occurrence.
    NegativeEquality,
}

#[derive(Clone, Debug)]
pub struct Options {
    pub preset: String,
    /// Term-ordering restrictions; off means the second release's unrestricted rules.
    pub ordering: bool,
    pub term_order: OrderKind,
    pub kbo_weights: crate::weights::Scheme,
    pub precedence: Precedence,
    pub selection: Selection,
    /// Resolution and factoring on equations and negative factoring, as the second release does.
    pub unrestricted_rules: bool,
    /// Paramodulation from a variable side of an equation, as the second release does.
    pub from_variables: bool,
    pub age_ratio: u32,
    pub weight_ratio: u32,
    /// Skip a new clause identical to a stored one.
    pub duplicates: bool,
    pub tautologies: bool,
    /// Duplicate literals and t != t literals removed by checked renaming steps.
    pub cleanup: bool,
    pub forward_subsumption: bool,
    /// Forward subsumption resolution and unit deletion, stated as `resolve` and `factor` steps.
    pub subsumption_resolution: bool,
    pub backward_subsumption: bool,
    pub forward_demodulation: bool,
    pub backward_demodulation: bool,
    /// Rewrite new clauses before they enter passive, not only when selected.
    pub demodulate_new: bool,
    pub equality_factoring: bool,
    pub max_weight: Option<u32>,
    pub max_depth: u32,
    pub max_literals: usize,
    pub given_limit: Option<u64>,
    pub max_certificate_bytes: usize,
    /// Stop rewriting one clause after this many steps.
    pub max_rewrites: u32,
    /// Matching steps allowed for one subsumption test.
    pub subsumption_budget: u32,
    /// Skip clause pairs whose symbols cannot unify; this changes no inference, only the work.
    pub filter: bool,
    /// Drop the heavier half of passive when memory passes 70% of the bound.
    pub prune_passive: bool,
    /// Drop passive inferences whose generating parent was deleted. This is an incomplete heuristic.
    pub orphan_deletion: bool,
    /// Maximum queued passive clauses. Dropping a nonempty clause loses completeness.
    pub max_passive: Option<u64>,
    /// Candidate indexes over the active set; the same inferences as the linear scan, in the same order.
    pub index: bool,
    /// Sequential time slices, each a share of the remaining search time and its own options; empty for one search.
    pub portfolio: Vec<(u32, Options)>,
    /// SInE premise selection with this tolerance, when the producer knows the goal; None keeps every input.
    pub sine: Option<f64>,
    /// Rounds of SInE selection from the goal; None runs to the fixpoint.
    pub sine_depth: Option<u32>,
    /// Percent applied to the selection weight of a clause with no goal ancestor (100 leaves it unchanged).
    pub nongoal_weight: u32,
    /// Symbols of the goal count half in the selection weight.
    pub goal_symbols: bool,
    /// Added to the selection weight per literal.
    pub literal_weight: u32,
    /// Added to the selection weight per level of the deepest term.
    pub depth_weight: u32,
    /// Record the first given clauses for `--trace` (debugging only).
    pub trace_given: u32,
    /// Destructive equality resolution among the cleanup steps.
    pub der: bool,
    /// Simplify each new clause by the active set (cleanup, demodulation, subsumption resolution, forward
    /// subsumption) before it enters passive.
    pub simplify_new: bool,
    /// Layered clause selection over the SInE level, cutoffs 0, 1 and unbounded, picked 1:2:3 by default.
    pub sine_layer: bool,
    /// Layered clause selection over the number of positive literals, cutoffs 1 (Horn) and unbounded, picked 1:1 by
    /// default. It excludes `sine_layer`.
    pub horn_layer: bool,
    /// Picks per layer of a layered selection, from the narrowest layer out; empty for the default ratio.
    pub layer_ratio: Vec<u32>,
    /// Select every clause admitted before the first given clause ahead of any derived clause.
    pub inputs_first: bool,
    /// The goal set also takes every input clause that mentions a constant of a goal clause.
    pub goal_constants: bool,
}

impl Options {
    pub fn preset(name: &str) -> Result<Self, String> {
        let mut options = Options {
            preset: name.to_owned(),
            ordering: false,
            term_order: OrderKind::Kbo,
            kbo_weights: crate::weights::Scheme::Uniform,
            precedence: Precedence::Arity,
            selection: Selection::None,
            unrestricted_rules: true,
            from_variables: true,
            age_ratio: 1,
            weight_ratio: 4,
            duplicates: true,
            tautologies: false,
            cleanup: false,
            forward_subsumption: false,
            subsumption_resolution: false,
            backward_subsumption: false,
            forward_demodulation: false,
            backward_demodulation: false,
            demodulate_new: false,
            equality_factoring: false,
            max_weight: None,
            max_depth: 64,
            max_literals: 256,
            given_limit: None,
            max_certificate_bytes: crate::proof::MAX_CERTIFICATE_BYTES,
            max_rewrites: 10_000,
            subsumption_budget: 100_000,
            filter: false,
            prune_passive: false,
            orphan_deletion: false,
            max_passive: None,
            index: false,
            portfolio: Vec::new(),
            sine: None,
            sine_depth: None,
            nongoal_weight: 100,
            goal_symbols: false,
            literal_weight: 1,
            depth_weight: 0,
            trace_given: 0,
            der: false,
            simplify_new: false,
            sine_layer: false,
            horn_layer: false,
            layer_ratio: Vec::new(),
            inputs_first: false,
            goal_constants: false,
        };
        let step = match name {
            "step1" => 1,
            "step2" => 2,
            "step3" => 3,
            "step4" => 4,
            "step5" => 5,
            _ => return Err(format!("unknown preset {name}")),
        };
        if step >= 2 {
            options.ordering = true;
            options.selection = Selection::HeaviestNegative;
            options.unrestricted_rules = false;
            options.from_variables = false;
        }
        if step >= 3 {
            options.tautologies = true;
            options.cleanup = true;
            options.forward_subsumption = true;
        }
        if step >= 5 {
            // The step 2 gate showed that turning this off loses domain-size problems (STEPS.md).
            options.from_variables = true;
            options.subsumption_resolution = true;
        }
        if step >= 4 {
            options.forward_demodulation = true;
            options.backward_demodulation = true;
            options.backward_subsumption = true;
        }
        Ok(options)
    }

    /// The preset given by `preset=NAME` (default step1), then every other key in order.
    pub fn from_settings(settings: &[(String, String)]) -> Result<Self, String> {
        let name = settings
            .iter()
            .filter(|(key, _)| key == "preset")
            .map(|(_, value)| value.as_str())
            .next_back()
            .unwrap_or("step1");
        let mut options = Self::preset(name)?;
        for (key, value) in settings {
            if key != "preset" {
                options.set(key, value)?;
            }
        }
        if options.sine_layer && options.horn_layer {
            return Err("sine_layer and horn_layer exclude each other".into());
        }
        if !options.layer_ratio.is_empty()
            && options.layer_ratio.len() != options.layer_cutoffs().len()
        {
            return Err(format!(
                "layer_ratio needs {} parts for the layering chosen",
                options.layer_cutoffs().len()
            ));
        }
        Ok(options)
    }

    /// The cutoffs of the layered selection, narrowest first (empty without layering).
    pub fn layer_cutoffs(&self) -> Vec<u32> {
        if self.sine_layer {
            vec![0, 1, u32::MAX]
        } else if self.horn_layer {
            vec![1, u32::MAX]
        } else {
            Vec::new()
        }
    }

    /// The picks per layer: `layer_ratio` when given, else 1:2:3 over the SInE level and 1:1 over Horn.
    pub fn layer_picks(&self) -> Vec<u32> {
        if !self.layer_ratio.is_empty() {
            self.layer_ratio.clone()
        } else if self.sine_layer {
            vec![1, 2, 3]
        } else if self.horn_layer {
            vec![1, 1]
        } else {
            Vec::new()
        }
    }

    fn set(&mut self, key: &str, value: &str) -> Result<(), String> {
        let flag = || match value {
            "on" | "true" | "1" => Ok(true),
            "off" | "false" | "0" => Ok(false),
            _ => Err(format!("{key} needs on or off")),
        };
        let number = || {
            value
                .parse::<u64>()
                .map_err(|_| format!("{key} needs a number"))
        };
        match key {
            "ordering" => match value {
                "kbo" | "lpo" => {
                    self.ordering = true;
                    self.term_order = if value == "kbo" {
                        OrderKind::Kbo
                    } else {
                        OrderKind::Lpo
                    };
                }
                _ => self.ordering = flag()?,
            },
            "kbo_weights" => {
                self.kbo_weights = match value {
                    "uniform" => crate::weights::Scheme::Uniform,
                    "constant-heavy" => crate::weights::Scheme::ConstantHeavy,
                    "invfreq" => crate::weights::Scheme::InverseFrequency,
                    _ => return Err("kbo_weights is uniform, constant-heavy or invfreq".into()),
                };
            }
            "precedence" => {
                self.precedence = match value {
                    "arity" => Precedence::Arity,
                    "invfreq" => Precedence::InverseFrequency,
                    _ => return Err("precedence is arity or invfreq".into()),
                }
            }
            "selection" => {
                self.selection = match value {
                    "none" => Selection::None,
                    "heaviest-negative" => Selection::HeaviestNegative,
                    "lightest-negative" => Selection::LightestNegative,
                    "lookahead" => Selection::Lookahead,
                    "ground-negative" => Selection::GroundNegative,
                    "negative-equality" => Selection::NegativeEquality,
                    _ => {
                        return Err(
                            "selection is none, heaviest-negative, lightest-negative, lookahead, ground-negative or negative-equality"
                                .into(),
                        );
                    }
                }
            }
            "unrestricted_rules" => self.unrestricted_rules = flag()?,
            "from_variables" => self.from_variables = flag()?,
            "age_weight" => {
                let (age, weight) = value.split_once(':').ok_or("age_weight is A:W")?;
                self.age_ratio = age.parse().map_err(|_| "age_weight is A:W")?;
                self.weight_ratio = weight.parse().map_err(|_| "age_weight is A:W")?;
                if self.age_ratio + self.weight_ratio == 0 {
                    return Err("age_weight needs a nonzero part".into());
                }
            }
            "duplicates" => self.duplicates = flag()?,
            "tautologies" => self.tautologies = flag()?,
            "cleanup" => self.cleanup = flag()?,
            "forward_subsumption" => self.forward_subsumption = flag()?,
            "subsumption_resolution" => self.subsumption_resolution = flag()?,
            "backward_subsumption" => self.backward_subsumption = flag()?,
            "forward_demodulation" => self.forward_demodulation = flag()?,
            "backward_demodulation" => self.backward_demodulation = flag()?,
            "demodulate_new" => self.demodulate_new = flag()?,
            "equality_factoring" => self.equality_factoring = flag()?,
            "max_weight" => self.max_weight = Some(number()? as u32),
            "max_depth" => self.max_depth = (number()? as u32).min(64),
            "max_literals" => self.max_literals = (number()? as usize).min(256),
            "given_limit" => self.given_limit = Some(number()?),
            "max_certificate_bytes" => self.max_certificate_bytes = number()? as usize,
            "max_rewrites" => self.max_rewrites = number()? as u32,
            "subsumption_budget" => self.subsumption_budget = number()? as u32,
            "filter" => self.filter = flag()?,
            "prune_passive" => self.prune_passive = flag()?,
            "orphan_deletion" => self.orphan_deletion = flag()?,
            "max_passive" => self.max_passive = Some(value.parse().map_err(|_| "bad max_passive")?),
            "index" => self.index = flag()?,
            "sine" => {
                self.sine = match value {
                    "off" => None,
                    _ => Some(
                        value
                            .parse::<f64>()
                            .ok()
                            .filter(|t| *t >= 1.0)
                            .ok_or("sine is off or a tolerance of at least 1")?,
                    ),
                }
            }
            "sine_depth" => self.sine_depth = Some(number()? as u32),
            "nongoal_weight" => self.nongoal_weight = (number()? as u32).max(1),
            "goal_symbols" => self.goal_symbols = flag()?,
            "literal_weight" => self.literal_weight = number()? as u32,
            "depth_weight" => self.depth_weight = number()? as u32,
            "trace_given" => self.trace_given = number()? as u32,
            "der" => self.der = flag()?,
            "simplify_new" => self.simplify_new = flag()?,
            "sine_layer" => self.sine_layer = flag()?,
            "horn_layer" => self.horn_layer = flag()?,
            "layer_ratio" => {
                let parts: Result<Vec<u32>, _> = value.split(':').map(str::parse).collect();
                self.layer_ratio = parts.map_err(|_| "layer_ratio is A:B[:C]")?;
                if self.layer_ratio.iter().all(|&part| part == 0) {
                    return Err("layer_ratio needs a nonzero part".into());
                }
            }
            "inputs_first" => self.inputs_first = flag()?,
            "goal_constants" => self.goal_constants = flag()?,
            // SHARE/PRESET[,KEY:VALUE]... separated by ';', for example 30/step3,filter:on;70/step5.
            "portfolio" => {
                let mut slices = Vec::new();
                for slice in value.split(';') {
                    let (share, rest) = slice
                        .split_once('/')
                        .ok_or("portfolio slice is SHARE/PRESET[,KEY:VALUE]...")?;
                    let share: u32 = share
                        .parse()
                        .map_err(|_| "portfolio share is a whole number")?;
                    let mut parts = rest.split(',');
                    let mut settings = vec![(
                        "preset".to_string(),
                        parts.next().unwrap_or_default().to_string(),
                    )];
                    for part in parts {
                        let (key, setting) = part
                            .split_once(':')
                            .ok_or("portfolio option is KEY:VALUE")?;
                        if key == "portfolio" {
                            return Err("portfolio slices cannot nest".into());
                        }
                        settings.push((key.to_string(), setting.to_string()));
                    }
                    if share == 0 {
                        return Err("portfolio share must be positive".into());
                    }
                    slices.push((share, Options::from_settings(&settings)?));
                }
                self.portfolio = slices;
            }
            _ => return Err(format!("unknown option {key}")),
        }
        Ok(())
    }

    pub fn describe(&self) -> String {
        format!("{self:?}")
    }
}
