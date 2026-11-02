// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Role policy is independent of Vampire's implementation; docs/DESIGN.md lists the role rules.
use crate::{Declaration, Encoded, EncodedBody, error};
use fang::{Error, ErrorKind};
use fang_quantified_fof_core as core;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    Axiom,
    Hypothesis,
    Definition,
    Assumption,
    Lemma,
    Theorem,
    Corollary,
    Conjecture,
    NegatedConjecture,
    Plain,
    Type,
    Interpretation,
    Logic,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InputClass {
    Premise,
    Goal,
    AlreadyNegated,
}

impl Role {
    pub fn read(word: &str, offset: usize) -> Result<Self, Error> {
        Ok(match word {
            "axiom" => Self::Axiom,
            "hypothesis" => Self::Hypothesis,
            "definition" => Self::Definition,
            "assumption" => Self::Assumption,
            "lemma" => Self::Lemma,
            "theorem" => Self::Theorem,
            "corollary" => Self::Corollary,
            "conjecture" => Self::Conjecture,
            "negated_conjecture" => Self::NegatedConjecture,
            "plain" => Self::Plain,
            "type" => Self::Type,
            "interpretation" => Self::Interpretation,
            "logic" => Self::Logic,
            "unknown" => Self::Unknown,
            _ => return Err(error(ErrorKind::InvalidInput, offset, "unknown input role")),
        })
    }

    /// No role without an implemented input meaning is silently used as an axiom.
    pub fn input_class(self, offset: usize) -> Result<InputClass, Error> {
        match self {
            Self::Axiom
            | Self::Hypothesis
            | Self::Definition
            | Self::Lemma
            | Self::Theorem
            | Self::Corollary => Ok(InputClass::Premise),
            Self::Conjecture => Ok(InputClass::Goal),
            Self::NegatedConjecture => Ok(InputClass::AlreadyNegated),
            Self::Unknown => Err(error(ErrorKind::InvalidInput, offset, "unknown input role")),
            Self::Assumption => Err(error(
                ErrorKind::Unsupported,
                offset,
                "assumption discharge is not implemented",
            )),
            Self::Plain | Self::Type | Self::Interpretation | Self::Logic => Err(error(
                ErrorKind::Unsupported,
                offset,
                "this role has no implemented problem-input semantics",
            )),
        }
    }
}

pub(crate) fn check_combination(roles: impl Iterator<Item = (Role, usize)>) -> Result<(), Error> {
    let mut goal = false;
    let mut negated = false;
    for (role, offset) in roles {
        match role.input_class(offset)? {
            InputClass::Goal => goal = true,
            InputClass::AlreadyNegated => negated = true,
            InputClass::Premise => {}
        }
        if goal && negated {
            return Err(error(
                ErrorKind::Unsupported,
                offset,
                "original and already-negated conjectures need an explicit provenance link",
            ));
        }
    }
    Ok(())
}

/// A borrowed original declaration and its selected polarity. No AST is copied.
#[derive(Debug)]
pub struct SignedDeclaration<'a> {
    pub source_index: usize,
    pub original: &'a Declaration<EncodedBody>,
    pub positive: bool,
}

impl SignedDeclaration<'_> {
    /// This calls the existing closed rectifier/polarity normalizer. Each call
    /// has its own core budget. CNF inputs have their separate clause path.
    pub fn normalize_fof(
        &self,
        signature: &core::Signature,
        limits: &core::Limits,
    ) -> Option<Result<core::Normalized, core::Error>> {
        match &self.original.body {
            EncodedBody::Fof(body) => Some(core::rectify_normalize_closed(
                body,
                self.positive,
                signature,
                limits,
            )),
            EncodedBody::Cnf(_) => None,
        }
    }
}

/// One satisfiability obligation, or one original conjecture with all premises.
/// Other conjectures never enter this obligation as assumptions or negations.
#[derive(Debug)]
pub struct Obligation<'a> {
    source: &'a Encoded,
    goal: Option<usize>,
}

impl<'a> Obligation<'a> {
    pub fn goal_index(&self) -> Option<usize> {
        self.goal
    }

    pub fn declarations(&self) -> impl Iterator<Item = SignedDeclaration<'a>> + '_ {
        self.source
            .declarations
            .iter()
            .enumerate()
            .filter_map(|(index, original)| {
                if original.role == Role::Conjecture {
                    (self.goal == Some(index)).then_some(SignedDeclaration {
                        source_index: index,
                        original,
                        positive: false,
                    })
                } else {
                    Some(SignedDeclaration {
                        source_index: index,
                        original,
                        positive: true,
                    })
                }
            })
    }
}

/// Streaming tasks avoid copying the premises for each conjecture. The caller
/// must close every yielded task before claiming that all conjectures follow.
pub struct Obligations<'a> {
    source: &'a Encoded,
    cursor: usize,
    satisfiability: bool,
}

impl<'a> Iterator for Obligations<'a> {
    type Item = Obligation<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.satisfiability {
            self.satisfiability = false;
            self.cursor = self.source.declarations.len();
            return Some(Obligation {
                source: self.source,
                goal: None,
            });
        }
        while self.cursor < self.source.declarations.len() {
            let index = self.cursor;
            self.cursor += 1;
            if self.source.declarations[index].role == Role::Conjecture {
                return Some(Obligation {
                    source: self.source,
                    goal: Some(index),
                });
            }
        }
        None
    }
}

impl Encoded {
    /// Recheck role policy even for caller-mutated public Encoded values.
    pub fn obligations(&self) -> Result<Obligations<'_>, Error> {
        check_combination(
            self.declarations
                .iter()
                .map(|d| (d.role, d.role_bytes.start)),
        )?;
        let mut has_goal = false;
        for declaration in &self.declarations {
            if declaration.role == Role::Conjecture {
                if !matches!(declaration.body, EncodedBody::Fof(_)) {
                    return Err(error(
                        ErrorKind::InvalidInput,
                        declaration.role_bytes.start,
                        "the conjecture role requires FOF, not CNF",
                    ));
                }
                has_goal = true;
            }
        }
        Ok(Obligations {
            source: self,
            cursor: 0,
            satisfiability: !has_goal,
        })
    }

    pub fn signature(&self) -> core::Signature {
        core::Signature {
            functions: self.functions.iter().map(|symbol| symbol.arity).collect(),
            predicates: self.reservation.extended_arities(),
        }
    }
}
