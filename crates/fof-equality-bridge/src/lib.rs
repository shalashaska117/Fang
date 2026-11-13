// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Isolated representation bridge. No FOF parser or preprocessing acceptance.
#![forbid(unsafe_code)]

use fang::syntax::{Clause as EncodedClause, Literal as EncodedLiteral};
use fang_equality_inference_core::{Atom, Clause, Literal};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    PredicateLimit,
    SymbolId,
    UnknownPredicate,
    PredicateArity,
    ReservedArity,
    LiteralLimit,
}

/// The maximum includes the additional equality slot. This checks scalar
/// capacity without allocating a predicate table.
pub fn reserved_id(predicate_count: usize, maximum: usize) -> Result<u32, Error> {
    if predicate_count >= maximum {
        return Err(Error::PredicateLimit);
    }
    if predicate_count > u32::MAX as usize {
        return Err(Error::SymbolId);
    }
    Ok(predicate_count as u32)
}

/// Construct only from the complete original predicate arity table. Private
/// fields prevent callers from forging an ID/table pair. This type cannot
/// establish that a caller's table actually describes its original source bytes.
#[derive(Debug, PartialEq, Eq)]
pub struct Reservation {
    original_predicates: Vec<usize>,
    equality: u32,
}

impl Reservation {
    pub fn new(original_predicates: Vec<usize>, maximum: usize) -> Result<Self, Error> {
        let equality = reserved_id(original_predicates.len(), maximum)?;
        Ok(Self {
            original_predicates,
            equality,
        })
    }

    pub fn equality_id(&self) -> u32 {
        self.equality
    }

    /// Construct the preprocessing table; original predicate IDs stay fixed.
    /// Its length is bounded by the maximum checked by new(). Allocation
    /// failure and physical memory use are outside this structural contract.
    pub fn extended_arities(&self) -> Vec<usize> {
        let mut result = Vec::new();
        let mut index = 0;
        while index < self.original_predicates.len() {
            result.push(self.original_predicates[index]);
            index += 1;
        }
        result.push(2);
        result
    }

    fn ordinary(&self, predicate: u32, arity: usize) -> Result<(), Error> {
        let index = predicate as usize;
        if index >= self.original_predicates.len() {
            return Err(Error::UnknownPredicate);
        }
        if self.original_predicates[index] != arity {
            return Err(Error::PredicateArity);
        }
        Ok(())
    }

    /// Move term trees unchanged. This checks predicate heads/arity, not function
    /// arities, variable scope or term depth; those are separate input invariants.
    #[expect(
        clippy::vec_init_then_push,
        reason = "vec! introduces a MaybeUninit type axiom in the pinned extraction"
    )]
    pub fn encode_literal(&self, literal: Literal) -> Result<EncodedLiteral, Error> {
        match literal.atom {
            Atom::Predicate(predicate, arguments) => {
                self.ordinary(predicate, arguments.len())?;
                Ok(EncodedLiteral {
                    positive: literal.positive,
                    predicate,
                    arguments,
                })
            }
            Atom::Equal(left, right) => {
                // The vec! expansion introduces an opaque MaybeUninit type in
                // the pinned Aeneas extraction. These pushes use its Vec model.
                let mut arguments = Vec::with_capacity(2);
                arguments.push(left);
                arguments.push(right);
                Ok(EncodedLiteral {
                    positive: literal.positive,
                    predicate: self.equality,
                    arguments,
                })
            }
        }
    }

    pub fn decode_literal(&self, literal: EncodedLiteral) -> Result<Literal, Error> {
        if literal.predicate == self.equality {
            if literal.arguments.len() != 2 {
                return Err(Error::ReservedArity);
            }
            let mut arguments = literal.arguments.into_iter();
            let left = arguments.next().ok_or(Error::ReservedArity)?;
            let right = arguments.next().ok_or(Error::ReservedArity)?;
            Ok(Literal {
                positive: literal.positive,
                atom: Atom::Equal(left, right),
            })
        } else {
            self.ordinary(literal.predicate, literal.arguments.len())?;
            Ok(Literal {
                positive: literal.positive,
                atom: Atom::Predicate(literal.predicate, literal.arguments),
            })
        }
    }

    /// Preserve literal order, duplicates and polarity. A failure returns no
    /// partial clause. Inputs are consumed; native destruction of caller-built
    /// deep terms and allocation failures are outside the typed error contract.
    pub fn encode_clause(&self, clause: Clause, maximum: usize) -> Result<EncodedClause, Error> {
        if clause.len() > maximum {
            return Err(Error::LiteralLimit);
        }
        let mut result = Vec::new();
        for literal in clause {
            result.push(self.encode_literal(literal)?);
        }
        Ok(result)
    }

    pub fn decode_clause(&self, clause: EncodedClause, maximum: usize) -> Result<Clause, Error> {
        if clause.len() > maximum {
            return Err(Error::LiteralLimit);
        }
        let mut result = Vec::new();
        for literal in clause {
            result.push(self.decode_literal(literal)?);
        }
        Ok(result)
    }
}
