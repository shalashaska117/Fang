// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Independent implementation of Fang's exact predicate/polarity index contract.
// Vampire is a design/reference comparison; no Vampire implementation is copied.
// Production Fang does not use this experimental crate.
#![forbid(unsafe_code)]

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiteralKey {
    pub predicate: usize,
    pub positive: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Position {
    pub clause: usize,
    pub literal: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Candidate {
    pub other: usize,
    pub left: usize,
    pub right: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Limits {
    pub predicate_count: usize,
    pub max_clauses: usize,
    pub max_positions: usize,
    pub max_buckets: usize,
    pub max_candidates: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub enum IndexError {
    ClauseOrder,
    InvalidPredicate,
    InvalidGiven,
    ClauseLimit,
    PositionLimit,
    BucketLimit,
    ResultLimit,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Bucket {
    predicate: usize,
    positive: bool,
    positions: Vec<Position>,
}

struct Cursor {
    bucket: usize,
    offset: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Index {
    clauses: Vec<Vec<LiteralKey>>,
    buckets: Vec<Bucket>,
    position_count: usize,
    limits: Limits,
}

fn same_key(left: &LiteralKey, right: &LiteralKey) -> bool {
    left.predicate == right.predicate && left.positive == right.positive
}

fn valid_keys(clause: &[LiteralKey], predicate_count: usize) -> bool {
    let mut index = 0;
    let mut valid = true;
    while index < clause.len() && valid {
        valid = clause[index].predicate < predicate_count;
        index += 1;
    }
    valid
}

impl Index {
    pub fn new(limits: Limits) -> Self {
        Self {
            clauses: Vec::new(),
            buckets: Vec::new(),
            position_count: 0,
            limits,
        }
    }

    pub fn active_count(&self) -> usize {
        self.clauses.len()
    }

    pub fn history(&self) -> &Vec<Vec<LiteralKey>> {
        &self.clauses
    }

    pub fn stored_positions(&self) -> usize {
        self.position_count
    }

    // The sentinel is buckets.len(), so sparse predicate IDs need no dense table.
    fn find_bucket(&self, predicate: usize, positive: bool) -> usize {
        let mut index = 0;
        let mut found = false;
        while index < self.buckets.len() && !found {
            let bucket = &self.buckets[index];
            if bucket.predicate == predicate && bucket.positive == positive {
                found = true;
            } else {
                index += 1;
            }
        }
        index
    }

    fn bucket_capacity_for(&self, clause: &[LiteralKey]) -> bool {
        let mut available = self.limits.max_buckets - self.buckets.len();
        let mut index = 0;
        let mut fits = true;
        while index < clause.len() && fits {
            let key = &clause[index];
            if self.find_bucket(key.predicate, key.positive) == self.buckets.len() {
                let mut earlier = 0;
                let mut repeated = false;
                while earlier < index && !repeated {
                    repeated = same_key(&clause[earlier], key);
                    earlier += 1;
                }
                if !repeated {
                    if available == 0 {
                        fits = false;
                    } else {
                        available -= 1;
                    }
                }
            }
            index += 1;
        }
        fits
    }

    /// Activate the next complete clause. Every returned error preserves self.
    /// Allocation aborts/panics from the Rust runtime are outside this contract.
    pub fn activate(
        &mut self,
        clause_id: usize,
        clause: Vec<LiteralKey>,
    ) -> Result<(), IndexError> {
        if clause_id != self.clauses.len() {
            return Err(IndexError::ClauseOrder);
        }
        if self.clauses.len() >= self.limits.max_clauses {
            return Err(IndexError::ClauseLimit);
        }
        if self.position_count > self.limits.max_positions
            || clause.len() > self.limits.max_positions - self.position_count
        {
            return Err(IndexError::PositionLimit);
        }
        if !valid_keys(&clause, self.limits.predicate_count) {
            return Err(IndexError::InvalidPredicate);
        }
        if self.buckets.len() > self.limits.max_buckets || !self.bucket_capacity_for(&clause) {
            return Err(IndexError::BucketLimit);
        }
        let new_position_count = self.position_count + clause.len();
        // All fallible validation precedes the first mutation.
        let mut position = 0;
        while position < clause.len() {
            let key = &clause[position];
            let bucket = self.find_bucket(key.predicate, key.positive);
            if bucket == self.buckets.len() {
                self.buckets.push(Bucket {
                    predicate: key.predicate,
                    positive: key.positive,
                    positions: Vec::new(),
                });
            }
            self.buckets[bucket].positions.push(Position {
                clause: clause_id,
                literal: position,
            });
            position += 1;
        }
        self.position_count = new_position_count;
        self.clauses.push(clause);
        Ok(())
    }

    /// Return every complementary occurrence in active clause/literal order.
    pub fn query_complement(&self, key: &LiteralKey) -> Result<Vec<Position>, IndexError> {
        if key.predicate >= self.limits.predicate_count {
            return Err(IndexError::InvalidPredicate);
        }
        let bucket = self.find_bucket(key.predicate, !key.positive);
        let mut result = Vec::new();
        if bucket < self.buckets.len() {
            let positions = &self.buckets[bucket].positions;
            if positions.len() > self.limits.max_candidates {
                return Err(IndexError::ResultLimit);
            }
            let mut index = 0;
            while index < positions.len() {
                result.push(Position {
                    clause: positions[index].clause,
                    literal: positions[index].literal,
                });
                index += 1;
            }
        }
        Ok(result)
    }

    /// Exact eligible subsequence of the existing (other, left, right) scan.
    /// The index must contain precisely the prefix through this latest given.
    pub fn candidates(&self, given_id: usize) -> Result<Vec<Candidate>, IndexError> {
        if given_id >= self.clauses.len() || given_id + 1 != self.clauses.len() {
            return Err(IndexError::InvalidGiven);
        }
        let clause = &self.clauses[given_id];
        let mut cursors = Vec::new();
        let mut left = 0;
        while left < clause.len() {
            let key = &clause[left];
            cursors.push(Cursor {
                bucket: self.find_bucket(key.predicate, !key.positive),
                offset: 0,
            });
            left += 1;
        }
        let mut result = Vec::new();
        let mut other = 0;
        let mut fits = true;
        while other < self.clauses.len() && fits {
            left = 0;
            while left < clause.len() && fits {
                let bucket = cursors[left].bucket;
                if bucket < self.buckets.len() {
                    let positions = &self.buckets[bucket].positions;
                    let mut offset = cursors[left].offset;
                    while offset < positions.len() && positions[offset].clause == other && fits {
                        if result.len() >= self.limits.max_candidates {
                            fits = false;
                        } else {
                            result.push(Candidate {
                                other,
                                left,
                                right: positions[offset].literal,
                            });
                            offset += 1;
                        }
                    }
                    cursors[left].offset = offset;
                }
                left += 1;
            }
            other += 1;
        }
        if fits {
            Ok(result)
        } else {
            Err(IndexError::ResultLimit)
        }
    }
}
