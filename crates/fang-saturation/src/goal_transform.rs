// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Fresh ground goal constants are search aids. Proof export must erase them.
use fang::syntax::Term;
use fang_equality_inference_core::{Atom, Clause, Literal};
use std::time::Instant;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Refusal {
    Work,
    Deadline,
}

pub(crate) struct Transform {
    pub clauses: Vec<Clause>,
    pub functions: Vec<usize>,
    /// Original ground term denoted by each appended constant, in symbol order.
    pub definitions: Vec<Term>,
    pub original_functions: usize,
    pub original_inputs: usize,
    pub fallback: Term,
}

struct Budget {
    left: usize,
    deadline: Option<Instant>,
}
impl Budget {
    fn tick(&mut self) -> Result<(), Refusal> {
        self.left = self.left.checked_sub(1).ok_or(Refusal::Work)?;
        if self.left.is_multiple_of(256) && self.deadline.is_some_and(|end| Instant::now() >= end) {
            return Err(Refusal::Deadline);
        }
        Ok(())
    }
}

fn collect(
    term: &Term,
    depth: usize,
    definitions: &mut Vec<Term>,
    fallback: &mut Option<Term>,
    budget: &mut Budget,
) -> Result<bool, Refusal> {
    budget.tick()?;
    if depth > 64 {
        return Err(Refusal::Work);
    }
    match term {
        Term::Var(_) => Ok(false),
        Term::Fun(_, args) => {
            for arg in args {
                if !collect(arg, depth + 1, definitions, fallback, budget)? {
                    return Ok(false);
                }
            }
            if args.is_empty() {
                if fallback.is_none() {
                    *fallback = Some(term.clone());
                }
            } else if !definitions.contains(term) {
                if definitions.len() == 256 {
                    return Err(Refusal::Work);
                }
                definitions.push(term.clone());
            }
            Ok(true)
        }
    }
}

pub(crate) fn prepare(
    clauses: &[Clause],
    functions: &[usize],
    deadline: Option<Instant>,
) -> Result<Option<Transform>, Refusal> {
    if deadline.is_some_and(|end| Instant::now() >= end) {
        return Err(Refusal::Deadline);
    }
    let mut budget = Budget {
        left: 16384,
        deadline,
    };
    let mut definitions = vec![];
    let mut fallback = None;
    let mut negatives = 0;
    for clause in clauses {
        budget.tick()?;
        let [
            Literal {
                positive,
                atom: Atom::Equal(left, right),
            },
        ] = clause.as_slice()
        else {
            return Ok(None);
        };
        if !positive {
            negatives += 1;
            if !collect(left, 0, &mut definitions, &mut fallback, &mut budget)?
                || !collect(right, 0, &mut definitions, &mut fallback, &mut budget)?
            {
                return Ok(None);
            }
        }
    }
    if negatives == 0 || definitions.is_empty() {
        return Ok(None);
    }
    // Enlarging the signature must not make an invalid original symbol valid.
    if crate::search::validate(clauses, functions, &[]).is_err() {
        return Ok(None);
    }
    let Some(fallback) = fallback else {
        return Ok(None);
    };
    let Some(total) = functions.len().checked_add(definitions.len()) else {
        return Err(Refusal::Work);
    };
    if total > u32::MAX as usize {
        return Err(Refusal::Work);
    }
    let mut output = clauses.to_vec();
    for (index, term) in definitions.iter().enumerate() {
        budget.tick()?;
        output.push(vec![Literal {
            positive: true,
            atom: Atom::Equal(
                term.clone(),
                Term::Fun((functions.len() + index) as u32, vec![]),
            ),
        }]);
    }
    let mut signature = functions.to_vec();
    signature.resize(total, 0);
    if deadline.is_some_and(|end| Instant::now() >= end) {
        return Err(Refusal::Deadline);
    }
    Ok(Some(Transform {
        clauses: output,
        functions: signature,
        definitions,
        original_functions: functions.len(),
        original_inputs: clauses.len(),
        fallback,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn c(s: u32) -> Term {
        Term::Fun(s, vec![])
    }
    fn f(t: Term) -> Term {
        Term::Fun(2, vec![t])
    }
    fn eq(positive: bool, a: Term, b: Term) -> Clause {
        vec![Literal {
            positive,
            atom: Atom::Equal(a, b),
        }]
    }

    #[test]
    fn fresh_symbols_preserve_original_inputs_and_nested_goal_terms() {
        let inputs = vec![
            eq(true, f(Term::Var(0)), Term::Var(0)),
            eq(false, f(f(c(0))), f(c(0))),
        ];
        let transformed = prepare(&inputs, &[0, 0, 1], None).unwrap().unwrap();
        assert_eq!(&transformed.clauses[..2], &inputs);
        assert_eq!(transformed.definitions, vec![f(c(0)), f(f(c(0)))]);
        assert_eq!(transformed.functions, vec![0, 0, 1, 0, 0]);
        assert_eq!(transformed.clauses[2], eq(true, f(c(0)), c(3)));
        assert_eq!(transformed.clauses[3], eq(true, f(f(c(0))), c(4)));
    }

    #[test]
    fn nonground_or_nonunit_goals_bypass_and_expired_work_refuses() {
        assert!(
            prepare(&[eq(false, f(Term::Var(0)), c(0))], &[0, 0, 1], None)
                .unwrap()
                .is_none()
        );
        let mut clause = eq(false, f(c(0)), c(1));
        clause.extend(eq(true, c(0), c(1)));
        assert!(prepare(&[clause], &[0, 0, 1], None).unwrap().is_none());
        assert!(matches!(
            prepare(&[], &[], Some(Instant::now())),
            Err(Refusal::Deadline)
        ));
    }

    #[test]
    fn defining_constants_have_exactly_one_extension_in_each_small_interpretation() {
        fn eval(term: &Term, constants: &[usize], unary: u8) -> usize {
            match term {
                Term::Fun(2, xs) => usize::from((unary >> eval(&xs[0], constants, unary)) & 1),
                Term::Fun(f, xs) if xs.is_empty() => constants[*f as usize],
                _ => panic!("ground unary fixture"),
            }
        }
        let inputs = vec![eq(true, f(c(0)), c(1)), eq(false, f(f(c(0))), c(0))];
        let transformed = prepare(&inputs, &[0, 0, 1], None).unwrap().unwrap();
        assert_eq!(transformed.definitions.len(), 2);
        for a in 0..2 {
            for b in 0..2 {
                for unary in 0u8..4 {
                    let holds = |clause: &Clause, constants: &[usize]| {
                        let Atom::Equal(x, y) = &clause[0].atom else {
                            unreachable!()
                        };
                        (eval(x, constants, unary) == eval(y, constants, unary))
                            == clause[0].positive
                    };
                    let original_holds = inputs.iter().all(|clause| holds(clause, &[a, b, 0]));
                    let mut extensions = 0;
                    let mut full_models = 0;
                    for d0 in 0..2 {
                        for d1 in 0..2 {
                            let constants = [a, b, 0, d0, d1];
                            if transformed.clauses[2..]
                                .iter()
                                .all(|clause| holds(clause, &constants))
                            {
                                extensions += 1;
                            }
                            if transformed
                                .clauses
                                .iter()
                                .all(|clause| holds(clause, &constants))
                            {
                                full_models += 1;
                            }
                        }
                    }
                    assert_eq!(extensions, 1);
                    assert_eq!(full_models, usize::from(original_holds));
                }
            }
        }
    }
}
