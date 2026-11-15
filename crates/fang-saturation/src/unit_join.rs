// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Bounded ground-joinability tests for unit equations with at most four variables.
//! Each total variable preorder is checked. Variables equated by a case are
//! identified; the remaining variable ranks constrain a conservative uniform KBO.
//! A refused or unjoined case keeps the equation available for ordinary search.
#[path = "connected.rs"]
pub(crate) mod connected;
use crate::term::{Bank, Head, TermId};
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap};
use std::time::Instant;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Term {
    Var(u32),
    Fun(u32, Vec<Term>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Refusal {
    Work,
    Deadline,
    Depth,
    Variables,
    Rules,
}

struct Budget {
    remaining: usize,
    deadline: Option<Instant>,
}
impl Budget {
    fn tick(&mut self) -> Result<(), Refusal> {
        self.remaining = self.remaining.checked_sub(1).ok_or(Refusal::Work)?;
        if self.remaining.is_multiple_of(256)
            && self.deadline.is_some_and(|end| Instant::now() >= end)
        {
            return Err(Refusal::Deadline);
        }
        Ok(())
    }
}

fn from_bank(bank: &Bank, at: TermId, depth: usize, budget: &mut Budget) -> Result<Term, Refusal> {
    budget.tick()?;
    if depth > 64 {
        return Err(Refusal::Depth);
    }
    if bank.weight(at) > 4096 {
        return Err(Refusal::Work);
    }
    Ok(match bank.head(at) {
        Head::Var(x) => Term::Var(x),
        Head::Sym(f) => Term::Fun(
            f,
            bank.args(at)
                .iter()
                .map(|&child| from_bank(bank, child, depth + 1, budget))
                .collect::<Result<_, _>>()?,
        ),
    })
}

fn variables(term: &Term, out: &mut BTreeSet<u32>, budget: &mut Budget) -> Result<(), Refusal> {
    budget.tick()?;
    match term {
        Term::Var(x) => {
            out.insert(*x);
        }
        Term::Fun(_, args) => {
            for child in args {
                variables(child, out, budget)?;
            }
        }
    }
    Ok(())
}

/// Surjections to ordered blocks enumerate total preorders, including equalities.
fn preorders(n: usize) -> Result<Vec<Vec<u32>>, Refusal> {
    if n > 4 {
        return Err(Refusal::Variables);
    }
    if n == 0 {
        return Ok(vec![vec![]]);
    }
    let mut output = vec![];
    for blocks in 1..=n {
        for code in 0..blocks.pow(n as u32) {
            let mut rest = code;
            let mut ranks = vec![];
            let mut used = 0u32;
            for _ in 0..n {
                let rank = (rest % blocks) as u32;
                rest /= blocks;
                used |= 1 << rank;
                ranks.push(rank);
            }
            if used == (1 << blocks) - 1 {
                output.push(ranks);
            }
        }
    }
    Ok(output)
}

fn identify(
    term: &Term,
    vars: &[u32],
    ranks: &[u32],
    budget: &mut Budget,
) -> Result<Term, Refusal> {
    budget.tick()?;
    Ok(match term {
        Term::Var(x) => Term::Var(ranks[vars.binary_search(x).map_err(|_| Refusal::Variables)?]),
        Term::Fun(f, args) => Term::Fun(
            *f,
            args.iter()
                .map(|t| identify(t, vars, ranks, budget))
                .collect::<Result<_, _>>()?,
        ),
    })
}

fn profile(term: &Term, counts: &mut [u32; 4], budget: &mut Budget) -> Result<u32, Refusal> {
    budget.tick()?;
    match term {
        Term::Var(x) => {
            let slot = counts.get_mut(*x as usize).ok_or(Refusal::Variables)?;
            *slot = slot.checked_add(1).ok_or(Refusal::Work)?;
            Ok(1)
        }
        Term::Fun(_, args) => {
            let mut weight = 1u32;
            for arg in args {
                weight = weight
                    .checked_add(profile(arg, counts, budget)?)
                    .ok_or(Refusal::Work)?;
            }
            Ok(weight)
        }
    }
}

/// A contained variable of at least the other rank gives a strict subterm bound.
fn contains_at_least(term: &Term, rank: u32, budget: &mut Budget) -> Result<bool, Refusal> {
    budget.tick()?;
    match term {
        Term::Var(x) => Ok(*x >= rank),
        Term::Fun(_, args) => {
            for child in args {
                if contains_at_least(child, rank, budget)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
    }
}

/// Every returned comparison must hold for all ground substitutions satisfying
/// the variable preorder. Unknown comparisons are never treated as decreasing.
fn compare(
    a: &Term,
    b: &Term,
    symbols: &[u32],
    budget: &mut Budget,
) -> Result<Option<Ordering>, Refusal> {
    budget.tick()?;
    if a == b {
        return Ok(Some(Ordering::Equal));
    }
    match (a, b) {
        (Term::Var(x), Term::Var(y)) => Ok(Some(x.cmp(y))),
        (Term::Fun(..), Term::Var(y)) => {
            Ok(contains_at_least(a, *y, budget)?.then_some(Ordering::Greater))
        }
        (Term::Var(x), Term::Fun(..)) => {
            Ok(contains_at_least(b, *x, budget)?.then_some(Ordering::Less))
        }
        (Term::Fun(f, xs), Term::Fun(g, ys)) => {
            let mut ac = [0; 4];
            let mut bc = [0; 4];
            let aw = profile(a, &mut ac, budget)?;
            let bw = profile(b, &mut bc, budget)?;
            let covers_a = ac.iter().zip(bc).all(|(&x, y)| x >= y);
            let covers_b = bc.iter().zip(ac).all(|(&x, y)| x >= y);
            let mut comparison = aw.cmp(&bw);
            if comparison == Ordering::Equal {
                let fr = symbols.get(*f as usize).ok_or(Refusal::Rules)?;
                let gr = symbols.get(*g as usize).ok_or(Refusal::Rules)?;
                comparison = fr.cmp(gr);
                if comparison == Ordering::Equal {
                    if f != g || xs.len() != ys.len() {
                        return Ok(None);
                    }
                    let Some((x, y)) = xs.iter().zip(ys).find(|(x, y)| x != y) else {
                        return Ok(Some(Ordering::Equal));
                    };
                    let Some(order) = compare(x, y, symbols, budget)? else {
                        return Ok(None);
                    };
                    comparison = order;
                }
            }
            Ok(match comparison {
                Ordering::Greater if covers_a => Some(Ordering::Greater),
                Ordering::Less if covers_b => Some(Ordering::Less),
                _ => None,
            })
        }
    }
}

fn matches(
    pattern: &Term,
    target: &Term,
    subst: &mut HashMap<u32, Term>,
    budget: &mut Budget,
) -> Result<bool, Refusal> {
    budget.tick()?;
    Ok(match pattern {
        Term::Var(x) => match subst.get(x) {
            Some(bound) => bound == target,
            None => {
                subst.insert(*x, target.clone());
                true
            }
        },
        Term::Fun(f, xs) => match target {
            Term::Fun(g, ys) if f == g && xs.len() == ys.len() => {
                for (x, y) in xs.iter().zip(ys) {
                    if !matches(x, y, subst, budget)? {
                        return Ok(false);
                    }
                }
                true
            }
            _ => false,
        },
    })
}

fn bounded_clone(term: &Term, depth: usize, budget: &mut Budget) -> Result<Term, Refusal> {
    budget.tick()?;
    if depth > 64 {
        return Err(Refusal::Depth);
    }
    Ok(match term {
        Term::Var(x) => Term::Var(*x),
        Term::Fun(f, args) => Term::Fun(
            *f,
            args.iter()
                .map(|t| bounded_clone(t, depth + 1, budget))
                .collect::<Result<_, _>>()?,
        ),
    })
}

fn instantiate(
    term: &Term,
    subst: &HashMap<u32, Term>,
    depth: usize,
    budget: &mut Budget,
) -> Result<Option<Term>, Refusal> {
    budget.tick()?;
    if depth > 64 {
        return Err(Refusal::Depth);
    }
    match term {
        Term::Var(x) => subst
            .get(x)
            .map(|t| bounded_clone(t, depth, budget))
            .transpose(),
        Term::Fun(f, args) => {
            let mut out = vec![];
            for arg in args {
                let Some(value) = instantiate(arg, subst, depth + 1, budget)? else {
                    return Ok(None);
                };
                out.push(value);
            }
            Ok(Some(Term::Fun(*f, out)))
        }
    }
}

fn rewrite(
    term: &Term,
    rules: &[(Term, Term)],
    symbols: &[u32],
    depth: usize,
    budget: &mut Budget,
) -> Result<Option<Term>, Refusal> {
    budget.tick()?;
    if depth > 64 {
        return Err(Refusal::Depth);
    }
    for (left, right) in rules {
        for (from, to) in [(left, right), (right, left)] {
            let mut subst = HashMap::new();
            if !matches(from, term, &mut subst, budget)? {
                continue;
            }
            let Some(next) = instantiate(to, &subst, depth, budget)? else {
                continue;
            };
            if compare(term, &next, symbols, budget)? == Some(Ordering::Greater) {
                return Ok(Some(next));
            }
        }
    }
    if let Term::Fun(f, args) = term {
        for (index, arg) in args.iter().enumerate() {
            if let Some(next) = rewrite(arg, rules, symbols, depth + 1, budget)? {
                let mut next_args = args.clone();
                next_args[index] = next;
                return Ok(Some(Term::Fun(*f, next_args)));
            }
        }
    }
    Ok(None)
}

fn normalize(
    mut term: Term,
    rules: &[(Term, Term)],
    symbols: &[u32],
    budget: &mut Budget,
) -> Result<Term, Refusal> {
    for _ in 0..128 {
        let Some(next) = rewrite(&term, rules, symbols, 0, budget)? else {
            return Ok(term);
        };
        let mut counts = [0; 4];
        // Also bound expanded intermediate terms, including substitutions.
        if profile(&next, &mut counts, budget)? > 4096 {
            return Err(Refusal::Work);
        }
        term = next;
    }
    Err(Refusal::Work)
}

pub(crate) fn joinable(
    bank: &Bank,
    left: TermId,
    right: TermId,
    equations: &[(TermId, TermId)],
    symbols: &[u32],
    deadline: Option<Instant>,
) -> Result<bool, Refusal> {
    if deadline.is_some_and(|end| Instant::now() >= end) {
        return Err(Refusal::Deadline);
    }
    if equations.len() > 64 {
        return Err(Refusal::Rules);
    }
    let mut budget = Budget {
        remaining: 200_000,
        deadline,
    };
    let left = from_bank(bank, left, 0, &mut budget)?;
    let right = from_bank(bank, right, 0, &mut budget)?;
    let mut vars = BTreeSet::new();
    variables(&left, &mut vars, &mut budget)?;
    variables(&right, &mut vars, &mut budget)?;
    let vars: Vec<_> = vars.into_iter().collect();
    let cases = preorders(vars.len())?;
    let mut rules = vec![];
    for &(a, b) in equations {
        rules.push((
            from_bank(bank, a, 0, &mut budget)?,
            from_bank(bank, b, 0, &mut budget)?,
        ));
    }
    for ranks in cases {
        let a = identify(&left, &vars, &ranks, &mut budget)?;
        let b = identify(&right, &vars, &ranks, &mut budget)?;
        if normalize(a, &rules, symbols, &mut budget)?
            != normalize(b, &rules, symbols, &mut budget)?
        {
            return Ok(false);
        }
    }
    if deadline.is_some_and(|end| Instant::now() >= end) {
        return Err(Refusal::Deadline);
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kbo::{Cmp, Order, Precedence};

    fn budget() -> Budget {
        Budget {
            remaining: 10_000_000,
            deadline: None,
        }
    }
    fn v(x: u32) -> Term {
        Term::Var(x)
    }
    fn c(x: u32) -> Term {
        Term::Fun(x, vec![])
    }
    fn f(a: Term, b: Term) -> Term {
        Term::Fun(2, vec![a, b])
    }
    fn g(a: Term) -> Term {
        Term::Fun(3, vec![a])
    }
    fn bank_term(bank: &mut Bank, term: &Term, images: Option<&[TermId]>) -> TermId {
        match term {
            Term::Var(x) => images.map_or_else(|| bank.var(*x), |values| values[*x as usize]),
            Term::Fun(symbol, args) => {
                let children: Vec<_> = args.iter().map(|t| bank_term(bank, t, images)).collect();
                bank.app(*symbol, &children)
            }
        }
    }

    #[test]
    fn all_weak_orders_include_equalities_without_duplicates() {
        for (n, expected) in [1, 1, 3, 13, 75].into_iter().enumerate() {
            let cases = preorders(n).unwrap();
            assert_eq!(cases.len(), expected);
            assert_eq!(cases.iter().collect::<BTreeSet<_>>().len(), expected);
            for case in cases {
                assert_eq!(case.len(), n);
                if n > 0 {
                    let used: BTreeSet<_> = case.iter().copied().collect();
                    assert_eq!(
                        used.into_iter().collect::<Vec<_>>(),
                        (0..=*case.iter().max().unwrap()).collect::<Vec<_>>()
                    );
                }
            }
        }
        assert_eq!(preorders(5), Err(Refusal::Variables));
    }

    #[test]
    fn every_claimed_orientation_survives_matching_ground_substitutions() {
        let mut bank = Bank::new();
        let order = Order::new(&[0, 0, 2, 1], &[0; 4], 4, Precedence::Arity);
        let symbols = [0, 1, 3, 2];
        let terms = vec![
            v(0),
            v(1),
            c(0),
            c(1),
            f(v(0), v(1)),
            f(v(1), v(0)),
            g(v(0)),
            g(v(1)),
            f(g(v(0)), v(1)),
            f(v(1), g(v(0))),
            g(g(v(0))),
            f(v(0), v(0)),
            f(v(1), v(1)),
            f(c(0), v(0)),
            f(c(1), v(1)),
        ];
        let ground = vec![
            c(0),
            c(1),
            g(c(0)),
            g(c(1)),
            f(c(0), c(0)),
            f(c(0), c(1)),
            f(c(1), c(0)),
            f(c(1), c(1)),
            g(g(c(0))),
            g(g(c(1))),
        ];
        let ground: Vec<_> = ground
            .iter()
            .map(|t| bank_term(&mut bank, t, None))
            .collect();
        let mut checked = 0;
        for ranks in preorders(2).unwrap() {
            for a in &terms {
                for b in &terms {
                    let left = identify(a, &[0, 1], &ranks, &mut budget()).unwrap();
                    let right = identify(b, &[0, 1], &ranks, &mut budget()).unwrap();
                    let Some(claimed) = compare(&left, &right, &symbols, &mut budget()).unwrap()
                    else {
                        continue;
                    };
                    for &x in &ground {
                        for &y in &ground {
                            let expected_case = match ranks[0].cmp(&ranks[1]) {
                                Ordering::Less => Cmp::Less,
                                Ordering::Equal => Cmp::Equal,
                                Ordering::Greater => Cmp::Greater,
                            };
                            if order.compare(&bank, x, y) != expected_case {
                                continue;
                            }
                            let mut images = [x; 4];
                            images[ranks[0] as usize] = x;
                            images[ranks[1] as usize] = y;
                            let ga = bank_term(&mut bank, &left, Some(&images));
                            let gb = bank_term(&mut bank, &right, Some(&images));
                            let expected = match claimed {
                                Ordering::Less => Cmp::Less,
                                Ordering::Equal => Cmp::Equal,
                                Ordering::Greater => Cmp::Greater,
                            };
                            assert_eq!(
                                order.compare(&bank, ga, gb),
                                expected,
                                "{a:?} / {b:?}, ranks {ranks:?}"
                            );
                            checked += 1;
                        }
                    }
                }
            }
        }
        assert!(checked > 10_000, "{checked}");
    }

    #[test]
    fn permutative_equations_join_in_every_case_but_arbitrary_equations_do_not() {
        let mut bank = Bank::new();
        let comm = (f(v(0), v(1)), f(v(1), v(0)));
        let eq = (
            bank_term(&mut bank, &comm.0, None),
            bank_term(&mut bank, &comm.1, None),
        );
        let left = bank_term(&mut bank, &f(v(0), f(v(1), v(2))), None);
        let right = bank_term(&mut bank, &f(v(0), f(v(2), v(1))), None);
        assert_eq!(
            joinable(&bank, left, right, &[eq], &[0, 1, 3, 2], None),
            Ok(true)
        );
        let x = bank.var(0);
        let y = bank.var(1);
        assert_eq!(joinable(&bank, x, y, &[eq], &[0, 1, 3, 2], None), Ok(false));
        assert_eq!(
            joinable(&bank, left, right, &[], &[0, 1, 3, 2], None),
            Ok(false)
        );
        assert_eq!(
            joinable(&bank, left, right, &vec![eq; 65], &[0, 1, 3, 2], None),
            Err(Refusal::Rules)
        );
        assert_eq!(
            joinable(
                &bank,
                left,
                right,
                &[eq],
                &[0, 1, 3, 2],
                Some(Instant::now())
            ),
            Err(Refusal::Deadline)
        );
    }

    fn evaluate(term: &Term, assignment: &[usize], binary: u8, unary: u8) -> usize {
        match term {
            Term::Var(x) => assignment[*x as usize],
            Term::Fun(0, _) => 0,
            Term::Fun(1, _) => 1,
            Term::Fun(2, args) => {
                let a = evaluate(&args[0], assignment, binary, unary);
                let b = evaluate(&args[1], assignment, binary, unary);
                ((binary >> (a * 2 + b)) & 1) as usize
            }
            Term::Fun(3, args) => {
                ((unary >> evaluate(&args[0], assignment, binary, unary)) & 1) as usize
            }
            _ => panic!("test signature"),
        }
    }

    #[test]
    fn joined_equations_hold_in_all_two_element_models_of_the_rules() {
        let mut bank = Bank::new();
        let rule = (f(v(0), v(1)), f(v(1), v(0)));
        let equation = (
            bank_term(&mut bank, &rule.0, None),
            bank_term(&mut bank, &rule.1, None),
        );
        let terms = vec![
            v(0),
            v(1),
            v(2),
            f(v(0), v(1)),
            f(v(1), v(0)),
            f(v(0), f(v(1), v(2))),
            f(v(0), f(v(2), v(1))),
            g(f(v(0), v(1))),
            g(f(v(1), v(0))),
            f(g(v(0)), v(1)),
            f(v(1), g(v(0))),
        ];
        let mut checked = 0;
        let mut joined = 0;
        for left in &terms {
            for right in &terms {
                let a = bank_term(&mut bank, left, None);
                let b = bank_term(&mut bank, right, None);
                if joinable(&bank, a, b, &[equation], &[0, 1, 3, 2], None) != Ok(true) {
                    continue;
                }
                joined += 1;
                for binary in 0..16 {
                    for unary in 0..4 {
                        let model = (0..4).all(|code| {
                            let assignment = [code & 1, (code >> 1) & 1, 0];
                            evaluate(&rule.0, &assignment, binary, unary)
                                == evaluate(&rule.1, &assignment, binary, unary)
                        });
                        if !model {
                            continue;
                        }
                        for code in 0..8 {
                            let assignment = [code & 1, (code >> 1) & 1, (code >> 2) & 1];
                            assert_eq!(
                                evaluate(left, &assignment, binary, unary),
                                evaluate(right, &assignment, binary, unary)
                            );
                            checked += 1;
                        }
                    }
                }
            }
        }
        assert!(joined > terms.len());
        assert!(checked > 4000, "{checked}");
        // This model satisfies commutativity but refutes the negative control x=y.
        assert_ne!(
            evaluate(&v(0), &[0, 1], 0, 0),
            evaluate(&v(1), &[0, 1], 0, 0)
        );
    }

    #[test]
    fn substitutions_and_oversized_terms_refuse_without_unbounded_expansion() {
        let mut bank = Bank::new();
        let a = bank.app(0, &[]);
        let mut term = a;
        for _ in 0..13 {
            term = bank.app(2, &[term, term]);
        }
        assert_eq!(
            joinable(&bank, term, a, &[], &[0, 1, 3, 2], None),
            Err(Refusal::Work)
        );
        let term = g(g(v(0)));
        let mut subst = HashMap::new();
        subst.insert(0, g(g(c(0))));
        assert_eq!(
            instantiate(&term, &subst, 63, &mut budget()),
            Err(Refusal::Depth)
        );
        let mut limited = Budget {
            remaining: 0,
            deadline: None,
        };
        assert_eq!(
            compare(&v(0), &v(1), &[0, 1, 3, 2], &mut limited),
            Err(Refusal::Work)
        );
        assert_eq!(instantiate(&v(1), &subst, 0, &mut budget()), Ok(None));
    }
}
