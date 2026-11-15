// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Inference-local connectedness: every term in the path is below its peak.
use super::*;

fn contains(term: &Term, variable: u32, budget: &mut Budget) -> Result<bool, Refusal> {
    budget.tick()?;
    match term {
        Term::Var(x) => Ok(*x == variable),
        Term::Fun(_, args) => {
            for arg in args {
                if contains(arg, variable, budget)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
    }
}

// Unlike the preorder comparator, this makes no assumptions about variables.
fn strict_compare(
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
        (Term::Var(_), Term::Var(_)) => Ok(None),
        (Term::Fun(..), Term::Var(y)) => Ok(contains(a, *y, budget)?.then_some(Ordering::Greater)),
        (Term::Var(x), Term::Fun(..)) => Ok(contains(b, *x, budget)?.then_some(Ordering::Less)),
        (Term::Fun(f, xs), Term::Fun(g, ys)) => {
            let mut ac = [0; 4];
            let mut bc = [0; 4];
            let aw = profile(a, &mut ac, budget)?;
            let bw = profile(b, &mut bc, budget)?;
            let mut order = aw.cmp(&bw);
            if order == Ordering::Equal {
                order = symbols
                    .get(*f as usize)
                    .ok_or(Refusal::Rules)?
                    .cmp(symbols.get(*g as usize).ok_or(Refusal::Rules)?);
                if order == Ordering::Equal {
                    if f != g || xs.len() != ys.len() {
                        return Ok(None);
                    }
                    let Some((x, y)) = xs.iter().zip(ys).find(|(x, y)| x != y) else {
                        return Ok(Some(Ordering::Equal));
                    };
                    let Some(next) = strict_compare(x, y, symbols, budget)? else {
                        return Ok(None);
                    };
                    order = next;
                }
            }
            Ok(match order {
                Ordering::Greater if ac.iter().zip(bc).all(|(&x, y)| x >= y) => Some(order),
                Ordering::Less if bc.iter().zip(ac).all(|(&x, y)| x >= y) => Some(order),
                _ => None,
            })
        }
    }
}

fn positions(
    term: &Term,
    path: &mut Vec<usize>,
    out: &mut Vec<Vec<usize>>,
    budget: &mut Budget,
) -> Result<(), Refusal> {
    budget.tick()?;
    out.push(path.clone());
    if let Term::Fun(_, args) = term {
        for (index, arg) in args.iter().enumerate() {
            path.push(index);
            positions(arg, path, out, budget)?;
            path.pop();
        }
    }
    Ok(())
}

fn at<'a>(mut term: &'a Term, path: &[usize]) -> Option<&'a Term> {
    for &index in path {
        let Term::Fun(_, args) = term else {
            return None;
        };
        term = args.get(index)?;
    }
    Some(term)
}

fn replace(
    term: &Term,
    path: &[usize],
    replacement: &Term,
    depth: usize,
    budget: &mut Budget,
) -> Result<Term, Refusal> {
    budget.tick()?;
    if path.is_empty() {
        return bounded_clone(replacement, depth, budget);
    }
    let Term::Fun(symbol, args) = term else {
        return Err(Refusal::Rules);
    };
    let mut result = Vec::with_capacity(args.len());
    for (index, arg) in args.iter().enumerate() {
        result.push(if index == path[0] {
            replace(arg, &path[1..], replacement, depth + 1, budget)?
        } else {
            bounded_clone(arg, depth + 1, budget)?
        });
    }
    Ok(Term::Fun(*symbol, result))
}

fn path_below(
    left: Term,
    right: &Term,
    peak: &Term,
    rules: &[(Term, Term)],
    symbols: &[u32],
    budget: &mut Budget,
) -> Result<bool, Refusal> {
    if strict_compare(&left, peak, symbols, budget)? != Some(Ordering::Less)
        || strict_compare(right, peak, symbols, budget)? != Some(Ordering::Less)
    {
        return Ok(false);
    }
    let mut seen = vec![left];
    let mut cursor = 0;
    while cursor < seen.len() {
        budget.tick()?;
        if &seen[cursor] == right {
            return Ok(true);
        }
        let term = seen[cursor].clone();
        let mut places = vec![];
        positions(&term, &mut vec![], &mut places, budget)?;
        for place in places {
            let subterm = at(&term, &place).ok_or(Refusal::Rules)?;
            for (a, b) in rules {
                for (from, to) in [(a, b), (b, a)] {
                    let mut sigma = HashMap::new();
                    if !matches(from, subterm, &mut sigma, budget)? {
                        continue;
                    }
                    let Some(value) = instantiate(to, &sigma, place.len(), budget)? else {
                        continue;
                    };
                    let next = replace(&term, &place, &value, 0, budget)?;
                    if profile(&next, &mut [0; 4], budget)? > 4096 {
                        return Err(Refusal::Work);
                    }
                    if strict_compare(&next, peak, symbols, budget)? != Some(Ordering::Less) {
                        continue;
                    }
                    if &next == right {
                        return Ok(true);
                    }
                    if !seen.contains(&next) {
                        if seen.len() == 64 {
                            return Err(Refusal::Work);
                        }
                        seen.push(next);
                    }
                }
            }
        }
        cursor += 1;
    }
    Ok(false)
}

pub(crate) fn connected(
    bank: &Bank,
    left: TermId,
    right: TermId,
    peak: TermId,
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
    let a = from_bank(bank, left, 0, &mut budget)?;
    let b = from_bank(bank, right, 0, &mut budget)?;
    let p = from_bank(bank, peak, 0, &mut budget)?;
    let mut vars = BTreeSet::new();
    for term in [&a, &b, &p] {
        variables(term, &mut vars, &mut budget)?;
    }
    if vars.len() > 4 {
        return Err(Refusal::Variables);
    }
    let vars: Vec<_> = vars.into_iter().collect();
    let ranks: Vec<_> = (0..vars.len() as u32).collect();
    let a = identify(&a, &vars, &ranks, &mut budget)?;
    let b = identify(&b, &vars, &ranks, &mut budget)?;
    let p = identify(&p, &vars, &ranks, &mut budget)?;
    let mut rules = vec![];
    for &(x, y) in equations {
        rules.push((
            from_bank(bank, x, 0, &mut budget)?,
            from_bank(bank, y, 0, &mut budget)?,
        ));
    }
    let result = path_below(a, &b, &p, &rules, symbols, &mut budget)?;
    if deadline.is_some_and(|end| Instant::now() >= end) {
        return Err(Refusal::Deadline);
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_constant_graphs_agree_with_independent_bounded_reachability() {
        let mut bank = Bank::new();
        let terms: Vec<_> = (0..4).map(|s| bank.app(s, &[])).collect();
        let high = bank.app(4, &[terms[0]]);
        let mut peaks = terms.clone();
        peaks.push(high);
        let edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];
        let mut checked = 0;
        for mask in 0..64 {
            let rules: Vec<_> = edges
                .iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, &(a, b))| (terms[a], terms[b]))
                .collect();
            for (bound, &peak) in peaks.iter().enumerate() {
                // Constants have ranks 0..3. The unary peak exceeds all constants.
                let mut reach = [[false; 4]; 4];
                for (i, row) in reach.iter_mut().enumerate() {
                    row[i] = i < bound;
                }
                for (i, &(a, b)) in edges.iter().enumerate() {
                    if mask & (1 << i) != 0 && a < bound && b < bound {
                        reach[a][b] = true;
                        reach[b][a] = true;
                    }
                }
                for k in 0..4 {
                    for i in 0..4 {
                        for j in 0..4 {
                            reach[i][j] |= reach[i][k] && reach[k][j];
                        }
                    }
                }
                for i in 0..4 {
                    for j in 0..4 {
                        assert_eq!(
                            connected(
                                &bank,
                                terms[i],
                                terms[j],
                                peak,
                                &rules,
                                &[0, 1, 2, 3, 4],
                                None
                            )
                            .unwrap(),
                            reach[i][j],
                            "mask={mask}, bound={bound}, {i} -> {j}"
                        );
                        checked += 1;
                    }
                }
            }
        }
        assert_eq!(checked, 5120);
    }

    #[test]
    fn unconditional_comparisons_survive_all_sampled_ground_substitutions() {
        use crate::kbo::{Cmp, Order, Precedence};
        fn put(bank: &mut Bank, term: &Term, images: &[TermId; 2]) -> TermId {
            match term {
                Term::Var(x) => images[*x as usize],
                Term::Fun(f, args) => {
                    let args: Vec<_> = args.iter().map(|t| put(bank, t, images)).collect();
                    bank.app(*f, &args)
                }
            }
        }
        let x = Term::Var(0);
        let y = Term::Var(1);
        let a = Term::Fun(0, vec![]);
        let b = Term::Fun(1, vec![]);
        let f = |s, t| Term::Fun(2, vec![s, t]);
        let g = |s| Term::Fun(3, vec![s]);
        let terms = [
            x.clone(),
            y.clone(),
            a.clone(),
            b.clone(),
            f(x.clone(), y.clone()),
            f(y.clone(), x.clone()),
            g(x.clone()),
            g(y.clone()),
            f(g(x.clone()), y.clone()),
            f(x.clone(), x.clone()),
            f(y.clone(), y.clone()),
            g(g(x.clone())),
        ];
        let ground = [
            a.clone(),
            b.clone(),
            g(a.clone()),
            g(b.clone()),
            f(a.clone(), b.clone()),
            f(b, a),
        ];
        let mut bank = Bank::new();
        let order = Order::new(&[0, 0, 2, 1], &[0; 4], 4, Precedence::Arity);
        let images: Vec<_> = ground.iter().map(|t| put(&mut bank, t, &[0, 0])).collect();
        let mut checked = 0;
        for left in &terms {
            for right in &terms {
                let mut budget = Budget {
                    remaining: 200_000,
                    deadline: None,
                };
                if let Some(claimed) =
                    strict_compare(left, right, &[0, 1, 3, 2], &mut budget).unwrap()
                {
                    for &a in &images {
                        for &b in &images {
                            let l = put(&mut bank, left, &[a, b]);
                            let r = put(&mut bank, right, &[a, b]);
                            let expected = match claimed {
                                Ordering::Less => Cmp::Less,
                                Ordering::Equal => Cmp::Equal,
                                Ordering::Greater => Cmp::Greater,
                            };
                            assert_eq!(order.compare(&bank, l, r), expected);
                            checked += 1;
                        }
                    }
                }
            }
        }
        assert!(checked > 1000, "{checked}");
    }

    #[test]
    fn rising_valley_connects_but_touching_the_peak_does_not() {
        let mut bank = Bank::new();
        let a = bank.app(0, &[]);
        let b = bank.app(1, &[]);
        let c = bank.app(2, &[]);
        let d = bank.app(3, &[]);
        let peak = bank.app(4, &[d]);
        let symbols = [0, 2, 1, 3, 4];
        let rules = [(a, b), (b, c)];
        assert!(!joinable(&bank, a, c, &rules, &symbols, None).unwrap());
        assert!(connected(&bank, a, c, peak, &rules, &symbols, None).unwrap());
        assert!(!connected(&bank, a, c, b, &rules, &symbols, None).unwrap());
        assert!(!connected(&bank, a, c, peak, &rules[..1], &symbols, None).unwrap());
        assert_eq!(
            connected(&bank, a, c, peak, &rules, &symbols, Some(Instant::now())),
            Err(Refusal::Deadline)
        );
    }

    #[test]
    fn unordered_variables_remain_incomparable_and_renamings_preserve_paths() {
        let mut budget = Budget {
            remaining: 200_000,
            deadline: None,
        };
        assert_eq!(
            strict_compare(&Term::Var(0), &Term::Var(1), &[], &mut budget),
            Ok(None)
        );
        for (x, y) in [(0, 1), (15, 3), (65535, 0)] {
            let mut bank = Bank::new();
            let x = bank.var(x);
            let y = bank.var(y);
            let left = bank.app(0, &[x, y]);
            let right = bank.app(0, &[y, x]);
            let peak = bank.app(1, &[left]);
            assert!(connected(&bank, left, right, peak, &[(left, right)], &[0, 1], None).unwrap());
            assert!(!connected(&bank, left, right, left, &[(left, right)], &[0, 1], None).unwrap());
        }
    }
}
