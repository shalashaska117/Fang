# Roadmap

The second release reads TPTP CNF and FOF with and without equality, proves conjectures, checks every positive answer with a Lean checker against the original input, and prints TSTP refutations, for conjectures only when the problem is a single file. Its search is weak: it proved 2 of 111 sampled TPTP problems where Vampire proved 61. It is not a complete TPTP implementation or a CASC entry.

## Next: the search

The third version is about solving more problems. Each step is measured against Vampire on the same corpus, hardware and limits, and every new inference rule gets checker support before it can produce a checked answer.

- A term ordering (KBO) with ordered resolution and superposition.
- Subsumption and tautology deletion. Deleting clauses needs no change to the checker, because a proof only uses the clauses it derives from.
- Demodulation, with a matching certificate rule and its Lean proof.
- Clause selection by age and weight, and term indexes for unification and subsumption.
- Several strategies run in parallel.

The command gets three checking layers. `--check compiled` stays the default and `--check kernel` stays opt-in. A new `--check none` reports the search result without checking it and says so on every run; it is never the default, and its main use is measuring a search technique before the checker supports it. Kernel replay gets a split of its slowest proof phase, which made one of the release test inputs stop with Timeout.

TSTP output for conjectures in problems with include directives also belongs here.

## Later

- Many-sorted first-order logic and TFF input.
- Arithmetic, with its own certificate rules.
- A separate model checker before Fang reports satisfiability or countermodels.
- More of the Rust engine proved directly through Charon, Aeneas and Lean.
- Higher-order logic and THF, SMT-LIB, and checking external TSTP proofs.
- Results on the CASC divisions for first-order logic with and without equality (FNE, FEQ) and unit equality (UEQ), following the [division definitions](https://tptp.cs.miami.edu/CASC/J13/Design.html).

These are plans, not supported features. Each one needs a specification, an implementation, proofs, adversarial and differential tests, measurements and review. Unsupported input keeps failing explicitly.
