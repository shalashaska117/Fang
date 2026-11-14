# Roadmap

Version 3 covers TPTP CNF and FOF with equality, checked refutations and finite models, and TSTP output within the export scope described in [Usage](USAGE.md). Compiled Lean checking remains the default. Kernel replay is opt-in for supported refutations; the explicit unchecked mode labels its results.

## Version 4

The next version targets competitive first-order reasoning on FOF and CNF, including equality, unit equality and effectively propositional problems. Work includes broader strategy schedules, AVATAR splitting, learned selection, control of the passive clause set, lower runtime overhead and support for larger theories. Infinite-model satisfiability and the remaining signed-bundle refutation export gaps belong here.

Changes are evaluated against Vampire on fixed corpora with matching resource limits. Solved counts and timings on common solves are reported separately, with checking and requested output included.

The [version 4 work plan](V4-PLAN.md) lists the planned changes, their validation requirements and the first integration milestones.

## Later versions

- Version 5: FNT and TFN, including typed first-order input without arithmetic.
- Version 6: THF and SLH, for higher-order reasoning.
- Version 7: TFA, typed first-order arithmetic.
- Later work: SMT-LIB, arrays, datatypes and induction.

These are plans, not supported features. External proof checking through PRV/ProoVer is outside this roadmap. Unsupported input continues to receive an explicit refusal.
