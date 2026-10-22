# Roadmap

The minimum target is useful CNF and FOF theorem proving with checkable proofs.
The first experimental version covers a restricted, equality-free CNF fragment
with TSTP output. It is not a complete TPTP implementation or CASC entry.

## Next

- Improve CNF usability: comments, quoted names, common roles and controlled
  include handling, each with a checked link to the original problem.
- Add FOF preprocessing: Boolean formulas, quantifiers, variable scope,
  Skolemization and conjecture handling with certified transformations.
- Improve search with clause selection, simplification and more useful indexes.
  Measure time and memory before accepting performance claims.
- Make direct Rust verification reproducible through Charon, Aeneas and Lean,
  keeping its assumptions separate from independent certificate checking.

## Later

- Equality reasoning with checked superposition, equality resolution/factoring,
  term orderings and rewriting.
- Many-sorted first-order logic and TFF input.
- A separate model checker before reporting SAT or countermodels.
- Higher-order logic/THF, arithmetic, SMT-LIB and external TSTP proof checking.
- Broader CASC coverage and competitive performance on declared benchmark sets.

These are planned capabilities, not supported features. Each extension needs a
specification, implementation, proof obligations, adversarial and differential
tests, measurements and review. Unsupported inputs must keep failing explicitly.
