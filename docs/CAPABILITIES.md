# Capabilities

This page describes the second release of the `fang` command. See [Usage](USAGE.md) for the build, the exact input rules and the command options, [Design](DESIGN.md) for what is proved and trusted, and [Roadmap](ROADMAP.md) for what comes next.

- Available: usable through `fang` for the stated scope.
- Partial: only the listed subset is accepted.
- Not supported: rejected with an explicit status.

## Input formats

| Format | Status | Scope |
| --- | --- | --- |
| TPTP CNF | Available | With and without equality. Comments, quoted and integer names, includes with selections, annotations, distinct objects and the roles listed in Usage. |
| TPTP FOF | Available | With and without equality, all eight connectives, `$true` and `$false`, nested quantifiers, conjectures and the same file-level features as CNF. |
| TPTP TFF, THF | Not supported | `Inappropriate`. No typed or higher-order input. |
| SMT-LIB | Not supported | No parser. |

Numbers used as terms, arithmetic and typed defined symbols (`$sum`, `$less`, `$distinct` and the rest), and the roles `assumption`, `plain`, `type`, `interpretation` and `logic` are rejected as `Inappropriate`. No construct with a defined meaning is read as an ordinary symbol.

## Logic and theories

| Logic or theory | Status | Scope and limits |
| --- | --- | --- |
| Classical first-order logic, one nonempty domain | Available | CNF and FOF, through Skolemization, binder removal and clausification. The search is bounded and does not find every refutation. |
| Equality and disequality (`=`, `!=`) | Available | Built-in meaning in CNF and FOF. An ordinary predicate named `eq` has no equality meaning. |
| Conjectures | Available | Each selected conjecture is proved separately against the premises, and `Theorem` needs all of them. |
| Distinct objects | Available | Pairwise unequal constants. |
| Propositional logic | Partial | Nullary predicates and connectives. No SAT solver and no satisfiability result. |
| Integer, rational and real arithmetic | Not supported | No interpreted numbers or arithmetic symbols. |
| Many-sorted, polymorphic and higher-order logic | Not supported | No types, sorts, lambda terms or higher-order unification. |
| Built-in theories (arrays, bit-vectors, datatypes) | Not supported | User axioms are searched like any other premises. |
| Modal, intuitionistic and temporal logics | Not supported | The semantics is classical first-order logic. |
| Models and countermodels | Not supported | No model finder. Fang never reports `Satisfiable` or `CounterSatisfiable`. |

## Inference, preprocessing and search

| Component | Status | Scope and limits |
| --- | --- | --- |
| Quantified FOF preprocessing | Available | Normalization, binder removal, Skolemization and clausification, each with Lean proofs linking the clauses to the original formulas. |
| Binary resolution and factoring | Available | First-order unification with an occurs check. |
| Paramodulation and equality resolution | Available | Rewriting into non-variable positions. |
| Given-clause search | Available | One bounded strategy with a simple clause selection. |
| Term ordering, subsumption, demodulation | Not supported | Planned for the next version; their absence is the main reason the search is weak. |
| Splitting, strategy portfolios, parallel search | Not supported | |

## Results and verification

| Capability | Status and meaning |
| --- | --- |
| Checked `Theorem` and `Unsatisfiable` | Available. A compiled Lean checker accepts the certificate against the captured input files before the status is printed. |
| Lean kernel replay | Partial. An opt-in mode for single-file premise-only input. In the release campaign 15 of 16 test inputs were kernel-checked and one stopped with Timeout. |
| TSTP output | Partial. Available for single files and bundles without a conjecture, and for single files with conjectures, one document per conjecture. Not available for input that has conjectures and include directives. Rendering runs compiled Lean code. |
| External TSTP proof checking | Not supported. |
| Satisfiability or countermodels | Not supported. A search that ends without a refutation is `GaveUp` or a resource status. |
| Whole Rust engine verification | Not established. Selected Rust components have Aeneas proofs; the checker does not depend on the engine being correct. |

## Measured results

On 111 TPTP problems sampled from 37 domains (CNF and FOF, with and without equality, with conjectures and with includes), run with the default limits of 60 seconds and 2 GiB, Fang proved 2 and Vampire proved 61. On most of these problems Fang's search stops early at its bounds. Every positive answer Fang gives is checked, so the gap is in the search. Across all 286 problems of that run, which add 175 smaller test problems to the 111, Fang and Vampire never gave opposing answers.
