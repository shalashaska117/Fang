# Capabilities

This page describes `fang` built from the current V4 development tree. See [Usage](USAGE.md) for the build, the exact input rules and the command options, [Design](DESIGN.md) for what is proved and trusted, and the [V4 checklist](V4-CHECKLIST.md) for completed and remaining work.

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

Compiled checking accepts UTF-8 text inside comments. Syntax outside comments remains ASCII; malformed UTF-8 and NUL bytes are rejected. Kernel replay still has its separate input restrictions.

## Logic and theories

| Logic or theory | Status | Scope and limits |
| --- | --- | --- |
| Classical first-order logic, one nonempty domain | Available | CNF and FOF, through Skolemization, binder removal and clausification. The search is bounded and does not find every refutation. |
| Equality and disequality (`=`, `!=`) | Available | Built-in meaning in CNF and FOF. An ordinary predicate named `eq` has no equality meaning. |
| Conjectures | Available | Each selected conjecture is proved separately against the premises, and `Theorem` needs all of them. |
| Distinct objects | Available | Pairwise unequal constants. |
| Propositional logic | Partial | Nullary predicates and connectives through the refutation and finite-model routes. |
| Integer, rational and real arithmetic | Not supported | No interpreted numbers or arithmetic symbols. |
| Many-sorted, polymorphic and higher-order logic | Not supported | No types, sorts, lambda terms or higher-order unification. |
| Built-in theories (arrays, bit-vectors, datatypes) | Not supported | User axioms are searched like any other premises. |
| Modal, intuitionistic and temporal logics | Not supported | The semantics is classical first-order logic. |
| Finite models and countermodels | Available | `Satisfiable` and `CounterSatisfiable` require acceptance by the compiled Lean model checker. Infinite models are not supported. |

## Inference, preprocessing and search

| Component | Status | Scope and limits |
| --- | --- | --- |
| Quantified FOF preprocessing | Available | Normalization, binder removal, Skolemization and clausification, each with Lean proofs linking the clauses to the original formulas. |
| Binary resolution and factoring | Available | First-order unification with an occurs check. |
| Paramodulation and equality resolution | Available | Rewriting into non-variable positions. |
| Given-clause search | Available | Scheduled saturation strategies under the command budget. |
| Term ordering, subsumption, demodulation | Available | Used by the saturation search; any returned refutation still requires independent checking. |
| Equality factoring | Not supported | The checked prototype is not yet integrated into the installed search. |
| Splitting and learned strategy selection | Not supported | Still pending in the V4 plan. |

The low-level saturation producers also accept `--set orphan_deletion=on` and `--set max_passive=N`. Both are disabled by default; the public `fang` command does not expose these switches. They can discard useful clauses, so exhaustion after pruning remains an unknown result. The passive limit counts queued clauses, not all stored proof records or total memory. Returned certificates still require independent checking.

Low-level producers can select `--set ordering=lpo` or `--set ordering=kbo`. LPO uses the selected symbol precedence and a limit of 16,384 recursive comparison pairs; exceeding it leaves the terms incomparable. KBO remains the default, and no improvement in whole-search performance is claimed for the optional LPO strategy.

## Results and verification

| Capability | Status and meaning |
| --- | --- |
| Checked `Theorem` and `Unsatisfiable` | Available. A compiled Lean checker accepts the certificate against the captured input files before the status is printed. |
| Lean kernel replay | Partial. An opt-in mode for supported single-file premise-only input, with separate resource and syntax limits. |
| TSTP output | Partial. Available for premise-only single files and bundles, and for single files with conjectures. Cited certificates also support conjectures with includes and signed inputs with distinct objects. Fang prints one refutation document per proved conjecture. Checked finite models can be printed as `FiniteModel` documents. Rendering runs compiled Lean code; Usage lists export restrictions. |
| External TSTP proof checking | Not supported. |
| Checked `Satisfiable` and `CounterSatisfiable` | Available for finite models in compiled mode. An unsuccessful model search proves nothing. |
| Whole Rust engine verification | Not established. Selected Rust components have Aeneas proofs; the checker does not depend on the engine being correct. |

## Measurements

Performance depends on the installed build, corpus and resource limits. Historical release measurements are not measurements of the current source tree. The final benchmark reports record solved counts and compare times on matching solved sets.
