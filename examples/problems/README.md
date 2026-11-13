# Small example problems

`socrates.p` says in FOF that every human is mortal and that Socrates is human, and conjectures that Socrates is mortal. Fang reports `Theorem` after the signed checker accepts a refutation of the negated conjecture.

`equality.p` says that the morning star equals the evening star and that the morning star is bright, and conjectures that the evening star is bright. Fang reports `Theorem`; the proof uses equality.

`mortality.p` gives the same facts as three CNF clauses together with the clause that Socrates is not mortal. The clauses are inconsistent, so Fang reports `Unsatisfiable`, and `--output tstp` prints the refutation.

`open-world.p` keeps only the first two clauses of `mortality.p`. The clauses have a finite model. Fang can report `Satisfiable` after the compiled Lean model checker accepts one; `--output tstp` requests its `FiniteModel` document.

Copyright (c) 2026 Pietro Pellegrino. These examples use the project's BSD 3-Clause license.
