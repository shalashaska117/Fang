# TSTP text proofs

These Lean 4 proofs cover the actual exporter in
[`lean/TstpExport.lean`](../../lean/TstpExport.lean) for Fang's supported,
equality-free axiom CNF fragment. The Rust search produces a certificate; the
exporter decodes and checks that certificate before rendering a derivation.

`FinalComposition.lean` proves `export_complete_text`. A successful export has
an ordered typed derivation, exact parent and substitution metadata, original
input leaves up to variable renaming, a uniquely parsed row sequence and a final
empty clause. The theorem connects these rows to the original parsed problem.
`FinalAudit.lean` checks its full type and reports its Lean axioms.

Run the independent checker and TSTP proof suites from the repository root:

```sh
cargo build --release --locked --offline -p fang-install
target/release/fang-check-suite --with-tstp \
  --out /absolute/path/to/fresh-proof-output . "$LEAN_ROOT/bin/lean"
```

Use Linux or WSL, set `LEAN_ROOT` to the Lean 4.35.0 toolchain directory, and
choose a new output directory outside the source tree. The Rust runner copies
and hashes the source files, compiles the import graph in a fresh native
workspace and audits the axioms reported by each module. It includes these
45 TSTP modules and the ground-FOF text proofs, alongside the independent
checker suite. `sources.json` records the identities of the TSTP modules.
The release verification separately checks the exact 62 declarations of the
three TSTP audit modules. The general suite runner audits the declarations
present in the sources supplied to it.

No historical experiment directory or downloaded theorem-proving library is
needed to compile these proofs.
Lean checks these statements about the Lean definitions. Rust search correctness,
native compilation, process execution and delivery of the printed bytes are
separate obligations. The compiled checker profile performs no problem-specific
kernel replay. The kernel profile checks the captured input and certificate;
it does not turn compiled exporter output into a problem-specific kernel proof
of those printed bytes. Neither profile certifies SAT models or unsupported
input formats.

The trusted boundary includes Lean's kernel and permitted standard axioms, the
meaning of the encoded logic, the pinned toolchain and the recorded execution
environment. See [`docs/DESIGN.md`](../../docs/DESIGN.md) for the
verification boundary of the complete program.
