# Using Fang

The `fang` command reads a TPTP problem in CNF or FOF, searches for a refutation in Rust, and reports a result only after an independent Lean checker accepts that refutation against the original input. [Capabilities](CAPABILITIES.md) lists what is supported and [Design and verification](DESIGN.md) explains what the checker proves.

## Build

The tested host is Linux or WSL with rustup-managed Rust 1.90.0, Lean 4.35.0 and Python 3.14.4. Set `LEAN_ROOT` to the Lean 4.35.0 toolchain directory; with elan it is `~/.elan/toolchains/leanprover--lean4---v4.35.0`.

```sh
python3 tools/fetch-v8-backend.py --work .local/backend --lean-toolchain "$LEAN_ROOT"
python3 tools/build-v8-local.py --out .local/fang --lean-toolchain "$LEAN_ROOT" \
  --packages .local/backend/project/.lake/packages --lean-work /var/tmp/lean-build
export PATH="$PWD/.local/fang/bin:$PATH"
```

`fetch-v8-backend.py` needs network access. It clones Aeneas and its Lake packages at the revisions in `lean-v8/lake-manifest.json`, downloads the prebuilt mathlib cache and checks every package against `tools/v8_szs/backend-pins.json`. A missing or different cache stops it; mathlib is never built from source.

`build-v8-local.py` builds every binary from the repository: the Rust search engine and producers from `crates/`, and the Lean checkers and TSTP exporters from `lean-v8/`. It first checks every source against the pinned lists in `tools/v8_szs/`. The Lean build checks the backend packages before and after building, requires the exact import closure of each executable and reruns the axiom audits of the proof gates, which allow only `propext`, `Classical.choice` and `Quot.sound`. It takes about 20 minutes and close to 4 GiB of memory. The `--out`, `--work` and `--lean-work` directories must be new. The installation carries `LICENSE` and `LICENSES/`.

`fang --self-check` hashes every installed file and adapter source against the installation record, then exits without reading any input.

The restricted CNF and ground-FOF commands of the first release stay available as profiles. Build them with `python3 tools/build-fof-local.py --out .local/fang-v1 --lean-tools "$LEAN_ROOT/bin"` and pass `--older .local/fang-v1` to `build-v8-local.py`. `fang --profile cnf` and `fang --profile ground-fof` then run those commands with their own options and defaults (`fang --profile cnf --help`). Without `--older` the two profiles are not available.

## Run

```sh
fang examples/problems/socrates.p
fang examples/problems/mortality.p --output tstp
fang problem.p --tptp-root "$TPTP"
fang problem.p --wall-seconds 300 --memory-mib 8192
fang help
```

A run prints three comment lines. For `socrates.p`:

```
% Fang profile: v8, signed bundle (conjectures or other non-axiom roles)
% fang: checked by the compiled Lean checker (default mode; compiler and runtime trusted)
% SZS status Theorem for fang_a6a40b540a9238cb9ed43cee
```

The first line names the checking path the input took, the second the checking mode and what it trusts, and the third the SZS status. Each run keeps its captured input, candidate certificates, logs and manifest in a new directory, by default under `.local/runs/` in the current directory; `--artifacts PATH` chooses another directory, which must not exist. Run data stays local.

## Accepted input

Fang reads TPTP `cnf` and `fof` statements with equality: comments, quoted and integer names, all eight FOF connectives, `$true` and `$false`, `include` directives with or without a name selection, annotations, and distinct objects (`"double quoted"`), which are pairwise unequal. The roles `axiom`, `hypothesis`, `definition`, `lemma`, `theorem` and `corollary` are premises, `conjecture` is a goal and `negated_conjecture` is an already negated input.

An include path is resolved against the including file's directory first and then against `--tptp-root`, which defaults to the `TPTP` environment variable. A missing or cyclic include is an input error.

Fang rejects as `Inappropriate`: `tff`, `thf` and other formats; the roles `assumption`, `plain`, `type`, `interpretation` and `logic`, and subroles; input that has both a conjecture and a negated conjecture; numbers used as terms; and the arithmetic and typed defined symbols such as `$sum`, `$less` and `$distinct`. Numbers in annotations and integer statement names are fine. A quoted name such as `'$less'` is an ordinary symbol.

## Checking

For every input the default is `--check compiled`: only acceptance by a compiled Lean checker gives a positive status, and the Lean compiler, its runtime and the operating system are trusted. The input decides the checking path:

- A single file with premises only goes to the single-file checker.
- Premise-only input with includes, distinct objects or annotations goes to the bundle checker, which reads every file of the bundle.
- Input with a conjecture or another non-axiom role goes to the signed checker. It lists the selected conjectures and checks one certificate per conjecture, each a refutation of the premises with that conjecture negated.

Before running a path, `fang` hashes the adapter sources and the binaries of that path and checks them against the installation; after the run it checks that they were not replaced.

`--check kernel` replays the check in the Lean kernel for single-file premise-only input. It is opt-in and needs at least `--wall-seconds 600 --memory-mib 4096 --max-artifact-bytes 1073741824`; below them it is refused before the input is read. Only a kernel-checked answer gives a result. A ResourceOut, Timeout or MemoryOut keeps its name and every other kernel outcome is an Error. Bundle and conjecture input and `--output tstp` are refused with `--check kernel`. It is slow: on the 16 small test inputs of the release campaign a kernel run took 35 to 175 seconds and up to 3.2 GiB of memory. One of them, a problem with a biconditional, stopped with Timeout because one proof phase passed its 60-second limit, and inputs like it can do the same; the next version splits that phase. Each kernel run keeps 17 to 51 MiB of records under the installation's `kernel/run/` directory. Nothing falls back from one mode to the other.

## Statuses

| Status | Exit | Meaning |
| --- | --- | --- |
| `Theorem` | 0 | The input selects at least one conjecture and every selected conjecture has an accepted certificate. |
| `Unsatisfiable` | 0 | The input has no conjecture and its refutation was accepted. |
| `GaveUp` | 2 | The search ended without a refutation. This says nothing about the problem. |
| `InputError` | 3 | The input is not valid TPTP, or an include is missing or cyclic. |
| `Inappropriate` | 4 | The input uses something Fang does not support. |
| `ResourceOut` | 5 | A search, checker or size limit was reached. With a conjecture, running out of time or memory is also reported this way. |
| `Error` | 6 | Something failed, including a checker rejecting a candidate. This is never a result. |
| `Timeout`, `MemoryOut` | 7, 8 | The command reached its deadline or its memory limit. |
| `Forced` | 9 | The run was cancelled from outside. |

Fang never reports `Satisfiable` or `CounterSatisfiable`, and it never reports a partial set of proved conjectures.

## TSTP output

With `--output tstp`, after the checker accepts, `fang` prints a `CNFRefutation` document between `% SZS output start` and `% SZS output end` lines. Its leaves are the original statements with `file(...)` sources, followed by the preprocessing, clausification and inference steps down to `$false`. This works for single files and bundles without a conjecture, and for a single file with conjectures: once every selected conjecture is proved, Fang prints one document per conjecture, in index order, each between its own SZS output lines, and each refuting the premises together with that conjecture negated. Input that has conjectures and include directives keeps its status and gets no document. For a single file the exporters handle at most 1,000 statements. If the export fails, for any conjecture, or runs out of time, the status stays, no document is printed and one line on standard error says why. If the exporter breaks one of the command's own integrity rules (for example, it leaves a process running) or the run is cancelled, the status becomes `Error` or `Forced` instead; it never becomes a different positive status. Treat a document as complete only after the closing `SZS output end` line and a successful exit.

## Limits

| Option | Default | Meaning |
| --- | --- | --- |
| `--wall-seconds N` | `60` | Deadline for the whole command, from `0.25` to `86400`. |
| `--memory-mib N` | `2048` | Sampled memory limit for the command and its processes, from `16` to `1048576`. Sampling can miss brief peaks. |
| `--max-input-bytes N` | `1048576` | Bytes read from one input file; the checkers cap it at 1 MiB. |
| `--max-certificate-bytes N` | `1048576` | Bytes of one candidate certificate; the checkers cap it at 1 MiB. |
| `--max-solution-bytes N` | `16777216` | Bytes of the TSTP document, at most 16 MiB. |
| `--max-log-bytes N` | `4194304` | Bytes kept from each child output stream. |
| `--max-artifact-bytes N` | `268435456` | Bytes kept in the run directory. |

The time and memory limits cover the whole command, every conjecture included. The checkers also have fixed limits per problem: 7,081 function and constant symbols, 5,807 predicate symbols and 4,703 Skolem symbols. A bundle has at most 64 files, an include depth of 16, 1 MiB per file and 4 MiB in total. Input past one of these limits ends in `ResourceOut`. The search keeps at most 1,000 clauses, so a problem that clausifies to more than 1,000 clauses cannot be solved in this release; it ends in `ResourceOut` or `GaveUp`.

Expect `ResourceOut` or `GaveUp` on most problems of realistic size. In the release measurements Fang proved 2 of 111 sampled TPTP problems, against 61 for Vampire. A positive answer is always checked; `ResourceOut` and `GaveUp` say nothing about the problem.

## Development

```sh
cargo test --workspace
python3 tools/check-v8-sources.py
```

`cargo test` runs the Rust tests of the engine and producers. `check-v8-sources.py` compares the Rust and Lean sources with the pinned lists that the installer uses. The Rust producers on their own print unchecked candidates; use `fang` for checked results.
