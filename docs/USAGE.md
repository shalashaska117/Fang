# Using Fang

The `fang` command reads a TPTP problem in CNF or FOF and searches for a refutation or finite model in Rust. By default, an independent Lean checker must accept the result against the original input. [Capabilities](CAPABILITIES.md) lists what is supported and [Design and verification](DESIGN.md) explains what the checker proves.

## Build

The tested host is Linux or WSL with rustup-managed Rust 1.90.0 and Lean 4.35.0. Set `LEAN_ROOT` to the Lean 4.35.0 toolchain directory; with elan it is `~/.elan/toolchains/leanprover--lean4---v4.35.0`.

```sh
cargo build --release --locked --offline -p fang-install -p fang-source-checks
target/release/fang-fetch-v8-backend --work .local/backend --lean-toolchain "$LEAN_ROOT"
target/release/fang-build-v8-local --out .local/fang --lean-toolchain "$LEAN_ROOT" \
  --packages .local/backend/project/.lake/packages --lean-work /var/tmp/lean-build
export PATH="$PWD/.local/fang/bin:$PATH"
```

`fang-fetch-v8-backend` needs network access. It clones Aeneas and its Lake packages at the revisions in `lean-v8/lake-manifest.json`, downloads the prebuilt mathlib cache and checks every package against `tools/v8_szs/backend-pins.json`. A missing or different cache stops it; mathlib is never built from source.

`fang-build-v8-local` builds every binary from the repository: the Rust search engine and producers from `crates/`, and the Lean checkers and TSTP exporters from `lean-v8/`. It first checks every source against the pinned lists in `tools/v8_szs/`. The Lean build checks the backend packages before and after building, requires the exact import closure of each executable and reruns the axiom audits of the proof gates, which allow only `propext`, `Classical.choice` and `Quot.sound`. The `--out`, `--work` and `--lean-work` directories must be new. The installation carries `LICENSE` and `LICENSES/`.

`fang --self-check` verifies the installed launcher and the files pinned by its capability against the installation records, then exits without reading any input.

The restricted CNF and ground-FOF commands of the first release stay available as profiles. Build them with `target/release/fang-build-local --fof --out .local/fang-v1 --lean-tools "$LEAN_ROOT/bin"` and pass `--older .local/fang-v1` to `fang-build-v8-local`. `fang --profile cnf` and `fang --profile ground-fof` then run those commands with their own options and defaults (`fang --profile cnf --help`). Without `--older` the two profiles are not available.

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
% SZS status Theorem for socrates
```

The first line names the checking path the input took, the second the checking mode and what it trusts, and the third the SZS status. The problem name after `for` is the input file's name without a trailing `.p`; a file name without that ending is used as it is. The same name follows `for` in the SZS output lines around a TSTP document. Each run keeps its captured input, candidate certificates, logs and manifest in a new directory, by default under `.local/runs/` in the current directory; `--artifacts PATH` chooses another directory, which must not exist. Run data stays local.

## Accepted input

Fang reads TPTP `cnf` and `fof` statements with equality: comments, quoted and integer names, all eight FOF connectives, `$true` and `$false`, `include` directives with or without a name selection, annotations, and distinct objects (`"double quoted"`), which are pairwise unequal. The roles `axiom`, `hypothesis`, `definition`, `lemma`, `theorem` and `corollary` are premises, `conjecture` is a goal and `negated_conjecture` is an already negated input.

In the current V4 development build, comments may contain UTF-8 text. Syntax outside comments remains ASCII. Malformed UTF-8 and NUL bytes are rejected. This frontend extension is qualified for compiled checking; kernel replay retains its separate input restrictions.

An include path is resolved against the including file's directory first and then against `--tptp-root`, which defaults to the `TPTP` environment variable. A missing or cyclic include is an input error.

A name selection filters the included file's whole expansion, including formulas from nested includes. A selected name that is missing or names more than one formula causes `InputError`. This follows the [TPTP include rule](https://tptp-manual.tptp.org/home). The Vampire 5.1.0 build at commit `b75190a4b` used in the retained comparison filters the named file's own formulas, so nested selections can produce different answers.

Fang rejects as `Inappropriate`: `tff`, `thf` and other formats; the roles `assumption`, `plain`, `type`, `interpretation` and `logic`, and subroles; input that has both a conjecture and a negated conjecture; numbers used as terms; and the arithmetic and typed defined symbols such as `$sum`, `$less` and `$distinct`. Numbers in annotations and integer statement names are fine. A quoted name such as `'$less'` is an ordinary symbol.

## Checking

For every input the default is `--check compiled`: only acceptance by a compiled Lean checker gives a positive status, and the Lean compiler, its runtime and the operating system are trusted. The input decides the checking path:

- A single file with premises only goes to the single-file checker.
- Premise-only input with includes, distinct objects or annotations goes to the bundle checker, which reads every file of the bundle.
- Input with a conjecture or another non-axiom role goes to the signed checker. It lists the selected conjectures and checks one certificate per conjecture, each a refutation of the premises with that conjecture negated.

At startup, `fang` verifies the installed launcher and capability. Each selected binary must match its full content hash before its first execution. Before reporting a positive status, Fang checks that the hashed files still have the same device, inode, size and modification/change timestamps. This final check compares file identity; it is not a second content hash.

When refutation search leaves enough time, compiled mode can try the finite-model finder. A model gives `Satisfiable` or `CounterSatisfiable` only after the compiled Lean model checker accepts it. Kernel mode does not use this model path.

`--check none` reports the producer's refutation result without a checker. Each run explicitly says it is unchecked. This mode does not use the model finder and cannot be combined with `--output tstp`.

`--check kernel` replays the check in the Lean kernel for single-file premise-only input. It is opt-in and needs at least `--wall-seconds 600 --memory-mib 4096 --max-artifact-bytes 1073741824`; below them it is refused before the input is read. Only a kernel-checked answer gives a result. A ResourceOut, Timeout or MemoryOut keeps its name and every other kernel outcome is an Error. Bundle and conjecture input and `--output tstp` are refused with `--check kernel`. Kernel replay compiles and checks a proof for each input, so it costs more than compiled checking. Its proof phases have separate resource guards within the whole command budget. A run can exhaust those guards even when the input is inside the byte and syntax limits. Nothing falls back from one mode to the other.

## Statuses

| Status | Exit | Meaning |
| --- | --- | --- |
| `Theorem` | 0 | The input selects at least one conjecture and every selected conjecture has an accepted certificate. |
| `Unsatisfiable` | 0 | The input has no conjecture and its refutation was accepted. |
| `Satisfiable` | 0 | The compiled Lean model checker accepted a finite model of the input. |
| `CounterSatisfiable` | 0 | The compiled Lean model checker accepted a finite model that makes the premises true and a selected conjecture false. |
| `GaveUp` | 2 | The search ended without a checked refutation or finite model. This says nothing about the problem. |
| `InputError` | 3 | The input is not valid TPTP, or an include is missing or cyclic. |
| `Inappropriate` | 4 | The input uses something Fang does not support. |
| `ResourceOut` | 5 | A search, checker or size limit was reached. With a conjecture, running out of time or memory is also reported this way. |
| `Error` | 6 | Something failed, including a checker rejecting a candidate. This is never a result. |
| `Timeout`, `MemoryOut` | 7, 8 | The command reached its deadline or its memory limit. |
| `Forced` | 9 or signal-dependent | The run was cancelled from outside. A shell normally reports 143 for SIGTERM or 130 for SIGINT when the outer process ends by that signal; the retained run manifest records `Forced`. |

The acceptance descriptions above apply to checked modes. With `--check none`, `Theorem` and `Unsatisfiable` describe unchecked producer results. Fang never reports a partial set of proved conjectures. The model finder searches finite domains; failure to find a model does not prove unsatisfiability.

## TSTP output

With `--output tstp`, an accepted refutation can produce a `CNFRefutation` document. Its leaves name the original statements with `file(...)` sources, followed by preprocessing and inference steps down to `$false`. A checked finite model can produce a `FiniteModel` document. Each document is enclosed by matching `% SZS output start` and `% SZS output end` lines.

Refutation documents are supported for premise-only single files and bundles, and for supported single files with conjectures. The cited-certificate exporter also handles conjectures with includes and signed inputs with distinct objects, preserving the original file and statement identities. Fang prints one document per proved conjecture, in index order. Named, unnamed and cited exporters have different syntax and resource limits; acceptance by a checker does not guarantee that the corresponding exporter can print the result.

An unsupported export or ordinary exporter failure keeps the checked status and writes a reason to standard error. An integrity failure can instead change the status to `Error`, and cancellation to `Forced`. A positive status alone is not a complete proof or model document: require the closing output line and a successful exit.

## Limits

| Option | Default | Meaning |
| --- | --- | --- |
| `--wall-seconds N` | `60` | Deadline for the whole command, from `0.25` to `86400`. |
| `--memory-mib N` | `2048` | Sampled memory limit for the command and its processes, from `16` to `1048576`. Sampling can miss brief peaks. |
| `--max-input-bytes N` | `1048576` | Bytes read from one input file; the checkers cap it at 1 MiB. |
| `--max-certificate-bytes N` | `5081233` | Bytes of one candidate certificate; the refutation checkers cap it at 5,081,233 bytes and the model checker at 1 MiB. |
| `--max-solution-bytes N` | `16777216` | Bytes of the TSTP document, at most 16 MiB. |
| `--max-log-bytes N` | `4194304` | Bytes kept from each child output stream. |
| `--max-artifact-bytes N` | `268435456` | Bytes kept in the run directory. |

The time and memory limits cover the whole command, every conjecture included. The checkers also have fixed limits per problem: 83,412 function and constant symbols, 74,338 predicate symbols and 30,675 Skolem symbols. These symbol limits also apply to bundles.

A bundle has no separate limit on the number of files; its include depth is at most 16, with 1 MiB per file and 4 MiB in total. Fang follows at most 1,024 include directives, counting each repeated expansion. The selected formulas of any input may use at most 64 different distinct objects, since each pair adds a disequality clause. Input past one of these limits ends in `ResourceOut`.

The saturation search is limited by time and memory; there is no global 1,000-clause search cap. Preprocessing, checkers and exporters retain separate structural and operation limits. The named formula decoder is configured for height 2,984; unnamed exporters and kernel replay have narrower scope. Resources can run out before a configured structural limit is reached.

`ResourceOut` and `GaveUp` say nothing about whether the problem is satisfiable. Compare performance only using results from the same installed build, input corpus and resource limits.

## Development

```sh
cargo test --workspace
target/release/fang-check-sources
```

`cargo test` runs the Rust tests of the engine and producers. `fang-check-sources` compares the Rust and Lean sources with the pinned lists that the installer uses. The Rust producers on their own print unchecked candidates; use `fang` for checked results.
