# Fang

Fang is an automated theorem prover written in Rust, with independently checked
refutations.

The project is incomplete. This first experimental version accepts a restricted,
equality-free subset of TPTP CNF and produces TSTP proofs. Rust searches for a
refutation; a Lean 4 checker validates it against the original input before
Fang reports `Unsatisfiable`. FOF and equality are planned. Fang does not report SAT.

## Quick start

Use Linux or WSL with rustup-managed Rust 1.90.0, Lean 4.35.0 and Python 3.14.4.
Set `LEAN_BIN` to the directory containing `lean` and `lake`:

```sh
python3 tools/build-local.py --out .local/fang --lean-tools "$LEAN_BIN"
.local/fang/bin/fang-szs examples/problems/mortality.p \
  --artifacts .local/runs/mortality --output tstp
```

Use a new artifact directory for each run. The default checking profile replays
an input-specific theorem through Lean's kernel. TSTP rendering uses compiled
Lean code; this is not a proof of the entire Rust engine.

- [Usage](docs/USAGE.md): inputs, commands, limits and output.
- [Design and verification](docs/DESIGN.md): architecture and trust boundaries.
- [Roadmap](docs/ROADMAP.md): what comes next.

## Attribution

Fang is inspired by [Vampire](https://github.com/vprover/vampire). It is an
independent project and is not affiliated with or endorsed by the Vampire
authors. Fang contributions use [BSD-3-Clause](LICENSE); retained third-party
notices are in [LICENSES](LICENSES/).
