# V4 strategy corpora

These memberships were fixed on 2026-11-14 before any strategy runs on them. They are inputs for work on V4, not benchmark results. The original 1,536-occurrence V3 comparison remains a separate development and regression set; the final comparison must retain its repeated occurrences.

| Split | Problems | CNF | FOF |
| --- | ---: | ---: | ---: |
| Training | 256 | 142 | 114 |
| Validation | 64 | 32 | 32 |
| Held-out evaluation | 256 | 114 | 142 |

The `.txt` files list every selected filename. The `.tsv` files also identify its family and location in the archive. All source bytes come from `TPTP-v9.3.1.tgz`, SHA-256 `8e9462d9443a2250000224cf4f7002a64ea02cbe07fa5cdcdecfd0fe8cd81f03`.

## Selection

The selector groups filenames by their domain and problem number, such as `CSR114`. Different encodings and versions with that prefix belong to the same group. It considers CNF and FOF filenames only, chooses one representative per group, and excludes all groups found in the [published V3 problem list](https://github.com/shalashaska117/Fang/releases/download/v0.3.0-alpha.1/fang-v3-vs-vampire-problems.txt). That list contains 1,361 TPTP occurrences and 1,346 distinct TPTP filenames; its SHA-256 is `9d0852c809261597680c9a006ed0625c5d6b91f71572a13068c54a9efa81cf3b`.

The six explicit V4 targets `CSR114`, `CSR116`, `HWV116`, `COM146`, `COM123` and `CSR239` are also excluded. The combined exclusion list contains 1,186 groups. Local synthetic fixtures do not enter these splits.

Selection uses SHA-256 with seed `fang-v4-corpus-20261114-v1`. The first hash byte modulo eight assigns groups to training (0-3), validation (4) or held-out evaluation (5-7). Separate hashes choose a group's representative and rank the groups within each split. The first 256, 64 and 256 groups are retained, respectively. Archive order does not affect membership. The [safe Rust selector](selector/src/main.rs) defines the exact byte strings and tie-breaking rules.

These are hash samples of groups, without stratification by difficulty, satisfiability or equality. Different groups can share axiom files; no semantic deduplication is claimed. Unsupported inputs and resource failures must remain in the outcomes. They must not be replaced with easier problems.

## Use

Training outcomes may select strategy configurations and slice lengths. Validation may check those choices before the final freeze. The 256 held-out inputs must remain unused for tuning; freeze the selected schedule before running them. At membership freeze, only training and validation inputs had been extracted, and no strategy outcomes existed for any of the three splits.

The final report must distinguish the historical comparison from held-out evaluation and retain the requested three Fang checking modes, the pinned Vampire baseline, complete problem lists and per-occurrence timings. A result on these samples does not establish a general SOTA claim.

## Reproduction

Verify the two hashes above before using the archive and historical list. From the repository root, with the Rust toolchain installed:

```sh
tar -tzf TPTP-v9.3.1.tgz > members.txt
cargo run --locked --release \
  --manifest-path benchmarks/v4-corpus/selector/Cargo.toml -- \
  members.txt fang-v3-vs-vampire-problems.txt regenerated-membership
```

The output directory must not exist. Compare the generated membership files with this directory. `manifest.json` records their hashes and the selector source hashes. Its two tests cover variant grouping, typed-name rejection, exclusion, disjointness and independence from archive order. The published selector reproduced all eight membership files byte for byte.
