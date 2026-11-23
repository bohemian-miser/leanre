# `leanre` CLI

Python 3.11+ standard-library CLI (`pip install -e .` installs `leanre`, or invoke `python3 leanre/leanre.py`) paired with a native Rust kernel extractor (`leanre/kernel-rs/`) for reverse-engineering large Lean 4 proof trees and `lean4export` v3.1.0 archives.

## Subcommands

| Subcommand | Role & key flags |
|---|---|
| `init` | Auto-discover a Lean 4 / Lake repository and generate `leanre.toml` (`--dry-run`, `--force`, `--json`) |
| `scan` | Parallel scan of `.lean` source files into `leanre.db` (modules, imports, decls, Horn graph, hotspots; `--root auto`, `--max-hits-per-tag`) |
| `ndjson` | Stream-parse a `lean4export` v3.1.0 `.ndjson.zst` / `.gz` / `.ndjson` archive |
| `forensics` | Build snapshot reports, `workbench_bundle.json`, and `forensics_dossier.md` |
| `all` | Run `scan` + `ndjson` + `forensics` end-to-end |
| `diff` | Compare two BinDiff v1 / `forensics_report.json` snapshots |
| `kernel` | Native Rust [kernel extractor](../docs/KERNEL.md) & graph queries: `build`, `extract`, `enrich`, `verify-k3`, `validate-taint`, `slice`, `type-deps`, `cone-audit`, `callers`, `stats` (`--with-alias`, `--table`, `--continue-on-error`; prints `live` root-bitmask legend where `0`=dead and bit `1<<root_id` marks reachability per root, e.g. `live=31` across 5 roots), `anchor` (maps declarations and `Struct.field` directly to disk file:line + `--verify-md`), `hygiene` (`--cone-depth`, `--only`, `--include-noisy`, `--strict-binders`, `--semantic` for `default_zero_branch` & `le_refl_closure`, `--continue-on-error`) |
| `decompile` | Proof decompiler backing the [technical dossiers](../analysis/README.md): `resolve` (`--near`, `--exact-case`, `--continue-on-error`), `contract` (`--body`, `--include-thm`, `--preserve-lines`, `--grep`, `--fields-grep`, `-C`, `--body-lines A:B` / `N` / `LA:B`, `--deps-headers`, `--deps-max`), `producers` (`--live-only`, `--include-dead`, `--include-implications`), `readers` (`--field`, `--conjunct`), `unfold` (`--depth`), `horn` (`--have-wiring`, `--graph`, `--text`), `dom` (`--contains`, `--depth`, `--min-size`, `--with-cone`, `--project-only`, `--text`), `path`, `node`, `search`, `validate`, `spine-map` |
| `bundles` | Source-and-kernel census of 1-constructor structures, unread fields, `0`-field placeholders, `is_conditional_prop` (implication-guarded `Prop` fields), and producer/consumer sites (`--top`, `--min-fields`, `--only`, `--sort`, `--structure`, `--exact`, `--instantiations`, `--continue-on-error`, `--live-only`, `--limit`, `--include-eliminated`, `--json`) |
| `kdiff` | Kernel-exact BinDiff between two `kernel.db` snapshots (`--format {text,markdown,json}`, `--top`, `--filter`, `--annot-dir`, `--fail-on-regression`) |
| `portability` | Spec-only Mathlib-portability, external-boundary, and pairwise-overlap cone analyzer (`--targets-file`, `--no-src`, `--project-prefix`, `--tree`, `--top-boundary`, `--mega-threshold`, `--filter-mod`, `--json`) |
| `circuit` | 3-level Proof-Circuit JSON (`leanre.circuit/1`), vector `--svg`, and standalone zero-CDN pan/zoom `--html` generator: `macro` (pillars, shared diamonds, `k1n`/`k1a` motifs, islands; `--portability-json`, `--dom-threshold`), `bundle <target>` (structure / `Prop`-def IC pin-board & dangling consumers), `theorem <decl>` (binder bar, step wiring & `k1n` callee motifs; `--theme {dark,light}`, `--max-nodes`, `--exact-case`) |
| `export-site` | Export a self-contained offline static HTML explorer (`--demo`, `--decomp-dir`, `--trim-report`, `--cluster-labels`, `--portability`, `--kernel-db`, `--src-root`, `--with-bundles`, `--out`) |
| `trim` | Read-only [virtual proof stripper](../docs/TRIM.md) and disjoint bloat waterfall (`--config`, `--src`, `--kernel-db`, `--from-report`, `--json`) |
| `sighash` | Merkle [signature hashes](../docs/SIGHASH.md) (`k1n`/`k1a` kernel, `s1n`/`s1t`/`s1a` source) |
| `flirt` | [Header](../docs/FLIRT.md), [external-corpus](../docs/FLIRT_TIER2.md), and blinded-label fingerprinting (`tier1`, `tier2`, `tier3`, `cluster`) |
| `annot` | Portable JSONL [annotation packs](../docs/ANNOTATION_PACKS.md) (`validate`, `export`, `import`, `merge`, `diff`, `layers`, `reanchor`) |

## Quickstart

```bash
# Zero-toolchain demo on the bundled 5-file Lean fixture (<1s)
python3 leanre/leanre.py init --dry-run examples/tiny_demo
python3 leanre/leanre.py all --src examples/tiny_demo --ndjson examples/tiny_demo/demo.ndjson --out-dir /tmp/leanre_demo

# Run Python and Rust test suites
python3 -m unittest discover -s leanre -v
(cd leanre/kernel-rs && cargo test)

# Inspect saved trim waterfall, unread bundles, hygiene, contracts, circuits, and Markdown #L anchors
python3 leanre/leanre.py trim --from-report outputs/decomp/trim_report.json
python3 leanre/leanre.py bundles --instantiations HypsAlt --continue-on-error
python3 leanre/leanre.py kernel stats --with-alias UpperTheory.Top.VWin
python3 leanre/leanre.py kernel hygiene UpperTheory.Top.VWin --cone-depth 1 --semantic
python3 leanre/leanre.py decompile contract HypsAlt --fields-grep "covol|rRows" -C 1
python3 leanre/leanre.py decompile dom --contains ch_balance boundsMu UpperTheory.FinalTheorems.everyCharacter --text
python3 leanre/leanre.py circuit macro --svg /tmp/macro.svg --html /tmp/macro.html
python3 leanre/leanre.py kernel anchor --verify-md findings/*.md --src-root data/rh_mirror/src
python3 leanre/leanre.py annot validate annotations/
```
