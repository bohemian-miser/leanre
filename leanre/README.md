# `leanre` CLI

Python 3.11+ standard-library CLI (`pip install -e .` installs `leanre`, or invoke `python3 leanre/leanre.py`) paired with a native Rust kernel extractor (`leanre/kernel-rs/`) for reverse-engineering large Lean 4 proof trees and `lean4export` v3.1.0 archives.

## Subcommands

| Subcommand | Role |
|---|---|
| `init` | Auto-discover a Lean 4 / Lake repository and generate `leanre.toml` (`--dry-run`, `--force`, `--json`) |
| `scan` | Parallel scan of `.lean` source files into `leanre.db` (modules, imports, decls, Horn graph, hotspots) |
| `ndjson` | Stream-parse a `lean4export` v3.1.0 `.ndjson.zst` / `.ndjson` archive |
| `forensics` | Build snapshot reports, `workbench_bundle.json`, and `forensics_dossier.md` |
| `all` | Run `scan` + `ndjson` + `forensics` end-to-end |
| `diff` | Compare two `forensics_report.json` snapshots |
| `kdiff` | Kernel-exact BinDiff between two `kernel.db` snapshots (`--format`, `--filter`, `--annot-dir`, `--fail-on-regression`) |
| `kernel` | Native Rust [kernel extractor](../docs/KERNEL.md) (`extract`, `enrich`, `slice`, `type-deps`, `cone-audit`, `stats`, `callers`, `anchor`, `hygiene`) |
| `portability` | Spec-only Mathlib-portability, external-boundary, and pairwise-overlap cone analyzer (`--targets-file`, `--mega-threshold`, `--json`) |
| `export-site` | Export a self-contained offline static HTML explorer from blueprints, trim reports, clusters, and optional `kernel.db` |
| `sighash` | Merkle [signature hashes](../docs/SIGHASH.md) (`k1n`/`k1a` kernel, `s1n`/`s1t`/`s1a` source) |
| `flirt` | [Header](../docs/FLIRT.md), [external-corpus](../docs/FLIRT_TIER2.md), and blinded-label fingerprinting (`tier1`, `tier2`, `tier3`, `cluster`) |
| `annot` | Portable JSONL [annotation packs](../docs/ANNOTATION_PACKS.md) (`validate`, `export`, `import`, `merge`, `diff`, `layers`, `reanchor`) |
| `decompile` | Proof decompiler backing the [technical dossiers](../analysis/README.md) (`resolve`, multi-line `contract`, `unfold --stop-at`, `horn`, batch `dom`, 1-/2-point `path`, `node`, `search`, `validate`, `spine-map`) |
| `bundles` | Source-verified census of unread structure fields, `0`-field placeholders, and producer/consumer sites (`--top`, `--only`, batch `--structure`, `--instantiations`, `--exact`, `--live-only`, `--limit`, `--sort`, `--json`) |
| `trim` | Read-only [virtual proof stripper](../docs/TRIM.md) and bloat waterfall |

## Quickstart

```bash
# Zero-toolchain demo on the bundled 5-file Lean fixture (runs in <1s)
python3 leanre/leanre.py init --dry-run examples/tiny_demo
python3 leanre/leanre.py all --src examples/tiny_demo --ndjson examples/tiny_demo/demo.ndjson --out-dir /tmp/leanre_demo

# Run Python and Rust test suites
python3 -m unittest discover -s leanre -v
(cd leanre/kernel-rs && cargo test)

# Inspect saved trim waterfall, unread bundles, kernel cones, and Markdown #L anchors
python3 leanre/leanre.py trim --from-report outputs/decomp/trim_report.json
python3 leanre/leanre.py bundles --top 20
python3 leanre/leanre.py kernel cone-audit UpperTheory.Top.VWin --project-only
python3 leanre/leanre.py kernel anchor --verify-md findings/*.md --src-root data/rh_mirror/src
python3 leanre/leanre.py annot validate annotations/
```
