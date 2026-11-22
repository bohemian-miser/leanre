# `leanre` CLI

Python 3.9+ standard-library CLI paired with a native Rust kernel extractor (`leanre/kernel-rs/`) for reverse-engineering large Lean 4 proof trees and `lean4export` v3.1.0 archives.

## Subcommands

| Subcommand | Role |
|---|---|
| `scan` | Parallel scan of `.lean` source files into `leanre.db` (modules, imports, decls, Horn graph, hotspots) |
| `ndjson` | Stream-parse a `lean4export` v3.1.0 `.ndjson.zst` archive (`challenge.ndjson.zst`) |
| `forensics` | Build snapshot reports, `workbench_bundle.json`, and `forensics_dossier.md` |
| `all` | Run `scan` + `ndjson` + `forensics` end-to-end |
| `diff` | Compare two `forensics_report.json` snapshots |
| `kernel` | Native Rust [kernel extractor](../docs/KERNEL.md) (`solution.ndjson.zst` → `kernel.db`), cone slicer, `type-deps` |
| `sighash` | Merkle [signature hashes](../docs/SIGHASH.md) (`k1n`/`k1a` kernel, `s1n`/`s1t`/`s1a` source) |
| `flirt` | [Header](../docs/FLIRT.md), [external-corpus](../docs/FLIRT_TIER2.md), and blinded-label fingerprinting (`tier1`, `tier2`, `tier3`, `cluster`) |
| `annot` | Portable JSONL [annotation packs](../docs/ANNOTATION_PACKS.md) (`validate`, `export`, `import`, `merge`, `diff`, `layers`, `reanchor`) |
| `decompile` | Proof decompiler backing the [technical dossiers](../analysis/README.md) (`contract`, `unfold`, `horn`, `dom`, `path`, `node`, `search`, `validate`, `spine-map`) |
| `bundles` | Source-verified census of unread structure fields, `0`-field placeholders, and `:= True` slots (`--top`, `--only`, `--structure`, `--sort`, `--json`) |
| `trim` | Read-only [virtual proof stripper](../docs/TRIM.md) and bloat waterfall |

## Quickstart

```bash
# Inspect commands
python3 leanre/leanre.py --help

# Run Python and Rust test suites
python3 -m unittest discover -s leanre -v
(cd leanre/kernel-rs && cargo test)

# Render the saved virtual-trim waterfall and rank unread structure bundles
python3 leanre/leanre.py trim --from-report outputs/decomp/trim_report.json
python3 leanre/leanre.py bundles --top 20

# Validate portable annotation packs
python3 leanre/leanre.py annot validate annotations/
```
