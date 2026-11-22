# Phase 3 — Acceptance Gates & Swarm Contract

Repo: `./` (GitHub `bohemian-miser/leanre`).
Data home (gitignored, symlinked as `data/`): `<local-data-dir>`.
Guardrails 1–6: `research/04_verification_and_roadmap.md` §2. Canonical facts: `HANDOFF.md` §3.

A gate is PASS only when the **verifier** reproduces it independently (own script or
re-run from scratch), not when the owner reports it. Numbers that cannot be reproduced
are reported as measured, with the discrepancy explained — never adjusted to fit.

## Ownership (one worktree, disjoint paths)

| Worker | Owns (only these paths) |
|---|---|
| `kernel` | `leanre/kernel-rs/`, `leanre/kernel.py`, `leanre/test_kernel.py`, `outputs/kernel/`, `outputs/kernel_report.json`, `docs/KERNEL.md` |
| `flirt` | `leanre/sighash.py`, `leanre/flirt/` (tier1, tier3), `leanre/test_flirt*.py`, `outputs/flirt/`, `docs/SIGHASH.md`, `docs/FLIRT.md` |
| `xrepo` | `leanre/flirt/tier2*`, `leanre/test_tier2.py`, `data/corpora/`, `outputs/flirt/tier2*`, `docs/FLIRT_TIER2.md` |
| `annot` | `leanre/annot.py`, `leanre/test_annot.py`, `annotations/`, `docs/ANNOTATION_PACKS.md` |
| `workbench` | `workbench/**` |
| `verifier` | `outputs/phase3_verification_report.md`, `verify/` (read-only everywhere else) |
| coordinator | `leanre/leanre.py` CLI wiring, `README.md`, `HANDOFF.md`, `.gitignore`, `docs/PHASE3_GATES.md`, pushes |

Commit only your own paths (`git add <paths> && git commit -m ... -- <paths>`; retry on
`index.lock`). Never `git add -A`, never push, never `--no-verify`, never rewrite history.

## Gates

### K — Kernel-exact graph (`solution.ndjson.zst`)
- **K1** Compressed SHA-256 `61a8938a…5381` (7,699,933,588 B) and uncompressed SHA-256
  `5ea74b91…244e` (61,570,595,788 B) both match.
- **K2** Declaration count reported *with its counting rule*, reconciled against
  `1,468,418` (`con-leche` fold records) and `1,484,733` (`nanoda` via nasqret).
- **K3** Regression on `challenge.ndjson.zst`: new extractor reproduces `51,692` decls /
  `1,206,518` edges, TCB def-cone `2,570`, `+470` with the 3 Dirichlet GRH theorems,
  `sorryAx` fan-in `5`, identical to Phase 2 `ndjson.py`.
- **K4** Exact live/dead split from roots `Main.riemannHypothesis` (+ `riemannZeta_eq_zero_re`)
  and the 3 Dirichlet GRH theorems (per-root and union); reachable axioms listed exactly;
  `sorryAx` reachability stated.
- **K5** Declaration dominator tree: fast algorithm cross-checked against a brute-force
  (node-removal reachability) oracle on ≥1,000 sampled nodes + all top-50 dominators.
  Every emitted taint path (`kexactB` / `CutCptCopy` / `decide +kernel` / `Lean.ofReduceBool`
  style) is validated edge-by-edge against the stored graph.
- **K6** Decl → `.lean` module alignment against `outputs/leanre.db`, with exact
  coverage and an explicit unmatched bucket (no silent drops).
- **K7** Full pass wall-clock + peak RSS recorded; deterministic output (two runs, same hashes).

### F — FLIRT for Lean
- **F1** Tier 1 deterministically flags the known misfile (`GlobalTheory.PrimeRecip.table_ok`
  under `AbelianVarietyTheory/Proofs/DivisorProofs/`) and reproduces the
  `39,212 / 14,165 / 11,592` namespace split of `Development.AbelianVarietyTheory`.
- **F2** Tier 2 signature DB over Mathlib v4.33.1, PrimeNumberTheoremAnd, FLT, Carleson
  (pinned commits + licenses recorded). Measured precision/recall on a held-out
  self-match control, and a false-positive rate on a shuffled/negative control.
  Every match carries its evidence (which signature, which repo@commit).
- **F3** Tier 3 prompts are provably name-blinded (test: no project folder/file/decl
  identifiers leak); labels land only in a separate AI-draft layer, never in `[L]` facts;
  blinded-vs-unblinded agreement is reported.

### A — Annotation packs
- **A1** Key = declaration name + normalized signature hash (`docs/SIGHASH.md`); an
  annotation survives a proof-body change and a rename with unchanged signature (tests).
- **A2** Export → import → export is byte-identical; packs are sorted, one JSON object per
  line, schema-validated, with mandatory provenance tag `[L]/[A]/[C]/[S]/[M]` + author + layer.
- **A3** Layers are independently toggleable; AI-draft layers are off by default and
  visually distinct; conflicting imports are reported, not silently overwritten.

### W — Workbench
- **W1** Phase 2 selftest still 25/25; new kernel-exact + FLIRT + annotation views covered
  by added selftests in headless Chrome.
- **W2** API stays read-only/parameterized for analysis DBs; annotation writes go only to
  `annotations/`; SQLi + path-traversal probes still 403/404; zero external CDNs.

### R — Regression & guardrails
- **R1** `python3 -m unittest discover -s leanre -v` green (Phase 2 7/7 + new tests);
  `cargo test` green.
- **R2** `git ls-files` contains no `.lean`, nothing under `data/` or `research/sources/`,
  no file > 5 MB, no secrets; no quoted proof source beyond identifiers/counts/1-line headers.
- **R3** Guardrails 1–6 audited on every new doc/UI string: four layers never conflated,
  provenance tags present, synthetic vs extracted separated, canonical facts respected.
