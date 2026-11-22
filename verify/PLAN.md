# Phase 3 verification plan (verifier-owned)

Rule: a gate is PASS only when reproduced here, by re-running from scratch or by an
independent implementation in this directory. Worker-reported numbers are inputs to check,
never evidence. Unexplained discrepancy = FAIL or OPEN. Nothing in `verify/` imports from
`leanre/` (except where a gate is explicitly "re-run the owner's tests").

Big intermediates go to `verify/out/` (gitignored). Thread cap ~16.

| Gate | Independent check | Script |
|---|---|---|
| Baseline | 7/7 unittest; 9 Phase-2 gates recomputed from raw edge tables with a node-removal oracle; selftest on spare port; mirror count + pinned SHA; challenge SHA-256 ×2 | `baseline_phase2.py`, `selftest_workbench.sh` |
| K1 | own `sha256sum` of the `.zst` + own `zstd -dc --long=31 \| sha256sum` + byte counts (`wc -c`) | `k1_sha.sh` |
| K2 | own streaming parser: records vs constants, per-kind; reconcile 1,468,418 / 1,484,733 by rule, not by tuning | `oracle_ndjson.py` (full export) |
| K3 | own parser on challenge → 51,692 / 1,206,518 / 2,570 / +470 / sorryAx 5, set-equality of decls and typed edges with Phase 2; then set-equality with the Rust extractor's challenge output | `oracle_ndjson.py`, `k3_challenge_check.py`, `kernel_db_check.py` |
| K4 | own BFS on (a) kernel.db edges, (b) the verifier's own edge set from the full export; per-root + union live/dead; axioms; sorryAx | `kernel_db_check.py` |
| K5 | node-removal idom oracle on ≥1,000 sampled nodes + top-50 dominators (dominated-set size); every taint path edge-checked against stored edges AND against the verifier's edges | `graph_oracle.py`, `kernel_db_check.py` |
| K6 | recount coverage + unmatched bucket: matched + unmatched == total; spot-check a sample of alignments against the mirror on disk | `kernel_db_check.py` |
| K7 | re-run the extractor twice under `/usr/bin/time -v`; compare output hashes | manual, receipts in report |
| F1 | own scan of the mirror for the namespace split of `Development/AbelianVarietyTheory` and the misfile; compare to Tier-1 tables | `f1_check.py` |
| F2 | pinned commits resolve (`git rev-parse` in data/corpora), licenses present; recompute precision/recall/FPR from the match table and control definitions; inspect a random sample of matches by hand; check held-out split is really held out | `f2_check.py` |
| F3 | own grep of every Tier-3 prompt for any project folder/file/declaration identifier (token list built from leanre.db + mirror paths); labels only in AI-draft layer | `f3_check.py` |
| A1–A3 | own round-trip (export→import→export bytes), schema fuzz (missing tag/author/layer must be rejected), key survival under body change + rename, conflict import | `a_check.py` |
| W1 | own headless Chrome run on spare port; count checks; confirm the 25 Phase-2 checks still present; views without DBs degrade | `selftest_workbench.sh` |
| W2 | own SQLi + traversal probes on every endpoint enumerated from server.py; write probes outside `annotations/`; CDN grep; bind address | `w2_probe.py` |
| R1 | re-run unittest + cargo test from a clean state | manual |
| R2 | tracked + untracked-not-ignored tree: paths, sizes, secrets, internal hostnames, verbatim mirror lines | `audit_tree.py --leak` |
| R3 | read every new doc / UI string: four layers, tags, synthetic banners, canonical facts (grep list of forbidden phrasings + manual read) | `r3_grep.sh` + manual |

Canonical-fact tripwires (grep): "automorphy lifting", "4 Dirichlet", "Extended RH"/"ERH"
claimed, "RH is proved"/"proves RH"/"proof of RH" unqualified, `1,468,418`/`1,484,733`
without checker name, Masullo conflation, "first".
