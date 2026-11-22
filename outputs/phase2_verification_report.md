# Phase 2 Independent Verification Report — `leanre` ("Ghidra for Lean") & Real-Corpus Workbench

> **Verdict:** **100% PASS** (all 9/9 real-data acceptance gates, unit tests, security negative tests, JS/HTML checks, live headless Chrome `#selftest=1`, and Anti-Slop Guardrails 1–6 passed after 6 factual/precision defects were caught, patched, and independently re-verified).
> **Date:** 2026-11-21
> **Owner:** `@critic` (Verifier, Red-Teamer & Synthesis Lead)

---

## 1. Executive Scorecard

| Area / Owner | Deliverables Audited | Independent Verification Verdict | Defects Found & Disposition |
|---|---|---|---|
| **Data & Git Hygiene** (`@recon`) | [`.gitignore`](/.gitignore), [`data/MANIFEST.md`](/data/MANIFEST.md), `data/rh_mirror/`, `data/challenge.ndjson.zst` | **PASS** — commit `40e56bab`, exact `175,187` `.lean` files, compressed + unpacked SHA-256s match Sutherland's `SHA256SUMS` to the bit. | 0 defects. |
| **`leanre` CLI & Real Outputs** (`@rust-builder`) | [`leanre/`](/leanre), `outputs/leanre.db`, [`forensics_report.json`](/outputs/forensics_report.json), [`workbench_bundle.json`](/outputs/workbench_bundle.json), [`forensics_dossier.md`](/outputs/forensics_dossier.md) | **PASS (after remediation)** — `unittest` 7/7 OK, **9/9 acceptance gates PASS** to the exact digit via independent `sqlite3` queries, `leanre diff` exit 0, Guardrails 1–6 compliant. | 2 factual errors caught in `forensics.py` (#23: "4 Dirichlet" → **3 Dirichlet** + `+2` zeta RH; `362!` = **771 digits** & `Run1–4` = **131,070 steps**) → **patched (#24) & re-verified**. |
| **Interactive Workbench** (`@ui-builder`) | [`workbench/server.py`](/workbench/server.py), [`index.html`](/workbench/index.html), [`explain_kb.js`](/workbench/explain_kb.js), [`graph_view.js`](/workbench/graph_view.js), [`treemap_view.js`](/workbench/treemap_view.js), [`app.js`](/workbench/app.js), [`styles.css`](/workbench/styles.css) | **PASS (after remediation)** — `py_compile` OK, 4/4 JS clean in `jsc`, 0 HTML errors, 0 external CDNs, path-traversal & SQLi blocked, live headless Chrome `#selftest=1` **25/25 PASS (live=true)**, `file://` fallback verified. | 4 factual/precision slips caught in `explain_kb.js` (#26) → **patched (#27) & re-verified** (0 stale hits). |

---

## 2. Execution-Environment Constraints

- **Native-Binary Constraint Confirmed (Minute-1 Smoke Test, #19):** macOS binary-execution policy (`SIGKILL` exit 137) blocks executing newly compiled native Mach-O binaries on this host (confirming our Phase 1 operational warning in [`research/04_verification_and_roadmap.md`](/research/04_verification_and_roadmap.md) §1). Zero bypass was attempted.
- **Sanctioned Execution Stack (#20):** All Phase 2 code runs strictly on pre-authorized local tools: `/usr/bin/python3` (`3.9.6` stdlib only — `multiprocessing`, `sqlite3`, `http.server`), `7zz` (`26.02` native `zstd` streaming), Apple `jsc`, and Google Chrome. End-to-end real-corpus scan (`175,187` files + `51,692`-decl TCB export + forensics) runs in ~65 seconds.

---

## 3. Dataset Provenance, `.gitignore` & Checksum Audit (`@recon`)

Independently executed on local disk:

| Check | Expected (Primary Source) | Independently Measured | Result |
|---|---|---|---|
| **`.gitignore` coverage** | Exclude `data/`, `leanre/target/`, `outputs/*.db*`, `__pycache__/`, `.DS_Store` | Verified lines 1–20 of [`.gitignore`](/.gitignore) | **PASS** |
| **Mirror pinned commit** | `40e56bab026552e089d7afcfeff08d2defb9c005` (`Deicyde/riemann-hypothesis`) | `git -C data/rh_mirror rev-parse HEAD` → `40e56bab026552e089d7afcfeff08d2defb9c005` | **PASS** |
| **Mirror `.lean` file count** | `175,187` (unmodified `lean.tar.gz`, no `Challenge.lean`) | `find data/rh_mirror/src -name '*.lean' \| wc -l` → `175,187` | **PASS** |
| **`challenge.ndjson.zst` compressed SHA-256** | `c24ef99dab3556a52c7fb886e03cf22a242f3b96f82ae4cc40539e5d2f678ac6` | `shasum -a 256` → exact match (`46,881,299` bytes) | **PASS** |
| **`challenge.ndjson` unpacked SHA-256** | `bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9` | `7zz x -so data/challenge.ndjson.zst \| shasum -a 256` → exact match | **PASS** |
| **7 hotspot file:line anchors** | `Run1.lean:6`, `SmallLoop.lean:24`, `LamCopy.lean:15`, `RingSpecNormalisedCharacterEq.lean:97`, `IRRPrimeRecipSum.lean:119`, `InvFiveLogLeSumInvPrimes.lean:301`, `PrincipalizationCertificate.lean:12` | Direct `sed` / `cat` inspection of all 7 files matches verbatim | **PASS** |

---

## 4. `leanre` CLI, Acceptance Gates & Dossier Audit (`@rust-builder`)

### 4.1 Unit Tests & CLI Subcommands
- **`python3 -m unittest discover -s leanre -v`:** **7/7 OK** in `1.27 s` (includes 120-trial brute-force CHK dominator/BFS cross-validation, bottom-depth/reverse-reach exact tests, Horn header parser, comment stripping, clone normalization, synthetic scan/ndjson/diff round-trip, and live `leanre.db` acceptance-gate assertions).
- **`leanre diff` self-diff:** `python3 leanre/leanre.py diff outputs/forensics_report.json outputs/forensics_report.json` → exit 0, `identical_digests: true`, 0 count deltas across all 14 tracked structural metrics.

### 4.2 Independent SQLite Query Verification of All 9/9 Acceptance Gates
Executed directly against `outputs/leanre.db` (1.4 GB) via `/usr/bin/sqlite3`:

| # | Mandatory Acceptance Gate | Ground Truth `[C]` | Measured in `leanre.db` `[L]` | Verdict |
|---:|---|---:|---:|---|
| 1 | Total `.lean` modules | `175,187` | `175,187` | **PASS** |
| 2 | Project-to-project import edges | `753,261` | `753,261` | **PASS** |
| 3 | Hub module | `Supplements.Kernels.MainTheoremsAll` | `Supplements.Kernels.MainTheoremsAll` | **PASS** |
| 4 | Hub dominator subtree (`drew2apps` convention) | `175,185` | `175,185` | **PASS** |
| 5 | Top-level components under hub | `47,060` | `47,060` | **PASS** |
| 6 | Top-level singletons (shared) | `37,001` | `37,001` | **PASS** |
| 7 | Import-only shims | `150` | `150` | **PASS** |
| 8 | Duplicate project import lines | `308` | `308` | **PASS** |
| 9 | `challenge.ndjson.zst` declarations | `51,692` | `51,692` (`1,206,518` edges) | **PASS** |

Additional corpus metrics verified in `leanre.db`: `lines_wc = 17,374,215`, `bytes = 1,030,531,854`, `imports_mathlib = 136,003`, `zero_proj_imports = 5,927`, `max_bottom_depth = 202`, `declarations = 1,061,425`, `horn_edges = 162,961`, `forensic_hits = 670`.

### 4.3 Independent Cross-Checks of Headline Real-Data Discoveries
1. **Phase 1 Trailing-Newline Hypothesis Falsified (`[L]`):** Ran an independent Python byte-end scan over all `175,187` `.lean` files on disk → `total=175187, missing_trailing_nl=0` (`100.0%` end with `\n`). Confirms `drew2apps`'s `17,549,402` line count was an off-by-1-per-file artifact of `text.split('\n')`.
2. **TCB Semantic Surface (`[L]`):** Verified `tcb_decls` breakdown (`40,431 thm`, `10,238 def`, `969 inductive`, `46 opaque`, `4 quot`, `4 axiom`), ran an independent Python BFS over pure definition-to-definition edges from the 5 headline types → exact **`2,570`** definitions (`5.0%` of challenge), and verified `sorryAx` has `fan_in = 5` strictly on `edge_kind='value'` of the 5 `Challenge.lean` stubs (`in_rh_cone = 0, in_grh_cone = 0`).
3. **Exact Reachability Accounting (`[L]`):** Verified `in_rh_cone = 51,215` (`riemannHypothesis`), `+2` (`riemannZeta_eq_zero_re` + `RiemannZetaZerosOnLine`), `+470` (`in_grh_cone` for the 3 Dirichlet GRH theorems) = `51,687` reachable + `5` unreachable `export-targets.txt` primitives (`sorryAx`, `Nat.lor`, `Nat.xor`, `String.mk`, `String.mk._proof_1`) = `51,692`.
4. **Slowest & Timeout Hotspots (`[L]`):** Read raw source directly on disk and confirmed:
   - `DyadicPrimeIntervals/SmallLoop.lean:29` literally invokes `force (Nat.factorial 362)` (`362!`, independently verified **`771`** decimal digits) across `Run1` (`32,766` steps `[2..32768]`) and `Run2–4` (`32,768` steps each; total `131,070` steps).
   - `RingSpecNormalisedCharacterEq.lean:97–100` (`sigSpan_copy`, `40.3s` in `con-leche`) is literally a 2-line tactic body (`copy_cases h D D'; exact hs`) over massive dependent `D7`/`CopyAll` structures.
   - `InvFiveLogLeSumInvPrimes.lean:301` (`GlobalTheory.PrimeRecip.table_ok`, `17.2s`, `by decide +kernel`) is indeed a hardcoded prime witness table up to `16,900` misfiled under `AbelianVarietyTheory/Proofs/DivisorProofs/`.
   - `CutCptCopy.lean:78,82` confirmed 2 `addDecl` sites; `Imports.lean` confirmed `Term.elabTermAndSynthesize e none; g.assign (← instantiateMVars v)`; `OwnStruct.lean` confirmed `Kernel.isDefEq`.

### 4.4 Anti-Slop Guardrails 1–6 Audit of `outputs/forensics_dossier.md`
- **Guardrail 1 (4-Layer Disclaimer):** Present prominently at top of dossier.
- **Guardrail 2 (Provenance Tagging `[L]`/`[A]`/`[C]`/`[S]`/`[M]`):** Consistently applied on every section, table, and claim; zero ungrounded mathematical narrative.
- **Guardrail 3 (Real Telemetry Only):** Pinned to commit `40e56bab` and exact SHA-256 digests.
- **Guardrail 6 (No-License Compliance):** Zero wholesale `.lean` file dumps; quotes only identifiers, counts, and minimal 1-line headers.

---

## 5. `workbench/` Static, Security, API & Headless Chrome Audit (`@ui-builder`)

### 5.1 Static Code, Asset & Security Hygiene
- **`python3 -m py_compile workbench/server.py`:** **PASS**. Confirmed strictly Python 3.9 stdlib imports only (`argparse`, `collections`, `json`, `mimetypes`, `os`, `sqlite3`, `sys`, `time`, `http`, `pathlib`, `typing`, `urllib.parse`).
- **JS Syntax (Apple `jsc` `new Function(...)`):** **4/4 PASS** (`explain_kb.js`, `graph_view.js`, `treemap_view.js`, `app.js`).
- **HTML Balance & Zero External CDNs:** `index.html` has **0** unmatched/unclosed tags; **0** external CDN `src`/`href` dependencies across all 7 workbench files.
- **SQL & Filesystem Security:** Verified `server.py` binds to `127.0.0.1`, opens SQLite read-only, uses parameterized `?` queries, and never reads raw `.lean` files from `data/`.

### 5.2 Live Server API & Security Negative Test Suite (Port `18421` / `18422` against real 1.4 GB `leanre.db`)
| Test Case | Endpoint / Payload | Status | Latency | Result |
|---|---|---:|---:|---|
| Health | `GET /api/health` | `200` | `2.3 ms` | **PASS** |
| Overview | `GET /api/overview` (`modules=175,187`) | `200` | `337 ms` | **PASS** |
| Investigations | `GET /api/investigations` (4 presets) | `200` | `4.2 ms` | **PASS** |
| Search (prefix / flag / TCB / Horn) | `q=Main`, `flag=kexactB`, `q=riemannZeta&kind=tcb`, `q=EveryCharacter&kind=horn` | `200` | `2–368 ms` | **PASS** |
| Module Inspector (`Main`, `LamCopy`, TCB `riemannHypothesis`) | `GET /api/module?...` | `200` | `1.8–2.1 ms` | **PASS** |
| Subgraphs (all 4 modes) | `imports` (`5n/4e`), `horn` (`47n/58e`), `taint` (`tag:kexactB`, `39n/38e`), `tcb` (`25n/46e`) | `200` | `1.4–892 ms` | **PASS** |
| Playable Lab Bridge | `GET /prototypes/concept_map_demo.html` | `200` | `2.9 ms` | **PASS** |
| **Security: SQLi payload** | `GET /api/search?q=' OR 1=1 --` | `200` (`0` results) | — | **PASS** (parameterized) |
| **Security: Path traversal #1** | `GET /../data/rh_mirror/src/Main.lean` | `403` | `0.4 ms` | **PASS** (blocked, 0 leakage) |
| **Security: Path traversal #2** | `GET /%2e%2e/data/rh_mirror/src/Main.lean` | `404` | `0.4 ms` | **PASS** (blocked, 0 leakage) |
| **Security: Path traversal #3** | `GET /../../../../etc/passwd` | `403` | `0.3 ms` | **PASS** (blocked, 0 leakage) |

*(Note: `GET /api/module?name=Does.Not.Exist.Module` returns HTTP `200` with a JSON not-found payload rather than HTTP `404` — benign design choice for frontend error display, zero server crash.)*

### 5.3 Headless Chrome End-to-End Browser Verification
- **Live HTTP Mode (`http://127.0.0.1:18422/#selftest=1`):**
  > `SELFTEST PASS — 25 checks, 0 errors (live=true)`
- **Static `file://` Fallback Mode (`/workbench/index.html`):**
  Confirmed graceful offline fallback banner renders with exact launch command (`python3 workbench/server.py`) and zero crash.

---

## 6. Defect Remediation Log (Caught, Dispatched & Re-Verified)

All **6** factual/precision defects surfaced during independent Phase 2 verification were dispatched to owning builders, patched at the source, regenerated, and independently re-verified (`0` remaining stale strings across `leanre/`, `outputs/`, and `workbench/`):

| # | Owner | File(s) | Defect Caught by `@critic` | Fix & Re-Verification |
|---:|---|---|---|---|
| 1 | `@rust-builder` | `leanre/forensics.py:711,867` → `forensics_dossier.md`, `workbench_bundle.json` | Stated *"all 4 Dirichlet GRH theorems"* add `470` decls; `Main.lean` has **2** zeta RH theorems (`riemannHypothesis` + `riemannZeta_eq_zero_re` / `RiemannZetaZerosOnLine` = `+2`) and **3** Dirichlet GRH theorems (`+470`), summing `51,215 + 2 + 470 = 51,687` reachable + `5` unreachable = `51,692`. | Patched & regenerated (#24); independently re-verified via `grep` + `unittest`. |
| 2 | `@rust-builder` | `leanre/forensics.py:747,921` → `forensics_dossier.md`, `workbench_bundle.json` | Stated `362!` has `772` decimal digits (exact: **`771`**) and `DyadicPrimeIntervals.Run1–4` shard a `131,072`-step check into four `32,768`-step chunks (exact: **`131,070`** steps over `h = 2..131,072`; `Run1`: `32,766` steps, `Run2–4`: `32,768` each). | Patched & regenerated (#24); independently re-verified via `grep` + `unittest`. |
| 3 | `@ui-builder` | `workbench/explain_kb.js:24,138` | Inherited pre-#24 *"4 Dirichlet GRH"* phrasing for `Statements.lean` wrappers and TCB delta. | Patched to **1 zeta RH wrapper + 3 Dirichlet GRH wrappers** and exact `51,215 + 2 + 470 = 51,687` split (#27); re-verified. |
| 4 | `@ui-builder` | `workbench/explain_kb.js:127` | Inherited pre-#24 `131,072-step` / `four 32,768-step chunks` phrasing for `DyadicPrimeIntervals.Run1–4`. | Patched to `131,070-step (h = 2..131,072)` / `362! (771 digits)` / `Run1: 32,766; Run2–4: 32,768` (#27); re-verified. |
| 5 | `@ui-builder` | `workbench/explain_kb.js:38`, `workbench/server.py:1688` | Quoted approximate LOC (`RhOfRight.lean` 60 lines, `CritLine.lean` 35 lines). Disk `wc -l` is **`62`** and **`32`**. | Patched both files (#27); re-verified. |
| 6 | `@ui-builder` | `workbench/explain_kb.js:110` | Stated `run_tac in 21 files` without noting `21 = 16 run_tac + 5 BuildAid run_cmd`. | Patched to `run_tac/run_cmd in 21 files (16 run_tac + 5 BuildAid run_cmd)` (#27); re-verified via `jsc` + live Chrome `#selftest=1` (`25/25 PASS`). |

---

## 7. Quickstart: Running the Verified Phase 2 Stack

```bash
# 1. Launch the interactive "Ghidra for Lean" workbench over real 175,187-file DB + 51,692-decl TCB:
python3 workbench/server.py --port 8420
# Open http://127.0.0.1:8420/ (or http://127.0.0.1:8420/#selftest=1 to run the 25-check self-test)

# 2. Re-run the leanre test suite & real-DB acceptance gates:
python3 -m unittest discover -s leanre -v

# 3. Diff against a future simplified v2 release of Alpöge's proof:
python3 leanre/leanre.py diff \
  outputs/forensics_report.json \
  outputs/forensics_report_v2.json
```
