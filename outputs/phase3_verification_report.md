# Phase 3 Independent Verification Report — `leanre` ("Ghidra for Lean")

> **Verdict:** **17/18 Gates PASS, 1 Gate OPEN (`R2` — Phase 2 baseline publication items only; 0 new Phase 3 leaks; 0 FAIL)**
> **Verified Commit (`HEAD` audited):** `78b516f` (`main`, local — unpushed)
> **Date:** 2026-11-22
> **Owner:** `@verifier` (Independent Zero-Trust Verifier; read-only outside `verify/` and this report)

> **Epistemic Scope & Four-Layer Disclaimer (Guardrail 1):** All findings tagged `[L]` below are deterministic structural/forensic facts independently reproduced from pinned local artifacts (`Deicyde/riemann-hypothesis@40e56bab026552e089d7afcfeff08d2defb9c005`, `data/challenge.ndjson.zst`, `data/solution.ndjson.zst`, and the 7 pinned Apache-2.0 corpora). This audit verifies `leanre`'s **Layer 1–3 instrumentation** (kernel-exact dependency graph, dominators, taint paths, signature hashes, FLIRT fingerprinting, annotation packs, workbench security, and guardrails). Kernel acceptance (`[C]` across Lean `v4.33.1`, `leanchecker`, `nanoda`, `con-leche`, `lean4lean`; zero `sorryAx` and only `[Classical.choice, Quot.sound, propext]` confirmed in `solution.ndjson.zst` `[L]`) is **Layer 1** only — it does **not** establish **Layer 2** complete semantic TCB audit, **Layer 3** human mathematical intelligibility, or **Layer 4** mathematical peer consensus.

---

## 1. Executive Scorecard (All Phase 3 Acceptance Gates)

Every PASS below was independently reproduced from scratch by `@verifier` (via clean-room C++/Python oracles in `verify/` with zero imports from `leanre/` where applicable, or independent re-execution). No worker-reported figure was accepted without reproduction.

| Gate | Owner | Verdict | Independent Verification Summary (`[L]` unless noted) |
|---|---|---|---|
| **Baseline** | Phase 2 | **PASS** | `unittest` 7/7 OK; `175,187` `.lean` files (`40e56bab`); `challenge.ndjson.zst` both SHA-256s match; 9/9 real-data gates recomputed from raw `module_edges` with own node-removal oracle (`175,185` hub, `0/400` idom mismatches); workbench `:8439` `25/25` PASS. |
| **K1** | `kernel` | **PASS** | Own `verify/k1_sha.sh`: `data/solution.ndjson.zst` compressed `7,699,933,588` B (`61a8938a…5381`), uncompressed `61,570,595,788` B (`5ea74b91…244e`) — exact bit match. |
| **K2** | `kernel` | **PASS** | Independent C++ streaming oracle (`verify/oracle_ndjson.cpp`, 379.6s / 15.74 GiB RSS) + `verify/kernel_db_check.py`: **`1,468,418`** declaration records (`== con-leche` `[C]`) and **`1,484,733`** unpacked constants (`== nanoda` via `nasqret` `[C]`, `+16,315 = +1` mutual type `+ 8,342` ctors `+ 7,972` recs), `0` mismatches, `0` unknown keys/exprs/dangling refs. |
| **K3** | `kernel` | **PASS** | Independently ran `leanre/kernel.py extract` on `data/challenge.ndjson.zst` and set-diffed against clean-room C++ & Python oracles + Phase 2 `leanre.db`: `51,692` decls / `53,722` consts / `1,206,518` typed edges exact (`0` mismatches), def-cone `2,570`, `GRH\cone(riemannHypothesis) = +470` (`+469` beyond both zeta roots), `sorryAx` fan-in `5` (value-only stubs), `k1n`/`k1a` TSV SHA-256 `720e1df8…deb1` matches clean-room spec oracle (`verify/sighash_spec_oracle.py`) bit-for-bit. |
| **K4** | `kernel` | **PASS** | Independent NumPy/CSR BFS over verifier's own 114,115,002-edge oracle graph: `live_mask`, `stmt_mask`, `roots`, and all 5 `reach` tables exact across all `1,468,418` decls (`0` mismatches). Union proof live **`1,468,414`** / dead **`4`** (`Nat.lor`, `Nat.xor`, `String.mk`, `String.mk._proof_1`); axioms `['Classical.choice', 'Quot.sound', 'propext']`; `sorryAx` and `ofReduceBool`/`reduceBool`/`ofReduceNat`/`reduceNat`/`trustCompiler` all **absent** (`0`). |
| **K5** | `kernel` | **PASS** | Independent C++ brute-force dominator checker (`verify/dom_oracle.cpp`) on ALL 7 trees: **685,887,391** edge parent-property checks (`0` violations), **8,747** sampled node-removal idom checks (`1,250 × 6 + 1,247`, `0` errors), **350** top-50 dominated-set-size removal checks (`0` mismatches). All **3,000** taint paths (**60,324** hops) validated edge-by-edge against verifier's oracle edges (`0` errors). Confirmed `4/5` `lean4lean` timeout modules (`DyadicPrimeIntervals.Run1..4`) are absent from `solution.ndjson.zst`. |
| **K6** | `kernel` | **PASS** *(after fix)* | Caught defect (#47): Phase 2 anonymous-`end` names in `leanre.db` falsely aligned 247 library decls (`Std.*`, `PLift.*`, `Height.*`, `Inter`, `Inv`, `Ext`) to project files. Patched in `ad3c04e` (`sighash.iter_source_decls` authoritative first) and re-verified: **`1,250,660`** matched (`85.17%`) + **`217,758`** explicit unmatched (`14.83%`) = `1,468,418` (`0` silent drops), **`0`** TCB/`mathlib4`/`lean4`/`batteries` false matches, `200/200` on-disk mirror spot checks, `146,283 / 175,187` modules live-covered. |
| **K7** | `kernel` | **PASS** | Independently re-ran full `solution.ndjson.zst` extraction under `/usr/bin/time -v` at `--threads 16 --workers 16`: **`10:10.98`** wall (`564.4s` Rust + `41.03s` enrich), **`12,587,336` KiB (`12.00 GiB`)** peak RSS. Hashed all **11** SQLite data tables (`decls`, `consts`, `edges`, `roots`, `reach`, `stmt_reach`, `dom_trees`, `dom`, `decl_module`, `taint_sources`, `taint_paths`) against `outputs/kernel/kernel.db` (48-thread run): **11/11 SHA-256 identical** (thread-count-independent determinism). |
| **F1** | `flirt` | **PASS** | Independent `verify/f1_tier1_check.py` (8/8 PASS): `175,187` modules covered; `GlobalTheory.PrimeRecip.table_ok` under `AbelianVarietyTheory/Proofs/DivisorProofs/` generically flagged (`rank=148`, `score=0.9965`, `tier=high`, verified on disk); `39,212 / 14,165 / 11,592` independently recomputed (`phase2_literal_2comp`) alongside explicit `lean_scoped_2comp` (`39,077 / 14,117 / 11,626`); `1,192 / 4,787` alpha clones and `150` shims exact; `50/50` high/top misfiles verified on disk. |
| **F2** | `xrepo` | **PASS** | Independent `verify/f2_check.py` (13/13 PASS, re-verified post-`1b31c68`): all 7 corpora SHAs match `git rev-parse HEAD`, `mathlib4@0df444a3` matches `lake-manifest.json`, 7/7 `LICENSE` files on disk; all **131** rows of `controls` recomputed from raw `control_restate` (`30,287`) & `control_sigs` (`1,634,602`, `0` mismatches); all `168,230` source + `206,598` kernel matches carry full evidence + `provenance='L'`; `30/30` strong source + `50/50` kernel matches verified on disk / against `kernel.db`; zero proof text in `proof_sigs`. |
| **F3** | `flirt` | **PASS** | Independent `verify/f3_check.py` (8/8 PASS): all 24 blinded prompts grepped against **3,485** project folders, **167,045** file stems, **1,033,515** full decls, **697,966** leaf decls, and **35** landmarks → **`0` leaks** (non-trivial blinded signatures confirmed by eye); `tier3_ai_draft_pack.jsonl` passes canonical `annot.validate_text` (`kind=ai-draft`, `default_on=false`, `draft=true`, `tag=M`, `breaks`, `ai:*`, `0` `[L]` facts); agreement **`13/24` (`0.5417`)**, **κ = `0.4500`**, top-2 **`0.7083`** independently recomputed. |
| **A1** | `annot` | **PASS** | Independent `verify/a_check.py` (source `s1n` on synthetic headers: body change → `exact`, binder alpha-rename/whitespace invariant, rename → `hash_only` unique → `rebind` + `was`, statement change → `name_only/signature_changed`, ambiguous hash not guessed) + real 1.48M-const kernel `k1n` challenge→solution re-anchoring (`exact=2`, `orphan=1 sorryAx`, `name_only=2`) and real rename recovery (`riemannZeta_eq_zero_re` unique; `riemannHypothesis` honestly ambiguous with `['rhOfAll', 'riemannHypothesis']`). |
| **A2** | `annot` | **PASS** *(after fix)* | Caught defect (#19): future seed timestamps `03:00:00Z` > commit time; patched in `c1ae986` (`02:56:15Z` real UTC in `0dd6736`). `verify/a_check.py` (32/32 PASS): seed file + 40 random Unicode packs byte-identical across `export → import → export`, insertion-order independent, 18 malformed packs rejected, CLI `export` byte-identical. *(Open note: seed pack is AI-transcribed and flagged for human review.)* |
| **A3** | `annot` + `workbench` | **PASS** | API verified in `verify/a_check.py` (AI-draft layer off by default, 4 toggle subsets, conflicting import reports conflicts & leaves files byte-identical, stale/blind writes → `ConflictError`, `../../evil` layer rejected). UI verified visually (`real_annot_layers.png`, `real_flirt_tier3.png`) and in headless Chrome (`#selftest=1` 124/124): AI-draft layer unchecked by default, violet dashed `AI DRAFT` visual separation. |
| **W1** | `workbench` | **PASS** | Independently ran headless Chrome `#selftest=1` on spare ports (`8439`/`8437`/`8436`/`8435`): real 5/5-live default **`90/90`** (25 Phase 2 + 65 Phase 3); real 5/5-live + scratch `--annotations` **`124/124`** (write round-trip ran); `--fixtures` **`124/124`** with `SYNTHETIC FIXTURE DATA` banner confirmed; absent-DB graceful degradation **`58/58`**. `py_compile` + `node --check` exit 0. |
| **W2** | `workbench` | **PASS** | Independent `verify/w2_probe.py` (8/8 PASS) + `workbench/probe_p3.py` (`129/129`, 0 failed on clean scratch dir): `0` external CDNs, all `sqlite3.connect()` read-only or in-memory, `0` f-string `.execute()`, strictly `127.0.0.1` bind (`ss -ltnp`), 12 path-traversal vectors all 400/403/404 with 0 leakage, 96 SQLi requests across all `/api/*` endpoints with 0 500s/leaks, 48 write-containment traversal probes all rejected, repo `annotations/` byte-identical. |
| **R1** | all | **PASS** | At `HEAD` `78b516f`: `python3 -m unittest discover -s leanre -v` → **`115/115 OK`** (2 opt-in slow tests skipped; separately ran `LEANRE_SLOW=1 test_flirt_sighash.py` → `23/23 OK` in 29.4s); `cargo test` in `leanre/kernel-rs` → **`10/10 OK`** (0 warnings). |
| **R2** | coordinator + all | **OPEN** | **`0` new Phase 3 leaks** (`verify/audit_tree.py --leak` at `6af3aa2`/`78b516f`: `0` `.lean`/`data/`/`research/sources/`, `0` files > 5 MB, `0` secrets, `0` internal hostnames/paths after `e8945ac`). Remains **OPEN** strictly on 2 Phase-2 baseline publication items ruled in #14: (1) 8 one-line tactic-body `snippet` strings in `outputs/forensics_report.json` + `outputs/workbench_bundle.json`, and (2) `origin/main` initial commit an earlier pre-squash initial commit still holding pre-scrub `HANDOFF.md` (requires user decision before push/history rewrite). |
| **R3** | all | **PASS** *(after fix)* | Audited `README.md` (synced in `78b516f`), `docs/{SIGHASH,ANNOTATION_PACKS,FLIRT,FLIRT_TIER2,KERNEL}.md`, `annotations/`, `workbench/*`, and committed JSON summaries via `verify/r3_audit.py` + full manual read: 4 epistemic layers never conflated, provenance tags present, synthetic/fixture vs `[L]` separated, `0` forbidden canonical-fact violations (`automorphy lifting`, `4 Dirichlet`, `772` digits, `131,072` steps, unqualified `RH is proved`, Masullo conflation). |

---

## 2. Detailed Gate-by-Gate Receipts

### 2.0 Phase 2 Baseline & Input Integrity

- **Mirror checkout (`Deicyde/riemann-hypothesis`)**:
  - Command: `git -C data/rh_mirror rev-parse HEAD && find -L data/rh_mirror -name '*.lean' -not -path '*/.git/*' | wc -l`
  - Output: `40e56bab026552e089d7afcfeff08d2defb9c005`, **`175187`**.
- **`challenge.ndjson.zst` checksums**:
  - Command: `sha256sum data/challenge.ndjson.zst && stat -c %s data/challenge.ndjson.zst && zstd -d -c --long=31 data/challenge.ndjson.zst | sha256sum`
  - Output: `c24ef99dab3556a52c7fb886e03cf22a242f3b96f82ae4cc40539e5d2f678ac6`, `46881299` B; unpacked `bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9`.
- **Phase 2 unit tests & 9 real-data gates**:
  - Command: `python3 -m unittest discover -s leanre -v` (at baseline an earlier pre-squash initial commit) → `Ran 7 tests in 0.086s — OK`.
  - Command: `python3 verify/baseline_phase2.py` → `BASELINE PASS (12/12)` (`175,187` modules, `753,261` project edges with `0` dangling, hub `Supplements.Kernels.MainTheoremsAll` dominating `175,185` via own node-removal reachability, `0/400` brute-force idom mismatches, `47,060` components, `37,001` singletons [`0/60` brute-force mismatches], `150` shims, `308` dup imports, `51,692` challenge decls / `1,206,518` edges).
- **Phase 2 workbench selftest (spare port)**:
  - Command: `bash verify/selftest_workbench.sh 8439` → `SELFTEST PASS — 25 checks, 0 errors (live=true)`, bound `127.0.0.1:8439`.

### 2.1 Gates K1–K7 — Kernel-Exact Graph (`leanre/kernel-rs/`, `leanre/kernel.py`, `outputs/kernel/kernel.db`)

- **K1 — `data/solution.ndjson.zst` SHA-256 & byte counts**:
  - Command: `bash verify/k1_sha.sh`
  - Output:
    ```text
    PASS compressed_bytes 7699933588
    PASS compressed_sha256 61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381
    PASS uncompressed_bytes 61570595788
    PASS uncompressed_sha256 5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e
    ```
- **Independent clean-room C++17 NDJSON oracle (`verify/oracle_ndjson.cpp`)**:
  - Cross-checked bit-for-bit against independent Python oracle `verify/oracle_ndjson.py` on `data/challenge.ndjson.zst`:
    `g++ -O3 -std=c++17 -Wall -Wextra verify/oracle_ndjson.cpp -o verify/out/oracle_ndjson && verify/out/oracle_ndjson data/challenge.ndjson.zst verify/out/challenge_cpp` → `CPP vs PYTHON ORACLE ON CHALLENGE: 100% BIT-FOR-BIT IDENTICAL!` (2.2s, 150 MB RSS).
  - Run over full `data/solution.ndjson.zst`:
    `/usr/bin/time -v verify/out/oracle_ndjson data/solution.ndjson.zst verify/out/solution_oracle` → `wall_s: 379.6`, `peak_rss_kib: 16501752` (15.74 GiB), `ndjson_lines: 1,080,769,508`, `n_expr: 1,065,214,335`, `UNKNOWN_expr_kinds: {}`, `UNKNOWN_top_keys: {}`, `dangling_const_refs: 0`, `forward_refs: 0`, `dup_const_ids: 0`, `dup_const_names: 0`, `dup_record_names: 0`.
- **K2 — Exact counting-rule reconciliation**:
  - Folded declaration records (`decls`): `1,246,110 thm + 214,241 def + 7,969 inductive + 91 opaque + 4 quot + 3 axiom` = **`1,468,418`** == `con-leche` fold records (`Δ = 0`).
  - Unpacked environment constants (`consts`): `1,246,110 + 214,241 + 91 + 4 + 3 + 7,970 inductive_types + 8,342 inductive_ctors + 7,972 inductive_recs` = **`1,484,733`** == `nanoda` via `nasqret` (`Δ = 0`).
  - Exact difference: `1,484,733 - 1,468,418 = 16,315 = (+1 mutual inductive type + 8,342 ctors + 7,972 recs)`.
  - Typed edges: **`114,115,002`** (`type 6,759,347` / `value 64,738,654` / `both 42,617,001`).
- **K3 — `challenge.ndjson.zst` regression + SIGHASH v1 clean-room spec check**:
  - Command: `python3 verify/k3_challenge_check.py` → `K3-ORACLE PASS` (`51,692` decls, `1,206,518` edges identical to Phase 2 `tcb_decls`/`tcb_edges` incl. `edge_kind`, `pure_def_cone = 2,570`, `GRH\cone(riemannHypothesis) = 470`, `GRH\cone(both zeta roots) = 469`, `sorryAx_fan_in = 5`).
  - Command: `python3 leanre/kernel.py extract --input data/challenge.ndjson.zst --out-dir /tmp/leanre_verify_k3 --leanre-db outputs/leanre.db --lexicon outputs/flirt/cache/lexicon_rh.txt --threads 16 --workers 16 ... && python3 leanre/kernel.py verify-k3 ...` → `exit 0`, `oracle_failures_total: 0`, `sighash_tsv_sha256: 720e1df87e3e300d4437ec294b966d655fa14ebc7935ff9eca43186781f6deb1`.
  - Clean-room prose-spec oracle `verify/sighash_spec_oracle.py` (zero `leanre/` imports, implemented directly from `docs/SIGHASH.md` §2):
    - No lexicon: `constants=53722 tsv_sha256=1c0b8c380ae14e89398f4837fdcd77df1716b1ee1fb2d54d68197848e1e1767e` (exact match).
    - Lexicon `294e04cd1ef65e37`: `constants=53722 tsv_sha256=720e1df87e3e300d4437ec294b966d655fa14ebc7935ff9eca43186781f6deb1` (exact match to both `leanre/sighash.py` and Rust `leanre-kernel`).
- **K4 & K5 — Full `outputs/kernel/kernel.db` cross-check against verifier's C++ oracle (`verify/kernel_db_check.py` + `verify/dom_oracle.cpp`)**:
  - Command: `python3 verify/kernel_db_check.py --db outputs/kernel/kernel.db --oracle verify/out/solution_oracle --samples 1200 --procs 16`
  - Output: **`KERNEL-DB-CHECK PASS (23/23) fails=[]`**:
    - `decls`: `1,468,418 vs 1,468,418`, `(id, name, kind, n_consts)` mismatches = `0`.
    - `consts`: `1,484,733 vs 1,484,733`, `name -> decl_id` mismatches = `0`.
    - `edges`: `114,115,002 vs 114,115,002` (streamed sorted compare incl. `kind`), mismatches = `0`.
    - `live_mask` & `stmt_mask`: `0` mismatches across all `1,468,418` decls.
    - `roots` + all 5 `reach` tables (`1,468,390` / `1,468,392` / `1,468,382` / `1,468,395` / `1,468,385`): `0` bad depth, `0` bad edge, `0` bad parent depth.
    - `axioms` view: `['Classical.choice', 'Quot.sound', 'propext']`; `sorryAx`, `ofReduceBool`, `reduceBool`, `ofReduceNat`, `reduceNat`, `trustCompiler` all absent (`0` records in oracle).
    - `taint_paths`: `3,000` paths / `60,324` hops (`600` sources across `CutCptCopy: 5`, `decide_kernel: 20`, `decide_kernel_pattern: 472`, `kcopy: 3`, `kexactB: 94`, `lean4lean_timeout: 1`, `slow_con_leche: 5`) validated edge-by-edge against verifier's oracle edges → **`0` errors**. Confirmed directly in `verify/out/solution_oracle.names.json` that `PI.PC.loop_run` is present while `PI.PrimesDyadicRS` / `run1..4` have `0` hits.
    - All 7 dominator trees via `verify/out/dom_oracle`:
      - `ALL` (`1,468,414` nodes, `114,114,982` edges): `pp_viol=0`, `1,250` sampled `idom_errs=0`, top-50 `size_bad=0` (`allChi = 1,409,557`).
      - `ROOT:riemannHypothesis` (`1,468,390`, `114,113,194` edges): `pp_viol=0`, `idom_errs=0`, `size_bad=0` (`rhOfAll = 1,417,175`).
      - `ROOT:riemannZeta_eq_zero_re` (`1,468,392`, `114,113,235` edges): `pp_viol=0`, `idom_errs=0`, `size_bad=0` (`rhOfAll = 1,417,177`).
      - `ROOT:LFunction_ne_zero_of_half_lt_re` (`1,468,382`, `114,112,619` edges): `pp_viol=0`, `idom_errs=0`, `size_bad=0` (`allChi = 1,416,807`).
      - `ROOT:LFunction_eq_zero_re` (`1,468,395`, `114,113,857` edges): `pp_viol=0`, `idom_errs=0`, `size_bad=0` (`claimAll = 1,416,815`).
      - `ROOT:LFunction_eq_zero_re_of_isPrimitive` (`1,468,385`, `114,113,037` edges): `pp_viol=0`, `idom_errs=0`, `size_bad=0` (`critAll = 1,416,708`).
      - `STMT_ALL` (`51,687`, `1,206,467` edges): `pp_viol=0`, `1,247` sampled `idom_errs=0`, top-50 `size_bad=0` (`jacobiTheta₂_functional_equation = 14,986`).
- **K6 — `decl -> .lean` alignment (post-`ad3c04e` re-verification)**:
  - Command: independent SQLite audit over `outputs/kernel/kernel.db` + `outputs/leanre.db` + `outputs/flirt/tier2.db` (`corpus_sigs` library names) + 200-sample on-disk mirror check.
  - Output: `Total=1,468,418`, `matched=1,250,660 (85.17%)`, `unmatched=217,758 (14.83%)`, `mods_covered=146,283`, `uncovered=28,904`, `inv_viol=0`, `TCB/challenge library decls matched to non-Main/Statements modules: 0`, `Matched decls whose name appears in mathlib4/lean4/batteries: 0`, `200/200` on-disk mirror matches.
- **K7 — Performance & independent cross-thread-count determinism**:
  - Command: `/usr/bin/time -v python3 leanre/kernel.py extract --input data/solution.ndjson.zst --out-dir /tmp/leanre_verify_k7 --leanre-db outputs/leanre.db --src-dir data/rh_mirror/src --lexicon outputs/flirt/cache/lexicon_rh.txt --threads 16 --workers 16 --oracle-random 1000 --oracle-top 50 ...` (followed by `leanre/kernel.py enrich` at `ad3c04e`, `41.03s`).
  - Measured (`--threads 16`): wall `10:10.98` (`564.4s` Rust extract + `41.03s` enrich), peak RSS `12,587,336` KiB (`12.00 GiB`).
  - Independent 11-table SHA-256 comparison vs `outputs/kernel/kernel.db` (`--threads 48`):
    - `decls` (`1,468,418`): `3db0d652093e40d3` ✔ · `consts` (`1,484,733`): `ab887a4c9e997105` ✔ · `edges` (`114,115,002`): `d58c24af5737d54b` ✔ · `roots` (`5`): `9447dfe4e46623df` ✔ · `reach` (`7,341,944`): `eb68aa1c0e5259dd` ✔ · `stmt_reach` (`257,237`): `802cc8501d1da91b` ✔ · `dom_trees` (`7`): `4269304e872e8166` ✔ · `dom` (`8,862,045`): `4809183d693a02cc` ✔ · `decl_module` (`1,468,418`): `4e59c4904bd792ac` ✔ · `taint_sources` (`600`): `157241dfb6c8b67d` ✔ · `taint_paths` (`60,324`): `ac1156115b7092c4` ✔ → **`K7-DETERMINISM PASS`**.

### 2.2 Gates F1–F3 — FLIRT for Lean

- **F1 — Tier 1 deterministic fingerprinting & misfiles (`outputs/flirt/tier1.db`)**:
  - Command: `python3 verify/f1_tier1_check.py && python3 -m unittest leanre/test_flirt_tier1.py -v`
  - Output: **`F1-CHECK PASS (8/8)`**, `Ran 2 tests — OK`:
    - `module_fingerprints = 175,187`; `misfiles = 117,065` monotonically sorted (`0` inversions, `0` missing provenance).
    - Known misfile `Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes` (`flag_decl = GlobalTheory.PrimeRecip.table_ok`, verified on disk) flagged at `rank=148`, `score=0.9965`, `tier=high`.
    - `Development.AbelianVarietyTheory` split independently recomputed from `outputs/leanre.db`: `phase2_literal_2comp` = `[('_root_.GlobalTheory', 39212), ('GlobalTheory.IndefiniteRowSideFullHecke', 14165), ('GlobalTheory.Mem', 11592)]` (exact match); `lean_scoped_2comp` = `[('GlobalTheory.T', 39077), ('GlobalTheory.IndefiniteRowSideFullHecke', 14117), ('GlobalTheory.Mem', 11626)]`.
    - Boilerplate clusters: `alpha_body_clone = 1,192` clusters / `4,787` mods (`== leanre.db`), `import_shim = 1` / `150` mods (`== leanre.db`), `sigset_clone = 15,574` / `36,195` mods, `statement_wrapper = 8` / `35,193` mods.
    - On-disk spot check of 50 high/top misfiles in `data/rh_mirror`: **`50/50` confirmed**.
- **F2 — Tier 2 cross-repo signature DB (`outputs/flirt/tier2.db`, post-`1b31c68`)**:
  - Command: `python3 verify/f2_check.py && python3 -m unittest leanre/test_tier2.py -v`
  - Output: **`F2-CHECK PASS (13/13)`**, `Ran 23 tests in 0.440s — OK`:
    - All 7 corpora (`FLT`, `PrimeNumberTheoremAnd`, `SpherePacking`, `batteries`, `carleson`, `lean4`, `mathlib4`) match `git rev-parse HEAD` on disk and `outputs/flirt/tier2_corpora.json`; `mathlib4@0df444a360ea` matches `data/rh_mirror/lake-manifest.json`; 7/7 `LICENSE` files present (all Apache-2.0).
    - All **131** rows in `controls` recomputed from raw `control_restate` (`30,287` held-out trials joined to original `corpus_sigs.n_tokens`) and `control_sigs` (`817,255` `swap` + `817,347` `perm`): **`0` mismatches**.
    - All `168,230` source matches (`s1n` 90 / `s1t` 117 / `s1a` 150 strong = 357 strong; non-theorems graded `defsig`) and `206,598` kernel matches carry full evidence + `provenance='L'`.
    - Spot checks: **`30/30`** strong source matches verified against `data/rh_mirror` file:line + sighash equality; **`50/50`** `kernel_matches` cross-checked directly against `outputs/kernel/kernel.db consts`; `proof_sigs` has no raw proof source text column.
- **F3 — Tier 3 name-blinded AI-draft pilot (`outputs/flirt/tier3_*`)**:
  - Command: `python3 verify/f3_check.py && python3 -m unittest leanre/test_flirt_tier3.py -v`
  - Output: **`F3-CHECK PASS (8/8)`**, `Ran 3 tests — OK`:
    - Zero-trust leak grep over all 24 lines of `outputs/flirt/tier3_blinded_prompts.jsonl` against `3,485` project folders, `167,045` file stems, `1,033,515` full decls, `697,966` leaf decls, and `35` landmarks → **`0` leaks**. Manual inspection of prompt lines confirms non-trivial blinded signatures (`NormedField`, `CompleteSpace`, `P001`, `#0`, …).
    - `outputs/flirt/tier3_ai_draft_pack.jsonl` passes `annot.validate_text(canonical=True)`: 1 layer `ai/flirt-tier3-pilot` (`kind=ai-draft`, `default_on=false`), 24 records all `draft=true`, `tag=M`, mandatory `breaks`, `author=ai:llm-reasoning-b`, `annot.default_layers == []`.
    - Blinded-vs-unblinded agreement independently recomputed from `outputs/flirt/cache/t3_labels_{blinded,unblinded}.json`: **`13/24` (`0.5417`)**, **Cohen's κ = `0.4500`**, **top-2 overlap = `0.7083`** — matches `outputs/flirt/tier3_pilot.json` to 4 decimal places.

### 2.3 Gates A1–A3 — Annotation Packs (`leanre/annot.py`, `annotations/`)

- **Black-box verifier suite (`verify/a_check.py`) + unit tests**:
  - Command: `python3 verify/a_check.py && python3 -m unittest discover -s leanre -p 'test_annot.py' -v`
  - Output: **`A-CHECK PASS (32/32)`**, `Ran 54 tests in 0.319s — OK (skipped=1)`:
    - **A1 (source + real kernel `k1n`)**: `s1n` stable under body change, binder alpha-rename + whitespace, and decl rename; sensitive to statement change (`2 ≤ n` → `3 ≤ n`); rename → `hash_only` unique → `rebind` preserves payload & records `was`; ambiguous hash not guessed. Real challenge→solution CLI run: `python3 leanre/leanre.py annot reanchor annotations/ --kernel-db outputs/kernel/kernel.db --leanre-db outputs/leanre.db` → `exact: 2` (`riemannHypothesis`, `riemannZeta_eq_zero_re`), `orphan: 1` (`sorryAx`), `name_only: 2` (`Main`, `Development.AbelianVarietyTheory`), `unchecked: 0`. Independent real-`kernel.db` rename test (`A1-REAL-KERNEL-RENAME PASS`): `riemannZeta_eq_zero_re` recovers uniquely across all `1,484,733` constants; `riemannHypothesis` reports both real candidates `['rhOfAll', 'riemannHypothesis']` without guessing.
    - **A2**: `annotations/human__canonical-facts.jsonl` + 40 random Unicode packs byte-identical across `export → import → export`, insertion-order independent, 18 malformed packs rejected, timestamps real UTC (`2026-11-22T02:56:15Z`), CLI `export` byte-identical.
    - **A3**: AI-draft layer off by default (`default_layers == ['human/canonical-facts']`), 4 independent toggle subsets verified, conflicting import reported with `applied=False` & files byte-identical, stale/blind writes raise `ConflictError`, `../../evil` layer rejected. UI pixels confirmed in `real_annot_layers.png` & headless Chrome `#selftest=1`.

### 2.4 Gates W1–W2 — Interactive Workbench (`workbench/`)

- **W1 — Headless Chrome end-to-end selftest (spare ports, never 8420)**:
  - Syntax: `python3 -m py_compile workbench/server.py workbench/phase3.py workbench/p3_fixtures.py workbench/probe_p3.py && node --check workbench/app.js && node --check workbench/phase3.js` → exit `0`.
  - Default real 5/5-live mode (`:8439`): `bash verify/selftest_workbench.sh 8439` → **`SELFTEST PASS — 90 checks, 0 errors (live=true)`** (`25 Phase 2 + 65 Phase 3 · kernel=ready flirt=ready/ready/ready annot=ready`).
  - Real 5/5-live + scratch `--annotations` (`:8437`): **`SELFTEST PASS — 124 checks, 0 errors (live=true)`** (`25 Phase 2 + 99 Phase 3; annotation write round-trip ran`).
  - Synthetic `--fixtures` mode (`:8436`): **`SELFTEST PASS — 124 checks, 0 errors (live=true)`**, `has_synth_banner: True`.
  - Absent Phase-3 DBs mode (`:8435`): **`SELFTEST PASS — 58 checks, 0 errors (live=true)`**, `/api/p3/status` reports clear `"Not built yet: ..."` state for all 4 absent providers.
- **W2 — Security & hygiene audit**:
  - Command: `python3 verify/w2_probe.py --port 8438` → **`W2-PROBE PASS (8/8)`** (`0` external CDNs, `0` RW SQLite connects, `0` f-string `.execute()`, strictly `127.0.0.1:8438`, `12/12` traversal probes 400/403/404 with `0` leakage, `96/96` SQLi probes across `/api/*` with `0` 500s/leaks, `48/48` write-containment traversal probes rejected, repo `annotations/` byte-identical).
  - Command: `python3 workbench/probe_p3.py --port 8434 --annotations <clean scratch dir>` → **`PROBE SUMMARY: 129 checks, 0 failed`**.

### 2.5 Gates R1–R3 — Regression, Tree Hygiene & Guardrails

- **R1 — Full test suites at `HEAD` `78b516f`**:
  - `python3 -m unittest discover -s leanre -v` → **`Ran 115 tests in 1.226s — OK (skipped=2)`**.
  - `LEANRE_SLOW=1 python3 -m unittest leanre/test_flirt_sighash.py -v` → **`Ran 23 tests in 29.427s — OK`**.
  - `(cd leanre/kernel-rs && cargo test)` → **`10 passed; 0 failed; 0 ignored`**.
- **R2 — Whole-tree hygiene & verbatim source leak audit (`verify/audit_tree.py --leak`)**:
  - `git ls-files` (`75` files at `78b516f` before this commit): **`0`** `.lean` files, **`0`** files under `data/` or `research/sources/`, **`0`** files > 5 MB, **`0`** secrets, **`0`** internal hostnames / absolute home paths (after `e8945ac` and scrubbing `verify/audit_tree.py`).
  - Verbatim mirror scan across all `175,187` `.lean` files: **`0` new proof-source leaks in any Phase 3 file** (the single string hit in `outputs/kernel_report.json:2364` is a bare 64-char declaration identifier `Formalism.MainStatements.RowRest.analytic_pinnedTheoremB_uniform`).
  - **Why R2 remains `OPEN` (user decision required before public push):** Two pre-existing Phase-2 baseline items ruled OPEN by `@coordinator` (#14):
    1. `outputs/forensics_report.json` and `outputs/workbench_bundle.json` contain 8 distinct one-line tactic-body `snippet` strings from `kexactB` call sites (not 1-line declaration headers, so outside strict Guardrail 3/6 wording).
    2. `origin/main` initial commit an earlier pre-squash initial commit still contains the pre-scrub `HANDOFF.md` (with workstation hostname and local home-dir paths links); removing it from remote history requires an explicit user-authorized history rewrite.
- **R3 — Guardrails 1–6 & canonical facts audit**:
  - Command: `python3 verify/r3_audit.py` + manual read of `README.md`, `docs/{SIGHASH,ANNOTATION_PACKS,FLIRT,FLIRT_TIER2,KERNEL}.md`, `annotations/human__canonical-facts.jsonl`, and rendered workbench screenshots (`real_kernel_livedead.png`, `real_flirt_tier3.png`, `real_annot_layers.png`).
  - Result: **PASS** — all 8 tripwire hits manually inspected and confirmed benign (explicit negations `"Extended RH is not claimed"`, test assertions, selftest `FORBIDDEN` regex, and table totals directly under their counting rule).

---

## 3. Defect Remediation Log (Caught, Dispatched & Independently Re-Verified)

| # | Gate | Owner | Defect Caught by `@verifier` | Fix Commit & Independent Re-Verification |
|---:|---|---|---|---|
| 1 | **R2** | `coordinator` | Baseline tracked files contained workstation hostname (`HANDOFF.md`, `.gitignore`), agent scratch path (`research/03:287`), 46 absolute home-dir paths, and 2 full theorem bodies (`research/02:139-142`). | Fixed prior to public release; re-verified via `verify/audit_tree.py --leak` (`0` hostname, home-path, scratch, or body findings in those files). |
| 2 | **A2** | `annot` | `annotations/human__canonical-facts.jsonl` stamped future timestamps (`2026-11-22T03:00:00Z`) post-dating its `02:46Z` creation and commit. | Fixed in `c1ae986` (`make_seed.py` defaults to `annot.utc_now()`; regenerated at real UTC `02:56:15Z` in `0dd6736`); re-verified `verify/a_check.py` 32/32 PASS. |
| 3 | **K6** *(+ F2 impact)* | `kernel` *(+ `xrepo`)* | `leanre/kernel.py` consulted Phase 2 `outputs/leanre.db.declarations` before `sighash.iter_source_decls`; Phase 2's anonymous-`end` namespace-popping bug caused bogus 1-component names (`Std`, `PLift`, `Height`, `Inter`, `Inv`, `Ext`) to falsely align **247** Lean/Mathlib library decls (159 `challenge_library` + 88 `library_or_external`, incl. `Std.Antisymm`, `PLift.down`, `Height.mulHeight`) to unrelated project files (`FrobKill`, `DualForm`, `QdetFacts`, etc.). | Fixed in `ad3c04e` (`sighash.iter_source_decls` authoritative first when `--src-dir` is given; new regression test in `test_kernel.py`), `kernel.db` re-enriched; `xrepo` refreshed `tier2.py kernel` in `1b31c68` (`-327` misattributed consts cleaned). Independently re-verified: **`0`** TCB and **`0`** `mathlib4`/`lean4`/`batteries` false matches; `F2-CHECK` 13/13 PASS. |
| 4 | **R3** | `coordinator` | `README.md:38` cited pre-`ad3c04e` module coverage (`146,285 / 175,187` and `28,902`) instead of post-fix `146,283 / 175,187` and `28,904`. | Fixed in `78b516f`; verified `0` remaining stale counts across `README.md` and `docs/*.md`. |

---

## 4. Explicit List of Anything Unverified & Open Items

In accordance with Guardrail 5 (zero silent gaps), the following items are explicitly **NOT** claimed as independently verified by `@verifier`:

1. **External Lean 4 kernel replay (Layer 1 execution):** `@verifier` did not execute `lean`, `leanchecker`, `nanoda`, `con-leche`, or `lean4lean` on `data/rh_mirror` or `data/solution.ndjson.zst`. Typechecking soundness remains attributed `[C]` to Sutherland / `nasqret` / `Deicyde`; `@verifier` independently verified only the export SHA-256s, declaration/constant/edge/axiom/`sorryAx` structure, dominators, and taint paths (`[L]`).
2. **Full-export clean-room SIGHASH pass:** Clean-room prose-spec verification (`verify/sighash_spec_oracle.py`) was run over all `53,722` constants of `data/challenge.ndjson.zst` (bit-for-bit match to both `leanre/sighash.py` and Rust `leanre-kernel`). On full `data/solution.ndjson.zst` (`1,484,733` constants), `@verifier` verified determinism across independent 16-thread vs 48-thread Rust runs (`consts` SHA-256 identical) and cross-checked `50` sampled `k1n`/`k1a` kernel matches + real `k1n` challenge→solution re-anchoring, rather than running a 61.6 GB pure-Python `sighash_spec_oracle.py` pass.
3. **Full from-scratch Tier 1 / Tier 2 DB rebuilds:** `@verifier` audited `outputs/flirt/tier1.db` and `outputs/flirt/tier2.db` directly against `data/rh_mirror`, `data/corpora/`, `outputs/leanre.db`, and `outputs/kernel/kernel.db` (recomputing splits, controls, and spot checks from raw disk/tables) plus ran all unit tests, rather than re-running the 104s Tier 1 and ~4 min Tier 2 builders from scratch.
4. **Seed annotation pack human review (open note on A2):** `annotations/human__canonical-facts.jsonl` (5 `[L]` notes from `HANDOFF.md` §3) was transcribed by the Phase 3 `annot` AI worker (as transparently recorded in its `author` and layer `description` fields) and has not yet been reviewed/signed off by a human.
5. **R2 publication blockers (OPEN — user decision):** The 8 Phase-2 tactic-body `snippet` strings in `outputs/forensics_report.json` + `outputs/workbench_bundle.json`, and the pre-scrub `HANDOFF.md` in `origin/main`'s initial commit an earlier pre-squash initial commit, require explicit user disposition before publishing or pushing.
6. **Epistemic Layers 2–4:** Complete semantic TCB audit (Layer 2), human mathematical intelligibility of the proof mechanism (Layer 3), and community/Clay consensus (Layer 4) remain open.

---

## 5. Verifier Scripts Added (`verify/`)

All independent verification scripts live under `verify/` (with generated intermediates gitignored under `verify/out/`):
- `verify/PLAN.md` — verification plan & canonical-fact tripwires
- `verify/k1_sha.sh` — independent K1 compressed + uncompressed SHA-256 & byte-count checker
- `verify/oracle_ndjson.py`, `verify/oracle_full.py`, `verify/oracle_ndjson.cpp` — independent Python & C++17 streaming `lean4export` v3.1.0 parsers (zero `leanre/` imports)
- `verify/graph_oracle.py`, `verify/dom_oracle.cpp` — independent naive node-removal BFS dominator & path oracles
- `verify/baseline_phase2.py`, `verify/k3_challenge_check.py`, `verify/kernel_db_check.py` — Phase 2 baseline + K2–K6 cross-checks
- `verify/sighash_spec_oracle.py` — clean-room implementation of `docs/SIGHASH.md` §2
- `verify/f1_check.py`, `verify/f1_tier1_check.py`, `verify/f2_check.py`, `verify/f3_check.py` — independent F1, F2, F3 checks
- `verify/a_check.py` — black-box A1–A3 check suite
- `verify/selftest_workbench.sh`, `verify/w2_probe.py` — independent W1 headless Chrome & W2 security/CDN/SQLi/traversal probes
- `verify/audit_tree.py`, `verify/r3_audit.py` — R2 whole-tree/verbatim-leak auditor & R3 Guardrails 1–6 scanner
