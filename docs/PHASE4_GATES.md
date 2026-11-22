# Phase 4 — Proof Reverse-Engineering & Untangling Contract

Repo: `./` (`bohemian-miser/leanre`).
Mission: **Actually reverse-engineer and explain how the 17.37M-line proof works** (and spot any vacuity, junk values, degenerate contracts, or unverified literature wrappers) while upgrading `leanre` with the decompilation/untangling tools needed to inspect a proof this big.

Guardrails 1–6 (`research/04_verification_and_roadmap.md` §2) remain mandatory:
- **Zero ungrounded LLM math glue.** Every mathematical claim carries `[L]` / `[A]` / `[C]` / `[S]` / `[M]` with file:line anchors and declaration names pinned to `40e56bab` / `solution.ndjson.zst` (`5ea74b91…244e`).
- **Explicit honesty about what is *not* understood yet.** If a definition is a deeply nested custom `structure` whose full unfolding you did not inspect, mark it **`UNREAD / OPAQUE`** — NEVER bluff its mathematical meaning from its Lean name alone!
- **Zero license respect.** NEVER commit `.lean` files or paste multi-line proof bodies into `analysis/*.md` or `outputs/decomp/*.json`. Quote only identifiers, counts, hashes, dependency edges, normalized schematic summaries, and fair-use ≤1-line headers.
- **CPU/RAM hygiene:** 10 concurrent workers share 128 cores / 235 GiB RAM. Cap per-worker parallelism at **16 threads**, open `outputs/kernel/kernel.db` and `outputs/leanre.db` strictly `mode=ro`.

## Ownership (disjoint paths, commit only your own paths, never push)

| Worker | Model / Bucket | Owns |
|---|---|---|
| `spine` | `llm-model-b` (`pool-a`) | `leanre/decompile/`, `leanre/test_decompile.py`, `analysis/spine_and_diamond.md`, `outputs/decomp/spine_map.json` |
| `theta` | `llm-model-a` (`pool-a`) | `analysis/pillar_theta.md`, `outputs/decomp/pillar_theta.json` |
| `galois` | `llm-reasoning-a` (pool-c) | `analysis/pillar_galois.md`, `outputs/decomp/pillar_galois.json` |
| `volume` | `llm-reasoning-a` (pool-c) | `analysis/pillar_volume_lit.md`, `outputs/decomp/pillar_volume_lit.json` |
| `window` | `llm-reasoning-b` (`pool-b`) | `analysis/pillar_window.md`, `outputs/decomp/pillar_window.json` |
| `tcb` | `llm-reasoning-c` (`pool-b`) | `analysis/tcb_and_contracts.md`, `outputs/decomp/tcb_audit.json` |
| `arch` | `llm-fast` (pool-d) | `leanre/compute_sweep.py`, `analysis/compute_and_deadcode.md`, `outputs/decomp/compute_atlas.json` |
| `kernel` | `llm-reasoning-b` (`pool-b`) | `leanre/kernel.py`, `leanre/kernel-rs/`, `leanre/test_kernel.py`, `docs/KERNEL.md`, `outputs/kernel_report.json` |
| `flirt` | `llm-reasoning-b` (`pool-b`) | `leanre/flirt/` (`tier1*`, `tier3*`, `cluster*`), `leanre/test_flirt*.py`, `docs/FLIRT.md`, `outputs/flirt/` |
| `annot` | `llm-reasoning-b` (`pool-b`) | `annotations/`, `annotations/tools/`, `docs/ANNOTATION_PACKS.md`, `leanre/test_annot.py` |
| `linkn-audit` | `llm-reasoning-a` (pool-c) | `analysis/deep_followup_audit.md` |
| `workbench` | `llm-reasoning-b` (`pool-b`) | `workbench/**` |
| `verifier` | `llm-reasoning-b` (`pool-b`) | `verify/**`, `outputs/phase4_verification_report.md` (read-only everywhere else) |
| coordinator | `llm-coordinator` (coordinator) | `leanre/leanre.py`, `README.md`, `analysis/SYNTHESIS.md`, `docs/PHASE4_GATES.md`, `.gitignore`, pushes |

*(Note: commit only your own paths with `git add <paths> && git commit -m ... -- <paths>`. Retry on transient `index.lock`. Never `git add -A`, never rewrite history, never push.)*

## Gates (P4)

- **D1 — Spine & Horn Decompilation (`spine`):** Reusable `leanre decompile` / `leanre/decompile/` engine (extracting actual theorem signatures, `Prop`-level Horn graph `A ∧ B → C`, backward/forward slices, and `.lean` comment-free `structure` contracts) + complete verified decompilation from `Main` (`5` headline theorems) → `allChi` → `everyCharacter` → `everyCharacter_of_row` + **`331,598`-decl shared diamond** (`110,898` direct dominator children under `everyCharacter`).
- **D2 — Four Mathematical Pillars (`theta`, `galois`, `volume`, `window`):** Each pillar produces BOTH a machine-readable JSON DAG (`outputs/decomp/pillar_*.json`, schema posted on the board by `spine`) AND a brutally honest reverse-engineering dossier (`analysis/pillar_*.md`) grounded directly in read `.lean` signatures (depth 0–10+ along the dominator/Horn spine), naming:
  - exact formal `structure` / `def` / `Prop` contracts (every field listed & unfolded to Mathlib/ground types or flagged `OPAQUE`),
  - actual hypothesis→conclusion chain (distinguishing `[L]` real dependency edges vs `[A]` author-note claim vs `OPAQUE`),
  - explicit **Real vs Wrapper/Boilerplate/Vacuity Verdict** for each key lemma/named "published theorem" (`zarhin`, `fargues`, `poitouTate`, `abelianDeRham`, `harishChandraFinite`, `globalEulerChar`, `jacquetRallis`, `localConverseGL`, `deRham_potentiallySemistable`, etc.) — calling out degenerate or non-standard formalizations directly!
- **D3 — Layer 2 Semantic TCB & Contract Audit (`tcb`):** Inspects the `5` headline theorems, `Formalism.Gz` / `Gchi` (esp. the `χ = 1` division-by-`LFunction χ 1` question), `OpenLiteratureStatements`, `EveryCharacter`, `Row0b`, `VWin`, `IsRecT`, `ZeroFreeAll`, `Hyps`, `Closed`, `LinkN`, `DRS`, checking whether ANY bridge contract hides a vacuous hypothesis, degenerate instance, division-by-zero coercion, `rfl`-collapsed alias, or mismatch with standard mathematics.
- **D4 — Kernel Fixes & Computation/Dead-Code Atlas (`kernel`, `arch`):**
  - Fix the `lean4lean` timeout bug caught post-Phase-3: accurately resolve `ChebyshevPrimeBounds.SmallLoop` (9 live decls) AND determine with mathematical certainty whether `DyadicPrimeIntervals.Run1..4` (`PI.PrimesDyadicRS.K.run1..4`) are truly absent from `solution.ndjson.zst` (and check their `src/` importers!).
  - Reusable kernel-exact **cone slicer** (`leanre kernel slice <decl>`).
  - Full classification of the `28,904` `.lean` files with `0` matched live kernel decls (`truly unused/dead` vs `import-shim/re-export` vs `macro/elab/tactic-only` vs `alignment gap` vs `private/instance-only`).
  - Complete inventory of brute-force kernel computation (`decide +kernel`, `kexactB`, `CutCptCopy`, prime tables, dyadic intervals, factorial ladders, exact numeric thresholds).
- **D5 — FLIRT Calibration & Structural Clustering (`flirt`):**
  - Fix the **67% noise problem** in Tier 1 (`117,065` flagged modules → separate the bulk systematic namespace dump inside `AbelianVarietyTheory` from true high-precision misfile outliers, reporting exact precision/FDR & calibrated tier bands).
  - Cluster the live kernel graph into human-legible **semantic neighborhoods / coarse blueprint modules** (collapsing boilerplate wrappers & `CutCptCopy` shells).
  - **Expanded name-blinded Tier 3** with 1–2-hop type unfolding (replacing opaque project `def` names with their unfolded Mathlib primitives) on ≥100 high-leverage spine/diamond/pillar nodes (using `llm-fast` helpers if desired) to test whether unfolding lifts agreement above the Phase 3 `54.2%` baseline.
- **D6 — Interactive Proof-Untangling Workbench (`workbench`):** Wire `outputs/decomp/*.json` + calibrated FLIRT + kernel `slice` explorer into `workbench/` with interactive clickable spine/pillar blueprint view, side-by-side contract inspector, real headless-Chrome selftest & security probe pass.
- **V4 — Independent Math & Guardrail Audit (`verifier`):** Clean-room check of every mathematical claim, header quote, count, and dead-code claim in `analysis/*.md` and `outputs/decomp/*.json` against actual `.lean` files and `kernel.db`; spot-check for vacuity/bluffing/slop/license leaks (`R2` hard cap on body quoting); full `unittest` + `cargo test` + Chrome `#selftest=1` pass.
