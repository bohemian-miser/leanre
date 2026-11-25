# Lean Slopscore (`0–100`) & Blind Alternatives-First Audit Protocol

`leanre slop` measures how strongly a Lean 4 module, directory, or full formalization works **against the grain** of Lean 4 and Mathlib on a deterministic `0–100` scale (**lower is cleaner**; `≤ 15` passes the human Mathlib baseline; `100` is maximally glued-together, brute-forced, or scaffold-heavy).

## 1. Empirical Calibration

The rubric is calibrated against two ground-truth datasets rather than arbitrary style rules:

1. **Four human Mathlib-style baselines** — `SpherePacking`, `Carleson`, `FLT`, and `PrimeNumberTheoremAnd` — ensuring idiomatic human Lean 4 repositories stay cleanly `≤ 15` without false-positive penalties on normal one-line term proofs or Mathlib specialization lemmas.
2. **668 merged refactor PRs on `leanprover-community/riemann-hypothesis`** — covering Mathlib reuse and alignment, collapsing thin forwarding wrappers (`first | exact`) inside clumped files, removing redundant `attribute [local instance]` declarations, unifying twin copy-paste structures, pruning unused imports and unused structure fields, and eliminating brute-force tactic overrides (`maxHeartbeats`, `erw`/`convert` churn). Every merged cleanup pattern monotonically lowers the affected module's score.

> **Scope note:** A high slop score measures structural friction, glue code, and readability debt — **not** logical unsoundness. Conversely, a low slop score (`≤ 15`) does not constitute mathematical peer review.

## 2. Five Weighted Pillars

Formatting and comments are **hard-capped at `≤ 5` points** so stylistic polish can never mask structural or architectural debt:

| Pillar | Cap | Primary Signals |
| --- | ---: | --- |
| **1. Library grain** (`library_grain`) | `25` | Blanket `import Mathlib`, bloated import walls (`≥ 25` Mathlib imports or `≥ 35` imports on small files), `attribute [-instance]` / `attribute [local instance]` workarounds, low kernel library reuse (`< 15%`), custom `macro`/`syntax`/`elab` rules, global notations. |
| **2. Fragmentation & gluing** (`fragmentation`) | `25` | Single-theorem `:= by first \| exact` restate shims, `value_nodes == 1` kernel renaming shells, uncollapsed `first \| exact` wrappers inside `clump:auto` files, sibling `zlib` boilerplate repetition (`≥ 50%`), cross-repo normalized duplicate theorem statements, twin copy-paste structures sharing `≥ 5` identical sorted fields, numbered/variant twin declarations (`Foo` + `Foo2`/`FooAlt`), low name compressibility. |
| **3. Brute-force & compiler hammering** (`brute_force`) | `25` | `set_option maxHeartbeats` escalations, `exact_by_kernel` / `Kernel.isDefEq` / `run_tac` bypasses, kernel `type_nodes ≥ 10k` or proof AST `≥ 500` nodes/line, numbered `have h1..hN` chains, `≥ 20`-step unsegmented `have` walls without prose comments, deep anonymous `⟨_,_,_,_,_⟩` tuple unpacking, high `erw`/`convert`/`change`/`simp [*]` density, `≥ 160`-line commentless monolith declarations, `decide +kernel`, numeric table walls (`≥ 20%` digits). |
| **4. Scaffolding & over-bundled contracts** (`scaffolding`) | `20` | Zero-live-kernel modules, high intra-file dead declaration ratio (`≥ 35%`), `set_option linter.* false`, over-bundled structures (`≥ 10` fields) & kernel-unread structure fields, oversized signatures (`≥ 12` lines), placeholder/stub artifacts (`UnusedSlot*`, `:= True`, `*Placeholder`), dropped hypotheses (`intro _ _`). |
| **5. Hygiene** (`hygiene`) | `5` | Hard-capped light context signal: missing `/--` docstrings on multi-declaration files, zero comments on `≥ 40`-line files, excessive line width (`≥ 25%` over 120 chars or max line `≥ 220`). |

When structural points (`raw_sum - hygiene`) reach `≥ 14`, scores apply a `1.32×` contrast stretch (capped at `100`) to separate genuinely against-the-grain files from mildly noisy files while keeping clean human Mathlib files well below `15`.

## 3. CLI Usage

```bash
# Score a Lean 4 source directory (optionally enriched with kernel.db)
python3 leanre/leanre.py slop scan data/rh_mirror/src \
    --slug riemann-hypothesis \
    --kernel-db outputs/kernel/kernel.db \
    --out outputs/slop_rh_orig.json

# Apples-to-apples diff between two snapshots + live cold-gap detection (0 open PRs)
python3 leanre/leanre.py slop diff outputs/slop_rh_orig_src.json outputs/slop_rh_cleanup.json \
    --gh-repo leanprover-community/riemann-hypothesis \
    --label-before "Original archive (40e56bab)" \
    --label-after "Community cleanup (HEAD)" \
    --out outputs/rh_cleanup_diff.json

# Validate PR-extensible blind audit round records
python3 leanre/leanre.py slop audits --dir notes/audits
```

### Schemas

- `leanre.slop/1` — Per-project readability report (`data/slop.json`), including corpus line-weighted score, median/p90 module scores, 5-pillar means, score histogram, L1/L2/L3 directory rollups, and `Impact × Slop` audit queue hotspots.
- `leanre.slop_diff/1` — Commit-vs-commit comparison (`data/cleanup_diff.json`) with apples-to-apples deltas, top improved/regressed directories, and **Cold High-Slop Gaps** (high-slop L3 directories with zero matching open upstream PRs).
- `leanre.audits/1` — PR-extensible ledger of blind reconstruction audit rounds under `notes/audits/`.

## 4. Blind Alternatives-First Reconstruction Test (Audit Rounds)

Static metrics catch surface and structural anti-patterns, but the gold standard for mathematical readability is whether an independent reader or agent can understand and re-prove a module idiomatically. Each human or AI audit round recorded in `notes/audits/` follows the **Blind Alternatives-First Reconstruction Test**:

1. **Extract only the public statement interface** (imports, types, and theorem signatures — hiding proof bodies and internal helper wrappers).
2. **Design alternatives first (blind):** Without peeking at the original proof body, sketch 2–3 idiomatic Mathlib-native proof strategies and note which existing Mathlib lemmas or structures naturally carry the argument.
3. **Reconstruct and compare:** Attempt a clean proof (or inspect the original only after locking the blind design), then score the structural gap (`blind_slop`, `0–100`) between the original implementation and the idiomatic reconstruction:
   - `0–15`: Idiomatic — matches the natural Mathlib route with minimal glue.
   - `16–35`: Minor friction — local wrappers or avoidable type coercion.
   - `36–60`: Against the grain — custom re-implementations, heavy tuple plumbing, or uncollapsed restate layers.
   - `61–100`: Brute-force / opaque — extreme heartbeat overrides, monolithic `have h1..hN` walls, or dead scaffolding requiring architectural rewrite.
4. **Log the round** in `notes/audits/contrib/<author>__<slug>.json` (referencing pinned commit SHAs only; never pasting verbatim third-party Lean proof bodies) and validate with `python3 leanre/leanre.py slop audits --dir notes/audits`.
