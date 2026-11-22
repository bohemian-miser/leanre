# FLIRT for Lean — Architecture, Schemas & Guardrails

> **Epistemic scope & Guardrails 1–6 (`research/04_verification_and_roadmap.md` §2):**
> * **Tier 1** (`leanre/flirt/tier1.py`) and **Tier 2** (`leanre/flirt/tier2.py`) are 100% deterministic, zero-ML static extractors; every count, fingerprint, misfile score, clone cluster, and signature match is tagged **[L]** (extracted by us from pinned local inputs).
> * **Tier 3** (`leanre/flirt/tier3.py`) generates **heuristic AI-draft labels** strictly from name-blinded declaration headers, Mathlib imports, and standard `open` namespaces (zero proof bodies). Every Tier 3 output is tagged **[M]** with an explicit `breaks` caveat, lives **only** in an off-by-default `ai-draft` annotation layer (`default_on: false`, `draft: true`), and is **never** presented as `[L]` fact.
> * **Four-layer separation (Guardrail 1):** FLIRT instruments **Layer 3** (structural reverse engineering & human intelligibility) and **Layer 2** (statement-level cross-referencing). It makes **zero** claim about **Layer 1** kernel soundness (covered by `docs/KERNEL.md`) or **Layer 4** mathematical peer consensus.
> * **[M] Analogy & where it breaks:** Named after IDA Pro's FLIRT (Fast Library Identification and Recognition Technology), which fingerprints compiled library routines to isolate novel code in stripped binaries. The analogy **breaks** in Lean 4 because (a) two declarations with identical normalized statement shapes (`s1n`/`s1t`/`s1a`/`k1n`/`k1a`) need not rely on identical underlying definitions (especially when project-local symbols are abstracted), and (b) unmatched proof declarations are *not* evidence of mathematical novelty (source-level recall is bounded by syntax/notation differences).

---

## 0. Three-Tier Overview

| Tier | Owner | Module(s) | Outputs | Epistemic Tag |
|---|---|---|---|---|
| **Shared Spec** | `flirt` | `leanre/sighash.py` | `docs/SIGHASH.md` (`k1n`/`k1a`/`s1n`/`s1t`/`s1a`) | `[L]` |
| **Tier 1 (Calibrated Deterministic)** | `flirt` | `leanre/flirt/tier1.py` | `outputs/flirt/tier1.db` *(gitignored)*, `outputs/flirt/tier1_summary.json` | `[L]` |
| **Coarse Blueprint Clustering** | `flirt` | `leanre/flirt/cluster.py` | `outputs/flirt/clusters.json` | `[L]` |
| **Tier 2 (Cross-Repo)** | `xrepo` | `leanre/flirt/tier2*.py` | `outputs/flirt/tier2.db` *(gitignored)*, `outputs/flirt/tier2_summary.json`, **`docs/FLIRT_TIER2.md`** | `[L]` |
| **Tier 3 (Name-Blinded + Unfolded AI)** | `flirt` | `leanre/flirt/tier3.py` | `outputs/flirt/tier3_blinded_prompts.jsonl`, `outputs/flirt/tier3_pilot.json`, `outputs/flirt/tier3_ai_draft_pack.jsonl` | `[M]` (`ai-draft`) |

All committed outputs under `outputs/flirt/` contain **identifiers, counts, hashes, scores, and cluster metadata only** — never raw `.lean` source files or proof bodies (Guardrail 3 / Guardrail 6).

---

## 1. Tier 1 — Calibrated Deterministic Fingerprinting, Misfile Detection & Boilerplate Collapse (Gates F1 & D5)

### 1.1 Pinned Input & Reproduction

```bash
python3 leanre/flirt/tier1.py \
  --src data/rh_mirror/src \
  --expect-files 175187 \
  --threads 16 \
  --kernel-db outputs/kernel/kernel.db
```

* Input [L]: `Deicyde/riemann-hypothesis@40e56bab026552e089d7afcfeff08d2defb9c005` (`175,187` `.lean` files asserted by `--expect-files 175187`, `17,374,215` `wc -l` lines, `1,057,984` Lean-scoped named declarations).
* Runtime: ~115–121 s on 16 threads; writes `outputs/flirt/tier1.db` (314 MB, atomic rename, gitignored) and `outputs/flirt/tier1_summary.json` (260 KB, committed).
* Unit tests (synthetic fixtures): `python3 -m unittest leanre/test_flirt_tier1.py -v` (`3/3` OK).
* Independent F1 verifier: `python3 verify/f1_tier1_check.py` (`8/8` PASS).

### 1.2 Empirical Mathlib-Import Finding & Header-Only Fingerprinting [L]

Across all `175,187` modules:
* **`136,003`** modules (`77.6%`) use blanket `import Mathlib` (of which **`19,750`** duplicate `import Mathlib` at least twice).
* Only **`278`** modules (`0.16%`, `485` import lines) import granular `Mathlib.<Area>.*` submodules.

Because blanket `import Mathlib` carries almost no topic signal on its own, Tier 1 computes each module's fingerprint from **four body-free signals**:
1. Granular `Mathlib.*` / `Lean.*` / `Batteries.*` subimports (weight `3.0`).
2. Non-project `open` / `open scoped` namespaces (weight `2.0`).
3. Non-local header type-tokens extracted strictly from declaration binders & result types via `sighash.iter_source_decls` + `sighash.source_sig` (excluding project-local names resolved via the in-memory declaration lexicon, bound `#k`, universes `u#k`, and generic stop tokens; also capturing Lean 4 dot-notation domain projections such as `#0.Prime`; weight `1 + log2(count)`).
4. Explicit computational/metaprogramming markers (`decide +kernel`, `kexactB`, `kcopy`, `CutCptCopy`, `addDecl`, `run_tac`), tracked per enclosing declaration (weight `3.0`).

These feed an 11-domain deterministic taxonomy (`prime_elem_arith`, `analytic_nt_zeta`, `complex_real_analysis`, `measure_integration`, `algebraic_geometry`, `padic_local_fields`, `linear_matrix_rep`, `algebra_rings_poly`, `topology_manifold`, `computational_kernel_check`, `meta_lean_elab`) and a sparse L2-normalized TF-IDF sibling centroid per `folder_l3` (fallback `folder_l2` when `< 5` non-shim siblings).

### 1.3 Declared-Namespace vs Folder-Path Mismatch & Exact F1 Reproduction [L]

Tier 1 records **both** namespace counting rules explicitly in `namespace_folder_matrix(folder_l2, counting_rule, declared_ns, decl_count, module_count)`:

| Counting rule | Total decls under `Development.AbelianVarietyTheory` (`99,187` modules) | #1 namespace | #2 namespace | #3 namespace |
|---|---:|---:|---:|---:|
| **`phase2_literal_2comp`** *(column-0 keyword decls grouped by first 2 name components using Phase-2 `scanner.py` rules: literal `_root_.` kept as component 0; anonymous `end` pops namespace stack)* | **`457,031`** | `_root_.GlobalTheory`: **`39,212`** *(39,179 mods)* | `GlobalTheory.IndefiniteRowSideFullHecke`: **`14,165`** *(762 mods)* | `GlobalTheory.Mem`: **`11,592`** *(1,455 mods)* |
| **`lean_scoped_2comp`** *(column-0 named decls with `_root_.` stripped and `section`/`namespace`/multi-component `end` tracked via `sighash.iter_source_decls`)* | **`455,707`** | `GlobalTheory.T`: **`39,077`** *(39,044 mods)* | `GlobalTheory.IndefiniteRowSideFullHecke`: **`14,117`** *(762 mods)* | `GlobalTheory.Mem`: **`11,626`** *(1,456 mods)* |

*Note on the two rules:* The Phase-2 `39,212` `_root_.GlobalTheory` bucket arises almost entirely from single-declaration `*Statement` forwarding wrappers declaring `theorem _root_.GlobalTheory.T.<name> : ...` inside `Development/AbelianVarietyTheory/` (`27,878` `root_exact_forward` wrappers + `1,276` `root_statement_wrapper` wrappers). Both rules are stored side-by-side so Gate F1 reproduces `39,212 / 14,165 / 11,592` to the exact digit while `lean_scoped_2comp` exposes the true Lean namespace `GlobalTheory.T`.

### 1.4 Calibrated Multi-Band Misfile Scoring & Bulk Remapping Separation (Phase 4 D5, Zero Hardcoding) `[L]`

Phase 3 flagged `117,065` modules (`66.8%` of corpus) because the repo applies **systematic bulk folder → namespace remappings** (for example, `99.94%` of `Development.AbelianVarietyTheory` declares `GlobalTheory.*`, `100.0%` of `Development.AutomorphicSpectrum` declares `GlobalTheory.*`, `74.75%` of `Development.AutomorphicArithmetic` declares `UpperTheory.*`, `74.10%` of `Development.WeilBound` declares `PositivityTheory.*`, `78.82%` of `Formalism.PeriodIntegrals` declares `PI.*`, `99.79%` of `Development.EtaleCohomology` declares `LateralTheory.*`).

Phase 4 (`leanre.flirt.tier1/2`) separates **bulk folder→namespace remappings** from **isolated misfile outliers** automatically with zero hardcoded names:
1. **Bulk remapping detector (`bulk_namespace_remappings`):** Any `(folder_l2, declared_top_ns)` pair where `declared_top_ns ≠ folder_l2.split('.')[0]` with `>= 20` modules **and** `>= 10%` of `folder_l2`'s non-shim modules is classified as a systematic bulk remapping (`16` pairs detected, covering **`125,598`** modules = **`71.694%`** of corpus).
2. **Anomaly scoring formula** (for every non-shim module with `decl_count >= 1` and non-empty folder path):

```
raw = 0.28 * ns_outlier
    + 0.28 * folder_domain_conflict
    + 0.24 * centroid_distance
    + 0.20 * graph_isolation
    + (0.05 if top_ns_mismatch and not is_bulk_remap else 0.00)   # capped at 1.0
score = min(1.0, raw) * (0.50 if is_statement_wrapper else 1.00)
```

* `ns_outlier` = `1 / (1 + log10(ns_count_in_folder_l2))` when `ns_mismatch > 0` (computed on the 2-component declared namespace even inside a bulk-remapped folder, so an isolated namespace like `GlobalTheory.PrimeRecip` (`1 / 99,176` → `1.00`) still stands out sharply from pervasive conventions like `GlobalTheory.T` (`39,044 / 99,176` → `0.18`)).
* `folder_domain_conflict` = `1 - mass_in_expected_domains` when CamelCase folder words imply expected domain(s) and the module has ≥ 3 domain-weighted token hits (`0.0` for neutral folder names).
* `centroid_distance` = `1 - cosine_sim(module_tfidf, folder_l3_centroid)` ∈ `[0, 1]` (using leave-one-out sibling centroid on small folders `5 <= n <= 30` so small-folder outliers do not dilute their own distance).
* `graph_isolation` = `1.0` when `proj_import_count == 0` in a folder averaging ≥ `0.5` project imports; else `1 - same_folder_l2_import_ratio`.

**Calibrated Multi-Band Counts & Independent Kernel-Verified Precision (`outputs/kernel/kernel.db` 1-hop library type-dep cross-check, stride sample up to `400` live modules/band) `[L]`:**

| Band | Stored in `misfiles`? | `tier` | Modules | % of corpus | Live in kernel | Kernel-checked sample | Kernel domain-conflict precision *(0 expected-domain kernel lib deps)* |
|---|---|---|---:|---:|---:|---:|---:|
| **`extreme_outlier`** *(non-wrapper, `score >= 0.90`, `conflict >= 0.80`, `ns_rarity <= 0.005`)* | Yes | `high` | **`714`** | `0.408%` | `618` (`86.55%`) | `399` | **`84.21%`** (`336 / 399`) |
| **`cross_domain_misfile`** *(non-wrapper, `score >= 0.75`, `conflict >= 0.60`)* | Yes | `high` | **`2,569`** | `1.466%` | `2,264` (`88.13%`) | `400` | **`83.00%`** (`332 / 400`) |
| **`isolated_ns_outlier`** *(`score >= 0.65` non-bulk, or `>= 0.70` & `ns_rarity <= 0.02` in bulk folder)* | Yes | `medium` | **`17,409`** | `9.937%` | `14,660` (`84.21%`) | `397` | **`53.15%`** (`211 / 397`) |
| *Alertable `misfiles` total* | *Yes* | *`high`+`medium`* | **`20,692`** | **`11.811%`** | *`17,542`* | — | *Down from Phase 3 `117,065` (`66.8%`); `high` cut from `27,832` → **`3,283`** (`1.87%`)* |
| **`bulk_namespace_remapping`** *(excluded from `misfiles`)* | No *(tracked in `bulk_namespace_remappings`)* | — | **`125,598`** | `71.694%` | `104,868` (`83.49%`) | `379` | **`44.33%`** (`168 / 379`) |
| **`normal`** *(plus `179` unscored: `150` import shims + `27` non-shim `0`-decl files + `2` root-folder modules `Main`, `Statements`)* | No | — | **`28,718`** | `16.393%` | — | — | — |

Precision increases monotonically across all four bands (`44.33% → 53.15% → 83.00% → 84.21%`), confirming that bulk remapping separation isolates genuine cross-domain misfiles without throwing away live proof modules.

**F1 Known Misfile Verification [L]:**
Without any hardcoded module or declaration names, calibrated Tier 1 v2 flags:
* **Module:** `Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes` (`Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean`)
* **Flagged declaration:** `GlobalTheory.PrimeRecip.table_ok` (`decide_kernel`, line 301)
* **Score / Tier / Band / Rank:** **`0.9944`** / **`high`** / **`extreme_outlier`** / rank `#200` of `20,692` alertable misfiles (`175,187` modules)
* **Measured breakdown:** `declared_ns=GlobalTheory.PrimeRecip` (isolated `1/99,176` in bulk-remapped `Development.AbelianVarietyTheory`), `folder_expected=algebraic_geometry` vs `domain_observed=computational_kernel_check+complex_real_analysis` (`conflict=1.00`), `sibling_centroid_dist=0.98`, `0` project imports (`graph_isolation=1.00`), `flags=decide_kernel`.

Other high-scoring genuine `extreme_outlier` misfiles surfaced automatically under `Development/AbelianVarietyTheory/Proofs/`: `LogFactorialEqSumVonMangoldtMulDiv` (Chebyshev identity under `IwasawaDecomposition`), `HasTemperateGrowthElim` & `SchwartzSeminormSmulLeftLinearPhaseLe` (Schwartz-space analysis under `DivisorProofs`), `LegendreBoundsFactorialMultiIndexCapelli` (factorial digit-sum bounds under `UnramifiedDepth`), `SumLogDivSqPrimesTail` (prime tail sum under `DivisorProofs`).

### 1.5 Boilerplate & Clone Collapse [L]

| Cluster `kind` | Clusters | Modules covered | Redundant modules | Largest cluster | Definition |
|---|---:|---:|---:|---:|---|
| `alpha_body_clone` | **`1,192`** | **`4,787`** | **`3,595`** | `385` | Exact Phase-2 alpha-renamed file-body hash (`blake2b`, reproduces Phase 2 exactly) |
| `sigset_clone` | **`15,574`** | **`36,195`** | **`20,621`** | `2,418` | Identical sorted multiset of `(decl_kind, s1t)` signature hashes across differing proof bodies *(note: largest cluster groups single-decl `def X : Prop` statement placeholders)* |
| `import_shim` | **`1`** | **`150`** | **`150`** | `150` | Import-only re-export modules with 0 declarations (reproduces Phase 2 exactly) |
| `statement_wrapper` | **`8`** | **`35,193`** *(35,196 total)* | **`35,193`** | `27,878` | Single-decl `<= 15`-line `*Statement` forwarding wrappers grouped by `(folder_l2, wrapper_kind)` |

### 1.6 `outputs/flirt/tier1.db` SQLite Schema (`leanre.flirt.tier1/2`, backward-compatible with v1)

All analysis tables are read-only (`mode=ro`) for `workbench` and downstream tools:

```sql
meta(key TEXT PRIMARY KEY, value_json TEXT NOT NULL)

module_fingerprints(
    module TEXT PRIMARY KEY, file_path TEXT, folder_ns TEXT, folder_l2 TEXT, folder_l3 TEXT,
    lines_wc INTEGER, decl_count INTEGER, is_shim INTEGER, is_statement_wrapper INTEGER,
    imports_mathlib_all INTEGER, mathlib_subimports_json TEXT,
    proj_import_count INTEGER, same_folder_import_ratio REAL, opens_json TEXT,
    declared_ns_primary TEXT, declared_ns_all_json TEXT, uses_root_escape INTEGER,
    top_domain TEXT, domain_vector_json TEXT, type_tokens_top_json TEXT,
    fp_hash TEXT, sigset_hash TEXT, alpha_clone_sig TEXT, forensic_flags_json TEXT
)

misfiles(
    rank INTEGER PRIMARY KEY, module TEXT UNIQUE, file_path TEXT,
    declared_ns TEXT, folder_ns TEXT, folder_l2 TEXT,
    score REAL, tier TEXT, ns_mismatch_kind TEXT,
    ns_count_in_folder INTEGER, ns_rarity_in_folder REAL,
    domain_expected TEXT, domain_observed TEXT, folder_domain_conflict REAL,
    centroid_distance REAL, graph_isolation REAL, is_statement_wrapper INTEGER,
    flag_decl TEXT, reason TEXT, provenance TEXT,
    band TEXT, is_bulk_remap INTEGER
)

bulk_namespace_remappings(
    folder_l2 TEXT, declared_top_ns TEXT,
    module_count INTEGER, folder_non_shim_count INTEGER, share_of_folder REAL,
    PRIMARY KEY (folder_l2, declared_top_ns)
) WITHOUT ROWID

namespace_folder_matrix(
    folder_l2 TEXT, counting_rule TEXT, declared_ns TEXT,
    decl_count INTEGER, module_count INTEGER,
    PRIMARY KEY (folder_l2, counting_rule, declared_ns)
) WITHOUT ROWID

boilerplate_clusters(
    cluster_id TEXT PRIMARY KEY, kind TEXT, size INTEGER, redundant_modules INTEGER,
    total_lines INTEGER, representative TEXT, sig_hash TEXT, summary TEXT,
    sample_members_json TEXT
)

boilerplate_members(
    cluster_id TEXT, module TEXT, lines_wc INTEGER,
    PRIMARY KEY (cluster_id, module)
) WITHOUT ROWID

folder_fingerprints(
    folder TEXT, depth INTEGER, module_count INTEGER, non_shim_count INTEGER,
    decl_count INTEGER, lines_wc INTEGER, mathlib_all_count INTEGER,
    expected_domains_json TEXT, top_domains_json TEXT,
    top_declared_ns_json TEXT, top_type_tokens_json TEXT,
    PRIMARY KEY (folder, depth)
) WITHOUT ROWID
```

---

## 2. Tier 2 — Cross-Repo Signature Database (Gate F2)

Owned by `xrepo` and built directly on `docs/SIGHASH.md` v1 (`s1n` / `s1t` / `s1a` + kernel `k1n` / `k1a`). See **`docs/FLIRT_TIER2.md`** for pinned corpora (`mathlib4`, `lean4`, `batteries`, `PrimeNumberTheoremAnd`, `FLT`, `carleson`, `SpherePacking`), per-variant FDR thresholds, precision/recall/FPR controls, and `outputs/flirt/tier2.db` schema.

---

## 2b. Coarse Kernel Blueprint Clustering & Live Boilerplate Collapse (Phase 4 D5) `[L]`

To give `workbench` and human reviewers a navigable ~150-node architectural map of the `1,468,414`-declaration live cone without relying on misleading source folders, `leanre/flirt/cluster.py` partitions **100% of live kernel declarations** directly from `outputs/kernel/kernel.db` (`mode=ro`, dominator tree `ALL` `tree_id=0` + exact directed `edges`) joined read-only with `outputs/flirt/tier1.db` (`mode=ro`).

### 2b.1 Partition & Boilerplate Collapse Accounting `[L]`

1. **Kernel-graph-aware coarse partitioning:**
   * Isolates the Lean/Mathlib `tcb_library_root` (`BP005`, `58,857` live decls rooted at `Eq`).
   * Recursively cuts dominator subtrees with `sub_size >= 1,500` (splitting subtrees `> 25,000` into child dominator subtrees until each cluster is legible), yielding **`90` `dom_subtree` clusters**.
   * Groups remaining shared-diamond / multi-parent residual declarations by `(pillar, dominant_2comp_namespace)` merged with directed edge affinity, yielding **`45` `residual_neighborhood` clusters** and **`5` `residual_tail` clusters**.
   * Total: **`141` coarse clusters** covering **`1,468,414 / 1,468,414`** (`100.0%`) live kernel declarations and **`2,099 / 2,099`** inter-cluster directed kernel edge pairs (`type_edges`, `value_edges`, `both_edges`, `total_edges`).
2. **Exact mutually exclusive live-cone boilerplate collapse** (precedence `aux > copy_shell > stmt_wrapper > k1n_dup > effective_core`):

| Category | Live Decls | Share of Live Cone | Definition |
|---|---:|---:|---|
| **`aux_collapsed`** | **`522,274`** | `35.57%` | Compiler-generated auxiliaries (`is_aux = 1`: `._proof_*`, `.match_*`, `.rec*`, `.inj*`, etc.) |
| **`copy_shell_collapsed`** | **`103`** | `0.01%` | `CutCptCopy` / `kcopy` / `kexactB` metaprogrammed kernel copy shells |
| **`stmt_wrapper_collapsed`** | **`29,520`** | `2.01%` | Live decls in Tier 1 `is_statement_wrapper = 1` `*Statement` forwarding files |
| **`k1n_dup_collapsed`** | **`70,021`** | `4.77%` | Non-primary duplicate kernel statement hashes (`k1n`) across distinct live decls |
| **Total collapsed boilerplate** | **`621,918`** | **`42.35%`** | Sum of the 4 disjoint categories above |
| **`effective_core_decls`** | **`846,496`** | **`57.65%`** | Distinct non-auxiliary, non-wrapper, non-copy-shell mathematical declarations |
| **Total live kernel decls** | **`1,468,414`** | **`100.00%`** | Exact match to `outputs/kernel/kernel.db` (`146,283` live modules + `28,904` dead modules = `175,187`) |

### 2b.2 Per-Pillar Coarse Breakdown `[L]`

| Pillar (`pillar`) | Clusters | Live Decls | Effective Core Decls | Boilerplate Collapsed | Live Modules |
|---|---:|---:|---:|---:|---:|
| `pillar_theta` | `45` | `543,325` | `293,032` | `46.07%` | `54,458` |
| `shared_diamond` | `31` | `372,427` | `223,688` | `39.94%` | `26,779` |
| `pillar_volume_lit` | `35` | `305,998` | `181,750` | `40.60%` | `45,238` |
| `pillar_galois` | `19` | `95,102` | `52,308` | `45.00%` | `12,780` |
| `pillar_window` | `10` | `92,705` | `53,568` | `42.22%` | `11,297` |
| `tcb_mathlib_core` | `1` | `58,857` | `42,150` | `28.39%` | `8` |
| **Total** | **`141`** | **`1,468,414`** | **`846,496`** | **`42.35%`** | **`146,283`** *(unique across clusters)* |

### 2b.3 `outputs/flirt/clusters.json` Schema (`leanre.flirt.clusters/1`, 1,005 KB) & Reproduction

* Top-level keys: `schema`, `provenance`, `elapsed_seconds`, `params`, `totals`, `by_pillar`, `clusters[]`, `edges[]`.
* Each `clusters[]` item: `cluster_id` (`BP001`..`BP141`), `kind` (`dom_subtree` | `residual_neighborhood` | `residual_tail` | `tcb_library_root`), `pillar`, `root_decl`, `root_decl_id`, `idom_name`, `dom_depth`, `live_decls`, `user_decls`, `aux_collapsed`, `copy_shell_collapsed`, `stmt_wrapper_collapsed`, `k1n_dup_collapsed`, `effective_core_decls`, `collapse_pct`, `live_modules`, `total_lines_wc`, `intra_edges`, `in_degree_clusters`, `out_degree_clusters`, `tier1_top_domain`, `top_namespaces`, `top_folders_l2`, `compute_flags`, `boundary_decls`, `title_hint`, `provenance` (`"L"`).
* Each `edges[]` item: `{src, dst, type_edges, value_edges, both_edges, total_edges, provenance: "L"}`.

```bash
python3 -m unittest leanre/test_flirt_cluster.py -v
python3 leanre/flirt/cluster.py \
  --kernel-db outputs/kernel/kernel.db \
  --tier1-db outputs/flirt/tier1.db \
  --out outputs/flirt/clusters.json
```

---

## 3. Tier 3 — Name-Blinded AI Labeling with 1–2-Hop Kernel Type Unfolding (Gates F3 & D5)

### 3.1 Anti-Slop, 1–2-Hop Kernel Contract Unfolding & Double-Blind Protocol

To guard against the **Double-AI Slop Trap** (`research/04_verification_and_roadmap.md` §4 item 4 — an LLM hallucinating mathematical narratives from misleading AI-generated folder/file names), Tier 3 enforces five hard structural invariants:

1. **Header-only extraction:** Prompts include only Mathlib/Lean core imports, standard `open` namespaces, generic structural flags (`kernel_decide`, `metaprogram_decl_emitter`), cluster import degree counts, and canonical declaration headers (`sighash.source_sig` output). **Zero proof bodies are ever read or narrated.**
2. **1–2-hop kernel contract type unfolding (`KernelTypeUnfolder`, Phase 4 D5):** Phase 3 showed that opaque Horn-clause boundaries (`P001 → P002`) hide Mathlib types behind 1–2 layers of project-local `def` / `inductive` / `structure` wrappers. Phase 4 opens `outputs/kernel/kernel.db` read-only (`mode=ro`) and traverses **1–2 hops strictly through project-local `def`/`inductive`/`opaque`/`axiom` declarations** (NEVER traversing `thm` proof values), extracting direct Mathlib/Lean-core type dependencies filtered against Lean typeclass/algebra plumbing noise (`Field.toSemifield`, `Real.instLE`, etc.) and cross-checked against `std_allowlist` ∩ `tier2.db` library tokens. Across the 100 Phase 4 clusters, **`96 / 100`** receive non-empty unfolded Mathlib primitives (e.g. `NumberField.RingOfIntegers`, `IsDedekindDomain.HeightOneSpectrum`, `DirichletCharacter.LFunction`, `ValuationSubring`, `Padic`) with **zero project identifiers leaked**.
3. **Fail-closed name blinding:** A library allowlist (`outputs/flirt/cache/std_allowlist.txt`, ID `6122685b27dc2d38`) is built strictly from `mathlib4@0df444a3` (`8,311` files), `lean4@819816b2` (`2,485` files), and `batteries@4488d40d` (`191` files) (`321,671` library declarations; explicit `PROJECT_FORBIDDEN_ROOTS` subtracted). In blinded prompts (`outputs/flirt/tier3_blinded_prompts.jsonl`), every folder, file, namespace, and declaration name is replaced with deterministic opaque IDs (`C###`, `M##`, `D###`, `P###`, `f##`, `#k`, `u#k`). Any identifier not in the library allowlist fails closed to `P###`. Truncation occurs strictly on token boundaries.
4. **Provable leak test (`tier3.py leak-test` + `verify/f3_check.py`):** Runs two independent checks on every blinded record: (a) every alphabetic token in the data payload must be an opaque ID, Lean keyword, schema enum, or verified `std_allowlist` symbol; (b) zero project-exclusive folder/file/declaration names appear as tokens or substrings.
5. **Strict AI-draft layer isolation (`leanre/annot.py`):** The ingester (`tier3.py ingest`) refuses to emit `[L]`/`[A]`/`[C]`/`[S]` records or write into `human` layers. Every ingested label lands **only** in layer `ai/flirt-tier3-pilot` (`kind: "ai-draft"`, `default_on: false`, `draft: true`, `author: "ai:<model>"`, `tag: "M"`, mandatory `breaks` caveat), validated canonically via `annot.validate_text(..., canonical=True)`.

### 3.2 Phase 4 Controlled 3-Arm A/B Experiment — 100 High-Leverage Boundary Clusters `[M]`

Phase 4 scales Tier 3 from `24` to **`100` high-leverage boundary clusters (`C001`..`C100`)** across four cohorts (`20` calibrated Tier 1 `extreme_misfile` modules incl. `C020` `InvFiveLogLeSumInvPrimes`, `8` `spine_tcb` top-spine/pillar roots, `56` `pillar_dominator` subtrees from `clusters.json`, and `16` `diamond_neighborhood` residual clusters), evaluated in a controlled 3-arm experiment using three fresh isolated `llm-fast` instances:

* **Arm A — 0-hop Raw Blinded (`t3-raw-100`):** saw **only** `outputs/flirt/cache/tier3_blinded_raw_prompts.jsonl` (`unfold_hops=0`; `0` leaks across `13,070` tokens).
* **Arm B — 1–2-hop Unfolded Blinded (`t3-unfold-100`):** saw **only** `outputs/flirt/tier3_blinded_prompts.jsonl` (`unfold_hops=2`; **`0` leaks** across `23,358` tokens; `verify/f3_check.py` **8/8 PASS** against `3,485` folders, `167,045` file stems, `1,033,515` full decls, `697,966` leaf decls, and `35` landmarks).
* **Control — 0-hop Unblinded (`t3-unblind-100`):** saw **only** `outputs/flirt/cache/tier3_unblinded_prompts.jsonl` (real folder/module/declaration names + 0-hop headers, zero proof bodies).

**Summary Comparison — Phase 3 Baseline vs Phase 4 3-Arm A/B (`[L]` metrics over `[M]` labels):**

| Arm | `n` | Overall exact vs unblinded | Cohen's κ | Top-2 overlap | `other_mixed` abstentions | Mean conf | Degenerate `other_mixed == other_mixed` | **Substantive exact** *(on `54` concrete-domain control clusters)* | **Substantive top-2** *(on `54` concrete clusters)* |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| **Phase 3 baseline (0-hop blinded, `llm-reasoning-b`)** | `24` | `13 / 24` (`54.2%`) | `0.450` | `70.8%` | — | — | — | — | — |
| **Phase 4 Arm A: 0-hop raw blinded (`llm-fast`)** | `100` | `63 / 100` (`63.0%`) | `0.482` | `92.0%` | `55.0%` | `0.431` | **`37`** *(58.7% of raw matches!)* | `26 / 54` (`48.1%`) | `48 / 54` (`88.9%`) |
| **Phase 4 Arm B: 1–2-hop unfolded blinded (`llm-fast`)** | `100` | `42 / 100` (`42.0%`) | `0.346` | `76.0%` | **`10.0%`** *(`-45.0` pp)* | **`0.581`** *(`+0.150`)* | **`8`** *(`-29`)* | **`34 / 54` (`63.0%`)** *(`+14.8` pp vs raw; `+8.8` pp vs Ph.3)* | **`49 / 54` (`90.7%`)** |
| **Phase 4 Control: 0-hop unblinded (`llm-fast`)** | `100` | *(reference)* | — | — | `46.0%` | `0.772` | — | *(`54` concrete, `46` `other_mixed`)* | — |

**Per-Cohort Breakdown (Phase 4 100-Cluster A/B):**

| Cohort | `n` | 0-hop raw exact (κ / top-2) | 1–2-hop unfolded exact (κ / top-2) | Unfolded label Jaccard |
|---|---:|---:|---:|---:|
| **`extreme_misfile`** *(Tier 1 calibrated `extreme_outlier`, incl. `C020` `InvFiveLogLeSumInvPrimes`)* | `20` | `80.0%` (`0.748` / `100.0%`) | **`80.0%` (`0.748` / `100.0%`)** | `0.203` *(raw `0.175`)* |
| **`spine_tcb`** *(Statements/Main + major spine & pillar entries)* | `8` | `87.5%` (`0.750` / `100.0%`) | `62.5%` (`0.385` / `87.5%`) | `0.029` |
| **`pillar_dominator`** *(top `dom_subtree` clusters from `clusters.json`)* | `56` | `62.5%` (`0.375` / `89.3%`) | `30.4%` (`0.219` / `64.3%`) | `0.017` |
| **`diamond_neighborhood`** *(top `residual_neighborhood` clusters)* | `16` | `31.3%` (`0.245` / `87.5%`) | `25.0%` (`0.203` / `81.3%`) | `0.035` |

**Honest Interpretation of the Empirical Result (Why Raw vs Unfolded Diverge):**
1. **The `other_mixed == other_mixed` abstention illusion explains the raw-headline drop (`63.0% → 42.0%`):** On the `56` opaque Horn-clause `pillar_dominator` clusters, even the **0-hop unblinded control** abstained into `other_mixed` on **`46 / 100`** clusters because internal project names (`GlobalTheory.T.*`, `Formalism.L2.DIV.BrJ.*`) carry too little domain signal on their own. Arm A (0-hop raw blinded) also abstained on `55 / 100` clusters, producing **`37` degenerate `other_mixed == other_mixed` matches** (`58.7%` of all raw agreements).
2. **1–2-hop kernel contract unfolding genuinely breaks header opacity (`-45.0` pp abstentions, `+14.8` pp substantive lift):**
   * On the **`54` concrete-domain clusters** where the unblinded control committed to a mathematical domain (`unblinded ≠ other_mixed`), 1–2-hop unfolding lifted blinded exact agreement from **`48.1%` (`26/54`) → `63.0%` (`34/54`)** (**`+14.8` pp**, beating the Phase 3 `54.2%` baseline) and top-2 overlap to **`90.7%` (`49/54`)**, while lifting mean confidence from `0.431 → 0.581`.
   * On the **`46` opaque clusters where even the 0-hop unblinded control abstained**, 1–2-hop blinded unfolding resolved **`38 / 46` (`82.6%`)** into concrete Mathlib-grounded domains (`algebra_rings_poly` `14`, `padic_local_fields` `12`, `linear_matrix_rep` `8`, `analytic_nt_zeta` `2`, `measure_integration` `2`), leaving only `8 / 46` (`17.4%`) opaque — showing that kernel type unfolding surfaces real mathematical ground truth that **unblinded 0-hop names cannot see**.
3. **Why blinded-unfolded labels still disagree on `20 / 54` concrete clusters (confirming Guardrail 4):** On `C048` (`published_results_arithmetic`) and `C058` (`siegel_toroidal_integral_of_literature`), 2-hop unfolding exposed `DirichletCharacter.LFunction` contracts (`analytic_nt_zeta`) inside literature bundles whose filenames suggested `algebraic_geometry`; on `C039` (`volume_theorem_of_inputs`), `C056` (`HilbertSamuelMoriwaki.hsChain`), and `C096` (`HeightsAndTheta`), unfolding exposed `NumberField` / `IsDiscreteValuationRing` / `MvPolynomial` contracts (`algebra_rings_poly`) beneath `algebraic_geometry` names. On `C020` (`InvFiveLogLeSumInvPrimes`), both blinded (`computational_kernel_check`, `conf=0.90`) and unblinded (`prime_elem_arith`, `conf=0.93`) accurately described the prime-reciprocal `decide_kernel` check (`extreme_misfile` cohort: **`80.0%` exact, `100.0%` top-2 overlap**). All Tier 3 labels remain strictly quarantined in the off-by-default `[M]` `ai-draft` layer (`outputs/flirt/tier3_ai_draft_pack.jsonl`, `default_on: false`, `tag: "M"`, `draft: true`).

### 3.3 Output Schemas (`outputs/flirt/tier3_*`)

* `outputs/flirt/tier3_blinded_prompts.jsonl` — `100` canonical JSONL blinded prompt payloads with `unfolded_type_context` (`unfold_hops=2`, `prompt_sha256`, zero project names, zero proof bodies).
* `outputs/flirt/tier3_ai_draft_pack.jsonl` — canonical `leanre.annot/1` annotation pack (`ai/flirt-tier3-pilot`, `100` annotations, `default_on: false`, `tag: "M"`, `draft: true`), validated via `leanre annot validate`.
* `outputs/flirt/tier3_pilot.json` — structured report (`schema: leanre.flirt.tier3/2`) consumed by `workbench` (`/api/flirt/tier3`):
  * Top-level: `schema`, `provenance`, `breaks`, `layer`, `layer_kind`, `default_on`, `model`, `unfold_hops`, `generated_at`, `allowlist_id`, `lexicon_id`, `leak_test`, `agreement` (`agree`, `of`, `exact_rate`, `cohens_kappa`, `top2_overlap_rate`, `mean_label_jaccard`, `by_cohort`), `ab_unfolding_comparison` (`phase3_baseline_24`, `unblinded_control_0hop`, `raw_blinded_no_unfold`, `unfolded_blinded`, `delta_unfolded_minus_raw`, `delta_unfolded_minus_phase3_baseline`, `by_cohort`), `pack_file`, `pack_sha256`.
  * Per-cluster `clusters[]`: `cluster_id`, `cohort`, `target_kind`, `target_name`, `label`, `primary_domain`, `secondary_domain`, `model`, `author`, `layer`, `blinded`, `unblinded_label`, `unblinded_domain`, `agrees`, `confidence`, `size`, `members`, `declared_namespaces`, `evidence_tokens`, `uncertainty_note`, `prompt_sha256`, `provenance` (`"M"`), `draft` (`true`), `breaks`.

### 3.4 Reproduce Tier 3

```bash
python3 -m unittest leanre/test_flirt_tier3.py -v
python3 leanre/flirt/tier3.py prepare --mode phase4 --target-count 100 --unfold-hops 2 --workers 16
python3 leanre/flirt/tier3.py leak-test outputs/flirt/tier3_blinded_prompts.jsonl
python3 leanre/flirt/tier3.py ingest \
  --manifest outputs/flirt/cache/tier3_manifest.json \
  --blinded-labels outputs/flirt/cache/t3_labels_blinded.json \
  --unblinded-labels outputs/flirt/cache/t3_labels_unblinded.json \
  --raw-blinded-labels outputs/flirt/cache/t3_labels_blinded_raw.json \
  --model llm-fast
python3 leanre/annot.py validate outputs/flirt/tier3_ai_draft_pack.jsonl
python3 verify/f3_check.py
```
