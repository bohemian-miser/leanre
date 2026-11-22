# FLIRT Tier 2 — Cross-Repo Signature Matching

> **Epistemic scope & Guardrails 1–6:** Every count, hash, and match row documented here is **[L]** (extracted by us from pinned local inputs). None is an **[S]** claim about published mathematics.
>
> **What a match means — and does NOT mean:** A source-level match (`s1n` / `s1t` / `s1a`) means two declarations share the **same normalized statement shape** (binder telescope + result type, with own name, binder names, binder kinds, whitespace, and proof body removed per `docs/SIGHASH.md` v1). It is **NOT** evidence that the same mathematics is proved: source hashing performs no elaboration and no name resolution, identical text can elaborate differently under different `open`s or instances, and `s1a` deliberately abstracts project-local names into positional placeholders (`L#0`, `L#1`, …). Conversely, an unmatched proof declaration is **NOT** evidence of novelty — source-level recall against rephrased or notation-divergent statements is strictly limited (see §5–§6). Kernel-exact `k1n` matching (§7) eliminates elaboration ambiguity for statements that appear in `solution.ndjson.zst`, but still concerns **Layer 1 / Layer 2** syntactic/elaborated identity — never **Layer 3** (human comprehension) or **Layer 4** (mathematical consensus). [M: the IDA FLIRT analogy — fingerprinting library routines to separate standard math from a novel engine — breaks here because equal statement shapes do not imply equal definitions underneath, especially under `s1a` local-name abstraction.]

---

## 1. Pinned External Corpora (`outputs/flirt/tier2_corpora.json`)

All corpora are shallow-cloned into `data/corpora/` (**gitignored; never committed or redistributed**). `mathlib4` and `batteries` are pinned to the exact revisions in `data/rh_mirror/lake-manifest.json`; `lean4` is pinned to tag `v4.33.1` matching `data/rh_mirror/lean-toolchain` (`leanprover/lean4:v4.33.1`). The four non-library formalization projects are pinned to the commits observed on 2026-11-22 (they track newer Lean 4.35–4.36 toolchains; that skew is recorded per repo in `tier2_corpora.json`).

| Repo | URL | Commit SHA (pinned) | License | Toolchain | Subdirs | Lexicon ID (`s1a`) | `.lean` files [L] | Extracted sigs [L] |
|---|---|---|---|---|---|---|---:|---:|
| `mathlib4` | `https://github.com/leanprover-community/mathlib4` | `0df444a360eaa60ab8c11dca51a86af692955474` | Apache-2.0 | `lean4:v4.33.1` | `Mathlib` | *(library — none)* | 8,311 | 238,716 |
| `lean4` | `https://github.com/leanprover/lean4` | `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` | Apache-2.0 | `v4.33.1` (`stage1`) | `src/Init`, `src/Std` | *(library — none)* | 1,112 | 54,727 |
| `PrimeNumberTheoremAnd` | `https://github.com/AlexKontorovich/PrimeNumberTheoremAnd` | `a4fb6989b07e9c76b511807ae93e33e25b820e9b` | Apache-2.0 | `lean4:v4.35.0` | `PrimeNumberTheoremAnd` | `f542f725a8184a05` | 233 | 8,997 |
| `FLT` | `https://github.com/ImperialCollegeLondon/FLT` | `019805815d7da565ed1e9f427b6fbd0cbc9d00d3` | Apache-2.0 | `lean4:v4.35.0` | `FLT` | `c2048046017ea74d` | 260 | 3,133 |
| `batteries` | `https://github.com/leanprover-community/batteries` | `4488d40d070b9700d4d5a6aa342f0d40c31b2a2d` | Apache-2.0 | `lean4:v4.33.0` | `Batteries` | *(library — none)* | 191 | 3,033 |
| `carleson` | `https://github.com/fpvandoorn/carleson` | `f7487cc9da4d1e73f009dc0280cd5b958f3e2c78` | Apache-2.0 | `lean4:v4.36.0-rc1` | `Carleson` | `008cfc8fb5e4ef8f` | 124 | 3,021 |
| `SpherePacking` | `https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean` | `e07215872319dcadd7ced28670ae4daa13b74b8d` | Apache-2.0 | `lean4:v4.36.0` | `SpherePacking` | `e3bbec493c28953f` | 72 | 1,222 |
| **Total** | | | All Apache-2.0 | | | | **10,303** | **312,849** |

Target proof mirror [L]: `Deicyde/riemann-hypothesis@40e56bab026552e089d7afcfeff08d2defb9c005`, `175,187` `.lean` files, `1,056,258` extracted signatures (`817,403` theorems/lemmas: `782,764` `theorem` + `34,639` `lemma`; `238,855` non-theorems: `212,817` `def`, `13,125` `abbrev`, `8,120` `structure`, `4,652` `instance`, `98` `inductive`, `43` `class`). Proof lexicon: `outputs/flirt/cache/lexicon_rh.txt`, `lexicon_id = 294e04cd1ef65e37`, `1,051,704` declared names (`848,371` proof signatures reference at least one local identifier, `n_local > 0`).

---

## 2. Pipeline & SIGHASH v1 Integration

Code modules (all stdlib Python, multi-core capped at `--threads 24`, atomic DB build via `tier2_building.db` → rename):

- `leanre/flirt/tier2_corpora.py`: clones/verifies pinned commits + SPDX license headers, writes `outputs/flirt/tier2_corpora.json`.
- `leanre/flirt/tier2_extract.py`: source-level header extractor shared identically by both external corpora and the proof mirror. Strips comments, tracks `namespace`/`section`/`end`/`open`/`variable`/`include`/`omit`, approximates Lean 4 `variable` auto-inclusion, cuts strictly before the first depth-0 `:=`, `where`, or match-alternative `|` so **proof bodies are never emitted**.
- `leanre/flirt/tier2_sig.py`: binds to `leanre/sighash.py` (`sighash.source_sig`, frozen `docs/SIGHASH.md` spec v1) and returns `(s1n, s1t, s1a, n_tokens, n_local)`.
- `leanre/flirt/tier2.py`: parallel corpus + proof extraction, negative & restatement controls, per-variant FDR thresholding, SQLite build (`outputs/flirt/tier2.db`, gitignored) and committed summary (`outputs/flirt/tier2_summary.json`).
- `leanre/flirt/tier2_kernel.py`: kernel-exact matching (`k1n` / `k1a`) and ground-truth recall/precision audit against `outputs/kernel/kernel.db` (§7).

Three source-space schemes (per `docs/SIGHASH.md` §3–§4; never cross-compared with kernel `k1*` schemes):

| Variant | Meaning | Lexicon used |
|---|---|---|
| `s1n` | Exact free identifiers as written (normalized binders, telescope, universes, whitespace) | None |
| `s1t` | Free identifiers reduced to their last dot-component (`Nat.Prime` → `Prime`) | None |
| `s1a` | Name-independent: `s1t` + project-local identifiers replaced by positional `L#0, L#1, …` via `Lexicon.resolve_source` | Proof: `294e04cd1ef65e37`; PNT+/FLT/carleson/SpherePacking: per-repo lexicons; library repos (`mathlib4`/`lean4`/`batteries`): none (`s1a == s1t` per `SIGHASH.md` §4) |

Known extraction limits (documented, identical on both sides): no elaboration or name resolution; `@[to_additive]`/`alias`/macro-generated declarations have no source header; anonymous `instance`s and `example`s are skipped; statements containing inline `letI := …; P` are dropped rather than truncated mid-expression.

---

## 3. SQLite Schema (`outputs/flirt/tier2.db`, `leanre.flirt.tier2/2`)

**Guardrail 3 guarantee:** `proof_sigs` stores **hashes, coordinates, and names only** — no proof source text is stored anywhere in `tier2.db`. Only `corpus_sigs.sig_text` carries normalized 1-line headers (<= 400 chars), strictly from the Apache-2.0 public corpora.

```sql
meta(key TEXT PRIMARY KEY, value_json TEXT NOT NULL)
  -- schema, sighash_impl, threads, proof_files, proof_lexicon_id, proof_lexicon_names,
  -- strong_min_tokens, strong_min_tokens_by_variant, strong_ok_by_variant,
  -- fdr_target, fdr_at_threshold, fdr_by_variant, restate_modules, build_seconds, [kernel]

corpora(repo TEXT PK, url, commit_sha, license, lean_toolchain, mathlib_rev, lexicon_id,
        lean_files INT, decls INT)

corpus_sigs(id INT PK, repo, module, line_no INT, kind, name, is_private INT,
            s1n, s1t, s1a, n_tokens INT, n_local INT, sig_text)
  -- indexes: corpus_s1n, corpus_s1t, corpus_s1a, corpus_name

proof_sigs(id INT PK, module, line_no INT, kind, name,
           s1n, s1t, s1a, n_tokens INT, n_local INT)
  -- indexes: proof_module, proof_name, proof_s1n, proof_s1a

matches(proof_id INT, variant TEXT,        -- 's1n' | 's1t' | 's1a'
        sighash TEXT, n_tokens INT,
        grade TEXT,                        -- 'strong' | 'weak' (thm/lemma) | 'defsig' (non-thm)
        n_candidates INT, corpus_id INT,   -- best candidate (deterministic tie-break)
        repo, commit_sha, license, corpus_name,
        same_short_name INT, provenance TEXT,   -- always 'L'
        PRIMARY KEY (proof_id, variant))
  -- indexes: matches_grade(grade, variant), matches_corpus(corpus_id)

match_candidates(proof_id INT, variant TEXT, corpus_id INT,
                 PRIMARY KEY (proof_id, variant, corpus_id)) WITHOUT ROWID
  -- up to 5 top corpus candidates per match

module_summary(module TEXT PK, n_decls INT, n_thm INT,
               n_match_s1n INT, n_match_s1t INT, n_match_s1a INT,
               n_strong INT, n_thm_strong INT, n_strong_s1a INT)

control_sigs(control, proof_id INT, s1n, s1t, s1a, n_tokens INT,
             hit_s1n INT, hit_s1t INT, hit_s1a INT)

control_restate(corpus_id INT PK, n_tokens INT, extracted INT,
                outcome_s1n, outcome_s1t, outcome_s1a)   -- 'tp' | 'fp' | 'fn'

controls(control, variant, min_tokens INT, n INT, tp INT, fp INT, fn INT,
         precision REAL, recall REAL, fpr REAL, note TEXT,
         PRIMARY KEY (control, variant, min_tokens))

-- Convenience read-only view for workbench / queries:
matches_view AS
  SELECT m.proof_id, p.module AS proof_module, p.line_no AS proof_line,
         p.kind AS proof_kind, p.name AS proof_name, p.n_local AS proof_n_local,
         m.variant, m.sighash, m.n_tokens, m.grade, m.n_candidates,
         m.corpus_id, m.repo, m.commit_sha, m.license, m.corpus_name,
         s.module AS corpus_module, s.line_no AS corpus_line, s.kind AS corpus_kind,
         s.n_local AS corpus_n_local, s.sig_text AS corpus_sig_text,
         m.same_short_name, m.provenance
  FROM matches m JOIN proof_sigs p ON p.id=m.proof_id JOIN corpus_sigs s ON s.id=m.corpus_id;

-- Added by `python3 leanre/flirt/tier2.py kernel` over outputs/kernel/kernel.db (§7):
kernel_matches(decl_id INT, const_name TEXT, ckind TEXT, module TEXT,
               live_mask INT, stmt_mask INT, type_nodes INT, sig_size INT, is_aux INT,
               variant TEXT, sighash TEXT, n_candidates INT,
               lib_const_name TEXT, lib_ckind TEXT, lib_origin TEXT,
               lib_repo TEXT, lib_commit_sha TEXT, lib_license TEXT,
               same_short_name INT, provenance TEXT,
               PRIMARY KEY (const_name, variant))

kernel_const_origin(origin TEXT PK, n_consts INT, n_thms INT)
```

---

## 4. Grading Rule & Honest Controls [L]

### Pre-registered per-variant FDR rule

A theorem/lemma match is graded **`strong`** iff `n_tokens >= T_variant` and `strong_ok[variant] == True`, where `T_variant` is the smallest value on the fixed grid `(1, 4, 6, 8, 10, 12, 16, 20, 24, 32)` with **estimated false-discovery rate `FDR_est(variant, T) <= 0.05`**, defined conservatively as:

$$\mathrm{FDR}_{\text{est}}(v, T) = \min\!\left(1,\; \frac{\max(\mathrm{FPR}_{\text{swap}}(v, T),\; \mathrm{FPR}_{\text{perm}}(v, T)) \cdot N_{\text{query}}(T)}{N_{\text{real\_hits}}(v, T)}\right)$$

- **Disclosed history:** Our first draft gated on `FPR <= 0.001`. Because real exact-statement theorem matches have a base rate of $\approx 1.4 \times 10^{-4}$, a $0.03\%$ FPR still yielded mostly chance collisions on 1–4 token signatures. We replaced the rule **once** with `FDR_est <= 0.05` per variant; the resulting thresholds (`s1n >= 6`, `s1t >= 6`, `s1a >= 16`) are computed automatically and never tuned to a desired match count.
- **Non-theorems (`def`, `abbrev`, `structure`, `class`, `instance`, `inductive`)** are always graded **`defsig`** (never `strong`), because two definitions with the same type (e.g. `: Prop` or `(n : ℕ) : ℝ`) share a sighash regardless of their bodies.

### Negative controls (shuffled proof theorem signatures)

Two independent negative controls are generated directly from the real proof theorem signatures (any shuffled signature identical to its original is dropped, not counted):

1. **`neg_swap`** (`n = 817,255` at `T = 1`): pairs each theorem's binder telescope with a different theorem's result type (random derangement per batch) — well-formed-looking signatures with wrong statements. Stresses structural/short-conclusion collisions.
2. **`neg_perm`** (`n = 817,347` at `T = 1`): applies a random bijection over each batch's non-keyword identifier vocabulary. Note what each control stresses: for `s1n`/`s1t`, permuting Mathlib names into project names reduces collisions relative to `swap`; for `s1a`, permuting local names into other local names preserves `L#k` patterns, so taking `max(swap, perm)` is conservative across all three variants.

| Variant | Threshold `T` | `neg_swap` FP / N (FPR) | `neg_perm` FP / N (FPR) | Real thm hits | Est. FDR | Selected? |
|---|---:|---:|---:|---:|---:|---|
| `s1n` | `>= 1` | 60 / 817,255 (`7.3e-5`) | 158 / 817,347 (`1.9e-4`) | 118 | `1.0000` | |
| `s1n` | **`>= 6`** | **0 / 800,635 (`0.0`)** | **0 / 785,205 (`0.0`)** | **90** | **`0.0000`** | **YES (`strong`)** |
| `s1n` | `>= 16` | 0 / 755,298 (`0.0`) | 0 / 766,835 (`0.0`) | 77 | `0.0000` | |
| `s1t` | `>= 1` | 92 / 817,255 (`1.1e-4`) | 241 / 817,347 (`2.9e-4`) | 175 | `1.0000` | |
| `s1t` | **`>= 6`** | **3 / 800,635 (`3.7e-6`)** | **0 / 785,205 (`0.0`)** | **117** | **`0.0251`** | **YES (`strong`)** |
| `s1t` | `>= 12` | 1 / 774,675 (`1.3e-6`) | 0 / 774,222 (`0.0`) | 101 | `0.0099` | |
| `s1t` | `>= 16` | 0 / 755,298 (`0.0`) | 0 / 766,835 (`0.0`) | 95 | `0.0000` | |
| `s1a` | `>= 1` | 5,429 / 817,255 (`6.6e-3`) | 6,763 / 817,347 (`8.3e-3`) | 39,846 | `0.1697` | |
| `s1a` | `>= 6` | 941 / 800,635 (`1.2e-3`) | 324 / 785,205 (`4.1e-4`) | 8,526 | `0.1082` | |
| `s1a` | `>= 12` | 300 / 774,675 (`3.9e-4`) | 24 / 774,222 (`3.1e-5`) | 2,888 | `0.1038` | |
| `s1a` | **`>= 16`** | **0 / 755,298 (`0.0`)** | **0 / 766,835 (`0.0`)** | **150** | **`0.0000`** | **YES (`strong`)** |

Notice how cleanly the per-variant FDR gate separates signal from noise on `s1a`: below 16 tokens, local-name abstraction produces `39,696` `weak` collisions (e.g. `L#0 : Prop`, `∀ x, L#0 x`) with `~10–17%` estimated FDR, all quarantined as `weak`; at `n_tokens >= 16`, both negative controls drop to `0` false positives.

### Held-out synthetic restatement self-match control (`restate_selfmatch`)

A deterministic `1/8` holdout of corpus modules (`1,069` modules, `30,287` corpus theorems) is synthetically restated: new declaration name and namespace, alpha-renamed binders, flipped binder brackets (`()` ↔ `{}`), renamed universes, a random prefix of binders hoisted into `variable`, reflowed whitespace, and an unrelated dummy proof body. The restated text is fed back through the full `extract_decls` + `sig_hashes` pipeline.

*Caveat:* `tp` checks set-membership (`orig_corpus_id in candidates`), so we also report exact **unique-match rate** (`len(candidates) == 1`) and **mean candidate multiplicity** on TPs:

| Variant | Cutoff | N | TP | FP | FN | Precision | Recall | Unique-match rate (on TP) | Mean / Max cands |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `s1n` | `>= 1` | 30,287 | 28,873 | 0 | 1,414 | `1.0000` | `0.9533` | `98.20%` (28,353 / 28,873) | `1.026` / 13 |
| `s1n` | `>= 6` | 30,132 | 28,718 | 0 | 1,414 | `1.0000` | `0.9531` | | |
| `s1t` | `>= 1` | 30,287 | 28,886 | 0 | 1,401 | `1.0000` | `0.9537` | `97.90%` (28,278 / 28,886) | `1.033` / 14 |
| `s1t` | `>= 6` | 30,132 | 28,731 | 0 | 1,401 | `1.0000` | `0.9535` | | |
| `s1a` | `>= 1` | 30,287 | 28,886 | 0 | 1,401 | `1.0000` | `0.9537` | `97.44%` (28,147 / 28,886) | `1.049` / 15 |
| `s1a` | `>= 16` | 29,096 | 27,697 | 0 | 1,399 | `1.0000` | `0.9519` | | |

The ~4.6% FN rate on synthetic restatements comes from edge cases in source-level `variable` reconstruction (e.g. type-level universe-polymorphic `Category.{v₁}` or shadowing between section variables and inner `∏`/`∑` binders) — a deliberate upper bound on source-level recall; real-world recall on rephrased statements is much lower (audited against `kernel.db` in §7).

---

## 5. Real-Data Results on the 175,187-Module Proof Mirror [L]

| Bucket | Proof decls | Distinct sigs | Same short name | Breakdown by corpus |
|---|---:|---:|---:|---|
| **`s1n` strong** (`>= 6` tok) | **90** | 70 | 9 | mathlib4 59, FLT 11, PNT+ 10, carleson 6, lean4 3, SpherePacking 1 |
| **`s1t` strong** (`>= 6` tok) | **117** | 93 | 15 | mathlib4 80, PNT+ 13, FLT 12, carleson 6, lean4 5, SpherePacking 1 |
| **`s1a` strong** (`>= 16` tok) | **150** | 94 | 11 | mathlib4 61, PNT+ 41, FLT 31, carleson 10, lean4 4, SpherePacking 3 (**62 net-new** with `n_local > 0`) |
| `s1n` / `s1t` / `s1a` weak | 28 / 58 / 39,696 | 14 / 23 / 86 | 3 / 7 / 10 | Quarantined below per-variant FDR cutoff |
| `s1n` / `s1t` / `s1a` `defsig` | 42,188 / 42,195 / 43,708 | 307 / 311 / 336 | 28 / 28 / 35 | Non-theorem type-shape matches only (e.g. `: Prop`, `(n : ℕ) : ℝ`) |

Module coverage across `174,968` modules with >= 1 extracted signature (`175,187` total files; `219` files are pure import shims / empty):

| Top-level folder | Modules | Extracted sigs | Strong (`s1n`/`s1t`) | Modules with >= 1 strong |
|---|---:|---:|---:|---:|
| `Development` | 141,842 | 689,867 | 50 | 49 |
| `Formalism` | 18,228 | 239,316 | 43 | 41 |
| `GroundTheory` | 8,506 | 74,114 | 18 | 16 |
| `ReciprocityTheory` | 3,821 | 36,246 | 4 | 4 |
| `CompanionTheory` | 1,956 | 11,739 | 1 | 1 |
| `PositivityTheory` | 445 | 4,712 | 1 | 1 |
| `Lemmata` / `Main` / `Supplements` / `Statements` | 170 | 264 | 0 | 0 |
| **Total** | **174,968** | **1,056,258** | **117** | **112** (`135` incl. `s1a`) |

---

## 6. Concrete Examples — Why Exact vs `s1a` Both Matter [L]

### High-token `s1n` / `s1t` matches (identical normalized statements, zero local abstraction)

- **`mathlib4@0df444a3` `PadicInt.exists_pow_neg_lt`** (`45` tokens) — matched **4 times** across 4 separate proof modules under different names (`GlobalTheory.Cyc.exists_zpow_neg_lt`, `GlobalTheory.FundCont.exists_pow_lt`, `GlobalTheory.ExpImage.IntCoc.exists_pow_lt`, `GroundTheory.Global.Cyclotomic.exists_zpow_neg_lt`).
- **`FLT@01980581` `DimensionTheorem.length_quotient_map_quotient`** (`56` tokens) ↔ `GroundTheory.Heights₂.Heights.Inter.ReducedCut.length_quot_map_mk`.
- **`FLT@01980581` `HenselianLocalRing.of_finite`** (`53` tokens) ↔ `GlobalTheory.henselianLocalRing_of_finite`.
- **`FLT@01980581` `TateCurve.Blueprint.tsum_sq_mul_geometric_of_norm_lt_one`** (`48` tokens) ↔ `GlobalTheory.WpFam.RowReal.tsum_sq_mul_geometric_of_norm_lt_one`.
- **`PrimeNumberTheoremAnd@a4fb6989` `ZetaAppendix.sum_Icc_one_eq_sum_range_succ`** (`47` tokens) ↔ `Formalism.MainNotions.LatticeVariant.sum_Icc_one_eq_range`.
- **`mathlib4@0df444a3` `IsLocalRing.map_ringEquiv_maximalIdeal`** (`56` tokens) ↔ `GlobalTheory.FieldPair.AdjUp.map_maximalIdeal_equiv`.
- **`mathlib4@0df444a3` `MvPowerSeries.hasSubst_of_constantCoeff_zero`** (`56` tokens) ↔ `ReciprocityTheory.ChartRestriction.G.Pdiv.TL.hs_lemma_5`.

### Net-new `s1a` strong matches (`62` decls) — both genuine hits AND shape-only coincidences

1. **Genuine re-proved standard math under different local names:**
   - `PrimeNumberTheoremAnd@a4fb6989` `residue_eq_zero_of_not_pole_of_meromorphicAt` (`34` tok) ↔ `GroundTheory.Global.Elliptic.residue_eq_zero_of_meromorphicOrderAt_nonneg` (same statement about local `residue`).
   - `PrimeNumberTheoremAnd@a4fb6989` `residue_analyticAt_eq_zero` (`26` tok) ↔ `GroundTheory.Global.Elliptic.residue_eq_zero_of_analyticAt`.
   - `PrimeNumberTheoremAnd@a4fb6989` `Complex.zetaTimesSMinusOne_entire_eq_mul_riemannZeta` (`24` tok) ↔ `PI.ZW.zeta1_eq_sub_one_mul_riemannZeta_of_ne_one`.
   - `FLT@01980581` `TateCurve.Blueprint.e_add` / `norm_e` / `e_intMul` (`22–23` tok) ↔ **10+ independent re-definitions** of $e(z)$ (`e`, `ee`, `eu`, `eC`, `expUnit`, `psiC`) across `Development`, `PositivityTheory`, and `ReciprocityTheory`.
2. **Coincidental shape-only matches (why `s1a` match ≠ same mathematics!):**
   - `PrimeNumberTheoremAnd@a4fb6989` `Goldbach.even_conjecture_mono` (`26` tok) ↔ `PositivityTheory.ThKG.Below.mono` — both state "a local predicate on `ℕ` is antitone"; the proof is NOT proving Goldbach's conjecture.
   - `PrimeNumberTheoremAnd@a4fb6989` `BKLNW.C_bk_S_nonneg` (`36` tok) ↔ `Formalism.HermitianLatticeCounting.P.E3cut_nonneg_of_nonneg_of_nonneg` — both state "a 3-argument real function is `>= 0` when args 2 and 3 are `>= 0`".
   - `SpherePacking@e0721587` `ResToImagAxis.Real.mul` (`33` tok) ↔ `GlobalTheory.EisWronskian.Good.mul` — both state "a local predicate on `ℍ → ℂ` is closed under multiplication".

---

## 7. Kernel-Exact Matching & Ground-Truth Audit (`leanre/flirt/tier2_kernel.py`) [L]

Run against `outputs/kernel/kernel.db` (built over full `data/solution.ndjson.zst`, compressed SHA-256 `61a8938a…5381`, uncompressed SHA-256 `5ea74b91…244e`; `1,468,418` decl records, `1,484,733` kernel constants with frozen `k1n`/`k1a` hashes, lexicon `294e04cd1ef65e37`, post-K6 `decl_module` hash `605f7f65…`) in `24.6s`:

### Constant origin partition (explicit counting rule)

| Origin bucket | Rule | All consts [L] | Theorems (`ckind='thm'`) [L] |
|---|---|---:|---:|
| `project` | `decl_module.module IS NOT NULL` | 1,261,940 | 1,069,273 |
| `project_unaligned` | `unmatched:project_*` / `generated:*` / remaining non-library | 8,146 | 5,660 |
| `library_corpus` | Unaligned + exact normalized name in pinned `mathlib4`/`lean4`/`batteries` | 103,623 | 82,272 |
| `library_corpus_aux` | Unaligned + proper dot-prefix in those pinned corpora (e.g. `.mk`, `._proof_`, `._simp_`) | 101,210 | 81,351 |
| `library_other` | Unaligned + external/library prefix (e.g. `@[to_additive]`, `aesop`, `Qq`, core macros) | 9,814 | 7,554 |
| **Total** | | **1,484,733** | **1,246,110** |

### Kernel-exact (`k1n` / `k1a`) project-vs-library matches

| Slice | Project consts [L] | Distinct `k1n` | Same short name | Breakdown |
|---|---:|---:|---:|---|
| **`k1n` named theorems → exact corpus theorem** (`is_aux=0`, `lib_origin='library_corpus'`, `lib_ckind='thm'`) | **127** | **99** | 9 | `mathlib4` 117, `lean4` 10 |
| **`k1n` named theorems → any library theorem** (`is_aux=0`, excl. `._proof_`/`._simp_`/`.eq_N`/`.match_N`) | **173** | **120** | 18 | `mathlib4` 151, `lean4` 13, `library_other` 9 |
| `k1n` all theorems incl. compiler auxiliaries (`is_aux=1`: `._proof_*`, `._simp_*`, etc.) | 77,896 | 1,860 | 59,525 | `mathlib4` 74,657, `lean4` 3,165, `library_other` 69, `batteries` 5 |
| `k1n` non-theorems (`def`/`induct`/`ctor`/`rec` — elaborated type-shape only) | 25,403 | 236 | 652 | `mathlib4` 25,271, `lean4` 112, `library_other` 20 |

- **Why `k1a == k1n` on project-vs-library matches, while collapsing project-vs-project:** Library constants never reference project-local constants, so library `k1a == library k1n`. Inside the proof itself, however, `k1a` collapses **`1,074,933`** hashed project theorems → **`814,259`** distinct `k1n` (`260,674` exact internal statement duplicates) → **`743,120`** distinct `k1a` (`71,139` additional collapses when project-local constants are abstracted).
- **Top named Mathlib theorems re-proved verbatim in the kernel** (`is_aux=0`, `lib_origin='library_corpus'`): `PadicInt.exists_pow_neg_lt` (`×5`, `sig_size=89`), `Complex.two_pi_I_ne_zero` (`×4`, `sig_size=87`), `PadicInt.prime_p` (`×4`, `sig_size=85`), `PowerSeries.HasSubst.of_constantCoeff_zero'` (`×3`, `sig_size=167`), `Complex.norm_exp_I_mul_ofReal` (`×3`, `sig_size=45`), `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app` (`×2`, `sig_size=18,237`), `ModularGroup.denom_apply` (`×2`, `sig_size=2,369`), `AlgebraicGeometry.Scheme.hom_inv_apply` / `inv_hom_apply` (`×2`, `sig_size=711`), `AlgebraicGeometry.isReduced_of_isReduced_stalk` (`×2`, `sig_size=621`), `IsLocalRing.map_ringEquiv_maximalIdeal` (`×2`, `sig_size=425`), plus private Mathlib lemmas `NoetherNormalization.sum_r_mul_ne` (`sig_size=1,509`) and `NoetherNormalization.lt_up` (`sig_size=589`).

### Real-world ground-truth controls (non-synthetic) [L]

| Control | Variant | N | TP | FP | FN | Precision | Recall | What it measures |
|---|---|---:|---:|---:|---:|---:|---:|---|
| `kernel_lib_coverage` | `all_consts` | 214,647 | 204,833 | 0 | 9,814 | `1.0000` | **`0.9543`** | Export library constants covered by pinned `mathlib4`/`lean4`/`batteries` |
| `kernel_lib_coverage` | `thm_only` | 171,177 | 163,623 | 0 | 7,554 | `1.0000` | **`0.9559`** | Export library theorems covered by pinned dependency corpora |
| `kernel_source_recall` | `s1n` (all / `tn>=10`) | 125 / 124 | 38 / 38 | — | 87 / 86 | — | **`0.3040` / `0.3065`** | Real-world recall of `s1n` on kernel-identical (`k1n`) project-vs-corpus theorems |
| `kernel_source_recall` | `s1t` (`strong`, all / `tn>=10`) | 125 / 124 | 51 / 51 | — | 74 / 73 | — | **`0.4080` / `0.4113`** | Real-world recall of `s1t` on kernel-identical (`k1n`) project-vs-corpus theorems |
| `kernel_source_precision` | `s1n_strong` | 41 | 38 | 3 | — | **`0.9268`** | — | Source `s1n` strong matches (both sides in `kernel.db`) that agree on kernel `k1n` |
| `kernel_source_precision` | `s1t_strong` | 56 | 51 | 5 | — | **`0.9107`** | — | Source `s1t` strong matches (both sides in `kernel.db`) that agree on kernel `k1n` |
| `kernel_source_precision` | `s1t_all` (incl. `weak`) | 69 | 51 | 18 | — | `0.7391` | — | Unfiltered `s1t` precision; the `>= 6` FDR gate removes 13/18 real-world FPs |

**Inspection of the 5 real-world `s1t_strong` source FPs** (where source text matched identically, yet kernel `k1n` disagreed):
1. `Chebyshev.theta_nonneg` (`(x : ℝ) : 0 ≤ θ x`) ↔ `MainStatements.WeightKernel.PWeightDiag.θ_nonneg` — **different `θ` constants** (Chebyshev's $\theta$ vs a local weight kernel).
2. `IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers` ↔ `AdeleIntA.memO_lemma` — universe polymorphism (`Type*` in Mathlib vs monomorphic `Type 0` in the proof).
3. `Complex.equivRealProdCLM_symm_apply` ↔ `SiegelWeilFormula.KLI.mer_symm` — elaborated coercion/instance difference.
4. `ChainComplex.next_nat_succ` ↔ `PositivityTheory.KB.NaturalTheta.hnext` — elaborated instance/universe difference.
5. `Fintype.card_units_int` ↔ `Formalism.HC.Frame.natCard_int_units_eq_two` — elaborated `Fintype` instance difference.

This directly demonstrates both the power and the exact empirical limits of source-level matching: **`~91–93%` real-world kernel-verified precision** and **`~41%` real-world recall** (compared to `95.3%` synthetic restatement recall, which only tests cosmetic changes).

---

## 8. Reproduce

```bash
# 1. Clone/verify all 7 pinned corpora and write outputs/flirt/tier2_corpora.json
python3 leanre/flirt/tier2_corpora.py

# 2. Build outputs/flirt/tier2.db + outputs/flirt/tier2_summary.json (capped at 24 threads; ~4 min)
python3 leanre/flirt/tier2.py all --threads 24

# 3. (Once outputs/kernel/kernel.db exists) add kernel-exact k1n/k1a matches + ground-truth audit
python3 leanre/flirt/tier2.py kernel

# 4. Run Tier 2 unit + real-data test suite (23 tests)
python3 -m unittest leanre/test_tier2.py -v
```
