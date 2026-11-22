# `leanre` Forensics & TCB Dossier — Alpöge + Claude Nov 20, 2026 Lean 4 RH/GRH Archive

**Generated:** 2026-11-21 08:11 UTC  
**Pinned Source Mirror:** `Deicyde/riemann-hypothesis@40e56bab026552e089d7afcfeff08d2defb9c005` (`175,187` `.lean` files; unmodified `lean.tar.gz` SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`)  
**Pinned TCB Export:** Andrew Sutherland's `challenge.ndjson.zst` (46,881,299 bytes; SHA-256 `c24ef99dab3556a52c7fb886e03cf22a242f3b96f82ae4cc40539e5d2f678ac6`)  
**Tooling:** `leanre` Python 3.9 stdlib parallel scanner + streaming `7zz` NDJSON v3.1.0 parser (`outputs/leanre.db`, `outputs/forensics_report.json`, `outputs/workbench_bundle.json`)

> **Four-Layer Epistemic Disclaimer (Guardrail 1):** Machine verification certifies *Layer 1 (Kernel Validity)* — formal derivability from Lean's core axioms across independent kernels (`Lean v4.33.1`, `leanchecker`, Rust `nanoda`, `con-leche --compare`, `lean4lean` as of 2026-11-21 `[C]`). This dossier instruments *Layer 2 (Semantic TCB / Specification Fidelity)* and *Layer 3 (Reverse-Engineering & Structural Forensics)*. It does **not** constitute human analytic-number-theory peer review or *Layer 4 (Mathematical / Clay Prize Consensus)*.  
> **Provenance Tags (Guardrail 2):** `[L]` = directly extracted by `leanre` from pinned local `.lean` / `challenge.ndjson.zst` artifacts; `[A]` = Alpöge's 4-page `remark.pdf` (carrying Footnote 4's caveat); `[C]` = third-party verifier/community report (`Sutherland`, `Deicyde`, `drew2apps`, `keithadler`, `nasqret`, `jae-63`); `[S]` = standard published mathematics; `[M]` = CS/RE analogy (paired with limits).  
> **License Compliance (Guardrail 6):** The upstream archive carries no license file. This dossier quotes only declaration identifiers, file paths, statistics, and minimal fair-use 1-line signatures — zero wholesale `.lean` source redistribution.

---

## 1. Acceptance Gates & Exact Ground-Truth Telemetry `[L]`

All **9/9 mandatory acceptance gates PASS** against `drew2apps/rh-lean-decomposition` `[C]` and Sutherland's `con-leche-compare.log` `[C]`:

| Gate | Expected `[C]` | Measured `[L]` | Verdict | Notes |
|---|---:|---:|---|---|
| `modules_175187` | `175,187` | `175,187` | **PASS** |  |
| `project_import_edges_753261` | `753,261` | `753,261` | **PASS** |  |
| `hub_main_theorems_all` | `Supplements.Kernels.MainTheoremsAll` | `Supplements.Kernels.MainTheoremsAll` | **PASS** |  |
| `hub_dominates_175185` | `175,185` | `175,185` | **PASS** | Includes hub itself (175,184 strict descendants + hub = 175,185), matching drew2apps convention. |
| `top_level_components_47060` | `47,060` | `47,060` | **PASS** |  |
| `singleton_components_37001` | `37,001` | `37,001` | **PASS** |  |
| `import_only_shims_150` | `150` | `150` | **PASS** |  |
| `duplicate_project_imports_308` | `308` | `308` | **PASS** | Project-to-project duplicate imports (plus 19,750 duplicate `import Mathlib` lines discovered!). |
| `challenge_decls_51692` | `51,692` | `51,692` | **PASS** |  |

### Phase 1 Hypothesis Falsified by Direct Byte Inspection `[L]`
- In Phase 1 (`02_re_and_tooling_strategy.md`), noticing `17,549,402 - 17,374,215 = 175,187`, we hypothesized that every file lacked a trailing newline.
- **Falsified `[L]`:** Direct byte scan of all `175,187` files shows **`trailing_nl_present = 175,187`** and **`trailing_nl_missing = 0`** (`100.0%` end with `\n`, exact `wc -l` = `17,374,215`, exact bytes = `1,030,531,854`). The `+175,187` delta in `drew2apps` (`17,549,402`) comes from Python's `text.split('\n')` counting the trailing empty string after each file's final `\n`.

### Unexpected Import Hygiene Finding `[L]`
- While project-to-project duplicate imports match `drew2apps` at exactly **`308`**, counting *all* import lines reveals **`19,750` files that repeat `import Mathlib` twice** (`20,058` total duplicate import lines across the tree), on top of `136,003` (`77.6%`) importing wholesale `Mathlib`.

---

## 2. Semantic TCB X-Ray: Inside the 51,692-Declaration `challenge.ndjson.zst` `[L]`

Streaming `data/challenge.ndjson.zst` (`46.88 MB` compressed; `6,495,712` NDJSON v3.1.0 lines; `6,112,241` expression nodes; `1,206,518` declaration-to-declaration edges) exposes the exact trusted specification surface for all 5 headline theorems:

| Metric | Value `[L]` | Security / Audit Meaning |
|---|---:|---|
| Total NDJSON declaration records | `51,692` | Exact match to `con-leche-compare.log` (`51,692`) `[C]`. |
| Kernel-checked theorems (`thm`) | `40,431` (`78.22%`) | Internal well-definedness / coercion proofs inside Mathlib definitions — verified by kernels, **not** semantic trust assumptions. |
| Semantic definitions & axioms (`def`+`inductive`+`opaque`+`quot`+`axiom`) | `11,261` (`21.78%`) | `10,238 def` + `969 inductive` + `46 opaque` + `4 quot` + `4 axiom` (far leaner than Phase 1's 45% guess!). |
| **Pure definition-to-definition cone** (skipping proof bodies) | **`2,570`** | **Only 5.0% of the challenge export** (`0.17%` of the 1.47M-decl solution export) carries direct definitional meaning from the 5 headline statements. |
| Reachable from `riemannHypothesis` type | `51,215` | Full Mathlib closure needed to state classical RH (`riemannZeta`, `Complex`, `MeasureTheory`, `Filter`, ...). |
| Extra declarations for all 3 Dirichlet GRH theorems | **`470`** | Plus `+2` for `riemannZeta_eq_zero_re` / `RiemannZetaZerosOnLine` (`51,215 + 2 + 470 = 51,687` reachable); dominated by one crisp chain: `DirichletCharacter.LFunction` (`279`) → `ZMod.LFunction` (`278`) → `HurwitzZeta.hurwitzZeta` (`237`) → `hurwitzZetaOdd` (`236`) → `completedHurwitzZetaOdd` (`235`) → `hurwitzOddFEPair` (`233`). |
| `sorryAx` reachable from any headline `type` | **`False`** | `sorryAx` has `fan_in = 5` — strictly isolated to the 5 `Challenge.lean` placeholder proof `value` stubs. |
| Unreachable auxiliary `export-targets.txt` primitives | `5` | `sorryAx`, `Nat.lor`, `Nat.xor`, `String.mk`, `String.mk._proof_1` (`51,687 + 5 = 51,692`). |

### Why `con-leche` and `nanoda` Count Different Declaration Totals on One Export `[L]`
- In Lean export format v3.1.0, each `inductive` NDJSON line bundles its inductive types, constructors, and recursors into one record. In `challenge.ndjson.zst`, **`969` `inductive` records** unpack into `969` types + `1059` constructors + `971` recursors = `2,999` environment constants (`53,722` unpacked constants vs `51,692` NDJSON records; delta = `+2,030`). That exact bundling difference explains why `con-leche` counts `1,468,418` records while `nanoda` counts `1,484,733` unpacked constants on Sutherland's identical `solution.ndjson` `[C]`.

### Top Mathlib Namespaces Inside the Statement Closure `[L]`
| Namespace Prefix | Total Decls | Definitions | Theorems | In RH Defs |
|---|---:|---:|---:|---:|
| `_private.Mathlib` | 5,589 | 1,308 | 4,281 | 1,289 |
| `MeasureTheory` | 2,805 | 353 | 2,452 | 353 |
| `Set` | 1,888 | 188 | 1,700 | 187 |
| `Lean` | 1,397 | 543 | 854 | 543 |
| `Filter` | 1,313 | 162 | 1,151 | 162 |
| `List` | 1,167 | 336 | 831 | 336 |
| `Nat` | 1,148 | 301 | 847 | 298 |
| `_private.Init` | 1,109 | 607 | 502 | 604 |
| `Finset` | 950 | 96 | 854 | 96 |
| `Int` | 847 | 182 | 665 | 178 |
| `ENNReal` | 756 | 80 | 676 | 80 |
| `Real` | 735 | 114 | 621 | 114 |

---

## 3. Whole-Corpus Horn Skeleton (Dependency-Injection Circuit) `[L]`

Across all `1,061,425` extracted keyword declarations (`818,755` theorem/lemma + `242,670` def/abbrev/structure/class/instance/inductive/opaque/axiom), `leanre` extracted **`162,961` proposition-to-proposition Horn implications** (`REQUIRES A ⟹ PROVES B`).

Key verified top-spine logical contracts (which file-level import graphs obscure because major engines are passed as hypothesis arguments `[M]` — analogous to indirect function-pointer calls in a binary; note that text-level Horn extraction is heuristic and misses unnamed/unfolded aliases):

| Required Proposition | ⟹ Proved Proposition | Count | Sample Witness Theorem `[L]` | Module `[L]` |
|---|---|---:|---|---|
| `DFamP` | `RiemannHypothesis` | 1 | `Formalism.MainNotions.ZetaZeroFreeRegion.rh_of` | `Formalism.SharpRestriction.GlobalSchurBounds.RamificationTwoAndConjugationAtQAndD` |
| `FamilyCharacterSumBounds` | `RiemannHypothesis` | 1 | `Formalism.MainNotions.ZetaZeroFreeRegion.rh_of` | `Formalism.SharpRestriction.GlobalSchurBounds.RamificationTwoAndConjugationAtQAndD` |
| `FamilyPropTwoSix` | `RiemannHypothesis` | 1 | `Formalism.MainNotions.ZetaZeroFreeRegion.rh_of` | `Formalism.SharpRestriction.GlobalSchurBounds.RamificationTwoAndConjugationAtQAndD` |
| `FamilyTopBoundAbsolute` | `RiemannHypothesis` | 1 | `Formalism.MainNotions.ZetaZeroFreeRegion.rh_of` | `Formalism.SharpRestriction.GlobalSchurBounds.RamificationTwoAndConjugationAtQAndD` |
| `GlobalTheory.CovTop.CovolX` | `UpperTheory.EveryCharacter` | 1 | `UpperTheory.Lit.everyE₂` | `Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.EveryCharacterE` |
| `GlobalTheory.FunPr.Hypotheses₂` | `UpperTheory.EveryCharacter` | 1 | `UpperTheory.Lit.everyE₂` | `Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.EveryCharacterE` |
| `GlobalTheory.GLq.Green` | `BadW` | 2 | `GlobalTheory.BadWOn.badW_of_del_bound_of_T_bound` | `Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadWStOfRegular` |
| `GlobalTheory.GLq.Green` | `Formalism.HC.ZeroFreeAll` | 2 | `UpperTheory.Top.plugWin` | `Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter` |
| `GlobalTheory.GLq.Green` | `GlobalTheory.Fc.TopShape` | 1 | `UpperTheory.Top.shapeWin` | `Development.AutomorphicArithmetic.CharacterBoxes.ShapeWin` |
| `GlobalTheory.GLq.Green` | `GlobalTheory.GLq.IsCuspOf` | 2 | `GlobalTheory.ParamLabel.isCuspOf_cuspOn_of_green` | `Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharIsCuspidalOfMinpolyOfParam` |
| `GlobalTheory.GLq.Green` | `GlobalTheory.LabPin.TypeLab` | 2 | `GlobalTheory.Fc.LabLinked.typeLab_of_gen` | `Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodFtEntries` |
| `GlobalTheory.GLq.Green` | `GoodFTAll` | 6 | `DiscreteGroups.sglob.DzType.Rt.exists_representation_component_alt` | `Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepresentationComponent` |
| `GlobalTheory.GLq.Green` | `GroupRetwisting.LargeBaseConditionG` | 2 | `GlobalTheory.Fc.GoodLinked.eventually_goodRec` | `Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkedBundlesGoodOfLocalLanglands` |
| `GlobalTheory.GLq.Green` | `RL.At` | 6 | `GlobalTheory.Fc.GoodLinked.row_good_atAll` | `Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodFtEntries` |
| `GlobalTheory.GLq.Green` | `Ties` | 4 | `GlobalTheory.Fc.LabLinked.ties_at_wit` | `Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodFtEntries` |
| `GlobalTheory.GLq.Green` | `UpperTheory.EveryCharacter` | 2 | `UpperTheory.Top.every_character_of_green_v_win` | `Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter` |
| `GlobalTheory.GLq.Green` | `_root_.GlobalTheory.Fc.RL.LinkedAt` | 4 | `GlobalTheory.Fc.GoodLinked.linkedAt_goodFTAll` | `Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedBundlesGoodOfLocalLanglands` |
| `GlobalTheory.GLq.Green` | `_root_.GlobalTheory.Fc.TopShapeAlt` | 1 | `UpperTheory.Top.shape_closed_link_n_of_green` | `Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShape` |
| `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching` | `UpperTheory.EveryCharacter` | 2 | `UpperTheory.Lit.everyE₂` | `Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.EveryCharacterE` |
| `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree` | `UpperTheory.EveryCharacter` | 2 | `UpperTheory.Lit.everyE₂` | `Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.EveryCharacterE` |
| `GlobalTheory.Published.LocalLanglandsGL` | `UpperTheory.EveryCharacter` | 1 | `UpperTheory.Lit.everyE₂` | `Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.EveryCharacterE` |
| `Hyps` | `A9` | 2 | `LateralTheory.E.LeafClosedSH0Pf.a9_of_a0_a1_eigenbasis_a6` | `Development.EtaleCohomology.EtaleSheaves.A9OfA0A1EigenbasisA6` |

---

## 4. Deep Forensic Inspection of Slowest & Weirdest Proof Areas `[L]`

### 4.1 The 5 Slowest `con-leche` Declarations (`con-leche-master.log` `[C]` + Local Inspection `[L]`)

Every single one of the 5 slowest kernel-checked declarations in the entire 17.37M-line proof falls into just **two concrete engineering failure modes**:
1. **Dependent `HEq` / `subst` tactic explosion** (`lam_copy` 55.2s, `sigSpan_copy` 40.3s) — 2-to-32-line theorems calling `copy_cases h D D'` on huge dependent structures (`D7`/`CopyAll`) with `maxHeartbeats 4000000` and `maxRecDepth 100000`. Notably, `sigSpan_copy` has a **2-line tactic body** (`copy_cases h D D'; exact hs`) yet takes 40.3 seconds to kernel-check.
2. **Kernel-reduced finite prime computations via `decide +kernel`** (`PI.PC.loop_run` 35.1s, `factorial_ladder_one_forty_one` 25.0s, `GlobalTheory.PrimeRecip.table_ok` 17.2s) — base-case bounds for small `N` (`N < 16,900`, `20,000`, `131,072`) before asymptotic estimates take over.

| Rank | Declaration | `con-leche` `[C]` | Module `[L]` | LOC | Hops to `Main` | Mechanism `[L]` |
|---:|---|---:|---|---:|---:|---|
| 1 | `lam_copy` | **55.2s** | `Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamCopy` | 32 | 18 | HEq/Eq.rec tactic blowup via `copy_cases` destructuring dependent `D7`/`CopyAll` structures |
| 2 | `sigSpan_copy` | **40.3s** | `Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq` | 104 | 16 | HEq/Eq.rec tactic blowup via `copy_cases` destructuring dependent `D7`/`CopyAll` structures |
| 3 | `loop_run` | **35.1s** | `Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop` | 26 | 15 | Strictified (`force`) kernel-reduced prime sieve up to 131,071 via `decide +kernel` (Chebyshev bound) |
| 4 | `factorial_ladder_one_forty_one` | **25.0s** | `Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeRecipSum` | 341 | 10 | Geometric 10%-step prime-reciprocal ladder using `Nat.factorial 141` over 1,024 <= N < 20,000 via `decide +kernel` |
| 5 | `table_ok` | **17.2s** | `Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes` | 312 | 11 | Hardcoded 12-interval prime witness table for 100 <= N < 16,900 checked via `decide +kernel` (misfiled in AbelianVarietyTheory/Proofs/DivisorProofs) |

### 4.2 The 5 `lean4lean` Default-Fuel Timeout Modules `[L]`

All 5 modules that timed out at `lean4lean`'s default step budget (`lean4lean-default-fuel-timeouts.log` `[C]`) are kernel-reduced `decide +kernel` prime sieves:
- **`ChebyshevPrimeBounds.SmallLoop` (`PI.PC.loop_run`, 26 LOC, 15 hops to `Main`):** Defines a custom call-by-value strictness combinator `def force (x : Nat) (f : Nat → Bool)` to prevent exponential lazy-thunk blowup inside Lean's kernel reducer, then executes `loop 362 131070 2 0 1 = true := by decide +kernel` (iterating up to `131,071 ≈ 2^17`, maintaining `Q = ∏_{p ≤ 362} p`, verifying a fixed-point Chebyshev bound).
- **`DyadicPrimeIntervals.Run1–4` (8 LOC each, 13 hops to `Main`):** Shard a `131,070`-step dyadic prime-interval check from `h = 2` to `131,072` powered by `force (Nat.factorial 362)` (`362!`, 771 decimal digits) into four parallel chunks (`Run1`: `32,766` steps `[2..32768]`; `Run2–4`: `32,768` steps each over `[32768..65536]`, `[65536..98304]`, `[98304..131072]`) to fit under per-file heartbeat limits.

### 4.3 Metaprogramming & Elaborator-Bypass Audit (`kexactB`, `kcopy`, `CutCptCopy`, `run_tac`, `BuildAid`) `[L]`

- **`kexactB` (`Imports.lean`, 8 LOC, 9 hops to `Main`):** `Term.elabTermAndSynthesize e none; g.assign (← instantiateMVars v)` — explicitly skips elaborator `isDefEq` checking and delegates type-equality checking entirely to the kernel (faster on gigantic terms). Direct occurrences: **`50` files**; including macro wrappers (`kc%`, `kq%`, `kd%`, `tr_via`, `tr_clause`): **`72` files** (closest is **`6` hops from `Main`**). Soundness is preserved because independent kernels (`nanoda`, `con-leche`, `lean4lean`) re-check every exported term `[C]`.
- **`kcopy` (`OwnStruct.lean`, 66 LOC, 9 hops to `Main`):** Invokes `Kernel.isDefEq` directly inside MetaM to copy fields of `Formalism.*` structures across definitional-equality friction. Found in `4` modules (`6` hits).
- **`CutCptCopy` (`CutCptCopy.lean`, 91 LOC, 17 hops to `Main`):** Programmatically clones `Formalism.FourierDecayAlt.P.*` declarations under new names via `addDecl` (kernel-checked; 2 `addDecl` call sites at lines 78 and 82), remapping 3 theorems to compact-support versions (imported by `CutMainCpt` at 16 hops).
- **`run_tac` / `run_cmd`:** `37` total lines across `21` modules (`32` literal `run_tac` lines across `16` modules + `5` `run_cmd` lines in `BuildAid/D1..D5.lean` adding namespaces to Lean's library-suggestion deny list).
- **Zero Soundness Escape Hatches `[L]`:** Whole-corpus scan confirms **`0` `sorry`**, **`0` custom `axiom`**, **`0` `native_decide`**, **`0` `unsafe`**, and **`0` `implemented_by`/`extern`/`csimp`** across all `175,187` files.
- **Mutual Reflexive Inductive Anchor (`PrincipalizationCertificate.lean`, 107 LOC):** Confirmed `mutual` block declaring `PrincipalizationCertificate` with reflexive constructor parameter — the exact declaration that broke bundled v4.36 `con-leche`/`con-ron` before the `con-leche master` fix `[C]`.

### 4.4 AI Boilerplate & Exact File-Clone Forensics `[L]`
- Alpha-renaming all identifiers and numeric literals across non-import bodies identifies **`1,192` exact structural clone clusters** covering **`4,787` modules** (**`3,595` redundant modules**).
- Largest exact clone cluster: **`385` structurally identical files** (sig `5676a21df7f61489`, avg `6.2` LOC; examples: `CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CayleyHamiltonStatementStatement`, `CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlagFactsStatement`, `CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FubiniParabolicMultipleStatement` — even exhibiting doubled `*StatementStatement` AI naming artifacts!).

---

## 5. Namespace Reality Check: Directory Paths vs Actual Declarations `[L]`

| Library / Folder | Files | `wc -l` Lines | Declarations | Top Actual Inner Declaration Namespaces `[L]` |
|---|---:|---:|---:|---|
| **`Development`** | 141,928 | 12,232,663 | 692,993 | `GlobalTheory.CompanionTheory` (63,243), `_root_.GlobalTheory` (47,590), `UpperTheory.V` (25,807) |
| **`Formalism`** | 18,254 | 3,200,748 | 240,099 | `Formalism.L2` (65,575), `Formalism.MainNotions` (53,796), `Formalism.FourierDecayAlt` (35,397) |
| **`GroundTheory`** | 8,507 | 1,119,138 | 75,102 | `GroundTheory.Heights₂` (37,796), `GroundTheory.Automorphic` (10,968), `GroundTheory.ProfCoh` (6,250) |
| **`ReciprocityTheory`** | 3,845 | 563,016 | 36,446 | `ReciprocityTheory.ChartRestriction` (25,619), `ReciprocityTheory.AnForm` (2,318), `ReciprocityTheory.L2DbarEstimates` (1,863) |
| **`CompanionTheory`** | 2,027 | 194,218 | 11,775 | `GlobalTheory.CompanionTheory` (5,333), `CompanionTheory.D` (1,408), `_root_.GlobalTheory` (524) |
| **`PositivityTheory`** | 449 | 55,130 | 4,746 | `UpperTheory.Esk` (1,232), `UpperTheory.HilbertEisensteinWeightOne` (777), `Ad3.K` (759) |
| **`Lemmata`** | 167 | 9,232 | 251 | `Bl.DualWeylPullback` (8), `Bl.ProductIntegralBounds` (5), `Bl.RankOneOrbitForms` (5) |
| **`BuildAid`** | 5 | 20 | 0 | — |
| **`Supplements`** | 3 | 22 | 4 | `allChi` (1), `rhOfAll` (1), `critAll` (1) |
| **`Main`** | 1 | 12 | 5 | `riemannHypothesis` (1), `riemannZeta_eq_zero_re` (1), `LFunction_ne_zero_of_half_lt_re` (1) |
| **`Statements`** | 1 | 16 | 4 | `RiemannZetaZerosOnLine` (1), `DirichletLNonvanishingRightOfHalf` (1), `DirichletLZerosOnLine` (1) |

### Inside `Development/` (Depth-2 Breakdown — Exposing `AbelianVarietyTheory`) `[L]`

| Subfolder | Files | `wc -l` Lines | Share of Corpus | Top Actual Inner Declaration Namespaces `[L]` |
|---|---:|---:|---:|---|
| `Development.AbelianVarietyTheory` | 99,187 | 8,142,960 | 56.6% | `_root_.GlobalTheory` (39,212), `GlobalTheory.IndefiniteRowSideFullHecke` (14,165), `GlobalTheory.Mem` (11,592) |
| `Development.AutomorphicArithmetic` | 18,431 | 1,776,375 | 10.5% | `UpperTheory.V` (25,804), `UpperTheory.Gal` (8,967), `UpperTheory.ConvolutionTheory` (4,982) |
| `Development.AutomorphicSpectrum` | 15,147 | 1,195,844 | 8.6% | `GlobalTheory.CompanionTheory` (62,415), `_root_.GlobalTheory` (6,388), `PositivityTheory.Rg` (18) |
| `Development.WeilBound` | 7,051 | 848,547 | 4.0% | `PositivityTheory.Rg` (13,342), `PositivityTheory.SiegelWeilFormula` (4,208), `PositivityTheory.RgUd` (2,474) |
| `Development.EtaleCohomology` | 1,398 | 104,525 | 0.8% | `LateralTheory.E` (4,636), `LateralTheory.CohomologicalPurity` (1,547), `LateralTheory.EtaleFoundations` (1,374) |
| `Development.ResolutionOfSingularities` | 499 | 140,709 | 0.3% | `FunctorialResolution.EmbeddedResolution` (7,021), `FunctorialResolution.Blowup` (304), `AlgebraicGeometry.Scheme` (41) |
| `Development.DiscreteGroups` | 215 | 23,703 | 0.1% | `DiscreteGroups.sglob` (1,142), `DiscreteGroups.T1` (231), `PositivityTheory.Rg` (6) |

---

## 6. BinDiff v1 Structural Baseline (`leanre diff` Ready) `[L]`

Alpöge predicts the proof *"will be massively simplified, likely immediately"* `[A]`. `outputs/forensics_report.json` embeds a deterministic `bindiff_v1` baseline:
- **Snapshot SHA-256:** `92f18596bb1fcf6f93f2ffd31e30e6deadee9b4c83a60694a2350d8e7ea969fe`
- **Top-100 Dominators Digest:** `137bd40f7c6641802b3adde8239bbe9f05b3333dd91081e3de0b425537a051f7`
- **Namespaces Digest:** `6d6c4d764b5ac5212916a8fca2cde16d79bac96608d69acfdef42d9e76f2beb7`
- **Horn Spine Digest:** `68a35b96d5bc570ae713a0b7204248d90ada24e2b5af6961ef89ce5171b7d515`
- **TCB Shallow Definitions Digest:** `3748e2826374ff1493de142a96ba04a27822c2e082671ba546537bfac182cdd2`

Reproduce or diff against a future simplified v2 release:
```bash
python3 leanre/leanre.py all --src data/rh_mirror/src --ndjson data/challenge.ndjson.zst --out-dir outputs/
python3 leanre/leanre.py diff outputs/forensics_report.json outputs/forensics_report_v2.json
```
