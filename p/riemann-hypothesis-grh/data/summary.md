# RH 2026 — Readable (grh / main)

Readable Apache-2.0 RH & Dirichlet GRH formalization on leanprover-community/riemann-hypothesis main (based on lsernau/grh-lean grh/), cleanly partitioned into src/Lib (background missing from Mathlib) and src/New (the RH/GRH proof argument).

## Provenance & Scope

- **Repository:** [https://github.com/leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
- **Pinned commit:** `2fc633272442` (`2fc633272442a664eb260b76151c6e4e474c6b0b`)
- **License:** Apache-2.0
- **Analysis mode:** Source-level import and declaration scan (no compiled kernel export)
- **Entry module:** `Main` (reaches **802 / 802** modules, **100.0%**)

## Scale & Composition

| Metric | Value |
| --- | ---: |
| Lean modules | 802 |
| Lines of code | 476,438 |
| Project import edges | 1,731 |
| Declarations (source) | 23,791 |
| Theorems / lemmas | 18,185 |
| Defs / abbrevs / instances | 5,117 |
| Inductives / structures / classes | 489 |
| Custom `axiom` declarations | 0 |
| `sorry` / `admit` hits | 0 (0 files) |
| `decide +kernel` hits | 3 |

## Repository Notes & Caveats

- Comparator layout: challenge/statement files (`ComparatorChallenges/` / `*Challenge*.lean`) intentionally hold `sorry` placeholders separated from proof modules.

## Axioms, Incomplete Proofs, and Kernel Directives

### `decide +kernel`: 3 hits in 2 files

- [Lib.Shimura.HeckeTower.HeckeData:L526](https://github.com/leanprover-community/riemann-hypothesis/blob/2fc633272442a664eb260b76151c6e4e474c6b0b/src/Lib/Shimura/HeckeTower/HeckeData.lean#L526) — `New.Variety._anon_521`
- [Lib.GaloisRep.Main.QuadraticStep:L113](https://github.com/leanprover-community/riemann-hypothesis/blob/2fc633272442a664eb260b76151c6e4e474c6b0b/src/Lib/GaloisRep/Main/QuadraticStep.lean#L113) — `New.GaloisRep.IsSplitPrimeToDisc.exists_place_above_ne`
- [Lib.GaloisRep.Main.QuadraticStep:L114](https://github.com/leanprover-community/riemann-hypothesis/blob/2fc633272442a664eb260b76151c6e4e474c6b0b/src/Lib/GaloisRep/Main/QuadraticStep.lean#L114) — `New.GaloisRep.IsSplitPrimeToDisc.exists_place_above_ne`

## Duplication & Directory Alignment

- **Directory-vs-namespace outliers:** 93 files (11.6%; 5 high, 88 medium)
- **Identical-body file clones:** 0 clusters
- **Identical-signature file clusters:** 0 clusters
- **Import-only shims:** 0

## Most-Imported Modules (Top 10)

| Module | Direct Importers | Transitive Importers | Lines | Declarations |
| --- | ---: | ---: | ---: | ---: |
| [Lib.Base](https://github.com/leanprover-community/riemann-hypothesis/blob/2fc633272442a664eb260b76151c6e4e474c6b0b/src/Lib/Base.lean#L1) | 20 | 799 | 17 | 1 |
| [Lib.Shimura.Uniformisation.HolomorphicFamilies](https://github.com/leanprover-community/riemann-hypothesis/blob/2fc633272442a664eb260b76151c6e4e474c6b0b/src/Lib/Shimura/Uniformisation/HolomorphicFamilies.lean#L1) | 11 | 249 | 978 | 51 |
| [Lib.General.NumberTheory.PadicLimitsValuation](https://github.com/leanprover-community/riemann-hypothesis/blob/2fc633272442a664eb260b76151c6e4e474c6b0b/src/Lib/General/NumberTheory/PadicLimitsValuation.lean#L1) | 11 | 189 | 369 | 29 |
| [Lib.Cohomology.Etale.Basic](https://github.com/leanprover-community/riemann-hypothesis/blob/2fc633272442a664eb260b76151c6e4e474c6b0b/src/Lib/Cohomology/Etale/Basic.lean#L1) | 10 | 483 | 1,211 | 137 |
| [Lib.General.Groups.CongruenceSubgroups](https://github.com/leanprover-community/riemann-hypothesis/blob/2fc633272442a664eb260b76151c6e4e474c6b0b/src/Lib/General/Groups/CongruenceSubgroups.lean#L1) | 10 | 711 | 481 | 67 |
| [New.UpperBound.Objects.Rows](https://github.com/leanprover-community/riemann-hypothesis/blob/2fc633272442a664eb260b76151c6e4e474c6b0b/src/New/UpperBound/Objects/Rows.lean#L1) | 9 | 82 | 874 | 57 |
| [Lib.General.LinearAlgebra.Eigenvalues](https://github.com/leanprover-community/riemann-hypothesis/blob/2fc633272442a664eb260b76151c6e4e474c6b0b/src/Lib/General/LinearAlgebra/Eigenvalues.lean#L1) | 9 | 348 | 785 | 31 |
| [Lib.General.Analysis.HolomorphicIntegrals](https://github.com/leanprover-community/riemann-hypothesis/blob/2fc633272442a664eb260b76151c6e4e474c6b0b/src/Lib/General/Analysis/HolomorphicIntegrals.lean#L1) | 9 | 543 | 691 | 32 |
| [Lib.General.LinearAlgebra.BlockEmbeddings](https://github.com/leanprover-community/riemann-hypothesis/blob/2fc633272442a664eb260b76151c6e4e474c6b0b/src/Lib/General/LinearAlgebra/BlockEmbeddings.lean#L1) | 9 | 148 | 407 | 28 |
| [Lib.Shimura.HeckeTower.HeckeData](https://github.com/leanprover-community/riemann-hypothesis/blob/2fc633272442a664eb260b76151c6e4e474c6b0b/src/Lib/Shimura/HeckeTower/HeckeData.lean#L1) | 8 | 200 | 1,000 | 73 |
