# RH 2026 — Compact (76k)

Compact Apache-2.0 rewriting of the Alpöge–Claude RH & Dirichlet GRH formalization from lsernau/grh-lean (grh-compact/).

## Provenance & Scope

- **Repository:** [https://github.com/lsernau/grh-lean](https://github.com/lsernau/grh-lean)
- **Pinned commit:** `72fead102f66` (`72fead102f663d5c7a407964a13dc0cf9d977207`)
- **License:** Apache-2.0
- **Analysis mode:** Source-level import and declaration scan (no compiled kernel export)
- **Entry module:** `Main` (reaches **794 / 794** modules, **100.0%**)

## Scale & Composition

| Metric | Value |
| --- | ---: |
| Lean modules | 794 |
| Lines of code | 112,827 |
| Project import edges | 1,398 |
| Declarations (source) | 10,943 |
| Theorems / lemmas | 7,088 |
| Defs / abbrevs / instances | 3,604 |
| Inductives / structures / classes | 251 |
| Custom `axiom` declarations | 0 |
| `sorry` / `admit` hits | 0 (0 files) |
| `decide +kernel` hits | 3 |

## Repository Notes & Caveats

- Comparator layout: challenge/statement files (`ComparatorChallenges/` / `*Challenge*.lean`) intentionally hold `sorry` placeholders separated from proof modules.

## Axioms, Incomplete Proofs, and Kernel Directives

### `decide +kernel`: 3 hits in 3 files

- [Lib.GaloisRep.Main.SplitPlaceCount:L27](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/Main/SplitPlaceCount.lean#L27) — `IsSplitPrimeToDisc.exists_place_above_ne`
- [Lib.Shimura.IntegralModel.NeatLevel:L200](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/IntegralModel/NeatLevel.lean#L200) — `_anon_198`
- [New.Exchange.DeterminantVectors:L138](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/DeterminantVectors.lean#L138) — `surjOn_cone_integral_detVectors`

## Duplication & Directory Alignment

- **Directory-vs-namespace outliers:** 356 files (44.8%; 13 high, 343 medium)
- **Identical-body file clones:** 0 clusters
- **Identical-signature file clusters:** 0 clusters
- **Import-only shims:** 0

## Most-Imported Modules (Top 10)

| Module | Direct Importers | Transitive Importers | Lines | Declarations |
| --- | ---: | ---: | ---: | ---: |
| [Lib.General.LinearAlgebra.Base](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/LinearAlgebra/Base.lean#L1) | 11 | 792 | 155 | 31 |
| [Lib.Cohomology.Etale.TestRings](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cohomology/Etale/TestRings.lean#L1) | 7 | 173 | 79 | 13 |
| [Lib.Shimura.IntegralModel.NeatLevel](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/IntegralModel/NeatLevel.lean#L1) | 6 | 153 | 338 | 41 |
| [Lib.Adelic.Witt.FrameAction](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Witt/FrameAction.lean#L1) | 6 | 437 | 190 | 29 |
| [Lib.General.LinearAlgebra.CommonEigenvectors](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/LinearAlgebra/CommonEigenvectors.lean#L1) | 6 | 466 | 133 | 12 |
| [Lib.General.Analysis.OstrowskiTaussky](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Analysis/OstrowskiTaussky.lean#L1) | 6 | 682 | 106 | 16 |
| [Lib.General.Groups.ValuationPair](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Groups/ValuationPair.lean#L1) | 5 | 608 | 398 | 78 |
| [New.Seesaw.IndexTypes](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/IndexTypes.lean#L1) | 5 | 80 | 314 | 73 |
| [Lib.Weil.Unramified.SphericalHecke](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Unramified/SphericalHecke.lean#L1) | 5 | 259 | 258 | 39 |
| [Lib.Weil.DualPair.PairSumNegation](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/DualPair/PairSumNegation.lean#L1) | 5 | 140 | 250 | 33 |
