# Proof size, virtual stripping, and macro blowup

Virtual stripping removes unused files, dead intra-file declarations, 1-node renaming shells, clones, and duplicate imports from the `175,187`-file, `17,374,215`-line corpus (`1,468,414` live declarations; `2,472,831,289` `value_nodes`). The surviving core estimate is **`105,918` files (`60.46%`)**, **`12,904,172` lines (`74.27%`; conservative non-blank `13,063,244`)**, and **`1,310,025` declarations** (`1,100,417` project [`707,036` user + `393,381` compiler auxiliaries] plus `209,608` Mathlib/Lean library declarations; see [the trim report](../docs/TRIM.md)).

## Disjoint virtual stripping waterfall

| Stage | `.lean` files | `wc -l` lines | Live decls | Live `value_nodes` |
|---|---:|---:|---:|---:|
| Raw corpus and kernel export | `175,187` | `17,374,215` | `1,468,414` | `2,472,831,289` |
| Minus unused zero-kernel files | `-28,885` | `-2,376,906` | `0` | `0` |
| Minus dead declarations in live files | `0` | `-1,089,514` (`-979,578` non-blank) | `0` | `0` |
| Minus `value_nodes == 1` alias wrappers | `-38,481` | `-493,849` | `-43,261` | `-43,261` |
| Minus surviving clones and `k1n` duplicates | `-1,903` | `-509,506` | `-115,128` | `-106,842,294` |
| Minus surviving duplicate `import` lines | `0` | `-268` | `0` | `0` |
| **Irreducible core estimate** | **`105,918`** | **`12,904,172`** (`13,063,244` non-blank) | **`1,310,025`** | **`2,365,945,734`** |

## Breakdown of removed lines

- `28,885` unused zero-kernel files (`2,376,906` lines) drop first, keeping the `19` live alignment-gap files inside the `146,302` surviving modules; `28,471` are imported-but-unused code such as the dead [`run1`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run1.lean#L6)..[`run4`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/Run4.lean#L6) prime checks.
- `115,829` dead declarations sit inside `17,984` live modules (`1,089,514` block / `979,578` non-blank lines: `69,044` `theorem`, `36,873` `def`, `3,345` `example`). Extreme outliers include [a 6,333-line oscillatory-integral file](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/CuspSpanNormBounds/OscillatoryIntegralBounds.lean#L38) (`515` dead vs `17` live decls; `5,459` lines dead) and [a 2,178-line re-export hub](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/HermitianCurvature/HeisenbergConjugationMeasurePreserving.lean#L374) (`1,416` dead re-exports vs `102` live).
- `43,135` `value_nodes == 1` project `thm` forwarding aliases (`38,194` `GlobalTheory.T.*` plus `4,941` across other namespaces) and `126` `def`s delete `38,481` pure-alias files (`481,328` lines) and `4,308` inline spans (`12,521` lines).
- Those deleted pure-alias wrapper files also account for `13,583` of the corpus's `19,750` (`68.77%`) duplicate `import Mathlib` lines (`6,030` sit in unused files and `14` in clone/duplicate files), leaving only `123` Mathlib plus `145` project (`268` total) duplicate imports in the surviving core.
- After removing unused files and alias shells, `571` surviving alpha-body file clones (`32,781` lines) and `54,510` redundant user `thm` proofs across `30,055` [type-identical (`k1n`)](../docs/SIGHASH.md) clusters (`111,965` decls including exclusive auxiliaries; `476,725` lines) account for the final half-million trimmed lines.

## Bloat kept outside the waterfall

Two additional bloat sources stay outside the five waterfall steps because stripping them changes signatures or requires re-elaboration:

- `3,530` surviving signature-set clones (`130,243` lines across `15,574` raw [signature-abstracted (`s1a`)](../docs/SIGHASH.md) clusters) match modulo project-local type renaming rather than exact alpha-equivalence.
- Unread fields in live hypothesis bundles still drag proved subtrees into `solution.ndjson.zst`: [`cm_abelian_inputs_from_literature`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TopMainZj.lean#L59) pulls `907` dominated decls (`1,650,550` `value_nodes`, `254` exclusive `.lean` files, `13,166` lines) into an unread `LiteratureCMHypothesis` field, and `43` of `5,497` live single-constructor project structures have zero named projections in the export.
- `1,656` of the `115,829` kernel-absent declarations inside live files are `abbrev`s that may unfold during elaboration, and `2` of the `11` zero-kernel meta files (`CutCptCopy`, `HeckeNonvanishing.Imports`) execute during elaboration for live callers.

## Macro proof-term blowup

Source line counts understate kernel size where elaboration macros expand large terms (`copy_cases`, `kcopy`, and `cpt_copy_thms`):

- [`copy_cases`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RingSpecNormalisedCharacterEq.lean#L75) inflates 32-line [`lam_copy`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamCopy.lean#L15) to `5,538,373` `value_nodes` (`173,074` nodes/line) and [`sigSpan_copy`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RingSpecNormalisedCharacterEq.lean#L97) to `4,598,428` (`10,136,801` combined, `0.41%` of the export).
- Command macro [`cpt_copy_thms`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean#L87) (invoked in [the compact-cut module](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutMainCpt.lean#L945)) synthesizes `5` live `*Cpt` theorems (`6,253` `value_nodes`), and tactic [`kcopy`](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean#L53) drives `444` live decls (`470,706` `value_nodes`) across `3` live files.

<details>
<summary>Verify locally</summary>

```bash
python3 leanre/leanre.py trim --from-report outputs/decomp/trim_report.json
```

</details>
