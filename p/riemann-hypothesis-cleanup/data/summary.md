# RH 2026 — Community Cleanup (alpoge)

Community refactoring and consolidation of the Alpöge–Claude RH & Dirichlet GRH formalization preserved on the alpoge branch of leanprover-community/riemann-hypothesis.

## Provenance & Scope

- **Repository:** [https://github.com/leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
- **Pinned commit:** `d91ae2678eea` (`d91ae2678eea19a0c3045ffca37f1da757c2e719`)
- **License:** None (no license)
- **Analysis mode:** Source-level import and declaration scan (no compiled kernel export)
- **Entry module:** `Main` (reaches **59,248 / 59,261** modules, **100.0%**)

## Scale & Composition

| Metric | Value |
| --- | ---: |
| Lean modules | 59,261 |
| Lines of code | 14,561,196 |
| Project import edges | 366,045 |
| Declarations (source) | 735,474 |
| Theorems / lemmas | 575,503 |
| Defs / abbrevs / instances | 153,695 |
| Inductives / structures / classes | 6,276 |
| Custom `axiom` declarations | 0 |
| Proof `sorry` / `admit` hits | 0 (0 files) |
| Challenge-spec `sorry` hits | 5 (1 file) |
| `decide +kernel` hits | 19 |

## Repository Notes & Caveats

- Comparator layout: challenge/statement files (`ComparatorChallenges/` / `*Challenge*.lean`) intentionally hold `sorry` placeholders separated from proof modules.

## Axioms, Incomplete Proofs, and Kernel Directives

### Challenge-spec `sorry`: 5 hits in 1 file

- [Challenge:L19](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Challenge.lean#L19) — `riemannHypothesis`
- [Challenge:L21](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Challenge.lean#L21) — `riemannZeta_eq_zero_re`
- [Challenge:L23](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Challenge.lean#L23) — `LFunction_ne_zero_of_half_lt_re`
- [Challenge:L25](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Challenge.lean#L25) — `LFunction_eq_zero_re`
- [Challenge:L27](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Challenge.lean#L27) — `LFunction_eq_zero_re_of_isPrimitive`

### `decide +kernel`: 19 hits in 11 files

- [Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve:L155](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsVariableChangeEqLatticeCurve.lean#L155) — `GlobalTheory.g₃_eq_E₆`
- [Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsPolynomialModularJOfHasQExpansion:L101](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsPolynomialModularJOfHasQExpansion.lean#L101) — `GlobalTheory.qExpansion_E₄`
- [Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsPolynomialModularJOfHasQExpansion:L110](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsPolynomialModularJOfHasQExpansion.lean#L110) — `GlobalTheory.qExpansion_E₆`
- [Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ValuationCharacters.ConstOfFinite:L41](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/ValuationCharacters/ConstOfFinite.lean#L41) — `UpperTheory.V.Ws.redM_key`
- [Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ValuationCharacters.ConstOfFinite:L44](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/ValuationCharacters/ConstOfFinite.lean#L44) — `UpperTheory.V.Ws.redT_ex`
- [Formalism.LocalRingCardinality.SpanPowerMembership.Primes:L606](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L606) — `Formalism.BasicNotions.Examples₂.BB_disj0`
- [Formalism.LocalRingCardinality.SpanPowerMembership.Primes:L608](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L608) — `Formalism.BasicNotions.Examples₂.BB_disj0`
- [Formalism.LocalRingCardinality.SpanPowerMembership.Primes:L609](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L609) — `Formalism.BasicNotions.Examples₂.BB_disj0`
- [Formalism.LocalRingCardinality.SpanPowerMembership.Primes:L610](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L610) — `Formalism.BasicNotions.Examples₂.BB_disj0`
- [Formalism.LocalRingCardinality.SpanPowerMembership.Primes:L613](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L613) — `Formalism.BasicNotions.Examples₂.BB_disj0`
- [ReciprocityTheory.DualLattices.QExpansionMonoWCoeffZero:L36](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/ReciprocityTheory/DualLattices/QExpansionMonoWCoeffZero.lean#L36) — `ReciprocityTheory.PGsh.qExpansion_E₄_eq`
- [ReciprocityTheory.DualLattices.QExpansionMonoWCoeffZero:L43](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/ReciprocityTheory/DualLattices/QExpansionMonoWCoeffZero.lean#L43) — `ReciprocityTheory.PGsh.qExpansion_E₆_eq`
- [Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimes:L76](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean#L76) — `GlobalTheory.PrimeRecip.intervals_checked`
- [Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary:L180](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LatticeInvariantsPeriodPairDictionary.lean#L180) — `discr_of_cyclic`
- [Formalism.PieriBlockIdeals.PieriColumnMinors.CorollaryOfParamsSevenLinkageAlt:L318](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Formalism/PieriBlockIdeals/PieriColumnMinors/CorollaryOfParamsSevenLinkageAlt.lean#L318) — `PI.PC.loop_run`
- … and 4 more

## Duplication & Directory Alignment

- **Directory-vs-namespace outliers:** 6,102 files (10.3%; 1,038 high, 5,064 medium)
- **Identical-body file clones:** 112 clusters (300 redundant files)
- **Identical-signature file clusters:** 411 clusters (3,039 redundant files)
- **Import-only shims:** 0

## Most-Imported Modules (Top 10)

| Module | Direct Importers | Transitive Importers | Lines | Declarations |
| --- | ---: | ---: | ---: | ---: |
| [ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsCompletedStrictHens.lean#L1) | 1,136 | 32,571 | 39 | 7 |
| [Formalism.LocalToGlobal.IndefiniteReal.LinksDefs](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Formalism/LocalToGlobal/IndefiniteReal/LinksDefs.lean#L1) | 973 | 11,331 | 711 | 108 |
| [Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean#L1) | 892 | 30,412 | 1,334 | 154 |
| [ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/CubicalStructures/CubeSymmetricSwapFirst.lean#L1) | 802 | 32,687 | 201 | 40 |
| [Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean#L1) | 714 | 5,450 | 597 | 97 |
| [Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/GenusMassVolumes.lean#L1) | 602 | 25,281 | 406 | 73 |
| [Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Formalism/LocalToGlobal/IndefiniteReal/LocalNewformFunction.lean#L1) | 590 | 14,492 | 330 | 58 |
| [ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/GlobalSectionsRankAlgClosed.lean#L1) | 538 | 16,403 | 223 | 26 |
| [Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L1) | 536 | 19,245 | 134 | 16 |
| [ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull](https://github.com/leanprover-community/riemann-hypothesis/blob/d91ae2678eea19a0c3045ffca37f1da757c2e719/src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBPull.lean#L1) | 518 | 16,127 | 150 | 7 |
